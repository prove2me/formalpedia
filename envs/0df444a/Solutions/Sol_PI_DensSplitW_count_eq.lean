-- Prove2me | solution 1 for PI.DensSplitW.count_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:43:12.557998+00:00
-- url     : https://prove2.me/submissions/b8cd5a1a-4b68-4c30-ab67-ce627fb59bcd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_FiberCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_PhiXFinrankRange
import Theorems.Thm_PI_DensSplitW_cond_iff
import Theorems.Thm_PI_DensSplitW_phiX_surj
import Theorems.Thm_PI_DensSplitW_phiX_finrank_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.L2.SG.DensExact
open PI PI.DensSplitW
namespace PI.DensSplitW
theorem _root_.solution (hF : FiberCard) (K : Type) [Field K] [Fintype K] (n m : ℕ)
    (Ph : Matrix (Fin n) (Fin n) K) (Gm : Matrix (Fin m) (Fin m) K) (hPh : IsUnit Ph.det) :
    countSplit K n m Ph Gm = Nat.card {X : Fin m → Fin n → K // LinearIndependent K X} *
      (Fintype.card K ^ (Gm.rank * (n - m)) *
        ∏ i ∈ range (m - Gm.rank), (Fintype.card K ^ (n - m) - Fintype.card K ^ i)) := by
  classical
  have hfib : ∀ X : {X : Fin m → Fin n → K // LinearIndependent K X},
      Nat.card {Y : Fin m → Fin n → K // LinearIndependent K Y ∧
        ∀ i j, ∑ k, ∑ l, X.1 i k * Ph k l * Y j l = Gm i j} =
      Fintype.card K ^ (Gm.rank * (n - m)) *
        ∏ i ∈ range (m - Gm.rank), (Fintype.card K ^ (n - m) - Fintype.card K ^ i) := by
    intro X
    have e : {Y : Fin m → Fin n → K // LinearIndependent K Y ∧
          ∀ i j, ∑ k, ∑ l, X.1 i k * Ph k l * Y j l = Gm i j} ≃
        {Y : Fin m → Fin n → K // LinearIndependent K Y ∧ ∀ j, phiX Ph X.1 (Y j) = Gm.transpose j} :=
      Equiv.subtypeEquivRight (fun Y => and_congr_right_iff.mpr (fun _ => cond_iff Ph Gm X.1 Y))
    rw [Nat.card_congr e, hF K (Fin n → K) (Fin m → K) (phiX Ph X.1) (phiX_surj Ph hPh X.1 X.2)
      m Gm.transpose, phiX_finrank_ker Ph hPh X.1 X.2]
    have hr : Module.finrank K (Submodule.span K (Set.range (Gm.transpose : Fin m → Fin m → K))) =
        Gm.rank := by
      rw [Matrix.rank_eq_finrank_span_cols]
      rfl
    rw [hr]
  unfold countSplit
  rw [← Nat.card_coe_set_eq]
  have e2 : ↥{XY : (Fin m → Fin n → K) × (Fin m → Fin n → K) | LinearIndependent K XY.1 ∧
        LinearIndependent K XY.2 ∧ ∀ i j, ∑ k, ∑ l, XY.1 i k * Ph k l * XY.2 j l = Gm i j} ≃
      Σ X : {X : Fin m → Fin n → K // LinearIndependent K X},
        {Y : Fin m → Fin n → K // LinearIndependent K Y ∧
          ∀ i j, ∑ k, ∑ l, X.1 i k * Ph k l * Y j l = Gm i j} :=
    { toFun := fun s =>
        have hs : LinearIndependent K s.1.1 ∧ LinearIndependent K s.1.2 ∧
            ∀ i j, ∑ k, ∑ l, s.1.1 i k * Ph k l * s.1.2 j l = Gm i j := s.2
        ⟨⟨s.1.1, hs.1⟩, ⟨s.1.2, hs.2⟩⟩
      invFun := fun s => ⟨(s.1.1, s.2.1), by exact ⟨s.1.2, s.2.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e2, Nat.card_sigma, Finset.sum_congr rfl (fun X _ => hfib X),
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
end PI.DensSplitW
