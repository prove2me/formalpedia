-- Prove2me | solution 1 for PI.VolStabSW.FiniteFieldSplitting.card_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:11:05.249911+00:00
-- url     : https://prove2.me/submissions/e3c51086-29c3-4423-9d7b-d70ffa57c52d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFS
import Theorems.Thm_PI_VolStabSW_FiniteFieldSplitting_linInd_of_left_inv
import Theorems.Thm_PI_VolStabSW_FiniteFieldSplitting_card_left_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.FiniteFieldSplitting
open Matrix
variable {k : Type} [Field k] [Finite k]
namespace PI.VolStabSW.FiniteFieldSplitting
theorem _root_.solution {M a : ℕ} (ha : a ≤ M) :
    Nat.card {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} =
      (∏ i : Fin a, (Nat.card k ^ M - Nat.card k ^ (i : ℕ))) * Nat.card k ^ (a * (M - a)) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  let e : {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} ≃
      Σ P : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)},
        {W : Matrix (Fin a) (Fin M) k // W * P.1 = 1} :=
    { toFun := fun x ↦ ⟨⟨x.1.2, linInd_of_left_inv x.1.1 x.1.2 x.2⟩, ⟨x.1.1, x.2⟩⟩
      invFun := fun y ↦ ⟨(y.2.1, y.1.1), y.2.2⟩
      left_inv := fun x ↦ rfl
      right_inv := fun y ↦ rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp_rw [fun P : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)} ↦
    card_left_inv P.1 P.2]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  congr 1
  let e2 : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)} ≃
      {s : Fin a → Fin M → k // LinearIndependent k s} :=
    { toFun := fun P ↦ ⟨cols P.1, P.2⟩
      invFun := fun s ↦ ⟨fun i j ↦ s.1 j i, s.2⟩
      left_inv := fun P ↦ rfl
      right_inv := fun s ↦ rfl }
  rw [← Nat.card_eq_fintype_card, Nat.card_congr e2, card_linearIndependent
    (by rw [Module.finrank_fin_fun]; exact ha), Module.finrank_fin_fun, Nat.card_eq_fintype_card]
end PI.VolStabSW.FiniteFieldSplitting
