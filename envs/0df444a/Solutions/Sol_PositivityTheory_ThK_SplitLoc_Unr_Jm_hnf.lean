-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.Jm_hnf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:50:55.370951+00:00
-- url     : https://prove2.me/submissions/acd0959e-2ff3-4c1d-8280-f1da905d8234

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_sum_comp_surj
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_hermRed_surjective
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_dvd_hermMat_sub
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_finite_hermIdx
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_exists_hermGL
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_ord_gdet_of_mem_coset
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_Jm_eq_inter
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_Jm_eq_sum
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_cosetInt_congr
import Theorems.Thm_GlobalTheory_Doubling_IsRightSmooth_continuous
import Theorems.Thm_GlobalTheory_IwahoriInj_Inj_trans
import Theorems.Thm_GlobalTheory_SatakeBound_card_hermIdx
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SplitFlip_IsUnif_irreducible
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitLoc.Unr
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) {n : ℕ} {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _)
    (hs : ∀ x, φ x ≠ 0 → ∀ i j, x i j ∈ 𝒪[k]) (M : ℕ)
    (hp : ∀ x y : Matrix (Fin n) (Fin n) k, (∀ i j, valuation k (y i j) ≤ valuation k (ϖ : k) ^ M) → φ (x + y) = φ x) :
    ∃ T : (Fin n → ℕ) → ℂ,
      (∀ a, T a = (∏ i : Fin n, ((resCard k : ℂ) ^ (n - 1 - (i : ℕ))) ^ (a i - M)) * T (fun i => min (a i) M)) ∧
      (∀ m : ℤ, m < 0 → Jm n φ m = 0) ∧ ∀ t : ℕ, Jm n φ t = ∑ a ∈ Finset.piAntidiag Finset.univ t, T a := by
  classical
  have hfin : ∀ a : Fin n → ℕ, Finite (GlobalTheory.SatakeBound.HermIdx (⟨ϖ, hϖ.mem⟩ : 𝒪[k]) a) :=
    finite_hermIdx hϖ.irreducible
  let _ : ∀ a : Fin n → ℕ, Fintype (GlobalTheory.SatakeBound.HermIdx (⟨ϖ, hϖ.mem⟩ : 𝒪[k]) a) := fun a => Fintype.ofFinite _
  refine ⟨fun a => ∑ c, cosetInt φ (GlobalTheory.SatakeBound.hermGL hϖ.irreducible a c).val, fun a => ?_, fun m hm => ?_,
    Jm_eq_sum hϖ hφ.1.continuous hs⟩
  · have hr : Nat.card (GlobalTheory.SatakeBound.HermIdx (⟨ϖ, hϖ.mem⟩ : 𝒪[k]) a) =
        (∏ i : Fin n, (resCard k ^ (n - 1 - (i : ℕ))) ^ (a i - M)) *
          Nat.card (GlobalTheory.SatakeBound.HermIdx (⟨ϖ, hϖ.mem⟩ : 𝒪[k]) fun i => min (a i) M) := by
      rw [GlobalTheory.SatakeBound.card_hermIdx hϖ.irreducible, GlobalTheory.SatakeBound.card_hermIdx hϖ.irreducible,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← pow_add]
      congr 1
      omega
    have key := sum_comp_surj _ (hermRed_surjective _ a M) hr
      fun d => cosetInt φ (GlobalTheory.SatakeBound.hermGL hϖ.irreducible _ d).val
    push_cast at key
    refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) key
    exact cosetInt_congr hϖ hp (dvd_hermMat_sub _ a M c)
  · rw [Jm_eq_inter hs, show dShell n m ∩ {g : GL (Fin n) k | ∀ i j, g.val i j ∈ 𝒪[k]} = ∅ from ?_,
      setIntegral_empty]
    refine Set.eq_empty_of_forall_notMem fun g hg => ?_
    obtain ⟨a, c, h⟩ := exists_hermGL hϖ.irreducible hg.2
    have h1 := (ord_gdet_of_mem_coset hϖ h).symm.trans hg.1
    omega
end PositivityTheory.ThK.SplitLoc.Unr
