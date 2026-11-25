-- Prove2me | solution 1 for SupLatW.eq_supLat_of_covBy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:55:06.714676+00:00
-- url     : https://prove2.me/submissions/901fdca3-8fe2-4939-ac3b-b060b00fda04

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_FGTorsionFreeGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSupremumLine_EqSupLatOfCovBy
import Theorems.Thm_SupLatW_mem_stdLat_iff
import Theorems.Thm_SupLatW_alg_ne_zero
import Theorems.Thm_SupLatW_inv_smul_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SupLatW
open Formalism.MainNotions.Ext.CutC
namespace SupLatW
theorem _root_.solution {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) {r : ℕ}
    (M : Submodule R (Fin r → K)) (hM : stdLat R K r ⋖ M) :
    ∃ x : Fin r → R, (∃ i, ¬ ϖ ∣ x i) ∧ M = supLat R K ϖ x := by
  have h0 := alg_ne_zero (K := K) hϖ
  obtain ⟨m, hmM, hmL⟩ := SetLike.exists_of_lt hM.lt
  have hpm : ϖ • m ∈ stdLat R K r := by
    rcases (covBy_iff_lt_and_eq_or_eq.mp hM).2 (stdLat R K r ⊔ Submodule.span R {ϖ • m})
        le_sup_left
        (sup_le hM.le ((Submodule.span_singleton_le_iff_mem _ _).mpr (M.smul_mem _ hmM)))
      with h | h
    · rw [← h]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    · exfalso
      have hm' : m ∈ stdLat R K r ⊔ Submodule.span R {ϖ • m} := by rw [h]; exact hmM
      obtain ⟨l, hl, q, hq, hsum⟩ := Submodule.mem_sup.mp hm'
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hq
      have hu : IsUnit (1 - t * ϖ) := by
        rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (t * ϖ) with h' | h'
        · exact absurd (isUnit_of_mul_isUnit_right h') hϖ.not_isUnit
        · exact h'
      apply hmL
      have e : (1 - t * ϖ) • m = l := by
        rw [sub_smul, one_smul, mul_smul]
        exact (eq_sub_of_add_eq hsum).symm
      have e2 : m = (↑hu.unit⁻¹ : R) • l := by
        rw [← e, smul_smul, hu.val_inv_mul, one_smul]
      rw [e2]
      exact Submodule.smul_mem _ _ hl
  obtain ⟨z, hz⟩ := (mem_stdLat_iff _).mp hpm
  have hm : m = (algebraMap R K ϖ)⁻¹ • vecK R K z := by
    rw [← hz]
    funext i
    simp only [Pi.smul_apply]
    simp only [smul_eq_mul]
    simp only [Algebra.smul_def]
    rw [inv_mul_cancel_left₀ h0]
  have hz' : ∃ i, ¬ ϖ ∣ z i := by
    by_contra hn
    push Not at hn
    apply hmL
    rw [hm]
    exact (inv_smul_mem_iff hϖ z).mpr hn
  refine ⟨z, hz', ?_⟩
  have hle : supLat R K ϖ z ≤ M := by
    unfold supLat
    exact sup_le hM.le ((Submodule.span_singleton_le_iff_mem _ _).mpr (hm ▸ hmM))
  rcases (covBy_iff_lt_and_eq_or_eq.mp hM).2 (supLat R K ϖ z) le_sup_left hle with h | h
  · exfalso
    apply hmL
    rw [← h, hm]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · exact h.symm
end SupLatW
