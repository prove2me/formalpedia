-- Prove2me | solution 1 for SupLatW.covBy_supLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:55:01.931446+00:00
-- url     : https://prove2.me/submissions/5903c05e-9bc1-4ba3-bbfa-2d9adccdc2c6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_FGTorsionFreeGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSupremumLine_EqSupLatOfCovBy
import Theorems.Thm_SupLatW_mem_stdLat_iff
import Theorems.Thm_SupLatW_alg_ne_zero
import Theorems.Thm_SupLatW_inv_smul_mem_iff
import Theorems.Thm_SupLatW_dvd_of_not_isUnit

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
    (x : Fin r → R) (hx : ∃ i, ¬ ϖ ∣ x i) : stdLat R K r ⋖ supLat R K ϖ x := by
  have hv : (algebraMap R K ϖ)⁻¹ • vecK R K x ∉ stdLat R K r := by
    rw [inv_smul_mem_iff hϖ]
    push Not
    exact hx
  have hw : algebraMap R K ϖ * (algebraMap R K ϖ)⁻¹ = 1 := mul_inv_cancel₀ (alg_ne_zero hϖ)
  unfold supLat
  rw [covBy_iff_lt_and_eq_or_eq]
  refine ⟨SetLike.lt_iff_le_and_exists.mpr ⟨le_sup_left, _,
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _), hv⟩, ?_⟩
  intro C h1 h2
  by_cases hC : C ≤ stdLat R K r
  · exact Or.inl (le_antisymm hC h1)
  · right
    refine le_antisymm h2 (sup_le h1 ?_)
    rw [Submodule.span_singleton_le_iff_mem]
    obtain ⟨c, hcC, hcL⟩ := SetLike.not_le_iff_exists.mp hC
    obtain ⟨l, hl, q, hq, hsum⟩ := Submodule.mem_sup.mp (h2 hcC)
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hq
    have hs : IsUnit s := by
      by_contra hs
      obtain ⟨t, rfl⟩ := dvd_of_not_isUnit hϖ hs
      apply hcL
      rw [← hsum]
      refine Submodule.add_mem _ hl ?_
      have e : (ϖ * t) • ((algebraMap R K ϖ)⁻¹ • vecK R K x) = vecK R K (t • x) := by
        funext i
        simp only [vecK, Pi.smul_apply]
        simp only [smul_eq_mul]
        simp only [Algebra.smul_def, map_mul]
        linear_combination (algebraMap R K t * algebraMap R K (x i)) * hw
      rw [e, mem_stdLat_iff]
      exact ⟨_, rfl⟩
    have e : (algebraMap R K ϖ)⁻¹ • vecK R K x = (↑hs.unit⁻¹ : R) • (c - l) := by
      rw [← hsum, add_sub_cancel_left, smul_smul, hs.val_inv_mul, one_smul]
    rw [e]
    exact C.smul_mem _ (C.sub_mem hcC (h1 hl))
end SupLatW
