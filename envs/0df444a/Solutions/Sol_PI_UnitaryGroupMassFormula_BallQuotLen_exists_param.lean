-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BallQuotLen.exists_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:36:47.189365+00:00
-- url     : https://prove2.me/submissions/e57cf1b0-67ab-47c3-b8cd-b0951288b4ed

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Formalism_PeriodIntegrals_BallQuotLen
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BallQuotientLength_LengthBallQuotientEqSumMulFdeg
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_vL_add
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_vL_eq_addVal
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_vL_eq_zero_iff
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_vL_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BallQuotLen
open Formalism.MainNotions.Gaps.EtaleWeightGaps IsLocalRing
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {A : Type*} [CommRing A] [Algebra O A] {ϖ : O}
namespace PI.UnitaryGroupMassFormula.BallQuotLen
theorem _root_.solution [Finite (Pts O A)] (ζ₀ : Pts O A) [IsDVRAt ζ₀] :
    ∃ t : ↥(As O A), vL ζ₀ t = 1 ∧ ∀ ζ : Pts O A, ζ ≠ ζ₀ → t ∉ ζ.asIdeal := by
  classical
  haveI := Fintype.ofFinite (Pts O A)
  haveI : IsDomain (Loc ζ₀) := IsDVRAt.isDomain
  haveI : IsDiscreteValuationRing (Loc ζ₀) := IsDVRAt.isDVR
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Loc ζ₀)
  obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.mk'_surjective ζ₀.asIdeal.primeCompl π
  have hva : vL ζ₀ a = 1 := by
    rw [vL_eq_addVal]
    have e1 : algebraMap _ (Loc ζ₀) a = π * algebraMap _ (Loc ζ₀) (s : ↥(As O A)) := by
      rw [← has, IsLocalization.mk'_spec]
    obtain ⟨u, hu⟩ := IsLocalization.map_units (Loc ζ₀) s
    rw [e1, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_uniformizer hπ, ← hu,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit, add_zero]
  have h1 : ∀ x ∈ ζ₀.asIdeal, 1 ≤ vL ζ₀ x := by
    intro x hx
    rw [ENat.one_le_iff_ne_zero]
    intro h0
    exact ((vL_eq_zero_iff (ζ := ζ₀) x).mp h0) hx
  have h2 : ∀ x ∈ ζ₀.asIdeal ^ 2, 2 ≤ vL ζ₀ x := by
    intro x hx
    rw [sq] at hx
    refine Submodule.mul_induction_on hx (fun p hp q hq => ?_) (fun x y hx hy => ?_)
    · rw [vL_mul]
      calc (2 : ℕ∞) = 1 + 1 := by norm_num
        _ ≤ _ := add_le_add (h1 p hp) (h1 q hq)
    · exact le_trans (le_min hx hy) (vL_add (ζ := ζ₀) x y)
  have hcop : ζ₀.asIdeal ^ 2 ⊔ ⨅ ζ ∈ (Finset.univ.filter (· ≠ ζ₀)), ζ.asIdeal = ⊤ := by
    refine Ideal.sup_iInf_eq_top (fun ζ hζ => ?_)
    have hne : ζ₀.asIdeal ≠ ζ.asIdeal := by
      intro heq
      exact (Finset.mem_filter.mp hζ).2 (MaximalSpectrum.ext heq).symm
    have hc : IsCoprime ζ₀.asIdeal ζ.asIdeal :=
      Ideal.isCoprime_iff_sup_eq.mpr (ζ₀.isMaximal.coprime_of_ne ζ.isMaximal hne)
    exact Ideal.isCoprime_iff_sup_eq.mp (hc.pow_left (m := 2))
  have hone : (1 : ↥(As O A)) ∈ ζ₀.asIdeal ^ 2 ⊔ ⨅ ζ ∈ (Finset.univ.filter (· ≠ ζ₀)), ζ.asIdeal := by
    rw [hcop]
    exact Submodule.mem_top
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp hone
  have hjmem : ∀ ζ : Pts O A, ζ ≠ ζ₀ → j ∈ ζ.asIdeal := by
    intro ζ hz
    simp only [Submodule.mem_iInf] at hj
    exact hj ζ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩)
  refine ⟨a * j + i, ?_, ?_⟩
  · have hj' : j = 1 - i := eq_sub_of_add_eq' hij
    have ht : a * j + i = a + i * (1 - a) := by rw [hj']; ring
    have hr : 2 ≤ vL ζ₀ (i * (1 - a)) := by
      rw [vL_mul]
      exact le_trans (h2 i hi) le_self_add
    have hlt : vL ζ₀ a < vL ζ₀ (i * (1 - a)) := by
      rw [hva]
      exact lt_of_lt_of_le (by norm_num) hr
    rw [ht, vL_eq_addVal, map_add, AddValuation.map_add_of_distinct_val, ← vL_eq_addVal,
      ← vL_eq_addVal, min_eq_left hlt.le, hva]
    rw [← vL_eq_addVal, ← vL_eq_addVal]
    exact hlt.ne
  · intro ζ hz ht
    have hi' : i ∈ ζ.asIdeal := by
      have := ζ.asIdeal.sub_mem ht (ζ.asIdeal.mul_mem_left a (hjmem ζ hz))
      simpa using this
    have : (1 : ↥(As O A)) ∈ ζ.asIdeal := by
      rw [← hij]
      exact ζ.asIdeal.add_mem hi' (hjmem ζ hz)
    exact ζ.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr this)
end PI.UnitaryGroupMassFormula.BallQuotLen
