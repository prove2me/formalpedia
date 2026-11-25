-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_blockSum_nonneg_b0b5b7ed1f1e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:25:42.269122+00:00
-- url     : https://prove2.me/submissions/e1799ba1-ee76-45c4-a358-0606f947c8ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finite_support_blockFin_1d8804ad44af
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_log_places_eq_zero_ae84c0a90009

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {K : Type*} [Field K] [NumberField K]
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (y : Cone n K) (k : ι) (hy : y k ≠ 0) : 0 ≤ blockSum y k := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hy
  have ht : y k i0 ≠ 0 := hi0
  have hfin := finite_support_blockFin y k hy
  have hfin2 : (Function.support fun v : FinitePlace K ↦ Real.log (v (y k i0))).Finite := by
    refine Set.Finite.subset (FinitePlace.hasFiniteMulSupport ht) fun v hv h ↦ hv ?_
    simp only [h, Real.log_one]
  classical
  let T := hfin.toFinset ∪ hfin2.toFinset
  have e1 : ∑ᶠ v, blockFin y k v = ∑ v ∈ T, blockFin y k v :=
    finsum_eq_sum_of_support_subset _ fun v hv ↦ by
      simp only [T, Finset.coe_union, Set.mem_union, Finset.mem_coe, hfin.mem_toFinset]
      exact Or.inl hv
  have e2 : ∑ᶠ v : FinitePlace K, Real.log (v (y k i0)) = ∑ v ∈ T, Real.log (v (y k i0)) :=
    finsum_eq_sum_of_support_subset _ fun v hv ↦ by
      simp only [T, Finset.coe_union, Set.mem_union, Finset.mem_coe, hfin2.mem_toFinset]
      exact Or.inr hv
  have hle1 : ∑ v ∈ T, Real.log (v (y k i0)) ≤ ∑ v ∈ T, blockFin y k v :=
    Finset.sum_le_sum fun v _ ↦ Real.log_le_log (FinitePlace.pos_iff.mpr ht)
      (le_ciSup (f := fun i ↦ v (y k i)) (Set.finite_range _).bddAbove i0)
  have hle2 : ∑ σ : K →+* ℂ, Real.log ‖σ (y k i0)‖ ≤
      ∑ σ : K →+* ℂ, Real.log (l2Norm fun i ↦ σ (y k i)) :=
    Finset.sum_le_sum fun σ _ ↦ Real.log_le_log (norm_pos_iff.mpr ((map_ne_zero σ).mpr ht))
      (norm_le_l2Norm (fun i ↦ σ (y k i)) i0)
  have h0 := sum_log_places_eq_zero ht
  unfold blockSum
  rw [e1]
  rw [e2] at h0
  linarith
end GroundTheory.Heights₂.Heights
