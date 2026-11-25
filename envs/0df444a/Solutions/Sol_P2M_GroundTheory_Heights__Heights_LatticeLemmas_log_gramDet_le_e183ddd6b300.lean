-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_log_gramDet_le_e183ddd6b300
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:39:47.546641+00:00
-- url     : https://prove2.me/submissions/6efbbfab-f08e-4ab9-864e-392ebaf59ede

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamard
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_det_gram_re_le_prod_norm_sq_50acf4657243

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open GroundTheory.Heights₂.Heights InnerProductSpace
universe u v w
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution (h : HermitianMetric K E) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {s : ι → E} (hs : LinearIndependent (𝓞 K) s) :
    Real.log (gramDet h σ s) ≤ 2 * ∑ i, Real.log ‖fibreVec h σ (s i)‖ := by
  let e := Fintype.equivFin ι
  have hs' : LinearIndependent (𝓞 K) (s ∘ e.symm) := hs.comp _ e.symm.injective
  have hne : ∀ i, fibreVec h σ (s i) ≠ 0 := (linearIndependent_fibreVec h σ hs).ne_zero
  have hH := det_gram_re_le_prod_norm_sq (fun i ↦ fibreVec h σ ((s ∘ e.symm) i))
    (linearIndependent_fibreVec h σ hs')
  rw [← gramDet_reindex h σ e.symm s]
  calc Real.log (gramDet h σ (s ∘ e.symm))
      ≤ Real.log (∏ i, ‖fibreVec h σ ((s ∘ e.symm) i)‖ ^ 2) :=
        Real.log_le_log (gramDet_pos h σ hs') hH
    _ = 2 * ∑ i, Real.log ‖fibreVec h σ ((s ∘ e.symm) i)‖ := by
        rw [Real.log_prod (s := Finset.univ) (f := fun i ↦ ‖fibreVec h σ ((s ∘ e.symm) i)‖ ^ 2)
          (fun i _ ↦ pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne (e.symm i)))), Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Real.log_pow]
        push_cast
        ring
    _ = 2 * ∑ i, Real.log ‖fibreVec h σ (s i)‖ := by
        congr 1
        exact e.symm.sum_comp (fun i ↦ Real.log ‖fibreVec h σ (s i)‖)
end GroundTheory.Heights₂.Heights.LatticeLemmas
