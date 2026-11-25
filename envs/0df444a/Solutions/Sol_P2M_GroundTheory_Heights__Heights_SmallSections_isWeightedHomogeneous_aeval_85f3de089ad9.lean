-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SmallSections_isWeightedHomogeneous_aeval_85f3de089ad9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:17:00.353324+00:00
-- url     : https://prove2.me/submissions/a1a297e1-0c16-4e2e-901c-2158083460b7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SmallSections
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.SmallSections
theorem _root_.solution {σ : Type*} {F : MvPolynomial σ ℤ} {τ : ℕ} (hF : F.IsHomogeneous τ)
    {g : σ → MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hg : ∀ j, IsWeightedHomogeneous (coordDeg n) (g j) δ) :
    IsWeightedHomogeneous (coordDeg n) (aeval g F) (τ • δ) := by
  rw [F.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun μ hμ ↦ ?_
  have hw : (μ.sum fun _ e ↦ e) = τ := by
    have h := hF (mem_support_iff.mp hμ)
    rw [Finsupp.weight_apply] at h
    simpa using h
  have h := IsWeightedHomogeneous.prod μ.support (fun i ↦ g i ^ μ i) (fun i ↦ μ i • δ)
    (fun i _ ↦ (hg i).pow (μ i))
  rw [← hw, Finsupp.sum, Finset.sum_smul, aeval_monomial, algebraMap_eq]
  exact h.C_mul _
end GroundTheory.Heights₂.Heights.SmallSections
