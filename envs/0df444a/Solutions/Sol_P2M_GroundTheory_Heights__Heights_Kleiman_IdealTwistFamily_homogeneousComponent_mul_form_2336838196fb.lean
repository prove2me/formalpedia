-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_homogeneousComponent_mul_form_2336838196fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:17:31.441893+00:00
-- url     : https://prove2.me/submissions/93fb50b5-3d33-4a8d-9649-5815cbfbc9d7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily
variable {R : Type u} [CommRing R] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily
theorem _root_.solution (r g : Poly R N) {d : ℕ} (hg : g.IsHomogeneous d) (e : ℕ) :
    homogeneousComponent e (r * g) ∈ Submodule.span R
      {z | ∃ (h : Poly R N) (d' : ℕ), h.IsHomogeneous d' ∧ d' + d = e ∧ z = h * g} := by
  rw [show r * g = ∑ i ∈ Finset.range (r.totalDegree + 1), homogeneousComponent i r * g by
    rw [← Finset.sum_mul, sum_homogeneousComponent], map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hm : homogeneousComponent i r * g ∈ homogeneousSubmodule (Fin (N + 1)) R (i + d) :=
    (mem_homogeneousSubmodule _ _).mpr ((homogeneousComponent_isHomogeneous i r).mul hg)
  rw [homogeneousComponent_of_mem hm]
  split_ifs with h
  · exact Submodule.subset_span ⟨_, i, homogeneousComponent_isHomogeneous i r, h.symm, rfl⟩
  · exact Submodule.zero_mem _
end GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily
