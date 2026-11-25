-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_sup_span_X_homogeneous_29e7ce851657
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:23:25.129838+00:00
-- url     : https://prove2.me/submissions/fea947ff-62a1-4eb8-a8d3-cec68937333d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneMidSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplane
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_homogeneousComponent_mul_form_2336838196fb


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
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {R : Type u} [CommRing R] {N : ℕ} (pp : Ideal (Poly R N))
    (hh : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) (i : Fin (N + 1)) :
    ∀ f ∈ pp ⊔ Ideal.span {(X i : Poly R N)}, ∀ d : ℕ,
      homogeneousComponent d f ∈ pp ⊔ Ideal.span {(X i : Poly R N)} := by
  intro f hf d
  obtain ⟨g, hg, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  rw [map_add]
  refine Ideal.add_mem _ (Ideal.mem_sup_left (hh g hg d)) (Ideal.mem_sup_right ?_)
  have hspan := IdealTwistFamily.homogeneousComponent_mul_form r (X i) (isHomogeneous_X R i) d
  refine (Submodule.span_le.mpr ?_ : _ ≤ (Ideal.span {(X i : Poly R N)}).restrictScalars R) hspan
  rintro _ ⟨z, d', -, -, rfl⟩
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
end GroundTheory.Heights₂.Heights.Kleiman
