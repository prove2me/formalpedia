-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_idealMod_sup_le_eb914758f1ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:28:40.684508+00:00
-- url     : https://prove2.me/submissions/0d610343-283d-40f1-910e-70fbc319c899

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_MulQuotEqSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionNonvanishSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionMulInjSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutZeroNotLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AssemblyBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperSection

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
open GroundTheory.Heights₂.Heights.Kleiman.SnapperSections
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperSections
theorem _root_.solution (pp pp' : Ideal (Poly k N)) (hh : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp)
    (hh' : ∀ f ∈ pp', ∀ d : ℕ, homogeneousComponent d f ∈ pp') (I : Chart x) :
    idealMod (x := x) (pp ⊔ pp') I ≤ idealMod (x := x) pp I ⊔ idealMod (x := x) pp' I := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, m, e, hf, hm, hfe, hme, rfl⟩
  obtain ⟨g, hg, z, hz, hgz⟩ := Submodule.mem_sup.mp hf
  have hfe' : f = homogeneousComponent e g + homogeneousComponent e z := by
    rw [← map_add, hgz, homogeneousComponent_eq_self hfe]
  rw [SetLike.mem_coe, hfe', map_add, add_div]
  exact Submodule.add_mem_sup
    (Submodule.subset_span ⟨_, m, e, hh g hg e, hm, homogeneousComponent_isHomogeneous _ _, hme, rfl⟩)
    (Submodule.subset_span ⟨_, m, e, hh' z hz e, hm, homogeneousComponent_isHomogeneous _ _, hme, rfl⟩)
end GroundTheory.Heights₂.Heights.Kleiman.SnapperSections
