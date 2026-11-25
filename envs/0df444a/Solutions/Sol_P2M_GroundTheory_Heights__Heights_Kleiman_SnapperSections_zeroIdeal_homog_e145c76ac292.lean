-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_zeroIdeal_homog_e145c76ac292
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:38:46.469378+00:00
-- url     : https://prove2.me/submissions/8b6ae6b4-1858-4a44-a2c9-7affb5a781cd

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
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperSections
theorem _root_.solution (D : SubSystem k x Ω) (s : Ω) :
    ∀ f ∈ zeroIdeal D s, ∀ d : ℕ, homogeneousComponent d f ∈ zeroIdeal D s := by
  have hJ : (zeroIdeal D s).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) k) :=
    Ideal.homogeneous_span _ _ fun f ⟨c, hf, _⟩ => ⟨c, (mem_homogeneousSubmodule c f).mpr hf⟩
  intro f hf d
  have h := hJ d hf
  have hc : (DirectSum.decompose (homogeneousSubmodule (Fin (N + 1)) k) f d : Poly k N) =
      homogeneousComponent d f := decomposition.decompose'_apply f d
  rwa [hc] at h
end GroundTheory.Heights₂.Heights.Kleiman.SnapperSections
