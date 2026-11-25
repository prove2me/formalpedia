-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_RestrictGen_resid_add_fecc8d372056
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:47:04.497826+00:00
-- url     : https://prove2.me/submissions/2bb2eaae-b0ec-4160-b711-c8dfedbd5e27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsRestLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ResidOfMem
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_RestrictGen_resid_of_mem_862f94617fb4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial
noncomputable section
variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {K' : Type} [Field K'] [Algebra F K']
  (R : Subalgebra F Ω) (σ : R →ₐ[F] K')
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
namespace RestrictGen
theorem _root_.solution {a b : Ω} (ha : a ∈ R) (hb : b ∈ R) :
    RestrictGen.resid R σ (a + b) = RestrictGen.resid R σ a + RestrictGen.resid R σ b := by
  rw [RestrictGen.resid_of_mem R σ ha, RestrictGen.resid_of_mem R σ hb,
    RestrictGen.resid_of_mem R σ (add_mem ha hb), ← map_add]
  rfl
end RestrictGen
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
