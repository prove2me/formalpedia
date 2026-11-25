-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_modelToFrac_injective_32d3a043c434
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:38:16.451591+00:00
-- url     : https://prove2.me/submissions/f40e95bb-d647-4820-ac90-c642d51c9717

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalisationModelLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PNormalisationModelLocalizationX

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
open MvPolynomial ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.NormalisationModelLocalization
variable {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
variable (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
variable {M}
variable (M)
namespace GroundTheory.Heights₂.Heights.NormalisationModelLocalization
theorem _root_.solution (hJ : J.IsPrime) (hq : q ∈ zeroSet J) : Function.Injective (modelToFrac M hJ hq) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [modelToFrac_mk, ← RingHom.mem_ker, ker_toFracModel hJ hq] at hx
  exact Ideal.Quotient.eq_zero_iff_mem.2 hx
end GroundTheory.Heights₂.Heights.NormalisationModelLocalization
