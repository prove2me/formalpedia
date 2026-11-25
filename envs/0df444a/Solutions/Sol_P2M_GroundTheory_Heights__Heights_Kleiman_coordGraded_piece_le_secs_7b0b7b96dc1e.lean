-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_coordGraded_piece_le_secs_7b0b7b96dc1e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:03:05.970384+00:00
-- url     : https://prove2.me/submissions/4f241e3e-9d64-458a-9c03-15820a1d7ede

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistSections

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (y : Fin (N + 1) → Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (n : ℕ) :
    (coordGraded S y).piece (n : ℤ) ≤ (twistSys S y (n : ℤ)).secs := by
  change Submodule.span S _ ≤ _
  rw [Submodule.span_le]
  rintro _ ⟨f, e, hf, he, rfl⟩
  simp only [SetLike.mem_coe, SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem]
  intro I
  exact Submodule.subset_span ⟨f, 1, 0, e, one_mem _, hf, isHomogeneous_one _ _, by simp [he],
    by simp⟩
end GroundTheory.Heights₂.Heights.Kleiman
