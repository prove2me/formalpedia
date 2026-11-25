-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementForm_proof_bdb227fda16c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:41:53.833565+00:00
-- url     : https://prove2.me/submissions/1fd394a1-efa6-4c69-87c9-8af31d7b66c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open GroundTheory.Automorphic Module
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace ComplementForm
theorem _root_.solution (h : HermitianForm F E W) : ComplementForm.Statement h :=
  fun v w hp => ⟨ComplementForm.form h v w hp, fun _ _ => rfl⟩
end ComplementForm
end GroundTheory.Heights₂.Heights.FiniteCovolume
