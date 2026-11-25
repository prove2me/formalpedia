-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_traceHerm_apply_77d67d8cde12
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:28.269801+00:00
-- url     : https://prove2.me/submissions/72ceb498-57fd-42f7-8212-6bd3bf1e9e3f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StTraceHermNondegenerate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W) (y z : ι → E) :
    traceHerm h v y z = Algebra.trace ℚ E (h.toSesq (v.equivFun.symm y) (v.equivFun.symm z)) := rfl
end GroundTheory.Heights₂.Heights.FiniteCovolume
