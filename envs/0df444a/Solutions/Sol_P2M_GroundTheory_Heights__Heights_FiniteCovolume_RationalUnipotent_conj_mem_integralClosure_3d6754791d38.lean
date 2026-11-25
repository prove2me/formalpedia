-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_conj_mem_integralClosure_3d6754791d38
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:08:37.718867+00:00
-- url     : https://prove2.me/submissions/f37454af-0225-42ef-b569-d3473480fb42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StRationalUnipotent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PRationalUnipotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
open GroundTheory.Heights₂.Heights.FiniteCovolume.RationalUnipotent
omit [NumberField E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.RationalUnipotent
theorem _root_.solution {c : E} (hc : c ∈ integralClosure ℤ E) :
    conj F E c ∈ integralClosure ℤ E :=
  (mem_integralClosure_iff ℤ E).2
    (((mem_integralClosure_iff ℤ E).1 hc).map (conj F E).toAlgHom.toRingHom.toIntAlgHom)
end GroundTheory.Heights₂.Heights.FiniteCovolume.RationalUnipotent
