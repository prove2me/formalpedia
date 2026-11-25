-- Prove2me | solution 1 for ReciprocityTheory.Gal.resGal_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:00:54.334538+00:00
-- url     : https://prove2.me/submissions/ba70526f-ddf5-46a3-9b43-6f3884291b68

import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_ReciprocityTheory_Hypotheses_Descent
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalEA
import Theorems.Thm_ReciprocityTheory_Gal_resGal_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Gal.resGal_apply

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open ReciprocityTheory ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual ReciprocityTheory.Hyp
variable {F L Ω : Type*} [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω]
  [IsScalarTower F L Ω]
namespace ReciprocityTheory.Gal
theorem _root_.solution : Function.Injective (resGal F L Ω) := fun σ τ h =>
  AlgEquiv.ext fun x => by simpa using DFunLike.congr_fun h x
end ReciprocityTheory.Gal
