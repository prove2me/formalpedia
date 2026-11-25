-- Prove2me | solution 1 for ReciprocityTheory.Gal.isClosedEmbedding_resGal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:12:29.373192+00:00
-- url     : https://prove2.me/submissions/96b24367-6155-494a-8563-1d1757dadc35

import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_ReciprocityTheory_Hypotheses_Descent
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalEA
import Theorems.Thm_ReciprocityTheory_Gal_resGal_injective
import Theorems.Thm_ReciprocityTheory_Gal_continuous_resGal
import Theorems.Thm_ReciprocityTheory_Gal_isAlgClosure_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open ReciprocityTheory ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual ReciprocityTheory.Hyp
variable {F L Ω : Type*} [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω]
  [IsScalarTower F L Ω]
namespace ReciprocityTheory.Gal
theorem _root_.solution [IsAlgClosure F Ω] [CharZero L] :
    Topology.IsClosedEmbedding (resGal F L Ω) := by
  have := isAlgClosure_top (F := F) (L := L) (Ω := Ω)
  have : T2Space (G F Ω) := krullTopology_t2
  exact continuous_resGal.isClosedEmbedding resGal_injective
end ReciprocityTheory.Gal
