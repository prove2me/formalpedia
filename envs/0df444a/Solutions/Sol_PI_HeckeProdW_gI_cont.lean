-- Prove2me | solution 1 for PI.HeckeProdW.gI_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:42:01.422672+00:00
-- url     : https://prove2.me/submissions/1a899234-51a1-400d-b782-c77b272d1016

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Lemmata_MiscLemmasM_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_Kernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host RestrictedProduct Topology
open PI PI.HeckeProdW
variable (L : Type) [Field L] [NumberField L]
namespace PI.HeckeProdW
theorem _root_.solution : Continuous (gI L) := by
  show Continuous (fun x => ((1 : InfiniteAdeleRing L),
    (structureMap (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
      (fun v => v.adicCompletionIntegers L) Filter.cofinite x : FiniteAdeleRing (𝓞 L) L)))
  exact continuous_const.prodMk isEmbedding_structureMap.continuous
end PI.HeckeProdW
