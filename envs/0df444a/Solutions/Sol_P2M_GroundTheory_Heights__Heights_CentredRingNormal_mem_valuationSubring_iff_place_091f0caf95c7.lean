-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CentredRingNormal_mem_valuationSubring_iff_place_091f0caf95c7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:35.433402+00:00
-- url     : https://prove2.me/submissions/8b1dc2e8-65da-456a-8b9e-73ed616e86d2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightCentredRingNormal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PCentredRingNormal

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
open NumberField IsDedekindDomain
open GroundTheory.Heights₂.Heights.CentredRingNormal
variable {L : Type} [Field L] [NumberField L]
namespace GroundTheory.Heights₂.Heights.CentredRingNormal
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) (x : L) :
    x ∈ (v.valuation L).valuationSubring ↔ FinitePlace.mk v x ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, FinitePlace.mk_apply, FinitePlace.norm_embedding',
    NNReal.coe_le_one,
    ← map_one (WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v)),
    (WithZeroMulInt.toNNReal_strictMono
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).le_iff_le]
end GroundTheory.Heights₂.Heights.CentredRingNormal
