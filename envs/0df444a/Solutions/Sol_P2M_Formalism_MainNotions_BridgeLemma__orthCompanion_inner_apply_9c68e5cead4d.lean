-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__orthCompanion_inner_apply_9c68e5cead4d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:31:24.084234+00:00
-- url     : https://prove2.me/submissions/29cbdd13-1727-4da3-9608-fbd960cc258c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ExistsSmallMemFractionalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField NumberField.mixedEmbedding Formalism.HermitianLatticesTheory
open scoped nonZeroDivisors NNReal ENNReal
variable {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Fin 2 → V)
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution (x v : V) :
    h (orthCompanion h e x) v = -(h (e 1) x) * h (e 0) v + h (e 0) x * h (e 1) v := by
  simp only [orthCompanion, map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply,
    star_neg, star_star]
end Formalism.MainNotions.BridgeLemma₂
