-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__coords_orthCompanion_be2f4a1d53e6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:05.671603+00:00
-- url     : https://prove2.me/submissions/d2ed046e-c519-403f-bcaf-6640b31092d6

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
theorem _root_.solution (ho : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (x : V) :
    h (e 0) (orthCompanion h e x) = -(star (h (e 1) x)) ∧ h (e 1) (orthCompanion h e x) = star (h (e 0) x) := by
  constructor <;> simp [orthCompanion, ho]
end Formalism.MainNotions.BridgeLemma₂
