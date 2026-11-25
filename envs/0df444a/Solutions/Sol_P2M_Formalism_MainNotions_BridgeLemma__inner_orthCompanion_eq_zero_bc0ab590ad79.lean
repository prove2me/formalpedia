-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__inner_orthCompanion_eq_zero_bc0ab590ad79
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:54:19.143838+00:00
-- url     : https://prove2.me/submissions/8f25d556-48de-4036-8fc6-3d732ad400f7

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ExistsSmallMemFractionalIdeal
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__inner_eq_coords_orthonormal_pair_1a25b2c19c4f
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__coords_orthCompanion_be2f4a1d53e6

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
theorem _root_.solution (hspan : Submodule.span K (Set.range e) = ⊤)
    (ho : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (x : V) :
    h x (orthCompanion h e x) = 0 := by
  rw [inner_eq_coords_orthonormal_pair h e hspan ho, (coords_orthCompanion h e ho x).1, (coords_orthCompanion h e ho x).2]
  ring
end Formalism.MainNotions.BridgeLemma₂
