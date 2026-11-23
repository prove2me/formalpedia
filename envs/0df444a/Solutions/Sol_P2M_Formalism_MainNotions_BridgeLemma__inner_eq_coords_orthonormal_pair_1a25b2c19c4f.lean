-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__inner_eq_coords_orthonormal_pair_1a25b2c19c4f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:48.165395+00:00
-- url     : https://prove2.me/submissions/a606988d-a8c7-486a-b501-4a3edc0dce32

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ExistsSmallMemFractionalIdeal
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__eq_sum_coords_orthonormal_pair_0215a3f94e35

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
    (ho : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (u v : V) :
    h u v = star (h (e 0) u) * h (e 0) v + star (h (e 1) u) * h (e 1) v := by
  conv_lhs => rw [eq_sum_coords_orthonormal_pair h e hspan ho u, eq_sum_coords_orthonormal_pair h e hspan ho v]
  simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, ho, starRingEnd_apply]
  simp
  ring
end Formalism.MainNotions.BridgeLemma₂
