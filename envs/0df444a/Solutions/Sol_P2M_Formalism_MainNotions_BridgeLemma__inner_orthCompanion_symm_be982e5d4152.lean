-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__inner_orthCompanion_symm_be982e5d4152
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:54:20.186742+00:00
-- url     : https://prove2.me/submissions/e5a96d42-89c9-47e8-b008-6ab8f4d2e630

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ExistsSmallMemFractionalIdeal
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__inner_eq_coords_orthonormal_pair_1a25b2c19c4f

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
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Fin 2 → V) (hspan : Submodule.span K (Set.range e) = ⊤)
    (ho : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (x v : V) :
    h v (orthCompanion h e x) = star (h (orthCompanion h e x) v) := by
  rw [inner_eq_coords_orthonormal_pair h e hspan ho v, inner_eq_coords_orthonormal_pair h e hspan ho (orthCompanion h e x) v]
  simp only [star_add, star_mul', star_star]
  ring
end Formalism.MainNotions.BridgeLemma₂
