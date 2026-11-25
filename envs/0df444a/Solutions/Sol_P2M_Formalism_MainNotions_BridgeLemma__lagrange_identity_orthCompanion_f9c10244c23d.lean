-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__lagrange_identity_orthCompanion_f9c10244c23d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:45:14.035577+00:00
-- url     : https://prove2.me/submissions/92ffb606-9db2-45d0-a43e-0ac02d943084

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ExistsSmallMemFractionalIdeal
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__inner_eq_coords_orthonormal_pair_1a25b2c19c4f
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__orthCompanion_inner_apply_9c68e5cead4d

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
    (ho : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (x v v' : V) :
    h (orthCompanion h e x) v * star (h (orthCompanion h e x) v') = h x x * h v' v - h x v * h v' x := by
  rw [orthCompanion_inner_apply, orthCompanion_inner_apply, inner_eq_coords_orthonormal_pair h e hspan ho x x, inner_eq_coords_orthonormal_pair h e hspan ho v' v,
    inner_eq_coords_orthonormal_pair h e hspan ho x v, inner_eq_coords_orthonormal_pair h e hspan ho v' x]
  simp only [star_add, star_mul', star_neg, star_star]
  ring
end Formalism.MainNotions.BridgeLemma₂
