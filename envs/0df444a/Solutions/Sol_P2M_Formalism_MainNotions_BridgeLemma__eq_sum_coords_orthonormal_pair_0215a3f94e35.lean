-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__eq_sum_coords_orthonormal_pair_0215a3f94e35
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:06.108576+00:00
-- url     : https://prove2.me/submissions/994f6536-cf94-45e4-b086-4ba4f1dea18d

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
theorem _root_.solution (hspan : Submodule.span K (Set.range e) = ⊤)
    (ho : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (v : V) :
    v = h (e 0) v • e 0 + h (e 1) v • e 1 := by
  have hv : v ∈ Submodule.span K (Set.range e) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hv
  have hcoef : ∀ j, h (e j) v = c j := by
    intro j
    rw [← hc, map_sum]
    simp [map_smul, ho]
  rw [hcoef 0, hcoef 1]
  conv_lhs => rw [← hc]
  rw [Fin.sum_univ_two]
end Formalism.MainNotions.BridgeLemma₂
