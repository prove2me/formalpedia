-- Prove2me | solution 1 for PI.DvRows.GramDeterminantPositive.log_abs_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:03.766327+00:00
-- url     : https://prove2.me/submissions/ff5f176f-9fe4-4e17-9506-d3f100d70b8b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_MulVecInjectiveOfKer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open PI.DvRows.GramDeterminantPositive
open Matrix
open scoped ComplexOrder
open NumberField Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
namespace PI.DvRows.GramDeterminantPositive
theorem _root_.solution [IsTotallyComplex K] (x : K) (hx : x ≠ 0) :
    Real.log |((Algebra.norm ℚ x : ℚ) : ℝ)| = ∑ v : InfinitePlace K, 2 * Real.log ‖v.embedding x‖ := by
  have h := InfinitePlace.prod_eq_abs_norm x
  rw [← Rat.cast_abs, ← h, Real.log_prod]
  · refine Finset.sum_congr rfl fun v _ => ?_
    have hm : v.mult = 2 := InfinitePlace.mult_isComplex ⟨v, IsTotallyComplex.isComplex v⟩
    rw [Real.log_pow, InfinitePlace.norm_embedding_eq, hm]; push_cast; ring
  · intro v _
    exact pow_ne_zero _ (InfinitePlace.pos_iff.2 hx).ne'
end PI.DvRows.GramDeterminantPositive
