-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap.not_lt_of_dim_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:52.03208+00:00
-- url     : https://prove2.me/submissions/42e2fb66-acc1-42b7-bf3c-d6b30db6621d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
open SwapLoc
open ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap
namespace ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap
theorem _root_.solution {R : Type*} [CommRing R] {P Q : Ideal R} [hP : P.IsPrime] [Q.IsPrime]
    (hlt : P < Q) {d : ℕ} (hPd : ringKrullDim (R ⧸ P) = (d : WithBot ℕ∞))
    (hQd : ringKrullDim (R ⧸ Q) = (d : WithBot ℕ∞)) : False := by
  obtain ⟨z, hzQ, hzP⟩ := SetLike.exists_of_lt hlt
  have hz : Ideal.Quotient.mk P z ∈ nonZeroDivisors (R ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hz
  have hle : Ideal.span {Ideal.Quotient.mk P z} ≤ Q.map (Ideal.Quotient.mk P) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact Ideal.mem_map_of_mem _ hzQ
  let e : (R ⧸ P) ⧸ Q.map (Ideal.Quotient.mk P) ≃+* R ⧸ Q :=
    (DoubleQuot.quotQuotEquivQuotSup P Q).trans (Ideal.quotEquivOfEq (sup_eq_right.mpr hlt.le))
  have h2 : ringKrullDim (R ⧸ Q) ≤ ringKrullDim ((R ⧸ P) ⧸ Ideal.span {Ideal.Quotient.mk P z}) :=
    ringKrullDim_le_of_surjective ((e : _ →+* R ⧸ Q).comp (Ideal.Quotient.factor hle))
      (e.surjective.comp (Ideal.Quotient.factor_surjective hle))
  rw [hPd] at h1
  rw [hQd] at h2
  have h3 : (d : WithBot ℕ∞) + 1 ≤ (d : WithBot ℕ∞) := le_trans (by gcongr) h1
  have h4 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by exact_mod_cast h3
  have h5 : d + 1 ≤ d := by exact_mod_cast h4
  omega
end ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap
