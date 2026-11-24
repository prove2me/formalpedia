-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.exists_homog_chart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:37.451091+00:00
-- url     : https://prove2.me/submissions/2644df60-6271-48ec-afb7-bd759ed2663a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsMonomialNotMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt

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
variable [DecidableEq K]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution (V : Ideal (MRingOver F ι)) (j : ∀ k, ι k) (b : MRingOver F ι) :
    ∃ e₀ : K → ℕ, ∀ e, e₀ ≤ e → ∃ b' ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) e,
      Ideal.Quotient.mk (chartIdeal V j) b' = Ideal.Quotient.mk (chartIdeal V j) b := by
  have hX1 : ∀ k, Ideal.Quotient.mk (chartIdeal V j) (X ⟨k, j k⟩) = 1 := by
    intro k
    rw [← map_one (Ideal.Quotient.mk (chartIdeal V j)), Ideal.Quotient.eq]
    unfold chartIdeal
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
  refine ⟨fun _ => b.totalDegree, fun e he => ?_⟩
  have hd : ∀ m ∈ b.support, ∀ k, ∑ i, m ⟨k, i⟩ ≤ e k := by
    intro m hm k
    calc ∑ i, m ⟨k, i⟩ ≤ ∑ k', ∑ i, m ⟨k', i⟩ :=
          Finset.single_le_sum (f := fun k' => ∑ i, m ⟨k', i⟩) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ k)
      _ = m.sum fun _ n => n := by rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sigma]
      _ ≤ b.totalDegree := MvPolynomial.le_totalDegree hm
      _ ≤ e k := he k
  refine ⟨∑ m ∈ b.support, monomial m (coeff m b) * ∏ k, X ⟨k, j k⟩ ^ (e k - ∑ i, m ⟨k, i⟩),
    ?_, ?_⟩
  · refine Submodule.sum_mem _ fun m hm => ?_
    rw [mem_weightedHomogeneousSubmodule]
    have h1 : IsWeightedHomogeneous (mw (ι := ι)) (monomial m (coeff m b))
        (fun k => ∑ i, m ⟨k, i⟩) :=
      isWeightedHomogeneous_monomial _ _ _ (weight_mw m)
    have h2 : IsWeightedHomogeneous (mw (ι := ι))
        (∏ k, (X ⟨k, j k⟩ : MRingOver F ι) ^ (e k - ∑ i, m ⟨k, i⟩))
        (∑ k, (e k - ∑ i, m ⟨k, i⟩) • mw (ι := ι) ⟨k, j k⟩) :=
      IsWeightedHomogeneous.prod _ _ _ fun k _ =>
        (isWeightedHomogeneous_X (R := F) (w := mw (ι := ι)) (i := (⟨k, j k⟩ : Σ k, ι k))).pow _
    have h3 := h1.mul h2
    have hsum : ((fun k => ∑ i, m ⟨k, i⟩) +
        ∑ k, (e k - ∑ i, m ⟨k, i⟩) • mw (ι := ι) ⟨k, j k⟩) = e := by
      funext k
      have := hd m hm k
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, mw, smul_eq_mul, Pi.single_apply,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      omega
    rwa [hsum] at h3
  · rw [map_sum]
    conv_rhs => rw [MvPolynomial.as_sum b, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, map_prod]
    simp only [map_pow, hX1, one_pow, Finset.prod_const_one, mul_one]
end ReciprocityTheory.ChartRestriction.G.AI.I1
