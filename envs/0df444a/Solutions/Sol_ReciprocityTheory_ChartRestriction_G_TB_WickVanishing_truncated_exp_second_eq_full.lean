-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.truncated_exp_second_eq_full
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:12:58.302733+00:00
-- url     : https://prove2.me/submissions/3534b712-10cc-4eab-898b-ce15f3ee58bf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TruncatedExpSecondEqFull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open SecondColumnDegree DegreeTruncationOperator
section abelian₂
variable {k : Type} [CommRing k] {σ : Type}
end abelian₂
section Glue
variable {k : Type} [CommRing k] {ι : Type} [Fintype ι] {n : ℕ}
end Glue
section Trunc
variable {k : Type} [CommRing k] [Algebra ℚ k]
private lemma totalDegree_pderiv_le_of_le_succ {σ : Type} (l : σ) (q : MvPolynomial σ k) (D : ℕ)
    (hq : q.totalDegree ≤ D + 1) : (pderiv l q).totalDegree ≤ D := by
  classical
  conv_lhs => rw [q.as_sum]
  rw [map_sum]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [MvPolynomial.pderiv_monomial]
  by_cases hsl : s l = 0
  · rw [hsl, Nat.cast_zero, mul_zero, MvPolynomial.monomial_zero, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _
  · refine le_trans (b := (s - Finsupp.single l 1).sum fun _ e => e) ?_ ?_
    · first
      | exact MvPolynomial.totalDegree_monomial_le _ _
      | (by_cases hc : coeff s q * (s l : k) = 0
         · rw [hc, MvPolynomial.monomial_zero, MvPolynomial.totalDegree_zero]
           exact Nat.zero_le _
         · rw [MvPolynomial.totalDegree_monomial _ hc])
    · have hs' : (s.sum fun _ e => e) ≤ D + 1 := (MvPolynomial.le_totalDegree hs).trans hq
      have hsplit : s = (s - Finsupp.single l 1) + Finsupp.single l 1 := by
        ext x
        by_cases hx : l = x
        · subst hx
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_eq_same]
          omega
        · simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply,
            if_neg hx]
          omega
      have hsum : (s.sum fun _ e => e) = ((s - Finsupp.single l 1).sum fun _ e => e) + 1 := by
        conv_lhs => rw [hsplit]
        rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
      omega
private lemma totalDegree_secondOrder_le_of_le_add_two {σ : Type} [Fintype σ] (c : σ → σ → k) (q : MvPolynomial σ k) (D : ℕ)
    (hq : q.totalDegree ≤ D + 2) : (secondOrder k c q).totalDegree ≤ D := by
  unfold secondOrder
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun l _ => ?_)
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun l' _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact totalDegree_pderiv_le_of_le_succ l _ D (totalDegree_pderiv_le_of_le_succ l' q (D + 1) hq)
private lemma secondOrder_eq_zero_of_totalDegree_eq_zero {σ : Type} [Fintype σ] (c : σ → σ → k) (q : MvPolynomial σ k)
    (hq : q.totalDegree = 0) : secondOrder k c q = 0 := by
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hq
  rw [hq]
  unfold secondOrder
  simp [MvPolynomial.pderiv_C]
private lemma iterate_secondOrder_eq_zero_of_totalDegree_lt {σ : Type} [Fintype σ] (c : σ → σ → k) (i : ℕ) :
    ∀ q : MvPolynomial σ k, q.totalDegree + 1 ≤ i → (secondOrder k c)^[i] q = 0 := by
  induction i with
  | zero => intro q hq; omega
  | succ i ih =>
    intro q hq
    rw [Function.iterate_succ_apply]
    by_cases h0 : q.totalDegree = 0
    · rw [secondOrder_eq_zero_of_totalDegree_eq_zero c q h0]
      exact Function.iterate_fixed (secondOrder_eq_zero_of_totalDegree_eq_zero c 0 MvPolynomial.totalDegree_zero) i
    · exact ih _ (by have := totalDegree_secondOrder_le_of_le_add_two c q (q.totalDegree - 2) (by omega); omega)
end Trunc
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open SecondColumnDegree DegreeTruncationOperator
variable {k : Type} [CommRing k] [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {ι : Type} [Fintype ι] (c : ι → ι → k) (t : k) (D N : ℕ) (hDN : D ≤ N)
    (y : MvPolynomial ι k) (hy : y.totalDegree ≤ D) : expSecond k c t D y = E1 c t N y := by
  unfold expSecond E1
  have h1 : ∑ i ∈ Finset.range (D + 1),
        (t ^ i * algebraMap ℚ k (1 / (i.factorial : ℚ))) • (secondOrder k c)^[i] y =
      ∑ i ∈ Finset.range (N + 1),
        (t ^ i * algebraMap ℚ k (1 / (i.factorial : ℚ))) • (secondOrder k c)^[i] y := by
    apply Finset.sum_subset (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
    intro i _ hi
    simp only [Finset.mem_range] at hi
    rw [iterate_secondOrder_eq_zero_of_totalDegree_lt c i y (by omega), smul_zero]
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [one_div]
  ring
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
