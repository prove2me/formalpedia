-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.exists_homog_of_cone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:05:22.672803+00:00
-- url     : https://prove2.me/submissions/d631a9d5-e0ee-48c6-b119-76b42d32f65e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeO
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeQ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {n : ℕ} {c : MvPolynomial (Fin n) ℂ} (hc : c ≠ 0)
    {T : Set (Fin n → ℂ)} (hT : ∀ v ∈ T, ∀ t : ℂ, t ≠ 0 → (fun i => t * v i) ∈ T)
    (hcT : ∀ v ∈ T, eval v c = 0) :
    ∃ m, homogeneousComponent m c ≠ 0 ∧ (homogeneousComponent m c).IsHomogeneous m ∧
      ∀ v ∈ T, eval v (homogeneousComponent m c) = 0 := by
  have hscale : ∀ (m : ℕ) (t : ℂ) (v : Fin n → ℂ),
      eval (fun i => t * v i) (homogeneousComponent m c) = t ^ m * eval v (homogeneousComponent m c) := by
    intro m t v
    rw [homogeneousComponent_apply, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_filter] at hd
    have hdeg : ∑ i ∈ d.support, d i = m := by
      first
      | exact hd.2
      | (rw [← hd.2]; rfl)
      | simpa [Finsupp.degree] using hd.2
    simp only [eval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, hdeg]
    ring
  have hcomp : ∀ m, ∀ v ∈ T, eval v (homogeneousComponent m c) = 0 := by
    intro m v hv
    let Q : Polynomial ℂ := ∑ k ∈ Finset.range (c.totalDegree + 1),
      Polynomial.C (eval v (homogeneousComponent k c)) * Polynomial.X ^ k
    have hQ : ∀ t : ℂ, t ≠ 0 → Q.eval t = 0 := by
      intro t ht
      have h0 := hcT _ (hT v hv t ht)
      rw [← sum_homogeneousComponent c, map_sum] at h0
      simp only [Q, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      rw [← h0]
      exact Finset.sum_congr rfl fun k _ => by rw [hscale]; ring
    have hQ0 : Q = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply Set.Infinite.mono (s := {t : ℂ | t ≠ 0})
      · intro t ht
        exact hQ t ht
      · exact (Set.finite_singleton (0 : ℂ)).infinite_compl
    by_cases hm : m ≤ c.totalDegree
    · have h1 := congrArg (fun p => Polynomial.coeff p m) hQ0
      simpa [Q, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow,
        (by omega : m < c.totalDegree + 1)] using h1
    · rw [homogeneousComponent_eq_zero m c (by omega), map_zero]
  obtain ⟨m, -, hm⟩ : ∃ m ∈ Finset.range (c.totalDegree + 1), homogeneousComponent m c ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hc
    rw [← sum_homogeneousComponent c]
    exact Finset.sum_eq_zero hcon
  exact ⟨m, hm, homogeneousComponent_isHomogeneous m c, fun v hv => hcomp m v hv⟩
end ReciprocityTheory.ChartRestriction.G.Geo
