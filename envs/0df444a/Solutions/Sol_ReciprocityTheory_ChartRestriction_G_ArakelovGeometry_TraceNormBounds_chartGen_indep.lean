-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.chartGen_indep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:36.855503+00:00
-- url     : https://prove2.me/submissions/3a3269d5-f284-4feb-8953-214acc51f888

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjectiveFrameCoordNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_BasisOfLinearIndependentOfCardEqFinrank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
theorem _root_.solution (x : κ → Ω) (e : Fin (D + 1) → κ) (hfree : coordIdeal ℤ (x ∘ e) = ⊥)
    (l : Fin (D + 1)) : AlgebraicIndependent ℤ (chartGen x e l) := by
  classical
  have hne : x (e l) ≠ 0 := by
    intro hi
    have hk : MvPolynomial.X l ∈ coordIdeal ℤ (x ∘ e) := by
      unfold coordIdeal
      rw [RingHom.mem_ker]
      unfold coneMap
      simp [hi]
    rw [hfree, Ideal.mem_bot] at hk
    exact MvPolynomial.X_ne_zero l hk

  have hdehom : ∀ (F : MvPolynomial (Fin (D + 1)) ℤ) (n : ℕ), F.IsHomogeneous n →
      MvPolynomial.aeval (fun i => (x ∘ e) i / x (e l)) F =
        MvPolynomial.aeval (x ∘ e) F / x (e l) ^ n := by
    intro F n hF
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
      MvPolynomial.eval₂_eq', Finset.sum_div]
    refine Finset.sum_congr rfl fun d hd => ?_
    have h1 := hF (MvPolynomial.mem_support_iff.1 hd)
    have hdeg : ∑ i, d i = n := by
      rw [← h1]
      first
        | simp [Finsupp.weight_apply, Finsupp.sum_fintype]
        | simp [Finsupp.degree_eq_sum]
        | exact (Finsupp.sum_fintype _ _ (by simp)).symm
        | simp [Finsupp.degree, Finsupp.sum_fintype]
    rw [mul_div_assoc]
    congr 1
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hdeg]

  have hform : ∀ (F : MvPolynomial (Fin (D + 1)) ℤ) (n : ℕ), F.IsHomogeneous n →
      coneMap ℤ (x ∘ e) F = Polynomial.C (MvPolynomial.aeval (x ∘ e) F) * Polynomial.X ^ n := by
    intro F n hF
    unfold coneMap
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
      MvPolynomial.eval₂_eq', map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    have h1 := hF (MvPolynomial.mem_support_iff.1 hd)
    have hdeg : ∑ i, d i = n := by
      rw [← h1]
      first
        | simp [Finsupp.weight_apply, Finsupp.sum_fintype]
        | simp [Finsupp.degree_eq_sum]
        | exact (Finsupp.sum_fintype _ _ (by simp)).symm
        | simp [Finsupp.degree, Finsupp.sum_fintype]
    rw [← hdeg]
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, eq_intCast, map_mul,
      map_prod, map_pow, map_intCast]
    ring
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro P hP
  have hPΩ : MvPolynomial.aeval (fun k : {k // k ≠ l} => x (e k) / x (e l)) P = 0 := by
    have h1 := congrArg ((fnField (x ∘ e)).val.restrictScalars ℤ) hP
    rw [map_zero, ← AlgHom.comp_apply, MvPolynomial.comp_aeval] at h1
    exact h1
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = MvPolynomial.rename (Subtype.val : {k // k ≠ l} → Fin (D + 1)) P :=
    ⟨_, rfl⟩

  obtain ⟨H, hH⟩ : ∃ H : MvPolynomial (Fin (D + 1)) ℤ, H = ∑ n ∈ Finset.range (Q.totalDegree + 1),
      MvPolynomial.homogeneousComponent n Q * MvPolynomial.X l ^ (Q.totalDegree - n) := ⟨_, rfl⟩
  have hHhom : H.IsHomogeneous Q.totalDegree := by
    rw [hH]
    apply MvPolynomial.IsHomogeneous.sum
    intro n hn
    have hn' : n ≤ Q.totalDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
    have h2 := (MvPolynomial.homogeneousComponent_isHomogeneous n Q).mul
      ((MvPolynomial.isHomogeneous_X ℤ l).pow (Q.totalDegree - n))
    simpa [Nat.add_sub_of_le hn'] using h2
  have hterm : ∀ n ∈ Finset.range (Q.totalDegree + 1),
      MvPolynomial.aeval (x ∘ e) (MvPolynomial.homogeneousComponent n Q *
        MvPolynomial.X l ^ (Q.totalDegree - n)) =
      x (e l) ^ Q.totalDegree *
        MvPolynomial.aeval (fun i => (x ∘ e) i / x (e l)) (MvPolynomial.homogeneousComponent n Q) := by
    intro n hn
    have hn' : n ≤ Q.totalDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
    rw [map_mul, map_pow, MvPolynomial.aeval_X,
      hdehom _ n (MvPolynomial.homogeneousComponent_isHomogeneous n Q)]
    conv_rhs => rw [← Nat.add_sub_of_le hn', pow_add]
    have hc := pow_ne_zero n hne
    simp only [Function.comp_apply]
    field_simp
    try ring
  have hHy : MvPolynomial.aeval (x ∘ e) H = 0 := by
    rw [hH, map_sum, Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← map_sum,
      MvPolynomial.sum_homogeneousComponent, hQ, MvPolynomial.aeval_rename]
    have h3 : MvPolynomial.aeval ((fun i => (x ∘ e) i / x (e l)) ∘ Subtype.val) P = 0 := hPΩ
    rw [h3, mul_zero]
  have hH0 : H = 0 := by
    have hc : coneMap ℤ (x ∘ e) H = 0 := by
      rw [hform H _ hHhom, hHy, map_zero, zero_mul]
    have hk : H ∈ coordIdeal ℤ (x ∘ e) := by
      unfold coordIdeal
      rw [RingHom.mem_ker]
      exact hc
    rw [hfree, Ideal.mem_bot] at hk
    exact hk

  have hψ : (MvPolynomial.aeval fun k => if k = l then (1 : MvPolynomial (Fin (D + 1)) ℤ)
      else MvPolynomial.X k).comp (MvPolynomial.rename Subtype.val) =
      MvPolynomial.rename (R := ℤ) (Subtype.val : {k // k ≠ l} → Fin (D + 1)) := by
    apply MvPolynomial.algHom_ext
    intro k
    simp [k.2]
  have hQ0 : Q = 0 := by
    have h4 := congrArg (MvPolynomial.aeval fun k => if k = l then (1 : MvPolynomial (Fin (D + 1)) ℤ)
      else MvPolynomial.X k) hH0
    rw [hH, map_sum, map_zero] at h4
    simp only [map_mul, map_pow, MvPolynomial.aeval_X, ↓reduceIte, one_pow, mul_one] at h4
    rw [← map_sum, MvPolynomial.sum_homogeneousComponent, hQ, ← AlgHom.comp_apply, hψ] at h4
    rw [hQ]
    exact h4
  rw [hQ] at hQ0
  exact MvPolynomial.rename_injective _ Subtype.val_injective (hQ0.trans (map_zero _).symm)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
