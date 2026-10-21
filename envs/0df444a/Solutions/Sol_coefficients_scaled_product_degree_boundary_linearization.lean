-- Prove2me | solution 1 for coefficients_scaled_product_degree_boundary_linearization
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:14:37.881782+00:00
-- url     : https://prove2.me/submissions/cbb6e34b-2414-45c1-8773-2f02cda05dfe

import Mathlib
set_option autoImplicit false

open scoped BigOperators

namespace CspdblAux

/-- `f` has no terms of total degree `< d`. -/
def Vanish {n : Nat} (d : ℕ) (f : MvPowerSeries (Fin n) ℂ) : Prop :=
  ∀ s : Fin n →₀ ℕ, s.degree < d → MvPowerSeries.coeff s f = 0

lemma vanish_mono {n : Nat} {d d' : ℕ} (h : d ≤ d') {f : MvPowerSeries (Fin n) ℂ}
    (hf : Vanish d' f) : Vanish d f :=
  fun s hs => hf s (lt_of_lt_of_le hs h)

lemma vanish_zero {n : Nat} (d : ℕ) : Vanish d (0 : MvPowerSeries (Fin n) ℂ) := by
  intro s _; simp

lemma vanish_add {n : Nat} {d : ℕ} {f g : MvPowerSeries (Fin n) ℂ}
    (hf : Vanish d f) (hg : Vanish d g) : Vanish d (f + g) := by
  intro s hs; simp [hf s hs, hg s hs]

lemma vanish_mul {n : Nat} {a b : ℕ} {f g : MvPowerSeries (Fin n) ℂ}
    (hf : Vanish a f) (hg : Vanish b g) : Vanish (a + b) (f * g) := by
  classical
  intro s hs
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hp' : p.1 + p.2 = s := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hdeg : p.1.degree + p.2.degree = s.degree := by
    rw [← map_add, hp']
  by_cases h1 : p.1.degree < a
  · rw [hf _ h1, zero_mul]
  · have h2 : p.2.degree < b := by omega
    rw [hg _ h2, mul_zero]

/-- `F` and `G` agree up to degree `d`, and `G` has only terms of degree `≥ d`. -/
def Q {n : Nat} (F G : MvPowerSeries (Fin n) ℂ) (d : ℕ) : Prop :=
  Vanish (d + 1) (F - G) ∧ Vanish d G

lemma Q_mul {n : Nat} {F G F' G' : MvPowerSeries (Fin n) ℂ} {a b : ℕ}
    (h : Q F G a) (h' : Q F' G' b) : Q (F * F') (G * G') (a + b) := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  refine ⟨?_, vanish_mul h2 h2'⟩
  have e : F * F' - G * G' = (F - G) * (F' - G') + (F - G) * G' + G * (F' - G') := by ring
  rw [e]
  refine vanish_add (vanish_add ?_ ?_) ?_
  · exact vanish_mono (by omega) (vanish_mul h1 h1')
  · exact vanish_mono (by omega) (vanish_mul h1 h2')
  · exact vanish_mono (by omega) (vanish_mul h2 h1')

lemma Q_one {n : Nat} : Q (1 : MvPowerSeries (Fin n) ℂ) 1 0 := by
  refine ⟨?_, ?_⟩
  · simpa using vanish_zero (n := n) 1
  · intro s hs; omega

lemma Q_pow {n : Nat} {F G : MvPowerSeries (Fin n) ℂ} {a : ℕ} (h : Q F G a) (k : ℕ) :
    Q (F ^ k) (G ^ k) (a * k) := by
  induction k with
  | zero => simpa using Q_one
  | succ k ih =>
    have := Q_mul ih h
    rw [← pow_succ] at this
    rw [← pow_succ] at this
    simpa [mul_add, mul_comm] using this

lemma degree_one_eq_single {n : Nat} (s : Fin n →₀ ℕ) (hs : s.degree = 1) :
    ∃ j, s = Finsupp.single j 1 := by
  have hne : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hne
  have hj' : 1 ≤ s j := by simp at hj; omega
  have hle : Finsupp.single j 1 ≤ s := by
    rw [Finsupp.single_le_iff]; exact hj'
  refine ⟨j, ?_⟩
  obtain ⟨t, ht⟩ := exists_add_of_le hle
  have hd : (Finsupp.single j 1 + t).degree = 1 := by rw [← ht]; exact hs
  rw [map_add, Finsupp.degree_single] at hd
  have : t.degree = 0 := by omega
  rw [Finsupp.degree_eq_zero_iff] at this
  rw [ht, this, add_zero]

end CspdblAux

open CspdblAux in
theorem solution
    {n : Nat}
    (phi : Fin n → MvPowerSeries (Fin n) Complex)
    (hzero : ∀ i, MvPowerSeries.coeff 0 (phi i) = 0)
    (hlinear : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (phi i) =
      (if i = j then 1 else 0))
    (m : Fin n →₀ Nat)
    (D : Nat)
    (e : Fin n → Nat)
    (hdeg : (∑ i, m i) = D)
    (hedeg : (∑ i, e i) = D) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (m.prod (fun i k => phi i ^ k)) =
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (m.prod (fun i k => MvPowerSeries.X i ^ k)) := by
  classical
  have hQ1 : ∀ i, Q (phi i) (MvPowerSeries.X i) 1 := by
    intro i
    refine ⟨?_, ?_⟩
    · intro s hs
      have hs2 : s.degree = 0 ∨ s.degree = 1 := by omega
      rcases hs2 with h0 | h1
      · rw [Finsupp.degree_eq_zero_iff] at h0
        subst h0
        rw [map_sub, hzero i, MvPowerSeries.coeff_zero_X, sub_zero]
      · obtain ⟨j, rfl⟩ := degree_one_eq_single s h1
        simp [hlinear i j, MvPowerSeries.coeff_index_single_X, eq_comm]
    · intro s hs
      have h0 : s.degree = 0 := by omega
      rw [Finsupp.degree_eq_zero_iff] at h0
      subst h0
      simp [MvPowerSeries.coeff_zero_X]
  have hQ : ∀ S : Finset (Fin n), Q (∏ i ∈ S, phi i ^ m i) (∏ i ∈ S, MvPowerSeries.X i ^ m i)
      (∑ i ∈ S, m i) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using Q_one
    | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
      have := Q_mul (Q_pow (hQ1 a) (m a)) ih
      simpa using this
  have hfin := hQ Finset.univ
  rw [hdeg] at hfin
  have hprod : ∀ f : Fin n → MvPowerSeries (Fin n) ℂ,
      m.prod (fun i k => f i ^ k) = ∏ i, f i ^ m i := by
    intro f
    rw [Finsupp.prod]
    apply Finset.prod_subset (Finset.subset_univ _)
    intro i _ hi
    simp [Finsupp.notMem_support_iff.mp hi]
  rw [hprod, hprod (fun i => MvPowerSeries.X i)]
  have hd : (Finsupp.equivFunOnFinite.symm e).degree < D + 1 := by
    rw [Finsupp.degree_eq_sum]; simp [hedeg]
  have := hfin.1 _ hd
  rw [map_sub, sub_eq_zero] at this
  exact this
