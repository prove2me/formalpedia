-- Prove2me | solution 1 for RegretMatching.Approach.eq_34
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:18:34.231613+00:00
-- url     : https://prove2.me/submissions/23114a06-0444-4281-89ce-24e77007e14a

import Mathlib
import Definitions.Def_RegretMatching_Approach_Setting
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open RegretMatching.Approach

theorem solution
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (i : ι)
    (q : S i → ℝ) (lam : OffDiag (S i) → ℝ) (s : ∀ i, S i) :
    ∑ l : OffDiag (S i), lam l * q l.1.1 *
        (u i (Function.update s i l.1.2) - u i (Function.update s i l.1.1)) =
      ∑ j : S i, (∑ k : S i, q k * lamMat lam k j - q j * ∑ k : S i, lamMat lam j k) *
        u i (Function.update s i j) := by
  set U : S i → ℝ := fun j => u i (Function.update s i j) with hU
  set G : S i × S i → ℝ := fun p => lamMat lam p.1 p.2 * q p.1 * (U p.2 - U p.1) with hG
  have hG0 : ∀ p : S i × S i, ¬ (p.1 ≠ p.2) → G p = 0 := by
    intro p hp
    have : p.1 = p.2 := not_not.1 hp
    simp [hG, lamMat, this]
  have h1 : ∑ l : OffDiag (S i), lam l * q l.1.1 * (U l.1.2 - U l.1.1) = ∑ p : S i × S i, G p := by
    have e : ∀ l : OffDiag (S i), lam l * q l.1.1 * (U l.1.2 - U l.1.1) = G l.1 := by
      intro l
      simp [hG, lamMat, l.2]
    simp_rw [e]
    rw [← Finset.sum_subtype (Finset.univ.filter (fun p : S i × S i => p.1 ≠ p.2)) (by simp) G]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : p.1 ≠ p.2
    · simp [h]
    · simp [h, hG0 p h]
  show ∑ l : OffDiag (S i), lam l * q l.1.1 * (U l.1.2 - U l.1.1) = ∑ j : S i, (∑ k : S i, q k * lamMat lam k j - q j * ∑ k : S i, lamMat lam j k) * U j
  rw [h1, Fintype.sum_prod_type]
  simp only [hG, mul_sub, Finset.sum_sub_distrib, sub_mul, Finset.sum_mul, Finset.mul_sum]
  have hc : ∑ x : S i, ∑ y : S i, lamMat lam x y * q x * U y = ∑ x : S i, ∑ y : S i, q y * lamMat lam y x * U x := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have h2 : ∑ x : S i, ∑ y : S i, lamMat lam x y * q x * U x = ∑ x : S i, ∑ y : S i, q x * lamMat lam x y * U x :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  linarith [hc, h2]
