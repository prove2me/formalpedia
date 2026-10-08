-- Prove2me | solution 1 for PenaltyLag.Exact.corollary_3_4_r0
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:43:38.714911+00:00
-- url     : https://prove2.me/submissions/427a2a2c-a676-4d4c-9551-0c43c4e9d17a

import Mathlib
import Definitions.Def_PenaltyLag_Exact_Basic
open scoped BigOperators
open PenaltyLag.Exact PenaltyLag.Asymptotic

theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (xbar : E) (ybar : PenaltyLag.Asymptotic.Mult m) :
    IsSaddle0 X f₀ f xbar ybar ↔ KuhnTuckerConditions X f₀ f xbar ybar := by
  classical
  constructor
  · rintro ⟨hx, hy, hmin⟩
    have hn : ∀ i, 0 ≤ ybar i := by
      by_contra hh
      have hz := hy 0
      simp [L0, hh] at hz
    have hyR : ∀ y : Mult m, (∀ i, 0 ≤ y i) →
        (∑ i, y i * f i xbar) ≤ ∑ i, ybar i * f i xbar := by
      intro y hny
      have hh := hy y
      simp only [L0, if_pos hn, if_pos hny] at hh
      have hhr := EReal.coe_le_coe_iff.mp hh
      linarith
    have hfneg : ∀ i, f i xbar ≤ 0 := by
      intro i
      let y : Mult m := WithLp.toLp 2 (fun j => ybar j + if j = i then 1 else 0)
      have hny : ∀ j, 0 ≤ y j := by
        intro j
        dsimp [y]
        split_ifs <;> linarith [hn j]
      have hh := hyR y hny
      simp [y, add_mul, Finset.sum_add_distrib] at hh
      linarith
    have hp : ∀ i, ybar i * f i xbar ≤ 0 := fun i => mul_nonpos_of_nonneg_of_nonpos (hn i) (hfneg i)
    have hs0 : (∑ i, ybar i * f i xbar) = 0 := by
      have h0 := hyR 0 (by simp)
      have h1 : (∑ i, ybar i * f i xbar) ≤ 0 := Finset.sum_nonpos (fun i hi => hp i)
      simp at h0
      linarith
    have hp0 : ∀ i, ybar i * f i xbar = 0 := by
      exact fun i => (Finset.sum_eq_zero_iff_of_nonpos (fun j hj => hp j)).mp hs0 i (Finset.mem_univ i)
    refine ⟨fun i => ⟨hn i, hfneg i, hp0 i⟩, hx, ?_⟩
    intro x hxx
    have hh := hmin x hxx
    simp only [L0, if_pos hn] at hh
    exact EReal.coe_le_coe_iff.mp hh
  · rintro ⟨hk, hx, hmin⟩
    have hn : ∀ i, 0 ≤ ybar i := fun i => (hk i).1
    have hz : (∑ i, ybar i * f i xbar) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact (hk i).2.2
    refine ⟨hx, ?_, ?_⟩
    · intro y
      by_cases hny : ∀ i, 0 ≤ y i
      · have hh : (∑ i, y i * f i xbar) ≤ 0 :=
          Finset.sum_nonpos fun i hi => mul_nonpos_of_nonneg_of_nonpos (hny i) (hk i).2.1
        simp only [L0, if_pos hn, if_pos hny]
        exact EReal.coe_le_coe_iff.mpr (by linarith)
      · simp [L0, hny]
    · intro x hxx
      simp only [L0, if_pos hn]
      exact EReal.coe_le_coe_iff.mpr (hmin x hxx)

#print axioms solution
