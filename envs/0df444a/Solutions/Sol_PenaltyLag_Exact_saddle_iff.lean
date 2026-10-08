-- Prove2me | solution 1 for PenaltyLag.Exact.saddle_iff
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:25:00.588281+00:00
-- url     : https://prove2.me/submissions/f7091f11-1a37-442b-99c6-3559edf20e0e

import Mathlib
import Definitions.Def_PenaltyLag_Exact_Basic

namespace PenaltyLag.Exact
open PenaltyLag.Asymptotic

noncomputable def term (r c y : ℝ) : ℝ := (max 0 (y + 2*r*c))^2 - y^2

theorem term_nonpos {r c : ℝ} (hr : 0 < r) (hc : c ≤ 0) (y : ℝ) : term r c y ≤ 0 := by
  unfold term
  by_cases h : y + 2*r*c ≤ 0
  · rw [max_eq_left h]; nlinarith [sq_nonneg y]
  · rw [max_eq_right (le_of_not_ge h)]
    have hrc : r*c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr.le hc
    nlinarith

theorem term_unbounded {r c : ℝ} (hr : 0 < r) (hc : 0 < c) (B : ℝ) :
    ∃ y, B < term r c y := by
  let y := max 0 (B / (4*r*c)) + 1
  have hp : 0 < 4*r*c := by positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have ht : B < (4*r*c)*y := by
    have hd : B / (4*r*c) < y := by dsimp [y]; linarith [le_max_right 0 (B/(4*r*c))]
    simpa [mul_comm] using (div_lt_iff₀ hp).mp hd
  refine ⟨y, ?_⟩
  unfold term
  rw [max_eq_right (by positivity)]
  nlinarith [sq_nonneg (r*c)]

theorem lag_feasible_le {E : Type*} {m : ℕ} (f₀ : E → ℝ) (f : Fin m → E → ℝ)
    {r : ℝ} (hr : 0 < r) {x : E} (hx : ∀ i, f i x ≤ 0) (y : Mult m) :
    Lr f₀ f r x y ≤ f₀ x := by
  have hs : (∑ i, term r (f i x) (y i)) ≤ 0 :=
    Finset.sum_nonpos (fun i _ => term_nonpos hr (hx i) (y i))
  have hp : 0 ≤ 1/(4*r) := by positivity
  have hh := mul_nonpos_of_nonneg_of_nonpos hp hs
  simpa [Lr, theta, term] using (add_le_add_left hh (f₀ x))

theorem lag_zero_feasible {E : Type*} {m : ℕ} (f₀ : E → ℝ) (f : Fin m → E → ℝ)
    {r : ℝ} (hr : 0 < r) {x : E} (hx : ∀ i, f i x ≤ 0) :
    Lr f₀ f r x (0 : Mult m) = f₀ x := by
  have ht (i : Fin m) : max 0 (2*r*f i x) = 0 :=
    max_eq_left (mul_nonpos_of_nonneg_of_nonpos (by positivity) (hx i))
  simp [Lr, theta, ht]

theorem max_lag_feasible {E : Type*} {m : ℕ} (f₀ : E → ℝ) (f : Fin m → E → ℝ)
    {r : ℝ} (hr : 0 < r) (x : E) (ybar : Mult m)
    (hmax : ∀ y, Lr f₀ f r x y ≤ Lr f₀ f r x ybar) :
    (∀ i, f i x ≤ 0) ∧ Lr f₀ f r x ybar = f₀ x := by
  have hc : ∀ i, f i x ≤ 0 := by
    intro i
    by_contra hn
    obtain ⟨t, ht⟩ := term_unbounded hr (lt_of_not_ge hn) (term r (f i x) (ybar i))
    let y : Mult m := WithLp.toLp 2 (Function.update (fun j => ybar j) i t)
    have hs : (∑ j, term r (f j x) (y j)) =
        (∑ j, term r (f j x) (ybar j)) - term r (f i x) (ybar i) + term r (f i x) t := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
        ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      have he : (∑ j ∈ Finset.univ.erase i, term r (f j x) (y j)) =
          ∑ j ∈ Finset.univ.erase i, term r (f j x) (ybar j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hji := (Finset.mem_erase.mp hj).1
        simp [y, hji]
      simp [he, y]
    have hh := hmax y
    change f₀ x + (1/(4*r)) * (∑ j, term r (f j x) (y j)) ≤
      f₀ x + (1/(4*r)) * (∑ j, term r (f j x) (ybar j)) at hh
    rw [hs] at hh
    have hp : 0 < 1/(4*r) := by positivity
    nlinarith
  exact ⟨hc, le_antisymm (lag_feasible_le f₀ f hr hc ybar)
    (by simpa [lag_zero_feasible f₀ f hr hc] using hmax 0)⟩

theorem primal_of_optimal {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ)
    (f : Fin m → E → ℝ) (xbar : E) (hx : IsOptimal X f₀ f xbar) :
    primalValue X f₀ f = (f₀ xbar : EReal) := by
  apply le_antisymm
  · exact iInf_le_of_le xbar (iInf_le_of_le hx.1 (iInf_le_of_le hx.2.1 le_rfl))
  · apply le_iInf; intro x
    apply le_iInf; intro hxX
    apply le_iInf; intro hxf
    exact_mod_cast hx.2.2 x hxX hxf

theorem saddle_characterization {E : Type*} {m : ℕ}
    (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ)
    (r : ℝ) (hr : 0 < r) (xbar : E) (ybar : Mult m) :
    IsSaddle X f₀ f r xbar ybar ↔
      IsOptimal X f₀ f xbar ∧ IsKTVector X f₀ f r ybar := by
  constructor
  · rintro ⟨hxX, hmax, hmin⟩
    obtain ⟨hxf, he⟩ := max_lag_feasible f₀ f hr xbar ybar hmax
    have hopt : IsOptimal X f₀ f xbar := by
      refine ⟨hxX, hxf, ?_⟩
      intro x hx hfx
      calc f₀ xbar = Lr f₀ f r xbar ybar := he.symm
           _ ≤ Lr f₀ f r x ybar := hmin x hx
           _ ≤ f₀ x := lag_feasible_le f₀ f hr hfx ybar
    have hg : gr X f₀ f r ybar = (f₀ xbar : EReal) := by
      apply le_antisymm
      · have hh : gr X f₀ f r ybar ≤ (Lr f₀ f r xbar ybar : EReal) :=
          iInf_le_of_le xbar (iInf_le_of_le hxX le_rfl)
        simpa [he] using hh
      · apply le_iInf; intro x
        apply le_iInf; intro hx
        exact_mod_cast (he ▸ hmin x hx)
    refine ⟨hopt, ?_, ?_⟩
    · rw [hg]; exact EReal.bot_lt_coe _
    · rw [hg, primal_of_optimal X f₀ f xbar hopt]
  · rintro ⟨hopt, hkt⟩
    have hg : gr X f₀ f r ybar = (f₀ xbar : EReal) :=
      hkt.2.trans (primal_of_optimal X f₀ f xbar hopt)
    have hl (x : E) (hx : x ∈ X) : f₀ xbar ≤ Lr f₀ f r x ybar := by
      have hh : gr X f₀ f r ybar ≤ (Lr f₀ f r x ybar : EReal) :=
        iInf_le_of_le x (iInf_le_of_le hx le_rfl)
      rw [hg] at hh
      exact_mod_cast hh
    have he : Lr f₀ f r xbar ybar = f₀ xbar :=
      le_antisymm (lag_feasible_le f₀ f hr hopt.2.1 ybar) (hl xbar hopt.1)
    refine ⟨hopt.1, ?_, ?_⟩
    · intro y; rw [he]; exact lag_feasible_le f₀ f hr hopt.2.1 y
    · intro x hx; rw [he]; exact hl x hx

end PenaltyLag.Exact

open PenaltyLag.Exact
theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (xbar : E) (ybar : PenaltyLag.Asymptotic.Mult m) :
    IsSaddle X f₀ f r xbar ybar ↔ (IsOptimal X f₀ f xbar ∧ IsKTVector X f₀ f r ybar) :=
  saddle_characterization X f₀ f r hr xbar ybar
#print axioms solution
