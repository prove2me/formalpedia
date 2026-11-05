-- Prove2me | solution 1 for StrongConv.norm_adjFree
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T00:17:41.75814+00:00
-- url     : https://prove2.me/submissions/957a7633-9674-496c-9ed2-56f53e567458

import Mathlib
import Definitions.Def_StrongConv

section
noncomputable section
namespace StrongConv.CitedGraphs.PartK
open scoped InnerProductSpace
/-! # Part K: Kesten, `‖A_F‖ = 2√(2d-1)` (upper bound by a Schur test, lower bound by radial test vectors). -/
theorem leftReg_apply {d : ℕ} (g : FreeGroup (Fin d)) (f : L2Free d) (h : FreeGroup (Fin d)) :
    leftReg g f h = f (g⁻¹ * h) := rfl

theorem star_leftReg {d : ℕ} (g : FreeGroup (Fin d)) : star (leftReg g) = leftReg g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  rw [← (Equiv.mulLeft g).tsum_eq (fun i => ⟪x i, (leftReg g y) i⟫_ℂ)]
  simp [leftReg_apply]

end StrongConv.CitedGraphs.PartK
end
end

section
noncomputable section
namespace StrongConv.CitedGraphs
open Filter
/-! ## The permutation model: Rayleigh quotients on `{1_N}⊥` -/

/-! ## Alon–Boppana (Nilli's argument) -/

/-! ## Friedman's tangle -/

end StrongConv.CitedGraphs
end
end

section
namespace StrongConv.CitedGraphs.PartK
set_option linter.unusedSectionVars false
variable {α : Type*} [DecidableEq α]
/-! Part K helpers: one-letter multiplication in a free group. -/
/-- The letter `x^{±1}` as a group element. -/
def ltr (y : α × Bool) : FreeGroup α := FreeGroup.mk [y]

end StrongConv.CitedGraphs.PartK
end

section
noncomputable section
namespace StrongConv.CitedGraphs.PartK
open scoped InnerProductSpace
theorem ltr_true {d : ℕ} (i : Fin d) : ltr (i, true) = FreeGroup.of i := rfl

end StrongConv.CitedGraphs.PartK
end
end

section
namespace StrongConv.CitedGraphs.PartK
set_option linter.unusedSectionVars false
variable {α : Type*} [DecidableEq α]
/-- The inverse letter. -/
def flp (y : α × Bool) : α × Bool := (y.1, !y.2)

theorem flp_flp (y : α × Bool) : flp (flp y) = y := by
  simp [flp]

/-- `flp` as an involutive equivalence. -/
def flpEquiv : (α × Bool) ≃ (α × Bool) where
  toFun := flp
  invFun := flp
  left_inv := flp_flp
  right_inv := flp_flp

theorem ltr_flp (y : α × Bool) : ltr (flp y) = (ltr y)⁻¹ := by
  simp [ltr, flp, FreeGroup.inv_mk, FreeGroup.invRev]

end StrongConv.CitedGraphs.PartK
end

section
noncomputable section
namespace StrongConv.CitedGraphs.PartK
open scoped InnerProductSpace
theorem ltr_false {d : ℕ} (i : Fin d) : ltr (i, false) = (FreeGroup.of i)⁻¹ := by
  rw [← ltr_true, ← ltr_flp]; rfl

theorem adjFree_apply (d : ℕ) (f : L2Free d) (w : FreeGroup (Fin d)) :
    adjFree d f w = ∑ y : Fin d × Bool, f (ltr y * w) := by
  rw [adjFree, ContinuousLinearMap.sum_apply, lp.coeFn_sum, Finset.sum_apply,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [sLimit, star_leftReg, ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply,
    leftReg_apply, inv_inv, Fintype.sum_bool]
  rw [ltr_true, ltr_false, add_comm]

end StrongConv.CitedGraphs.PartK
end
end

section
namespace StrongConv.CitedGraphs.PartK
set_option linter.unusedSectionVars false
variable {α : Type*} [DecidableEq α]
theorem ltr_flp_mul (y : α × Bool) (u : FreeGroup α) : ltr y * (ltr (flp y) * u) = u := by
  rw [ltr_flp, mul_inv_cancel_left]

end StrongConv.CitedGraphs.PartK
end

section
noncomputable section
namespace StrongConv.CitedGraphs.PartK
open scoped InnerProductSpace
variable {α : Type*} [DecidableEq α] [Fintype α]
theorem tsum_reindex (H : FreeGroup α → FreeGroup α → ℝ)
    (hH : ∀ y, Summable (fun w => H w (ltr y * w))) :
    ∑' w, ∑ y, H w (ltr y * w) = ∑' u, ∑ y, H (ltr y * u) u := by
  have hH' : ∀ y, Summable (fun u => H (ltr y * u) u) := fun y =>
    (Equiv.mulLeft (ltr (flp y))).summable_iff.mp (by
      simpa [Function.comp_def, ltr_flp_mul] using hH (flp y))
  rw [Summable.tsum_finsetSum (fun y _ => hH y), Summable.tsum_finsetSum (fun y _ => hH' y)]
  rw [← (flpEquiv (α := α)).sum_comp (fun y => ∑' u, H (ltr y * u) u)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [← (Equiv.mulLeft (ltr (flp y))).tsum_eq (fun w => H w (ltr y * w))]
  simp [flpEquiv, ltr_flp_mul]

end StrongConv.CitedGraphs.PartK
end
end

section
noncomputable section
namespace StrongConv.CitedGraphs.PartK
open scoped InnerProductSpace
theorem norm_sq_eq_tsum {d : ℕ} (f : L2Free d) : ‖f‖ ^ 2 = ∑' w, ‖f w‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) f
  simpa using h

theorem summable_norm_sq {d : ℕ} (f : L2Free d) : Summable (fun w => ‖f w‖ ^ 2) := by
  have h := (lp.memℓp f).summable (p := 2) (by norm_num)
  simpa using h

theorem summable_norm_sq_comp {d : ℕ} (f : L2Free d) (g : FreeGroup (Fin d)) :
    Summable (fun w => ‖f (g * w)‖ ^ 2) :=
  (Equiv.mulLeft g).summable_iff.mpr (summable_norm_sq f)

/-- Weighted Cauchy–Schwarz. -/
theorem weighted_cs {ι : Type*} (s : Finset ι) (z : ι → ℂ) (c : ι → ℝ) (hc : ∀ i ∈ s, 0 < c i)
    (h1 : 0 < ∑ i ∈ s, 1 / c i) (h2 : ∑ i ∈ s, 1 / c i ≤ 1) :
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ ∑ i ∈ s, c i * ‖z i‖ ^ 2 := by
  have hS := Finset.sq_sum_div_le_sum_sq_div s (fun i => ‖z i‖) (g := fun i => 1 / c i)
    (fun i hi => by have := hc i hi; positivity)
  have e : ∀ i ∈ s, ‖z i‖ ^ 2 / (1 / c i) = c i * ‖z i‖ ^ 2 := fun i hi => by
    have := hc i hi; field_simp
  rw [Finset.sum_congr rfl e] at hS
  have h0 : ‖∑ i ∈ s, z i‖ ≤ ∑ i ∈ s, ‖z i‖ := norm_sum_le _ _
  calc ‖∑ i ∈ s, z i‖ ^ 2 ≤ (∑ i ∈ s, ‖z i‖) ^ 2 := by gcongr
    _ ≤ (∑ i ∈ s, ‖z i‖) ^ 2 / ∑ i ∈ s, 1 / c i := le_div_self (by positivity) h1 h2
    _ ≤ _ := hS

/-- The Schur weight. -/
def wt (q : ℝ) {d : ℕ} (w u : FreeGroup (Fin d)) : ℝ :=
  if FreeGroup.norm u < FreeGroup.norm w then 2 else 2 * q

theorem card_filter_add {d : ℕ} (P : Fin d × Bool → Prop) [DecidablePred P] :
    ((Finset.univ.filter P).card : ℝ) + (Finset.univ.filter (fun y => ¬ P y)).card = 2 * d := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin d × Bool))) P
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at this
  exact_mod_cast (by omega : (Finset.univ.filter P).card + (Finset.univ.filter (fun y => ¬ P y)).card = 2 * d)

end StrongConv.CitedGraphs.PartK
end
end

section
namespace StrongConv.CitedGraphs.PartK
set_option linter.unusedSectionVars false
variable {α : Type*} [DecidableEq α]
theorem toWord_ltr_mul (y : α × Bool) (w : FreeGroup α) :
    (ltr y * w).toWord = FreeGroup.reduce (y :: w.toWord) := by
  rw [FreeGroup.toWord_mul, ltr, FreeGroup.toWord_mk, FreeGroup.reduce_singleton]
  rfl

theorem norm_ltr_mul_of_eq (y : α × Bool) (w : FreeGroup α) (tl : List (α × Bool))
    (h : w.toWord = flp y :: tl) :
    FreeGroup.norm (ltr y * w) + 1 = FreeGroup.norm w := by
  unfold FreeGroup.norm
  rw [toWord_ltr_mul, FreeGroup.reduce.cons, FreeGroup.reduce_toWord, h]
  simp [flp]

theorem norm_ltr_mul_of_ne (y : α × Bool) (w : FreeGroup α)
    (h : ∀ tl, w.toWord ≠ flp y :: tl) :
    FreeGroup.norm (ltr y * w) = FreeGroup.norm w + 1 := by
  unfold FreeGroup.norm
  rw [toWord_ltr_mul, FreeGroup.reduce.cons, FreeGroup.reduce_toWord]
  rcases hw : w.toWord with _ | ⟨hd, tl⟩
  · simp
  · have : ¬ (y.1 = hd.1 ∧ y.2 = !hd.2) := by
      rintro ⟨h1, h2⟩
      apply h tl
      rw [hw]
      congr 1
      ext
      · exact h1.symm
      · simp [flp, h2]
    simp [this]

/-- If one letter does not increase the length, it is the inverse of the first letter. -/
theorem eq_of_norm_ltr_mul_le (y : α × Bool) (w : FreeGroup α)
    (h : FreeGroup.norm (ltr y * w) ≤ FreeGroup.norm w) :
    ∃ tl, w.toWord = flp y :: tl := by
  by_contra hc
  push Not at hc
  have := norm_ltr_mul_of_ne y w hc
  omega

theorem norm_ltr_mul_le_iff (y : α × Bool) (w : FreeGroup α) :
    FreeGroup.norm (ltr y * w) ≤ FreeGroup.norm w ↔ FreeGroup.norm (ltr y * w) < FreeGroup.norm w := by
  constructor
  · intro h
    obtain ⟨tl, htl⟩ := eq_of_norm_ltr_mul_le y w h
    have := norm_ltr_mul_of_eq y w tl htl
    omega
  · exact le_of_lt

theorem norm_ltr_mul_of_not_lt (y : α × Bool) (w : FreeGroup α)
    (h : ¬ FreeGroup.norm (ltr y * w) < FreeGroup.norm w) :
    FreeGroup.norm (ltr y * w) = FreeGroup.norm w + 1 := by
  apply norm_ltr_mul_of_ne
  intro tl htl
  have := norm_ltr_mul_of_eq y w tl htl
  omega

theorem norm_ltr_mul_of_lt (y : α × Bool) (w : FreeGroup α)
    (h : FreeGroup.norm (ltr y * w) < FreeGroup.norm w) :
    FreeGroup.norm (ltr y * w) + 1 = FreeGroup.norm w := by
  obtain ⟨tl, htl⟩ := eq_of_norm_ltr_mul_le y w h.le
  exact norm_ltr_mul_of_eq y w tl htl

theorem down_unique (y y' : α × Bool) (w : FreeGroup α)
    (h : FreeGroup.norm (ltr y * w) ≤ FreeGroup.norm w)
    (h' : FreeGroup.norm (ltr y' * w) ≤ FreeGroup.norm w) : y = y' := by
  obtain ⟨tl, htl⟩ := eq_of_norm_ltr_mul_le y w h
  obtain ⟨tl', htl'⟩ := eq_of_norm_ltr_mul_le y' w h'
  rw [htl] at htl'
  have := (List.cons.inj htl').1
  rw [← flp_flp y, this, flp_flp]

end StrongConv.CitedGraphs.PartK
end

section
namespace StrongConv.CitedGraphs.PartK
set_option linter.unusedSectionVars false
variable {α : Type*} [DecidableEq α]
variable [Fintype α]
theorem card_down_le_one (w : FreeGroup α) :
    (Finset.univ.filter (fun y : α × Bool => FreeGroup.norm (ltr y * w) < FreeGroup.norm w)).card
      ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact down_unique a b w ha.le hb.le

end StrongConv.CitedGraphs.PartK
end

section
noncomputable section
namespace StrongConv.CitedGraphs.PartK
open scoped InnerProductSpace
theorem sum_inv_wt_le {d : ℕ} (hd : 1 ≤ d) (w : FreeGroup (Fin d)) :
    ∑ y : Fin d × Bool, 1 / wt (2 * d - 1) w (ltr y * w) ≤ 1 := by
  have hq : (1 : ℝ) ≤ 2 * d - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  simp only [wt, apply_ite (fun x : ℝ => 1 / x)]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hc := card_down_le_one w
  have hadd := card_filter_add (d := d) (fun y => FreeGroup.norm (ltr y * w) < FreeGroup.norm w)
  set c := ((Finset.univ.filter (fun y : Fin d × Bool =>
    FreeGroup.norm (ltr y * w) < FreeGroup.norm w)).card : ℝ) with hcdef
  have hc1 : c ≤ 1 := by rw [hcdef]; exact_mod_cast hc
  have hc0 : 0 ≤ c := by positivity
  set e := ((Finset.univ.filter (fun y : Fin d × Bool =>
    ¬ FreeGroup.norm (ltr y * w) < FreeGroup.norm w)).card : ℝ)
  have he : e = 2 * d - c := by linarith
  rw [he]
  have hq0 : (0 : ℝ) < 2 * (2 * d - 1) := by linarith
  have : (2 * d - c) * (1 / (2 * (2 * d - 1))) ≤ 1 - c * (1 / 2) := by
    rw [mul_one_div, div_le_iff₀ hq0]
    nlinarith
  linarith

theorem sum_wt_le {d : ℕ} (hd : 1 ≤ d) (u : FreeGroup (Fin d)) :
    ∑ y : Fin d × Bool, wt (2 * d - 1) (ltr y * u) u ≤ 4 * (2 * d - 1) := by
  have hq : (1 : ℝ) ≤ 2 * d - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  simp only [wt]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hc := card_down_le_one u
  have hadd := card_filter_add (d := d) (fun y => FreeGroup.norm u < FreeGroup.norm (ltr y * u))
  have hcard : (Finset.univ.filter (fun y : Fin d × Bool =>
      ¬ FreeGroup.norm u < FreeGroup.norm (ltr y * u))) =
      (Finset.univ.filter (fun y : Fin d × Bool => FreeGroup.norm (ltr y * u) < FreeGroup.norm u)) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    exact norm_ltr_mul_le_iff y u
  rw [hcard] at hadd ⊢
  set c := ((Finset.univ.filter (fun y : Fin d × Bool =>
    FreeGroup.norm (ltr y * u) < FreeGroup.norm u)).card : ℝ) with hcdef
  have hc1 : c ≤ 1 := by rw [hcdef]; exact_mod_cast hc
  have hc0 : 0 ≤ c := by positivity
  nlinarith

theorem wt_pos {d : ℕ} (hd : 1 ≤ d) (w u : FreeGroup (Fin d)) : 0 < wt (2 * d - 1) w u := by
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  unfold wt; split_ifs <;> linarith

theorem wt_le {d : ℕ} (hd : 1 ≤ d) (w u : FreeGroup (Fin d)) :
    wt (2 * d - 1) w u ≤ 2 * (2 * d - 1) := by
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  unfold wt; split_ifs <;> linarith

theorem adjFree_norm_sq_le {d : ℕ} (hd : 1 ≤ d) (f : L2Free d) :
    ‖adjFree d f‖ ^ 2 ≤ 4 * (2 * d - 1) * ‖f‖ ^ 2 := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hq : (1 : ℝ) ≤ 2 * d - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [norm_sq_eq_tsum, norm_sq_eq_tsum]
  simp_rw [adjFree_apply]
  have hsum_y : ∀ y : Fin d × Bool, Summable (fun w =>
      wt (2 * d - 1) w (ltr y * w) * ‖f (ltr y * w)‖ ^ 2) := fun y =>
    Summable.of_nonneg_of_le (fun w => mul_nonneg (wt_pos hd _ _).le (sq_nonneg _))
      (fun w => mul_le_mul_of_nonneg_right (wt_le hd _ _) (sq_nonneg _))
      ((summable_norm_sq_comp f (ltr y)).mul_left (2 * (2 * (d : ℝ) - 1)))
  have hR : Summable (fun w => ∑ y : Fin d × Bool,
      wt (2 * d - 1) w (ltr y * w) * ‖f (ltr y * w)‖ ^ 2) :=
    summable_sum (fun y _ => hsum_y y)
  have hpt : ∀ w, ‖∑ y : Fin d × Bool, f (ltr y * w)‖ ^ 2 ≤
      ∑ y : Fin d × Bool, wt (2 * d - 1) w (ltr y * w) * ‖f (ltr y * w)‖ ^ 2 := fun w =>
    weighted_cs _ _ _ (fun y _ => wt_pos hd _ _)
      (Finset.sum_pos (fun y _ => one_div_pos.mpr (wt_pos hd _ _)) Finset.univ_nonempty)
      (sum_inv_wt_le hd w)
  have hL : Summable (fun w => ‖∑ y : Fin d × Bool, f (ltr y * w)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun w => sq_nonneg _) hpt hR
  calc ∑' w, ‖∑ y : Fin d × Bool, f (ltr y * w)‖ ^ 2
      ≤ ∑' w, ∑ y : Fin d × Bool, wt (2 * d - 1) w (ltr y * w) * ‖f (ltr y * w)‖ ^ 2 :=
        Summable.tsum_le_tsum hpt hL hR
    _ = ∑' u, ∑ y : Fin d × Bool, wt (2 * d - 1) (ltr y * u) u * ‖f u‖ ^ 2 :=
        tsum_reindex (fun w u => wt (2 * d - 1) w u * ‖f u‖ ^ 2) hsum_y
    _ = ∑' u, (∑ y : Fin d × Bool, wt (2 * d - 1) (ltr y * u) u) * ‖f u‖ ^ 2 := by
        simp [Finset.sum_mul]
    _ ≤ ∑' u, 4 * (2 * d - 1) * ‖f u‖ ^ 2 := by
        have hB : Summable (fun u => 4 * (2 * (d : ℝ) - 1) * ‖f u‖ ^ 2) :=
          (summable_norm_sq f).mul_left _
        have hle : ∀ u, (∑ y : Fin d × Bool, wt (2 * d - 1) (ltr y * u) u) * ‖f u‖ ^ 2 ≤
            4 * (2 * d - 1) * ‖f u‖ ^ 2 := fun u =>
          mul_le_mul_of_nonneg_right (sum_wt_le hd u) (sq_nonneg _)
        exact Summable.tsum_le_tsum hle
          (Summable.of_nonneg_of_le (fun u => mul_nonneg
            (Finset.sum_nonneg (fun y _ => (wt_pos hd _ _).le)) (sq_nonneg _)) hle hB) hB
    _ = 4 * (2 * d - 1) * ∑' u, ‖f u‖ ^ 2 := tsum_mul_left

theorem norm_adjFree_le (d : ℕ) (hd : 1 ≤ d) :
    ‖adjFree d‖ ≤ 2 * Real.sqrt (2 * d - 1) := by
  have hq : (0 : ℝ) ≤ 2 * d - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun f => ?_)
  have h := adjFree_norm_sq_le hd f
  have h2 : (2 * Real.sqrt (2 * d - 1) * ‖f‖) ^ 2 = 4 * (2 * d - 1) * ‖f‖ ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hq]; ring
  rw [← h2] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp h

end StrongConv.CitedGraphs.PartK
end
end

section
noncomputable section
namespace StrongConv.CitedGraphs
open Filter
/-!
# Blueprint: Kesten, Alon–Boppana (Nilli), Friedman's tangle lower bound

Interfaces for the three cited graph results of CGTvH §8. Every lemma below is `sorry`; the three
published statements are proved from them at the end of this file.
-/
/-! ## Kesten: the 2d-regular tree -/
alias norm_adjFree_le := StrongConv.CitedGraphs.PartK.norm_adjFree_le

end StrongConv.CitedGraphs
end
end

section
noncomputable section
namespace StrongConv.CitedGraphs.PartK
open scoped InnerProductSpace
/-! ## Lower bound -/
theorem finite_ball (d n : ℕ) : {w : FreeGroup (Fin d) | FreeGroup.norm w ≤ n}.Finite :=
  (List.finite_length_le (Fin d × Bool) n).preimage FreeGroup.toWord_injective.injOn

theorem summable_of_norm_le {d : ℕ} (g : FreeGroup (Fin d) → ℝ) (n : ℕ)
    (h : ∀ w, g w ≠ 0 → FreeGroup.norm w ≤ n) : Summable g :=
  summable_of_ne_finset_zero (s := (finite_ball d n).toFinset) (fun w hw => by
    by_contra hne
    exact hw (by simpa using h w hne))

/-- `(2d-1)^{-1/2}`. -/
def rr (d : ℕ) : ℝ := (Real.sqrt (2 * d - 1))⁻¹

/-- The radial test function `rr^{|w|}` on the ball of radius `n`. -/
def FF (d n : ℕ) (w : FreeGroup (Fin d)) : ℝ :=
  if FreeGroup.norm w ≤ n then rr d ^ FreeGroup.norm w else 0

theorem FF_ne_zero {d n : ℕ} (w : FreeGroup (Fin d)) (h : FF d n w ≠ 0) : FreeGroup.norm w ≤ n := by
  unfold FF at h; split_ifs at h with h1
  · exact h1
  · exact absurd rfl h

theorem FF_one (d n : ℕ) : FF d n 1 = 1 := by
  simp [FF, FreeGroup.norm_one]

theorem sqrt_mul_rr {d : ℕ} (hd : 1 ≤ d) : Real.sqrt (2 * d - 1) * rr d = 1 := by
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h : 0 < Real.sqrt (2 * d - 1) := Real.sqrt_pos.mpr (by linarith)
  unfold rr
  exact mul_inv_cancel₀ h.ne'

theorem FF_down {d : ℕ} (hd : 1 ≤ d) (n : ℕ) (y : Fin d × Bool) (w : FreeGroup (Fin d))
    (h : FreeGroup.norm (ltr y * w) < FreeGroup.norm w) :
    FF d n w * FF d n (ltr y * w) = Real.sqrt (2 * d - 1) * FF d n w ^ 2 := by
  have h1 := norm_ltr_mul_of_lt y w h
  set j := FreeGroup.norm (ltr y * w)
  unfold FF
  rw [← h1]
  by_cases hn : j + 1 ≤ n
  · rw [if_pos hn, if_pos (by omega)]
    have := sqrt_mul_rr hd
    calc rr d ^ (j + 1) * rr d ^ j = (Real.sqrt (2 * d - 1) * rr d) * (rr d ^ (j + 1) * rr d ^ j) := by
          rw [this, one_mul]
      _ = _ := by ring
  · rw [if_neg hn]; simp

theorem FF_up_sq {d : ℕ} (n : ℕ) (y : Fin d × Bool) (u : FreeGroup (Fin d))
    (h : FreeGroup.norm u < FreeGroup.norm (ltr y * u)) :
    FF d (n + 1) (ltr y * u) ^ 2 = rr d ^ 2 * FF d n u ^ 2 := by
  have h1 := norm_ltr_mul_of_not_lt y u (by omega)
  unfold FF
  rw [h1]
  by_cases hn : FreeGroup.norm u ≤ n
  · rw [if_pos (by omega), if_pos hn]; ring
  · rw [if_neg (by omega), if_neg hn]; ring

end StrongConv.CitedGraphs.PartK
end
end

section
namespace StrongConv.CitedGraphs.PartK
set_option linter.unusedSectionVars false
variable {α : Type*} [DecidableEq α]
variable [Fintype α]
theorem card_down_eq_one (w : FreeGroup α) (hw : w ≠ 1) :
    (Finset.univ.filter (fun y : α × Bool => FreeGroup.norm (ltr y * w) < FreeGroup.norm w)).card
      = 1 := by
  rcases hwd : w.toWord with _ | ⟨hd, tl⟩
  · exact absurd (FreeGroup.toWord_eq_nil_iff.mp hwd) hw
  · rw [Finset.card_eq_one]
    refine ⟨flp hd, ?_⟩
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      obtain ⟨tl', htl'⟩ := eq_of_norm_ltr_mul_le y w h.le
      rw [hwd] at htl'
      rw [(List.cons.inj htl').1, flp_flp]
    · rintro rfl
      have := norm_ltr_mul_of_eq (flp hd) w tl (by rw [hwd, flp_flp])
      omega

theorem card_down_one :
    (Finset.univ.filter (fun y : α × Bool =>
      FreeGroup.norm (ltr y * (1 : FreeGroup α)) < FreeGroup.norm (1 : FreeGroup α))).card = 0 := by
  simp [FreeGroup.norm_one]

end StrongConv.CitedGraphs.PartK
end

section
noncomputable section
namespace StrongConv.CitedGraphs.PartK
open scoped InnerProductSpace
theorem card_down_real {d : ℕ} (w : FreeGroup (Fin d)) :
    ((Finset.univ.filter (fun y : Fin d × Bool =>
      FreeGroup.norm (ltr y * w) < FreeGroup.norm w)).card : ℝ) = if w = 1 then 0 else 1 := by
  split_ifs with hw
  · subst hw; exact_mod_cast card_down_one
  · exact_mod_cast card_down_eq_one w hw

/-- Sum of the down-terms of a function. -/
theorem sum_down {d : ℕ} (g : FreeGroup (Fin d) → ℝ) (w : FreeGroup (Fin d)) :
    ∑ y : Fin d × Bool, (if FreeGroup.norm (ltr y * w) < FreeGroup.norm w then g w else 0) =
      if w = 1 then 0 else g w := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    card_down_real]
  split_ifs <;> simp

theorem TT_succ {d : ℕ} (hd : 1 ≤ d) (n : ℕ) :
    ∑' w, FF d n w ^ 2 + 1 ≤ ∑' w, FF d (n + 1) w ^ 2 := by
  have hq : (1 : ℝ) ≤ 2 * d - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hrq : (2 * (d : ℝ) - 1) * rr d ^ 2 = 1 := by
    have := sqrt_mul_rr hd
    have h2 : Real.sqrt (2 * d - 1) ^ 2 = 2 * d - 1 := Real.sq_sqrt (by linarith)
    rw [← h2, ← mul_pow, this, one_pow]
  set G := fun w => FF d (n + 1) w ^ 2 with hG
  have hsG : Summable G := summable_of_norm_le _ (n + 1) (fun w hw => FF_ne_zero w (by
    intro h0; apply hw; simp [hG, h0]))
  have hsF : Summable (fun w => FF d n w ^ 2) := summable_of_norm_le _ n (fun w hw => FF_ne_zero w (by
    intro h0; apply hw; simp [h0]))
  -- `T(n+1) - 1 = ∑_{w ≠ 1} G w`
  have e1 : ∑' w, G w = ∑' w, (if w = (1 : FreeGroup (Fin d)) then (1 : ℝ) else 0) +
      ∑' w, (if w = 1 then 0 else G w) := by
    rw [← Summable.tsum_add (summable_of_norm_le _ 0 (fun w hw => by
      split_ifs at hw with h
      · subst h; simp [FreeGroup.norm_one]
      · exact absurd rfl hw)) (summable_of_norm_le _ (n + 1) (fun w hw => by
      split_ifs at hw with h
      · exact absurd rfl hw
      · exact FF_ne_zero w (by intro h0; apply hw; simp [hG, h0])))]
    congr 1; ext w
    split_ifs with h
    · subst h; simp [hG, FF_one]
    · simp
  rw [tsum_ite_eq] at e1
  -- reindex
  have e2 : ∑' w, (if w = 1 then 0 else G w) = ∑' w, ∑ y : Fin d × Bool,
      (fun w u => if FreeGroup.norm u < FreeGroup.norm w then G w else 0) w (ltr y * w) := by
    congr 1; ext w; rw [sum_down]
  rw [tsum_reindex (fun w u => if FreeGroup.norm u < FreeGroup.norm w then G w else 0)
    (fun y => summable_of_norm_le _ (n + 1) (fun w hw => by
    split_ifs at hw with h
    · exact FF_ne_zero w (by intro h0; apply hw; simp [hG, h0])
    · exact absurd rfl hw))] at e2
  have e3 : ∀ u, ∑ y : Fin d × Bool,
      (if FreeGroup.norm u < FreeGroup.norm (ltr y * u) then G (ltr y * u) else 0) =
      ((Finset.univ.filter (fun y : Fin d × Bool =>
        FreeGroup.norm u < FreeGroup.norm (ltr y * u))).card : ℝ) * (rr d ^ 2 * FF d n u ^ 2) := by
    intro u
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_congr rfl (fun y hy => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact (FF_up_sq n y u hy : G (ltr y * u) = _))]
    rw [Finset.sum_const, nsmul_eq_mul]
  have e4 : ∀ u, FF d n u ^ 2 ≤ ((Finset.univ.filter (fun y : Fin d × Bool =>
        FreeGroup.norm u < FreeGroup.norm (ltr y * u))).card : ℝ) * (rr d ^ 2 * FF d n u ^ 2) := by
    intro u
    have hc := card_down_le_one u
    have hadd := card_filter_add (d := d) (fun y => FreeGroup.norm u < FreeGroup.norm (ltr y * u))
    have hcard : (Finset.univ.filter (fun y : Fin d × Bool =>
        ¬ FreeGroup.norm u < FreeGroup.norm (ltr y * u))) =
        (Finset.univ.filter (fun y : Fin d × Bool =>
          FreeGroup.norm (ltr y * u) < FreeGroup.norm u)) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      exact norm_ltr_mul_le_iff y u
    rw [hcard] at hadd
    have hc1 : ((Finset.univ.filter (fun y : Fin d × Bool =>
        FreeGroup.norm (ltr y * u) < FreeGroup.norm u)).card : ℝ) ≤ 1 := by exact_mod_cast hc
    have hup : 2 * (d : ℝ) - 1 ≤ ((Finset.univ.filter (fun y : Fin d × Bool =>
        FreeGroup.norm u < FreeGroup.norm (ltr y * u))).card : ℝ) := by linarith
    have h0 : 0 ≤ rr d ^ 2 * FF d n u ^ 2 := by positivity
    calc FF d n u ^ 2 = (2 * (d : ℝ) - 1) * (rr d ^ 2 * FF d n u ^ 2) := by
          rw [← mul_assoc, hrq, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hup h0
  simp_rw [e3] at e2
  have hle : ∑' u, FF d n u ^ 2 ≤ ∑' w, (if w = 1 then 0 else G w) := by
    rw [e2]
    refine Summable.tsum_le_tsum e4 hsF (summable_of_norm_le _ n (fun u hu => ?_))
    apply FF_ne_zero u
    intro h0; apply hu; simp [h0]
  linarith

theorem TT_ge {d : ℕ} (hd : 1 ≤ d) (n : ℕ) : (n : ℝ) + 1 ≤ ∑' w, FF d n w ^ 2 := by
  induction n with
  | zero =>
    have : (fun w : FreeGroup (Fin d) => FF d 0 w ^ 2) = fun w => if w = 1 then 1 else 0 := by
      ext w
      by_cases h : w = 1
      · subst h; simp [FF_one]
      · have : ¬ FreeGroup.norm w ≤ 0 := by
          rw [Nat.le_zero, FreeGroup.norm_eq_zero]; exact h
        simp [FF, this, h]
    rw [this, tsum_ite_eq]; simp
  | succ n ih =>
    have := TT_succ hd n
    push_cast
    linarith

theorem summable_of_FF {d n : ℕ} (g : FreeGroup (Fin d) → ℝ) (h : ∀ w, FF d n w = 0 → g w = 0) :
    Summable g :=
  summable_of_norm_le g n (fun w hw => FF_ne_zero w (fun h0 => hw (h w h0)))

theorem rayleigh_FF {d : ℕ} (hd : 1 ≤ d) (n : ℕ) :
    ∑' w, FF d n w * ∑ y : Fin d × Bool, FF d n (ltr y * w) =
      2 * Real.sqrt (2 * d - 1) * (∑' w, FF d n w ^ 2 - 1) := by
  set c := Real.sqrt (2 * d - 1)
  let HD : FreeGroup (Fin d) → FreeGroup (Fin d) → ℝ := fun w u =>
    if FreeGroup.norm u < FreeGroup.norm w then FF d n w * FF d n u else 0
  let HU : FreeGroup (Fin d) → FreeGroup (Fin d) → ℝ := fun w u =>
    if FreeGroup.norm w < FreeGroup.norm u then FF d n w * FF d n u else 0
  have hsplit : ∀ w, FF d n w * ∑ y : Fin d × Bool, FF d n (ltr y * w) =
      ∑ y : Fin d × Bool, HD w (ltr y * w) + ∑ y : Fin d × Bool, HU w (ltr y * w) := by
    intro w
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    simp only [HD, HU]
    by_cases h : FreeGroup.norm (ltr y * w) < FreeGroup.norm w
    · rw [if_pos h, if_neg (by omega), add_zero]
    · have := norm_ltr_mul_of_not_lt y w h
      rw [if_neg h, if_pos (by omega), zero_add]
  have hsD : ∀ y : Fin d × Bool, Summable (fun w => HD w (ltr y * w)) := fun y =>
    summable_of_FF (n := n) _ (fun w h0 => by simp [HD, h0])
  have hsU : ∀ y : Fin d × Bool, Summable (fun w => HU w (ltr y * w)) := fun y =>
    summable_of_FF (n := n) _ (fun w h0 => by simp [HU, h0])
  have hU : ∑' w, ∑ y : Fin d × Bool, HU w (ltr y * w) =
      ∑' w, ∑ y : Fin d × Bool, HD w (ltr y * w) := by
    rw [tsum_reindex HU hsU]
    congr 1; ext u
    refine Finset.sum_congr rfl (fun y _ => ?_)
    simp only [HU, HD, mul_comm]
  have hD : ∀ w, ∑ y : Fin d × Bool, HD w (ltr y * w) =
      c * FF d n w ^ 2 - if w = 1 then c else 0 := by
    intro w
    have : ∀ y : Fin d × Bool, HD w (ltr y * w) =
        if FreeGroup.norm (ltr y * w) < FreeGroup.norm w then c * FF d n w ^ 2 else 0 := by
      intro y
      simp only [HD]
      split_ifs with h
      · exact FF_down hd n y w h
      · rfl
    simp_rw [this]
    rw [sum_down (fun w => c * FF d n w ^ 2)]
    split_ifs with h
    · subst h; simp [FF_one]
    · simp
  rw [tsum_congr hsplit, Summable.tsum_add (summable_sum (fun y _ => hsD y))
    (summable_sum (fun y _ => hsU y)), hU, tsum_congr hD]
  have hs1 : Summable (fun w => c * FF d n w ^ 2) :=
    summable_of_FF (n := n) _ (fun w h0 => by simp [h0])
  have hs2 : Summable (fun w : FreeGroup (Fin d) => if w = 1 then c else 0) :=
    summable_of_norm_le _ 0 (fun w hw => by
      split_ifs at hw with h
      · subst h; simp [FreeGroup.norm_one]
      · exact absurd rfl hw)
  rw [Summable.tsum_sub hs1 hs2, tsum_mul_left, tsum_ite_eq]
  ring

/-- The test vector. -/
def vec (d n : ℕ) : L2Free d :=
  ⟨fun w => ((FF d n w : ℝ) : ℂ), by
    show Memℓp _ 2
    rw [memℓp_gen_iff (by norm_num)]
    refine summable_of_norm_le _ n (fun w hw => FF_ne_zero w (fun h0 => hw ?_))
    simp [h0]⟩

theorem vec_apply (d n : ℕ) (w : FreeGroup (Fin d)) : vec d n w = ((FF d n w : ℝ) : ℂ) := rfl

theorem norm_vec_sq (d n : ℕ) : ‖vec d n‖ ^ 2 = ∑' w, FF d n w ^ 2 := by
  rw [norm_sq_eq_tsum]
  congr 1; ext w
  rw [vec_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem re_inner_vec (d n : ℕ) :
    RCLike.re ⟪vec d n, adjFree d (vec d n)⟫_ℂ =
      ∑' w, FF d n w * ∑ y : Fin d × Bool, FF d n (ltr y * w) := by
  rw [lp.inner_eq_tsum]
  have : ∀ w, ⟪(vec d n) w, (adjFree d (vec d n)) w⟫_ℂ =
      ((FF d n w * ∑ y : Fin d × Bool, FF d n (ltr y * w) : ℝ) : ℂ) := by
    intro w
    rw [adjFree_apply]
    simp [vec_apply, mul_comm]
  rw [tsum_congr this, ← Complex.ofReal_tsum]
  simp

theorem le_norm_adjFree (d : ℕ) (hd : 1 ≤ d) :
    2 * Real.sqrt (2 * d - 1) ≤ ‖adjFree d‖ := by
  set c := 2 * Real.sqrt (2 * d - 1)
  have hc : 0 ≤ c := by positivity
  have key : ∀ n : ℕ, c * (1 - 1 / ((n : ℝ) + 1)) ≤ ‖adjFree d‖ := by
    intro n
    have hT := TT_ge hd n
    set T := ∑' w, FF d n w ^ 2 with hTdef
    have hT0 : 0 < T := by linarith [(by positivity : (0 : ℝ) ≤ n)]
    have h1 := re_inner_le_norm (𝕜 := ℂ) (vec d n) (adjFree d (vec d n))
    have h2 := (adjFree d).le_opNorm (vec d n)
    rw [re_inner_vec, rayleigh_FF hd n, ← hTdef] at h1
    have h3 : c * (T - 1) ≤ ‖adjFree d‖ * T := by
      have hv := norm_vec_sq d n
      rw [← hTdef] at hv
      calc c * (T - 1) ≤ ‖vec d n‖ * ‖adjFree d (vec d n)‖ := h1
        _ ≤ ‖vec d n‖ * (‖adjFree d‖ * ‖vec d n‖) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = ‖adjFree d‖ * ‖vec d n‖ ^ 2 := by ring
        _ = ‖adjFree d‖ * T := by rw [hv]
    have h4 : c * (1 - 1 / ((n : ℝ) + 1)) ≤ c * (1 - 1 / T) := by
      apply mul_le_mul_of_nonneg_left _ hc
      have : 1 / T ≤ 1 / ((n : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) hT
      linarith
    refine h4.trans ?_
    have : c * (1 - 1 / T) = c * (T - 1) / T := by field_simp
    rw [this, div_le_iff₀ hT0]
    exact h3
  by_contra hlt
  push Not at hlt
  set ε := c - ‖adjFree d‖
  have hε : 0 < ε := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (c / ε)
  have := key n
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have : c / ((n : ℝ) + 1) < ε := by
    rw [div_lt_iff₀ hn1]
    rw [div_lt_iff₀ hε] at hn
    nlinarith
  have : c * (1 - 1 / ((n : ℝ) + 1)) = c - c / ((n : ℝ) + 1) := by ring
  linarith

end StrongConv.CitedGraphs.PartK
end
end

section
noncomputable section
namespace StrongConv.CitedGraphs
open Filter
alias le_norm_adjFree := StrongConv.CitedGraphs.PartK.le_norm_adjFree

/-! ## The three published statements -/
theorem norm_adjFree_dev (d : ℕ) (hd : 1 ≤ d) :
    ‖adjFree d‖ = 2 * Real.sqrt (2 * d - 1) :=
  le_antisymm (norm_adjFree_le d hd) (le_norm_adjFree d hd)

end StrongConv.CitedGraphs
end
end
open StrongConv in
theorem solution (d : ℕ) (hd : 1 ≤ d) :
    ‖adjFree d‖ = 2 * Real.sqrt (2 * d - 1) :=
  StrongConv.CitedGraphs.norm_adjFree_dev d hd
