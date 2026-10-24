-- Prove2me | solution 1 for SampleDrivenOS.Linear.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T13:48:56.636424+00:00
-- url     : https://prove2.me/submissions/6aac9abc-00d0-4fb2-ab18-5b5c8d305694

import Mathlib
import Definitions.Def_SampleDrivenOS_Linear_Setting
import Theorems.Thm_SampleDrivenOS_Linear_b9_reduction
import Theorems.Thm_SampleDrivenOS_Linear_b9_equiv_a
import Theorems.Thm_SampleDrivenOS_Linear_b9_a_deriv_nonpos
import Theorems.Thm_SampleDrivenOS_Linear_alphaStar_mem_Icc

set_option autoImplicit false
open SampleDrivenOS.Linear

lemma thm9_w_le_one {p : ℝ} (hp0 : 0 ≤ p) (k : ℕ) :
    p ^ k * (1 + (k : ℝ) * (1 - p)) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : p ^ k * (1 + (k : ℝ) * (1 - p)) - p ^ (k + 1) * (1 + ((k + 1 : ℕ) : ℝ) * (1 - p))
        = p ^ k * (1 - p) ^ 2 * ((k : ℝ) + 1) := by push_cast; ring
    have : 0 ≤ p ^ k * (1 - p) ^ 2 * ((k : ℝ) + 1) := by positivity
    linarith

lemma thm9_w_bounds {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (i : ℕ) :
    0 ≤ p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)) ∧
      p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)) ≤ 1 := by
  refine ⟨?_, ?_⟩
  · have : 0 ≤ 1 - p := by linarith
    positivity
  · have := thm9_w_le_one hp0.le (i + 1)
    push_cast at this
    exact this

/-- `a(p)` is continuous on `[q, 1]` for `q > 0`: the series is dominated by
`M / ((i+1)(i+2))`. -/
lemma aB9_continuousOn (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (q : ℝ) (hq : 0 < q) :
    ContinuousOn (aB9 s) (Set.Icc q 1) := by
  set M : ℝ := Real.log (1 / q) - Real.log (1 - s) with hM
  have hsum : Summable (fun i : ℕ => M * (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2)))) := by
    have h : Summable (fun i : ℕ => 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) := by
      have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
      refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) this
      push_cast
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    exact h.mul_left M
  have hD : ∀ x ∈ Set.Icc q 1, ∀ i : ℕ,
      1 - s ≤ 1 / x - s * (1 - x ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - x))) ∧
      1 / x - s * (1 - x ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - x))) ≤ 1 / q := by
    intro x hx i
    have hx0 : 0 < x := lt_of_lt_of_le hq hx.1
    obtain ⟨hw0, hw1⟩ := thm9_w_bounds hx0 hx.2 i
    have h1 : 1 ≤ 1 / x := by rw [le_div_iff₀ hx0]; linarith [hx.2]
    have h2 : 1 / x ≤ 1 / q := one_div_le_one_div_of_le hq hx.1
    constructor <;> nlinarith
  have hcont : ContinuousOn (fun x => ∑' i : ℕ,
      Real.log (1 / x - s * (1 - x ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - x)))) /
        (((i : ℝ) + 1) * ((i : ℝ) + 2))) (Set.Icc q 1) := by
    refine continuousOn_tsum (u := fun i : ℕ => M * (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))))
      (fun i => ?_) hsum (fun i x hx => ?_)
    · apply ContinuousOn.div_const
      apply ContinuousOn.log
      · apply ContinuousOn.sub
        · apply ContinuousOn.div continuousOn_const continuousOn_id
          intro x hx; exact (lt_of_lt_of_le hq hx.1).ne'
        · fun_prop
      · intro x hx
        have := (hD x hx i).1
        linarith
    · obtain ⟨h1, h2⟩ := hD x hx i
      have hpos : 0 < 1 - s := by linarith
      have hA : 0 < ((i : ℝ) + 1) * ((i : ℝ) + 2) := by positivity
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hA, div_le_iff₀ hA]
      have hl1 : Real.log (1 - s) ≤ Real.log (1 / x - s * (1 - x ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - x)))) :=
        Real.log_le_log hpos h1
      have hl2 : Real.log (1 / x - s * (1 - x ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - x)))) ≤ Real.log (1 / q) :=
        Real.log_le_log (by linarith) h2
      have hq1 : q ≤ 1 := le_trans hx.1 hx.2
      have hlq : 0 ≤ Real.log (1 / q) := Real.log_nonneg (by rw [le_div_iff₀ hq]; linarith)
      have hls : Real.log (1 - s) ≤ 0 := Real.log_nonpos hpos.le (by linarith)
      have : M * (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) * (((i : ℝ) + 1) * ((i : ℝ) + 2)) = M := by
        field_simp
      rw [this, abs_le]
      constructor <;> linarith
  unfold aB9
  exact hcont.add (by fun_prop)

lemma aB9_one (s : ℝ) : aB9 s 1 = s := by
  unfold aB9
  simp
  ring

theorem solution (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (a : ℝ) (ha : SampleDrivenOS.Limit.IsAlphaTilde p a)
    (s : ℝ) (hs : SampleDrivenOS.Limit.IsAlphaStar s) : s * p ≤ a := by
  obtain ⟨hp0, hp1⟩ := hp
  have hs0 : 0 < s := hs.1
  have hs1 : s < 1 := hs.2.1
  have hs' := alphaStar_mem_Icc s hs
  -- `a` is antitone on `[p, 1]`
  have hanti : AntitoneOn (aB9 s) (Set.Icc p 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc p 1) (aB9_continuousOn s hs0 hs1 p hp0)
    · intro x hx
      rw [interior_Icc] at hx
      obtain ⟨d, hd, _⟩ := b9_a_deriv_nonpos s hs hs' x ⟨by linarith [hx.1], hx.2⟩
      exact hd.differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      obtain ⟨d, hd, hd0⟩ := b9_a_deriv_nonpos s hs hs' x ⟨by linarith [hx.1], hx.2⟩
      rw [hd.deriv]
      exact hd0
  have hle : s ≤ aB9 s p := by
    have := hanti ⟨le_refl p, hp1.le⟩ ⟨hp1.le, le_refl 1⟩ hp1.le
    rwa [aB9_one] at this
  have h := (b9_equiv_a p ⟨hp0, hp1⟩ s ⟨hs0, hs1⟩).mpr hle
  have hsp : s * p < 1 := by nlinarith
  exact b9_reduction p ⟨hp0, hp1⟩ a ha s hs0 hsp h
