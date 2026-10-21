-- Prove2me | solution 1 for RandomLeadGBS.Diffusion.eq_14
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T10:18:26.854987+00:00
-- url     : https://prove2.me/submissions/89b8c691-b404-4281-97ba-3ed6d4e03cea

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model

open RandomLeadGBS.Diffusion

namespace GBSEq14

/-- Summing a summable family over one level `{s | s.1 = k}` of `ℤ × ℕ`. -/
lemma level_sum (g : State → ℝ) (hg : Summable g) (k : ℤ) :
    ∑' s : State, (if s.1 = k then g s else 0) = ∑' z : ℕ, g (k, z) := by
  have hs : Summable (fun s : State => if s.1 = k then g s else 0) := by
    refine Summable.of_norm_bounded hg.abs (fun s => ?_)
    split_ifs <;> simp
  rw [Summable.tsum_prod hs]
  have : (fun y : ℤ => ∑' z : ℕ, (if (y, z).1 = k then g (y, z) else 0)) =
      fun y => if y = k then ∑' z : ℕ, g (k, z) else 0 := by
    funext y
    by_cases hy : y = k
    · subst hy; simp
    · simp [hy]
  rw [this, tsum_ite_eq]

/-- Row sums of the rate matrix against a test function. -/
lemma row (P : Params) (r : ℝ) (s : State) (h : State → ℝ) :
    (fun s' => rate P r s s' * h s') =
      fun s' => (if s' = afterCustomer P r s then r * h (afterCustomer P r s) else 0) +
        (if s' = afterItem P r s then P.β * (s.2 : ℝ) * h (afterItem P r s) else 0) := by
  funext s'
  simp only [rate, add_mul]
  congr 1
  · split_ifs with h1
    · subst h1; rfl
    · simp
  · by_cases h1 : s' = afterItem P r s
    · subst h1
      by_cases hz : 1 ≤ s.2
      · simp [hz]
      · have : s.2 = 0 := by omega
        simp [this]
    · simp [h1]

lemma row_summable (P : Params) (r : ℝ) (s : State) (h : State → ℝ) :
    Summable (fun s' => rate P r s s' * h s') := by
  rw [row]
  exact (summable_of_ne_finset_zero (s := {afterCustomer P r s}) (by intro j hj; simp_all)).add
    (summable_of_ne_finset_zero (s := {afterItem P r s}) (by intro j hj; simp_all))

lemma row_tsum (P : Params) (r : ℝ) (s : State) (h : State → ℝ) :
    ∑' s', rate P r s s' * h s' =
      r * h (afterCustomer P r s) + P.β * (s.2 : ℝ) * h (afterItem P r s) := by
  rw [row, Summable.tsum_add
    (summable_of_ne_finset_zero (s := {afterCustomer P r s}) (by intro j hj; simp_all))
    (summable_of_ne_finset_zero (s := {afterItem P r s}) (by intro j hj; simp_all)),
    tsum_ite_eq, tsum_ite_eq]

lemma rate_nonneg (P : Params) (r : ℝ) (hr : 0 < r) (hβ : 0 < P.β) (s s' : State) :
    0 ≤ rate P r s s' := by
  unfold rate
  apply add_nonneg
  · split_ifs <;> linarith
  · split_ifs
    · positivity
    · rfl

/-- The flux identity: for a bounded test function `h`, stationarity gives
`E[ r h(after customer) + β Z h(after item) ] = E[(r + β Z) h]`. -/
lemma flux (P : Params) (r : ℝ) (hr : 0 < r) (hβ : 0 < P.β) (p : State → ℝ)
    (hp : IsStationary P r p) (h : State → ℝ) (hh : ∀ s, |h s| ≤ 1) :
    ∑' s, p s * (r * h (afterCustomer P r s) + P.β * (s.2 : ℝ) * h (afterItem P r s)) =
      ∑' s, p s * exitRate P r s * h s := by
  obtain ⟨hnn, _hsum, _hone, hsumx, hbal⟩ := hp
  -- summability of the double family
  have hG : Summable (fun x : State × State => p x.1 * rate P r x.1 x.2) := by
    refine (summable_prod_of_nonneg (fun x => mul_nonneg (hnn _) (rate_nonneg P r hr hβ _ _))).mpr
      ⟨fun s => ?_, ?_⟩
    · simpa using (row_summable P r s (fun _ => 1)).mul_left (p s)
    · have : (fun s : State => ∑' s' : State, p (s, s').1 * rate P r (s, s').1 (s, s').2) =
          fun s => p s * exitRate P r s := by
        funext s
        simp only
        rw [tsum_mul_left]
        have := row_tsum P r s (fun _ => 1)
        simp only [mul_one] at this
        rw [this, exitRate]
      rw [this]; exact hsumx
  have hF : Summable (Function.uncurry (fun s s' : State => p s * rate P r s s' * h s')) := by
    refine Summable.of_norm_bounded hG (fun x => ?_)
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (hnn _), abs_of_nonneg (rate_nonneg P r hr hβ _ _)]
    have := hh x.2
    have h0 : 0 ≤ p x.1 * rate P r x.1 x.2 := mul_nonneg (hnn _) (rate_nonneg P r hr hβ _ _)
    nlinarith
  symm
  calc ∑' s, p s * exitRate P r s * h s
      = ∑' s', (∑' s, p s * rate P r s s') * h s' := by
        congr 1; funext s'; rw [hbal s']
    _ = ∑' s', ∑' s, p s * rate P r s s' * h s' := by
        congr 1; funext s'; rw [tsum_mul_right]
    _ = ∑' s, ∑' s', p s * rate P r s s' * h s' := hF.tsum_comm
    _ = ∑' s, p s * (r * h (afterCustomer P r s) + P.β * (s.2 : ℝ) * h (afterItem P r s)) := by
        congr 1; funext s
        rw [← row_tsum, ← tsum_mul_left]
        congr 1; funext s'; ring

end GBSEq14

open GBSEq14

theorem solution (P : Params) (hP : P.Standing) (hx : ∀ r, P.xs r = 0) (r : ℝ) (hr : 0 < r)
    (p : State → ℝ) (hp : IsStationary P r p) :
    Summable (fun s : State => p s * (s.2 : ℝ)) ∧
    P.β * ∑' s : State, p s * (s.2 : ℝ) = r := by
  obtain ⟨hβ, -, -, -, -⟩ := hP
  have hp' := hp
  obtain ⟨hnn, hsum, hone, hsumx, _hbal⟩ := hp'
  have hsZ : Summable (fun s : State => p s * (s.2 : ℝ)) := by
    have : (fun s : State => p s * (s.2 : ℝ)) =
        fun s => (p s * exitRate P r s - r * p s) / P.β := by
      funext s; simp only [exitRate]; field_simp; ring
    rw [this]; exact (hsumx.sub (hsum.mul_left r)).div_const _
  -- level quantities
  set m : ℤ → ℝ := fun k => ∑' z : ℕ, p (k, z) with hm
  set w : ℤ → ℝ := fun k => ∑' z : ℕ, p (k, z) * (z : ℝ) with hw
  have hlev : ∀ k : ℤ, r * m (k + 1) + P.β * w (k - 1) = r * m k + P.β * w k := by
    intro k
    have hfl := flux P r hr hβ p hp (fun s => if s.1 = k then 1 else 0)
      (fun s => by split_ifs <;> simp)
    have hL : (fun s : State => p s * (r * (if (afterCustomer P r s).1 = k then (1:ℝ) else 0) +
        P.β * (s.2 : ℝ) * (if (afterItem P r s).1 = k then (1:ℝ) else 0))) =
        fun s => (if s.1 = k + 1 then r * p s else 0) +
          (if s.1 = k - 1 then P.β * (p s * (s.2 : ℝ)) else 0) := by
      funext s
      have e1 : (afterCustomer P r s).1 = s.1 - 1 := rfl
      have e2 : (afterItem P r s).1 = s.1 + 1 := rfl
      simp only [e1, e2]
      split_ifs <;> first | (exfalso; omega) | ring
    have hR : (fun s : State => p s * exitRate P r s * (if s.1 = k then (1:ℝ) else 0)) =
        fun s => (if s.1 = k then r * p s else 0) +
          (if s.1 = k then P.β * (p s * (s.2 : ℝ)) else 0) := by
      funext s
      simp only [exitRate]
      split_ifs <;> ring
    rw [hL, hR] at hfl
    have s1 : ∀ k' : ℤ, Summable (fun s : State => if s.1 = k' then r * p s else 0) := by
      intro k'
      refine Summable.of_norm_bounded ((hsum.mul_left r).abs) (fun s => ?_)
      split_ifs <;> simp <;> positivity
    have s2 : ∀ k' : ℤ, Summable (fun s : State =>
        if s.1 = k' then P.β * (p s * (s.2 : ℝ)) else 0) := by
      intro k'
      refine Summable.of_norm_bounded ((hsZ.mul_left P.β).abs) (fun s => ?_)
      split_ifs <;> simp <;> positivity
    rw [Summable.tsum_add (s1 _) (s2 _), Summable.tsum_add (s1 _) (s2 _),
      level_sum _ (hsum.mul_left r), level_sum _ (hsum.mul_left r),
      level_sum _ (hsZ.mul_left P.β), level_sum _ (hsZ.mul_left P.β)] at hfl
    simp only [tsum_mul_left] at hfl
    simpa [hm, hw] using hfl
  -- φ k = β w k - r m (k+1) is constant
  set φ : ℤ → ℝ := fun k => P.β * w k - r * m (k + 1) with hφ
  have hstep : ∀ k : ℤ, φ k = φ (k - 1) := by
    intro k
    have := hlev k
    simp only [hφ, sub_add_cancel]; linarith
  have hconst : ∀ k : ℤ, φ k = φ 0 := by
    intro k
    induction k using Int.induction_on with
    | zero => rfl
    | succ k ih => rw [hstep (k + 1)]; simpa using ih
    | pred k ih => have := hstep (-(k:ℤ)); linarith
  have hpnn : 0 ≤ p := fun s => hnn s
  have hsm : Summable m := ((summable_prod_of_nonneg hpnn).mp hsum).2
  have hsw : Summable w := by
    have h0 : 0 ≤ (fun s : State => p s * (s.2 : ℝ)) := fun s => mul_nonneg (hnn s) (by positivity)
    exact ((summable_prod_of_nonneg h0).mp hsZ).2
  have hsm1 : Summable (fun k : ℤ => r * m (k + 1)) :=
    (Equiv.addRight (1 : ℤ)).summable_iff.mpr (hsm.mul_left r)
  have hsφ : Summable φ := (hsw.mul_left P.β).sub hsm1
  have hφ0 : φ 0 = 0 := by
    have : Summable (fun _ : ℤ => φ 0) := by
      have : φ = fun _ => φ 0 := funext hconst
      rwa [this] at hsφ
    exact (summable_const_iff (φ 0)).mp this
  have hab : ∀ k, P.β * w k = r * m (k + 1) := by
    intro k; have := hconst k; rw [hφ0] at this; simp only [hφ] at this; linarith
  refine ⟨hsZ, ?_⟩
  rw [Summable.tsum_prod hsZ, ← tsum_mul_left]
  have : (fun k : ℤ => P.β * ∑' z : ℕ, p (k, z) * (z : ℝ)) = fun k => r * m (k + 1) := by
    funext k; exact hab k
  rw [this]
  have h1 : ∑' k : ℤ, r * m (k + 1) = ∑' k : ℤ, r * m k :=
    (Equiv.addRight (1 : ℤ)).tsum_eq (fun k => r * m k)
  rw [h1, tsum_mul_left]
  have : ∑' k : ℤ, m k = 1 := by
    rw [← hone, Summable.tsum_prod hsum]
  rw [this, mul_one]
