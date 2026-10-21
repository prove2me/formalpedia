-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P42.circularFlow_turningPoints
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T01:49:07.823823+00:00
-- url     : https://prove2.me/submissions/d96109a0-5fd3-4349-b54a-ed43b6f1ae33

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42
open QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)


theorem g65c_radial_id (c n r l : ℝ) (u : ℝ → ℝ) (hc : 0 < c) (hr : 0 < r) (hu : u r ^ 2 < c ^ 2) :
    radialF c n u r l =
      (1 / (1 - (u r) ^ 2 / c ^ 2)) *
        (n ^ 2 * (1 - u r * l / (c * r)) ^ 2 - (u r / c - l / r) ^ 2) := by
  have hD : 1 - u r ^ 2 / c ^ 2 ≠ 0 := by
    have : u r ^ 2 / c ^ 2 < 1 := by rw [div_lt_one (by positivity)]; exact hu
    linarith
  have hD' : c ^ 2 - u r ^ 2 ≠ 0 := by linarith
  unfold radialF
  field_simp
  ring

theorem g65c_branch (c n r s u' : ℝ) (u : ℝ → ℝ) (hc : 0 < c) (hr : 0 < r)
    (hu : HasDerivAt u u' r) (hs : s = 1 ∨ s = -1) (hne : n * u r + s * c ≠ 0)
    (hD : u r ^ 2 < c ^ 2) :
    HasDerivAt (turningBranch c n u s)
      (turningBranch c n u s r / r - (n ^ 2 - 1) / (n * u r + s * c) ^ 2 * r * u' * c) r ∧
    HasDerivAt (fun a => radialF c n u a (turningBranch c n u s r))
      (s * 2 * n / r * (turningBranch c n u s r / r - (n ^ 2 - 1) / (n * u r + s * c) ^ 2 * r * u' * c)) r := by
  have h1 : HasDerivAt (fun a => a * (n * c + s * u a)) (1 * (n * c + s * u r) + r * (s * u')) r :=
    (hasDerivAt_id' r).mul ((hu.const_mul s).const_add (n * c))
  have h2 : HasDerivAt (fun a => n * u a + s * c) (n * u') r := (hu.const_mul n).add_const _
  have hs2 : s ^ 2 = 1 := by rcases hs with h | h <;> subst h <;> norm_num
  constructor
  · refine (h1.div h2 hne).congr_deriv ?_
    unfold turningBranch
    rcases hs with h | h <;> subst h
    · have hne' : n * u r + c ≠ 0 := by simpa using hne
      simp only [one_mul, neg_mul, ← sub_eq_add_neg] at *
      field_simp
      ring
    · have hne' : n * u r - c ≠ 0 := by simpa [sub_eq_add_neg] using hne
      simp only [one_mul, neg_mul, ← sub_eq_add_neg] at *
      field_simp
      ring
  · set L := turningBranch c n u s r with hL
    have hDne : 1 - u r ^ 2 / c ^ 2 ≠ 0 := by
      have : u r ^ 2 / c ^ 2 < 1 := by rw [div_lt_one (by positivity)]; exact hD
      linarith
    have hA : HasDerivAt (fun a => L ^ 2 / a ^ 2) (-(L ^ 2 * (2 * r)) / (r ^ 2) ^ 2) r := by
      have := (hasDerivAt_const r (L ^ 2)).fun_div (hasDerivAt_pow 2 r) (by positivity)
      refine this.congr_deriv ?_
      simp
    have hDa : HasDerivAt (fun a => 1 - u a ^ 2 / c ^ 2) (-(2 * u r * u' / c ^ 2)) r := by
      have := ((hu.pow 2).div_const (c ^ 2)).const_sub 1
      refine this.congr_deriv ?_
      simp
    have hQ := (hasDerivAt_const r (n ^ 2 - 1)).fun_div hDa hDne
    have hB : HasDerivAt (fun a => 1 - u a * L / (c * a)) (-((u' * L * (c * r) - u r * L * c) / (c * r) ^ 2)) r := by
      have := ((hu.mul_const L).fun_div ((hasDerivAt_id' r).const_mul c) (by positivity)).const_sub 1
      refine this.congr_deriv ?_
      simp
    have H := ((hasDerivAt_const r (1:ℝ)).sub hA).add (hQ.mul (hB.pow 2))
    refine H.congr_deriv ?_
    have hD' : c ^ 2 - u r ^ 2 ≠ 0 := by
      intro h; apply hDne; field_simp; linarith
    simp only [Pi.pow_apply, Nat.cast_ofNat, show (2:ℕ) - 1 = 1 from rfl, pow_one]
    rw [hL]
    unfold turningBranch
    rcases hs with h | h <;> subst h
    · have hne' : n * u r + c ≠ 0 := by simpa using hne
      have h3 : n * u r * c + c ^ 2 ≠ 0 := by
        rw [show n * u r * c + c ^ 2 = c * (n * u r + c) by ring]; exact mul_ne_zero hc.ne' hne'
      simp only [one_mul, neg_mul, ← sub_eq_add_neg] at *
      field_simp
      ring
    · have hne' : n * u r - c ≠ 0 := by simpa [sub_eq_add_neg] using hne
      have h3 : n * u r * c - c ^ 2 ≠ 0 := by
        rw [show n * u r * c - c ^ 2 = c * (n * u r - c) by ring]; exact mul_ne_zero hc.ne' hne'
      simp only [one_mul, neg_mul, ← sub_eq_add_neg] at *
      field_simp
      ring

theorem g65c_radial_zero (c n r l : ℝ) (u : ℝ → ℝ) (hc : 0 < c) (hn : 1 < n) (hr : 0 < r)
    (hu0 : 0 ≤ u r) (hu : u r < c) :
    radialF c n u r l = 0 ↔
      l = turningBranch c n u 1 r ∨ (n * u r ≠ c ∧ l = turningBranch c n u (-1) r) := by
  have hD : 1 - u r ^ 2 / c ^ 2 ≠ 0 := by
    have : u r ^ 2 / c ^ 2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
    linarith
  have hD' : c ^ 2 - u r ^ 2 ≠ 0 := by nlinarith
  have key : radialF c n u r l * (1 - u r ^ 2 / c ^ 2) * (c * r) ^ 2 =
      (r * (n * c + u r) - l * (n * u r + c)) * (r * (n * c - u r) - l * (n * u r - c)) := by
    unfold radialF
    field_simp
    ring
  have hne : (1 - u r ^ 2 / c ^ 2) * (c * r) ^ 2 ≠ 0 := mul_ne_zero hD (by positivity)
  have hp : 0 < n * u r + c := by nlinarith
  have hnc : 0 < n * c - u r := by nlinarith
  constructor
  · intro h
    rw [h, zero_mul, zero_mul] at key
    rcases mul_eq_zero.1 key.symm with h1 | h1
    · left
      simp only [turningBranch, one_mul]
      field_simp
      linarith
    · right
      have hq : n * u r ≠ c := by
        intro he
        rw [show n * u r - c = 0 by linarith] at h1
        nlinarith
      refine ⟨hq, ?_⟩
      have hq' : n * u r - c ≠ 0 := by intro h; apply hq; linarith
      simp only [turningBranch, neg_mul, one_mul, ← sub_eq_add_neg]
      field_simp
      linarith
  · intro h
    have : (r * (n * c + u r) - l * (n * u r + c)) * (r * (n * c - u r) - l * (n * u r - c)) = 0 := by
      rcases h with h | ⟨hq, h⟩
      · subst h
        simp only [turningBranch, one_mul]
        field_simp
        ring
      · subst h
        have hq' : n * u r - c ≠ 0 := by intro h; apply hq; linarith
        simp only [turningBranch, neg_mul, one_mul, ← sub_eq_add_neg]
        field_simp
        ring
    rw [← key] at this
    rcases mul_eq_zero.1 this with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact h2
      · exact absurd h2 hD
    · exact absurd h1 (by positivity)

theorem g65c_vs (c W r : ℝ) (hc : 0 < c) (hW : 0 < W) (hr : 0 < r) :
    HasDerivAt (vortexSpeed c W) (-W / (vortexGamma c W r ^ 3 * r ^ 2)) r := by
  have hc2 : c ^ 2 * r ^ 2 ≠ 0 := by positivity
  have hg : HasDerivAt (fun r => 1 + W ^ 2 / (c ^ 2 * r ^ 2))
      ((0 * (c ^ 2 * r ^ 2) - W ^ 2 * (c ^ 2 * ((2:ℕ) * r ^ (2 - 1)))) / (c ^ 2 * r ^ 2) ^ 2) r :=
    ((hasDerivAt_const r (W ^ 2)).fun_div ((hasDerivAt_pow 2 r).const_mul (c ^ 2)) hc2).const_add 1
  have hgpos : 0 < 1 + W ^ 2 / (c ^ 2 * r ^ 2) := by positivity
  have hγ := hg.sqrt hgpos.ne'
  have hd := hγ.mul (hasDerivAt_id' r)
  have hγp : 0 < vortexGamma c W r := Real.sqrt_pos.2 hgpos
  have hv := (hasDerivAt_const r W).fun_div hd (by
    show vortexGamma c W r * r ≠ 0; positivity)
  refine hv.congr_deriv ?_
  have key : vortexGamma c W r ^ 2 = 1 + W ^ 2 / (c ^ 2 * r ^ 2) := Real.sq_sqrt hgpos.le
  change _ = -W / (vortexGamma c W r ^ 3 * r ^ 2)
  simp only [Pi.mul_apply]
  simp only [show Real.sqrt (1 + W ^ 2 / (c ^ 2 * r ^ 2)) = vortexGamma c W r from rfl,
    Nat.cast_ofNat, show (2:ℕ) - 1 = 1 from rfl, pow_one]
  field_simp
  field_simp at key
  linear_combination (-(2 * W)) * key
theorem solution (c n r : ℝ) (u : ℝ → ℝ)
    (hc : 0 < c) (hn : 1 < n) (hr : 0 < r)
    (hu0 : 0 ≤ u r) (hu : u r < c) (hreg : DifferentiableAt ℝ u r) :
    (∀ l : ℝ, radialF c n u r l =
      (1 / (1 - (u r) ^ 2 / c ^ 2)) *
        (n ^ 2 * (1 - u r * l / (c * r)) ^ 2 - (u r / c - l / r) ^ 2)) ∧
    (∀ l : ℝ, radialF c n u r l = 0 ↔
      l = turningBranch c n u 1 r ∨
        (n * u r ≠ c ∧ l = turningBranch c n u (-1) r)) ∧
    (∀ s : ℝ, (s = 1 ∨ s = -1) → n * u r + s * c ≠ 0 →
      deriv (turningBranch c n u s) r = turningBranch c n u s r / r -
        (n ^ 2 - 1) / (n * u r + s * c) ^ 2 * r * deriv u r * c ∧
      deriv (fun a => radialF c n u a (turningBranch c n u s r)) r =
        s * 2 * n / r * deriv (turningBranch c n u s) r) ∧
    (∀ W : ℝ, 0 < W →
      r * deriv (vortexSpeed c W) r =
        -vortexSpeed c W r * (1 - (vortexSpeed c W r) ^ 2 / c ^ 2) ∧
      0 < turningBranch c n (vortexSpeed c W) 1 r ∧
      0 < deriv (turningBranch c n (vortexSpeed c W) 1) r ∧
      (n * vortexSpeed c W r < c → turningBranch c n (vortexSpeed c W) (-1) r < 0) ∧
      (c < n * vortexSpeed c W r →
        deriv (fun a => radialF c n (vortexSpeed c W) a
          (turningBranch c n (vortexSpeed c W) (-1) r)) r < 0)) := by


  have hc2 : u r ^ 2 < c ^ 2 := by nlinarith
  have gen : ∀ (v : ℝ → ℝ), DifferentiableAt ℝ v r → v r ^ 2 < c ^ 2 → ∀ s : ℝ, (s = 1 ∨ s = -1) →
      n * v r + s * c ≠ 0 →
      deriv (turningBranch c n v s) r = turningBranch c n v s r / r -
        (n ^ 2 - 1) / (n * v r + s * c) ^ 2 * r * deriv v r * c ∧
      deriv (fun a => radialF c n v a (turningBranch c n v s r)) r =
        s * 2 * n / r * deriv (turningBranch c n v s) r := by
    intro v hv hvc s hs hne
    obtain ⟨h1, h2⟩ := g65c_branch c n r s (deriv v r) v hc hr hv.hasDerivAt hs hne hvc
    rw [h1.deriv, h2.deriv]
    exact ⟨rfl, rfl⟩
  refine ⟨fun l => g65c_radial_id c n r l u hc hr hc2, fun l => g65c_radial_zero c n r l u hc hn hr hu0 hu,
    fun s hs hne => gen u hreg hc2 s hs hne, fun W hW => ?_⟩
  -- vortex speed facts
  have hvd := g65c_vs c W r hc hW hr
  have hgsq : vortexGamma c W r ^ 2 = 1 + W ^ 2 / (c ^ 2 * r ^ 2) := Real.sq_sqrt (by positivity)
  have hγp : 0 < vortexGamma c W r := Real.sqrt_pos.2 (by positivity)
  set γ := vortexGamma c W r with hγ
  set v := vortexSpeed c W r with hv
  have hvdef : v = W / (γ * r) := rfl
  have hvpos : 0 < v := by rw [hvdef]; positivity
  have hvc : v < c := by
    rw [hvdef, div_lt_iff₀ (by positivity)]
    have : γ ^ 2 * (c ^ 2 * r ^ 2) = c ^ 2 * r ^ 2 + W ^ 2 := by rw [hgsq]; field_simp
    have h : W ^ 2 < (c * (γ * r)) ^ 2 := by nlinarith [mul_pos hc hr]
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h
  have hvc2 : v ^ 2 < c ^ 2 := by nlinarith
  have hn1 : 0 < n ^ 2 - 1 := by nlinarith
  have hvd' : deriv (vortexSpeed c W) r < 0 := by
    rw [hvd.deriv]; apply div_neg_of_neg_of_pos (by linarith); positivity
  have hpos1 : 0 < n * v + 1 * c := by nlinarith
  have hnc : 0 < n * c + -1 * v := by nlinarith [mul_pos (sub_pos.2 hn) hc]
  have gb := fun s hs hne => gen (vortexSpeed c W) hvd.differentiableAt hvc2 s hs hne
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hvd.deriv, hvdef]
    have : γ ^ 2 * (c ^ 2 * r ^ 2) = c ^ 2 * r ^ 2 + W ^ 2 := by rw [hgsq]; field_simp
    field_simp
    linear_combination this
  · simp only [turningBranch]; rw [← hv]; positivity
  · rw [(gb 1 (Or.inl rfl) hpos1.ne').1]
    have : 0 < turningBranch c n (vortexSpeed c W) 1 r := by
      simp only [turningBranch]; rw [← hv]; positivity
    have h3 : 0 < (n ^ 2 - 1) / (n * v + 1 * c) ^ 2 * r * (-deriv (vortexSpeed c W) r) * c := by
      have := neg_pos.2 hvd'
      positivity
    rw [← hv]
    nlinarith [div_pos this hr]
  · intro hlt
    simp only [turningBranch]; rw [← hv]
    apply div_neg_of_pos_of_neg
    · exact mul_pos hr hnc
    · linarith
  · intro hgt
    have hne : n * v + -1 * c ≠ 0 := by nlinarith
    rw [(gb (-1) (Or.inr rfl) hne).2, (gb (-1) (Or.inr rfl) hne).1]
    have : 0 < turningBranch c n (vortexSpeed c W) (-1) r := by
      simp only [turningBranch]; rw [← hv]
      apply div_pos (mul_pos hr hnc)
      linarith
    have h3 : 0 < (n ^ 2 - 1) / (n * v + -1 * c) ^ 2 * r * (-deriv (vortexSpeed c W) r) * c := by
      have := neg_pos.2 hvd'
      have : 0 < (n * v + -1 * c) ^ 2 := by positivity
      positivity
    rw [← hv]
    have h4 : 0 < turningBranch c n (vortexSpeed c W) (-1) r / r -
        (n ^ 2 - 1) / (n * v + -1 * c) ^ 2 * r * deriv (vortexSpeed c W) r * c := by
      nlinarith [div_pos this hr]
    have h5 : 0 < 2 * n / r := by positivity
    have e : ∀ X : ℝ, (-1:ℝ) * 2 * n / r * X = -(2 * n / r * X) := fun X => by ring
    rw [e]; linarith [mul_pos h5 h4]
