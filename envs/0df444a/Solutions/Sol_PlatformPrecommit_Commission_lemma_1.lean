-- Prove2me | solution 1 for PlatformPrecommit.Commission.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T11:13:46.319297+00:00
-- url     : https://prove2.me/submissions/e775fc84-0f4e-4c7f-adf8-565040e5dce8

import Mathlib
import Definitions.Def_PlatformPrecommit_Commission_Setting

open PlatformPrecommit.Commission

namespace L1Aux

/-- Profit of a platform facing the intercepts `A` (demand) and `B` (supply). -/
noncomputable def f (A B p w : ℝ) : ℝ := (p - w) * min (max (A - p) 0) (max (w - B) 0)

theorem f_le (A B p w : ℝ) : f A B p w ≤ (A - B) ^ 2 / 8 := by
  unfold f
  set m := min (max (A - p) 0) (max (w - B) 0) with hm
  have hm0 : 0 ≤ m := le_min (le_max_right _ _) (le_max_right _ _)
  by_cases hpw : p - w ≤ 0
  · have : (p - w) * m ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hpw hm0
    have : 0 ≤ (A - B) ^ 2 / 8 := by positivity
    linarith
  push Not at hpw
  rcases hm0.eq_or_lt with h0 | h0
  · rw [← h0]; simp; positivity
  have h1 : m ≤ max (A - p) 0 := min_le_left _ _
  have h2 : m ≤ max (w - B) 0 := min_le_right _ _
  have hA : m ≤ A - p := by
    rcases le_total (A - p) 0 with h | h
    · rw [max_eq_right h] at h1; linarith
    · rwa [max_eq_left h] at h1
  have hB : m ≤ w - B := by
    rcases le_total (w - B) 0 with h | h
    · rw [max_eq_right h] at h2; linarith
    · rwa [max_eq_left h] at h2
  nlinarith [sq_nonneg (m - (A - B) / 4)]

/-- The unique maximizer when the maximum is positive. -/
theorem f_eq (A B p w : ℝ) (hpos : 0 < f A B p w) (hmax : (A - B) ^ 2 / 8 ≤ f A B p w) :
    p = (3 * A + B) / 4 ∧ w = (A + 3 * B) / 4 ∧
      min (max (A - p) 0) (max (w - B) 0) = (A - B) / 4 ∧ 0 < A - B := by
  unfold f at *
  set m := min (max (A - p) 0) (max (w - B) 0) with hm
  have hm0 : 0 ≤ m := le_min (le_max_right _ _) (le_max_right _ _)
  have hmpos : 0 < m := by
    rcases hm0.eq_or_lt with h0 | h0
    · rw [← h0] at hpos; simp at hpos
    · exact h0
  have hpw : 0 < p - w := by
    by_contra h; push Not at h; nlinarith
  have h1 : m ≤ max (A - p) 0 := min_le_left _ _
  have h2 : m ≤ max (w - B) 0 := min_le_right _ _
  have hA : m ≤ A - p := by
    rcases le_total (A - p) 0 with h | h
    · rw [max_eq_right h] at h1; linarith
    · rwa [max_eq_left h] at h1
  have hB : m ≤ w - B := by
    rcases le_total (w - B) 0 with h | h
    · rw [max_eq_right h] at h2; linarith
    · rwa [max_eq_left h] at h2
  have hsq : (m - (A - B) / 4) ^ 2 = 0 := by
    nlinarith [sq_nonneg (m - (A - B) / 4), mul_le_mul_of_nonneg_left (by linarith : p - w ≤ A - B - 2 * m) hmpos.le]
  have hmv : m = (A - B) / 4 := by nlinarith [sq_nonneg (m - (A - B) / 4)]
  have hpw' : p - w = A - B - 2 * m := by
    have : (p - w) * m ≥ (A - B - 2 * m) * m := by nlinarith
    have : p - w ≥ A - B - 2 * m := le_of_mul_le_mul_right this hmpos
    linarith
  refine ⟨by linarith, by linarith, hmv, by linarith⟩

theorem f_at (A B : ℝ) (h : 0 ≤ A - B) :
    f A B ((3 * A + B) / 4) ((A + 3 * B) / 4) = (A - B) ^ 2 / 8 := by
  unfold f
  have e1 : A - (3 * A + B) / 4 = (A - B) / 4 := by ring
  have e2 : (A + 3 * B) / 4 - B = (A - B) / 4 := by ring
  rw [e1, e2, max_eq_left (by linarith), min_self]; ring

theorem rival_ne (i : Fin 2) : rival i ≠ i := by
  fin_cases i <;> simp [rival]

theorem profP_eq (M : Model) (x : PW) (i : Fin 2) :
    profP M x i = f (M.Ω + M.γ * x.1 (rival i)) (M.β * x.2 (rival i)) (x.1 i) (x.2 i) := by
  simp only [profP, matchP, demand, supply, f]
  congr 2 <;> congr 1 <;> ring

theorem profP_dev (M : Model) (x : PW) (i : Fin 2) (a b : ℝ) :
    profP M (Function.update x.1 i a, Function.update x.2 i b) i =
      f (M.Ω + M.γ * x.1 (rival i)) (M.β * x.2 (rival i)) a b := by
  rw [profP_eq]
  simp only [Function.update_self, Function.update_of_ne (rival_ne i)]

theorem matchP_eq (M : Model) (x : PW) (i : Fin 2) :
    matchP M x i = min (max ((M.Ω + M.γ * x.1 (rival i)) - x.1 i) 0)
      (max (x.2 i - M.β * x.2 (rival i)) 0) := by
  simp only [matchP, demand, supply]
  congr 2; ring

end L1Aux

open L1Aux in
theorem solution (M : Model) (hM : M.Standing) :
    let D : ℝ := 4 - 3 * M.β - 3 * M.γ + 2 * M.β * M.γ
    let pw : PW :=
      (fun _ => (3 - 2 * M.β) / D * M.Ω, fun _ => 1 / D * M.Ω)
    (IsPNE M pw ∧ ∀ i, 0 < profP M pw i) ∧
    (∀ x, IsPNE M x → (∀ i, 0 < profP M x i) → ∀ i,
      x.1 i = (3 - 2 * M.β) / D * M.Ω ∧
      x.2 i = 1 / D * M.Ω ∧
      matchP M x i = (1 - M.β) / D * M.Ω ∧
      profP M x i = 2 * (1 - M.β) ^ 2 / D ^ 2 * M.Ω ^ 2) := by
  intro D pw
  obtain ⟨hΩ, hb0, hb1, hg0, hg1⟩ := hM
  have hD : 0 < D := by
    show 0 < 4 - 3 * M.β - 3 * M.γ + 2 * M.β * M.γ
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - M.β) (by linarith : (0:ℝ) ≤ 1 - M.γ)]
  -- the intercepts at the candidate
  have hAB : ∀ i, (M.Ω + M.γ * pw.1 (rival i)) - M.β * pw.2 (rival i) = 4 * (1 - M.β) / D * M.Ω := by
    intro i; simp only [pw]; field_simp; (try simp only [D]); ring
  have hp : ∀ i, pw.1 i = (3 * (M.Ω + M.γ * pw.1 (rival i)) + M.β * pw.2 (rival i)) / 4 := by
    intro i; simp only [pw]; field_simp; (try simp only [D]); ring
  have hw : ∀ i, pw.2 i = ((M.Ω + M.γ * pw.1 (rival i)) + 3 * (M.β * pw.2 (rival i))) / 4 := by
    intro i; simp only [pw]; field_simp; (try simp only [D]); ring
  have hval : ∀ i, profP M pw i = 2 * (1 - M.β) ^ 2 / D ^ 2 * M.Ω ^ 2 := by
    intro i
    rw [profP_eq]
    simp only [pw, f]
    have e1 : M.Ω + M.γ * ((3 - 2 * M.β) / D * M.Ω) - (3 - 2 * M.β) / D * M.Ω =
        (1 - M.β) / D * M.Ω := by field_simp; (try simp only [D]); ring
    have e2 : 1 / D * M.Ω - M.β * (1 / D * M.Ω) = (1 - M.β) / D * M.Ω := by ring
    have hz : 0 ≤ (1 - M.β) / D * M.Ω := mul_nonneg (div_nonneg (by linarith) hD.le) hΩ.le
    rw [e1, e2, max_eq_left hz, min_self]
    field_simp; (try simp only [D]); ring
  have hvpos : 0 < 2 * (1 - M.β) ^ 2 / D ^ 2 * M.Ω ^ 2 := by
    have : 0 < 1 - M.β := by linarith
    positivity
  refine ⟨⟨?_, fun i => by rw [hval i]; exact hvpos⟩, ?_⟩
  · refine ⟨trivial, ?_⟩
    intro i ab _
    show profP M (Function.update pw.1 i ab.1, Function.update pw.2 i ab.2) i ≤ profP M pw i
    rw [profP_dev, hval i]
    have := f_le (M.Ω + M.γ * pw.1 (rival i)) (M.β * pw.2 (rival i)) ab.1 ab.2
    rw [hAB i] at this
    calc _ ≤ _ := this
      _ = _ := by field_simp; ring
  · intro x hx hxpos
    -- each platform plays its unique best response
    have hbr : ∀ i, x.1 i = (3 * (M.Ω + M.γ * x.1 (rival i)) + M.β * x.2 (rival i)) / 4 ∧
        x.2 i = ((M.Ω + M.γ * x.1 (rival i)) + 3 * (M.β * x.2 (rival i))) / 4 ∧
        matchP M x i = ((M.Ω + M.γ * x.1 (rival i)) - M.β * x.2 (rival i)) / 4 ∧
        0 < (M.Ω + M.γ * x.1 (rival i)) - M.β * x.2 (rival i) := by
      intro i
      set A := M.Ω + M.γ * x.1 (rival i)
      set B := M.β * x.2 (rival i)
      have hpos := hxpos i
      rw [profP_eq] at hpos
      -- positivity forces A > B
      have hAB0 : 0 ≤ A - B := by
        by_contra hneg; push Not at hneg
        have := f_le A B (x.1 i) (x.2 i)
        -- refine: positive profit implies A - B > 2m > 0
        unfold f at hpos
        set m := min (max (A - x.1 i) 0) (max (x.2 i - B) 0)
        have hm0 : 0 ≤ m := le_min (le_max_right _ _) (le_max_right _ _)
        have hmpos : 0 < m := by
          rcases hm0.eq_or_lt with h0 | h0
          · rw [← h0] at hpos; simp at hpos
          · exact h0
        have h1 : m ≤ max (A - x.1 i) 0 := min_le_left _ _
        have h2 : m ≤ max (x.2 i - B) 0 := min_le_right _ _
        have hA : m ≤ A - x.1 i := by
          rcases le_total (A - x.1 i) 0 with h | h
          · rw [max_eq_right h] at h1; linarith
          · rwa [max_eq_left h] at h1
        have hB : m ≤ x.2 i - B := by
          rcases le_total (x.2 i - B) 0 with h | h
          · rw [max_eq_right h] at h2; linarith
          · rwa [max_eq_left h] at h2
        nlinarith
      have hdev := hx.2 i ((3 * A + B) / 4, (A + 3 * B) / 4) trivial
      simp only at hdev
      rw [profP_dev, profP_eq, f_at _ _ hAB0] at hdev
      obtain ⟨e1, e2, e3, e4⟩ := f_eq A B (x.1 i) (x.2 i) hpos hdev
      refine ⟨e1, e2, ?_, e4⟩
      rw [matchP_eq]; exact e3
    have r0 : rival 0 = 1 := rfl
    have r1 : rival 1 = 0 := rfl
    obtain ⟨p0, w0, _, _⟩ := hbr 0
    obtain ⟨p1, w1, _, _⟩ := hbr 1
    rw [r0] at p0 w0
    rw [r1] at p1 w1
    -- solve the linear system
    have hdet : 0 < (4 + 3 * M.γ) * (4 + 3 * M.β) - M.β * M.γ := by nlinarith
    have dp : x.1 0 = x.1 1 ∧ x.2 0 = x.2 1 := by
      have e1 : (4 + 3 * M.γ) * (x.1 0 - x.1 1) + M.β * (x.2 0 - x.2 1) = 0 := by linarith
      have e2 : M.γ * (x.1 0 - x.1 1) + (4 + 3 * M.β) * (x.2 0 - x.2 1) = 0 := by linarith
      have h1 : ((4 + 3 * M.γ) * (4 + 3 * M.β) - M.β * M.γ) * (x.1 0 - x.1 1) = 0 := by
        linear_combination (4 + 3 * M.β) * e1 - M.β * e2
      have h2 : ((4 + 3 * M.γ) * (4 + 3 * M.β) - M.β * M.γ) * (x.2 0 - x.2 1) = 0 := by
        linear_combination (4 + 3 * M.γ) * e2 - M.γ * e1
      constructor
      · have := (mul_eq_zero.mp h1).resolve_left hdet.ne'; linarith
      · have := (mul_eq_zero.mp h2).resolve_left hdet.ne'; linarith
    have hsol : x.1 0 = (3 - 2 * M.β) / D * M.Ω ∧ x.2 0 = 1 / D * M.Ω := by
      rw [← dp.1, ← dp.2] at p0 w0
      -- p = (3Ω + 3γp + βw)/4, w = (Ω + γp + 3βw)/4
      have ep : (4 - 3 * M.γ) * x.1 0 - M.β * x.2 0 = 3 * M.Ω := by linarith
      have ew : -M.γ * x.1 0 + (4 - 3 * M.β) * x.2 0 = M.Ω := by linarith
      have hD4 : (4 - 3 * M.γ) * (4 - 3 * M.β) - M.β * M.γ = 4 * D := by simp only [D]; ring
      constructor
      · field_simp
        have : 4 * D * x.1 0 = 4 * ((3 - 2 * M.β) * M.Ω) := by
          rw [← hD4]; linear_combination (4 - 3 * M.β) * ep + M.β * ew
        linarith
      · field_simp
        have : 4 * D * x.2 0 = 4 * M.Ω := by
          rw [← hD4]; linear_combination M.γ * ep + (4 - 3 * M.γ) * ew
        linarith
    have hall : ∀ i, x.1 i = (3 - 2 * M.β) / D * M.Ω ∧ x.2 i = 1 / D * M.Ω := by
      intro i; fin_cases i
      · exact hsol
      · exact ⟨dp.1 ▸ hsol.1, dp.2 ▸ hsol.2⟩
    intro i
    obtain ⟨hpi, hwi⟩ := hall i
    obtain ⟨_, _, hm, _⟩ := hbr i
    have hpr := (hall (rival i)).1
    have hwr := (hall (rival i)).2
    refine ⟨hpi, hwi, ?_, ?_⟩
    · rw [hm, hpr, hwr]; field_simp; (try simp only [D]); ring
    · rw [profP_eq]
      have hpos := hxpos i
      rw [profP_eq] at hpos
      have hle := f_le (M.Ω + M.γ * x.1 (rival i)) (M.β * x.2 (rival i)) (x.1 i) (x.2 i)
      have hdev := hx.2 i (((3 * (M.Ω + M.γ * x.1 (rival i)) + M.β * x.2 (rival i)) / 4),
        ((M.Ω + M.γ * x.1 (rival i)) + 3 * (M.β * x.2 (rival i))) / 4) trivial
      simp only at hdev
      obtain ⟨_, _, _, hABp⟩ := hbr i
      rw [profP_dev, profP_eq, f_at _ _ hABp.le] at hdev
      have : f (M.Ω + M.γ * x.1 (rival i)) (M.β * x.2 (rival i)) (x.1 i) (x.2 i) =
          (M.Ω + M.γ * x.1 (rival i) - M.β * x.2 (rival i)) ^ 2 / 8 := le_antisymm hle hdev
      rw [this, hpr, hwr]; field_simp; (try simp only [D]); ring
