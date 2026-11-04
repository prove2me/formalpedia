-- Prove2me | solution 1 for PreAwardInvest.WinWin.envelope_A2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T11:37:54.100319+00:00
-- url     : https://prove2.me/submissions/7e2d5193-47a8-4b8a-8e01-8f9a15e192a6

import Mathlib
import Definitions.Def_PreAwardInvest_WinWin_Model

open PreAwardInvest.WinWin
open MeasureTheory

/-- Abstract envelope theorem for a one-dimensional incentive-compatible direct mechanism. -/
theorem paw_envelope_abstract (W β : ℝ → ℝ) (lo hi : ℝ)
    (hIC : ∀ c ∈ Set.Icc lo hi, ∀ z ∈ Set.Icc lo hi,
      (β z - c) * W (β z) ≤ (β c - c) * W (β c)) :
    ∀ c ∈ Set.Icc lo hi,
      (β c - c) * W (β c) = (β hi - hi) * W (β hi) + ∫ y in c..hi, W (β y) := by
  set φ : ℝ → ℝ := fun y => W (β y) with hφ
  set U : ℝ → ℝ := fun c => (β c - c) * φ c with hU
  -- monotonicity of the allocation
  have hanti : AntitoneOn φ (Set.Icc lo hi) := by
    intro c hc z hz hcz
    have h1 := hIC c hc z hz
    have h2 := hIC z hz c hc
    simp only [hφ] at *
    rcases eq_or_lt_of_le hcz with h | h
    · rw [h]
    · nlinarith
  -- two-sided bounds on profit differences
  have hUlow : ∀ a ∈ Set.Icc lo hi, ∀ b ∈ Set.Icc lo hi,
      (b - a) * φ b ≤ U a - U b := by
    intro a ha b hb
    have := hIC a ha b hb
    simp only [hU, hφ] at *; nlinarith
  have hUup : ∀ a ∈ Set.Icc lo hi, ∀ b ∈ Set.Icc lo hi,
      U a - U b ≤ (b - a) * φ a := by
    intro a ha b hb
    have := hIC b hb a ha
    simp only [hU, hφ] at *; nlinarith
  have hII : ∀ a ∈ Set.Icc lo hi, ∀ b ∈ Set.Icc lo hi, IntervalIntegrable φ volume a b := by
    intro a ha b hb
    apply AntitoneOn.intervalIntegrable
    apply hanti.mono
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨le_trans ha.1 h1, le_trans h2 hb.2⟩
    · exact ⟨le_trans hb.1 h1, le_trans h2 ha.2⟩
  have hIlow : ∀ a ∈ Set.Icc lo hi, ∀ b ∈ Set.Icc lo hi, a ≤ b →
      (b - a) * φ b ≤ ∫ y in a..b, φ y := by
    intro a ha b hb hab
    have : ∫ y in a..b, φ b ≤ ∫ y in a..b, φ y := by
      apply intervalIntegral.integral_mono_on hab intervalIntegrable_const (hII a ha b hb)
      intro x hx
      exact hanti ⟨le_trans ha.1 hx.1, le_trans hx.2 hb.2⟩ hb hx.2
    simpa [intervalIntegral.integral_const] using this
  have hIup : ∀ a ∈ Set.Icc lo hi, ∀ b ∈ Set.Icc lo hi, a ≤ b →
      ∫ y in a..b, φ y ≤ (b - a) * φ a := by
    intro a ha b hb hab
    have : ∫ y in a..b, φ y ≤ ∫ y in a..b, φ a := by
      apply intervalIntegral.integral_mono_on hab (hII a ha b hb) intervalIntegrable_const
      intro x hx
      exact hanti ha ⟨le_trans ha.1 hx.1, le_trans hx.2 hb.2⟩ hx.1
    simpa [intervalIntegral.integral_const] using this
  set D : ℝ → ℝ → ℝ := fun a b => (U a - U b) - ∫ y in a..b, φ y with hD
  have hDbd : ∀ a ∈ Set.Icc lo hi, ∀ b ∈ Set.Icc lo hi, a ≤ b →
      |D a b| ≤ (b - a) * (φ a - φ b) := by
    intro a ha b hb hab
    have h1 := hUlow a ha b hb
    have h2 := hUup a ha b hb
    have h3 := hIlow a ha b hb hab
    have h4 := hIup a ha b hb hab
    rw [abs_le]; simp only [hD]; constructor <;> nlinarith
  have hDadd : ∀ a ∈ Set.Icc lo hi, ∀ b ∈ Set.Icc lo hi, ∀ e ∈ Set.Icc lo hi,
      D a e = D a b + D b e := by
    intro a ha b hb e he
    simp only [hD]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hII a ha b hb) (hII b hb e he)]
    ring
  intro c hc
  have hchi : c ≤ hi := hc.2
  have hhi : hi ∈ Set.Icc lo hi := ⟨le_trans hc.1 hc.2, le_rfl⟩
  suffices hD0 : D c hi = 0 by
    simp only [hD, hU] at hD0; linarith
  -- partition argument
  have key : ∀ n : ℕ, 0 < n → |D c hi| ≤ (hi - c) / n * (φ c - φ hi) := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    set h := (hi - c) / n with hh
    have hh0 : 0 ≤ h := div_nonneg (by linarith) hnpos.le
    have hxmem : ∀ m : ℕ, m ≤ n → c + m * h ∈ Set.Icc lo hi := by
      intro m hm
      have hm' : (m : ℝ) ≤ n := by exact_mod_cast hm
      have : (m : ℝ) * h ≤ hi - c := by
        rw [hh, mul_div_assoc']
        rw [div_le_iff₀ hnpos]; nlinarith
      exact ⟨by nlinarith [hc.1], by linarith⟩
    have ind : ∀ m : ℕ, m ≤ n → |D c (c + m * h)| ≤ h * (φ c - φ (c + m * h)) := by
      intro m
      induction m with
      | zero =>
        intro _
        simp [hD]
      | succ m ih =>
        intro hm
        have hm1 : m ≤ n := Nat.le_of_succ_le hm
        have hx := hxmem m hm1
        have hx1 := hxmem (m + 1) hm
        have hsplit := hDadd c hc _ hx _ hx1
        have hb := hDbd _ hx _ hx1 (by push_cast; nlinarith)
        have ih' := ih hm1
        rw [hsplit]
        calc |D c (c + ↑m * h) + D (c + ↑m * h) (c + ↑(m + 1) * h)|
            ≤ |D c (c + ↑m * h)| + |D (c + ↑m * h) (c + ↑(m + 1) * h)| := abs_add_le _ _
          _ ≤ h * (φ c - φ (c + ↑m * h)) +
              (c + ↑(m + 1) * h - (c + ↑m * h)) * (φ (c + ↑m * h) - φ (c + ↑(m + 1) * h)) :=
              add_le_add ih' hb
          _ = h * (φ c - φ (c + ↑(m + 1) * h)) := by push_cast; ring
    have := ind n le_rfl
    have hend : c + (n : ℝ) * h = hi := by
      rw [hh]; field_simp; ring
    rw [hend] at this
    linarith
  -- conclude
  have hφnn : 0 ≤ φ c - φ hi := by
    have := hanti hc hhi hchi; linarith
  by_contra hne
  have hpos : 0 < |D c hi| := abs_pos.mpr hne
  set K := (hi - c) * (φ c - φ hi) with hK
  have hK0 : 0 ≤ K := mul_nonneg (by linarith) hφnn
  obtain ⟨n, hn⟩ := exists_nat_gt (K / |D c hi|)
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg hK0 hpos.le) hn
    exact_mod_cast this
  have hk := key n hn0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have : (hi - c) / n * (φ c - φ hi) = K / n := by rw [hK]; ring
  rw [this, le_div_iff₀ hnpos] at hk
  rw [div_lt_iff₀ hpos] at hn
  linarith

theorem solution {N : ℕ} [NeZero N] (P : Params N) (hS : P.Standing) (τ : ℝ)
    (βI βA : Fin N → ℝ → ℝ) :
    (IsEqBIA P τ βI → ∀ i, ∀ c ∈ Set.Icc (cLoI P i) (cHiI P i),
      profitBIA P τ βI i (βI i c) c =
        profitBIA P τ βI i (βI i (cHiI P i)) (cHiI P i) +
          ∫ y in c..cHiI P i,
            ∫ cv, winProbBIA P τ (Function.update (bidProfile βI cv) i (βI i y)) i
              ∂(costVecLaw P)) ∧
    (IsEqBAI P βA → ∀ i, ∀ c ∈ Set.Icc (cLoI P i) (cHiI P i),
      profitBAI P βA i (βA i c) c =
        profitBAI P βA i (βA i (cHiI P i)) (cHiI P i) +
          ∫ y in c..cHiI P i,
            ∫ cv, winProbBAI P (Function.update (bidProfile βA cv) i (βA i y)) i
              ∂(costVecLaw P)) := by
  constructor
  · rintro ⟨-, hrange, hIC⟩ i
    exact paw_envelope_abstract
      (fun b => ∫ cv, winProbBIA P τ (Function.update (bidProfile βI cv) i b) i
        ∂(costVecLaw P)) (βI i) (cLoI P i) (cHiI P i)
      (fun c hc z hz => hIC i c hc (βI i z) (hrange i z hz))
  · rintro ⟨-, hrange, hIC⟩ i
    exact paw_envelope_abstract
      (fun b => ∫ cv, winProbBAI P (Function.update (bidProfile βA cv) i b) i
        ∂(costVecLaw P)) (βA i) (cLoI P i) (cHiI P i)
      (fun c hc z hz => hIC i c hc (βA i z) (hrange i z hz))
