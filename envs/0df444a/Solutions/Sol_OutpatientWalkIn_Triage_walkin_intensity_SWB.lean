-- Prove2me | solution 1 for OutpatientWalkIn.Triage.walkin_intensity_SWB
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T12:41:56.826063+00:00
-- url     : https://prove2.me/submissions/8b41e02c-70fb-42f9-b4e4-461ed6868125

import Mathlib
import Definitions.Def_OutpatientWalkIn_Triage_Queue
import Definitions.Def_OutpatientWalkIn_Triage_Setting

namespace P6Aux

open OutpatientWalkIn.Triage

/-- Convexity: a secant slope to the right of `a` dominates `f'(a)`. -/
theorem cvx_lower {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici 0) f) {a y x : ℝ}
    (ha : 0 ≤ a) (hay : a ≤ y) (hyx : y ≤ x) (hd : DifferentiableAt ℝ f a) :
    deriv f a * (x - y) ≤ f x - f y := by
  rcases eq_or_lt_of_le hyx with h | h
  · subst h; simp
  have hy0 : (0:ℝ) ≤ y := ha.trans hay
  have hx0 : (0:ℝ) ≤ x := hy0.trans hyx
  have key : deriv f a ≤ (f x - f y) / (x - y) := by
    rcases eq_or_lt_of_le hay with h' | h'
    · subst h'
      have := hf.deriv_le_slope (Set.mem_Ici.2 ha) (Set.mem_Ici.2 hx0) h hd
      rwa [slope_def_field] at this
    · have h1 := hf.deriv_le_slope (Set.mem_Ici.2 ha) (Set.mem_Ici.2 hy0) h' hd
      rw [slope_def_field] at h1
      have h2 := hf.slope_mono_adjacent (Set.mem_Ici.2 ha) (Set.mem_Ici.2 hx0) h' h
      linarith
  have hpos : 0 < x - y := sub_pos.2 h
  rwa [le_div_iff₀ hpos] at key

/-- Convexity: a secant slope to the left of `z` is dominated by `f'(z)`. -/
theorem cvx_upper {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici 0) f) {y x z : ℝ}
    (hy : 0 ≤ y) (hyx : y ≤ x) (hxz : x ≤ z) (hd : DifferentiableAt ℝ f z) :
    f x - f y ≤ deriv f z * (x - y) := by
  rcases eq_or_lt_of_le hyx with h | h
  · subst h; simp
  have hx0 : (0:ℝ) ≤ x := hy.trans hyx
  have hz0 : (0:ℝ) ≤ z := hx0.trans hxz
  have key : (f x - f y) / (x - y) ≤ deriv f z := by
    rcases eq_or_lt_of_le hxz with h' | h'
    · subst h'
      have := hf.slope_le_deriv (Set.mem_Ici.2 hy) (Set.mem_Ici.2 hx0) h hd
      rwa [slope_def_field] at this
    · have h1 := hf.slope_le_deriv (Set.mem_Ici.2 hx0) (Set.mem_Ici.2 hz0) h' hd
      rw [slope_def_field] at h1
      have h2 := hf.slope_mono_adjacent (Set.mem_Ici.2 hy) (Set.mem_Ici.2 hz0) h h'
      linarith
  have hpos : 0 < x - y := sub_pos.2 h
  rwa [div_le_iff₀ hpos] at key

/-- A function monotone on `[0, ∞)` has nonnegative derivative at an interior point. -/
theorem deriv_nonneg_of_mono {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici 0) f)
    (hm : StrictMonoOn f (Set.Ici 0)) {z : ℝ} (hz : 0 < z) (hd : DifferentiableAt ℝ f z) :
    0 ≤ deriv f z := by
  have h1 := hf.slope_le_deriv (Set.mem_Ici.2 (by linarith : (0:ℝ) ≤ z / 2))
    (Set.mem_Ici.2 hz.le) (by linarith : z / 2 < z) hd
  rw [slope_def_field] at h1
  have h2 : f (z / 2) < f z := hm (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 hz.le)
    (by linarith)
  have : 0 ≤ (f z - f (z / 2)) / (z - z / 2) := div_nonneg (by linarith) (by linarith)
  linarith

/-- In an observable equilibrium, `u²_S(δ)` equals the mixed walk-in/balk utility. -/
theorem eq_delta_char (M : Model) (hM : M.Standing) (μS : ℝ) (e : ObsStrategy)
    (he : M.IsObsEq μS e) :
    M.R - M.CD * e.δ = e.pW / (e.pW + e.pB) * M.u2W μS e.pW + e.pB / (e.pW + e.pB) * 0 := by
  obtain ⟨_, _, _, hCD, _⟩ := hM
  obtain ⟨hδ, _, _, _, h5, h6, _⟩ := he
  set U := e.pW / (e.pW + e.pB) * M.u2W μS e.pW + e.pB / (e.pW + e.pB) * 0
  have hge : M.R - M.CD * e.δ ≥ U := h5 e.δ hδ le_rfl
  by_contra hne
  have hgt : M.R - M.CD * e.δ > U := lt_of_le_of_ne hge (Ne.symm hne)
  have := h6 (e.δ + (M.R - M.CD * e.δ - U) / (2 * M.CD)) (by
    have : 0 < (M.R - M.CD * e.δ - U) / (2 * M.CD) := div_pos (by linarith) (by linarith)
    linarith)
  unfold Model.u2S at this
  have hc : M.CD * (e.δ + (M.R - M.CD * e.δ - U) / (2 * M.CD)) =
      M.CD * e.δ + (M.R - M.CD * e.δ - U) / 2 := by field_simp
  rw [hc] at this
  linarith

/-- If some patients balk, the equilibrium threshold is `R / C_D`. -/
theorem delta_of_pB_pos (M : Model) (hM : M.Standing) (μS : ℝ) (e : ObsStrategy)
    (he : M.IsObsEq μS e) (hpB : 0 < e.pB) : e.δ = M.R / M.CD := by
  have hc := eq_delta_char M hM μS e he
  have hCD : 0 < M.CD := hM.2.2.2.1
  obtain ⟨_, _, _, _, _, _, _, h8, h9⟩ := he
  have hu : M.u2W μS e.pW ≤ 0 := h9.resolve_left hpB.ne'
  have hU : e.pW / (e.pW + e.pB) * M.u2W μS e.pW = 0 := by
    rcases h8 with h | h
    · rw [h]; simp
    · rw [le_antisymm hu h]; simp
  rw [hU] at hc
  field_simp
  linarith

/-- `w` strictly increasing on `[0,∞)`: `w a ≤ w b`, `0 ≤ a, b` implies `a ≤ b`. -/
theorem w_le_iff (M : Model) (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    M.w a ≤ M.w b ↔ a ≤ b :=
  hM.2.2.2.2.2.2.2.2.2.1.le_iff_le (Set.mem_Ici.2 ha) (Set.mem_Ici.2 hb)

/-- Walking in is (weakly) profitable iff the walk-in intensity is at most `λ_E / μ̲_W`. -/
theorem u2W_nonneg_iff (M : Model) (hM : M.Standing) (μWl : ℝ) (hμWl : 0 < μWl)
    (h15 : M.R - M.CW * M.w (M.lamE / μWl) = 0) (μS pW : ℝ) (hx : 0 ≤ (M.lamE + pW * M.lam) / (M.mu - μS)) :
    0 ≤ M.u2W μS pW ↔ (M.lamE + pW * M.lam) / (M.mu - μS) ≤ M.lamE / μWl := by
  have hCW : 0 < M.CW := hM.2.2.2.2.1
  have hlamE : 0 ≤ M.lamE := hM.2.1
  unfold Model.u2W
  rw [← w_le_iff M hM hx (div_nonneg hlamE hμWl.le)]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

theorem u2W_nonpos_iff (M : Model) (hM : M.Standing) (μWl : ℝ) (hμWl : 0 < μWl)
    (h15 : M.R - M.CW * M.w (M.lamE / μWl) = 0) (μS pW : ℝ) (hx : 0 ≤ (M.lamE + pW * M.lam) / (M.mu - μS)) :
    M.u2W μS pW ≤ 0 ↔ M.lamE / μWl ≤ (M.lamE + pW * M.lam) / (M.mu - μS) := by
  have hCW : 0 < M.CW := hM.2.2.2.2.1
  have hlamE : 0 ≤ M.lamE := hM.2.1
  unfold Model.u2W
  rw [← w_le_iff M hM (div_nonneg hlamE hμWl.le) hx]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

theorem walkin_intensity_SnW (M : Model) (hM : M.Standing) (μWl : ℝ) (hμWl : 0 < μWl)
    (h15 : M.R - M.CW * M.w (M.lamE / μWl) = 0) :
    ∀ μS ∈ Set.Ico 0 M.mu, ∀ e : ObsStrategy, M.IsObsEq μS e → e.pB = 0 →
      (M.lam * e.pW + M.lamE) / (M.mu - μS) ≤ M.lamE / μWl := by
  intro μS hμS e he hpB
  have hW : 0 < M.mu - μS := sub_pos.2 hμS.2
  obtain ⟨_, hpW0, _, hsum, _, _, _, h8, _⟩ := he
  have hx : 0 ≤ (M.lamE + e.pW * M.lam) / (M.mu - μS) :=
    div_nonneg (by have := hM.2.1; have := hM.1; positivity) hW.le
  rcases h8 with h | h
  · exfalso; rw [h, hpB] at hsum; simp at hsum
  · have := (u2W_nonneg_iff M hM μWl hμWl h15 μS e.pW hx).1 h
    rwa [show M.lam * e.pW + M.lamE = M.lamE + e.pW * M.lam by ring]

theorem walkin_intensity_SWB (M : Model) (hM : M.Standing) (μWl : ℝ) (hμWl : 0 < μWl)
    (h15 : M.R - M.CW * M.w (M.lamE / μWl) = 0) :
    ∀ μS ∈ Set.Ico 0 M.mu, ∀ e : ObsStrategy, M.IsObsEq μS e → 0 < e.pW → 0 < e.pB →
      (M.lam * e.pW + M.lamE) / (M.mu - μS) = M.lamE / μWl := by
  intro μS hμS e he hpW hpB
  have hW : 0 < M.mu - μS := sub_pos.2 hμS.2
  obtain ⟨_, hpW0, _, hsum, _, _, _, h8, h9⟩ := he
  have hx : 0 ≤ (M.lamE + e.pW * M.lam) / (M.mu - μS) :=
    div_nonneg (by have := hM.2.1; have := hM.1; positivity) hW.le
  have a := (u2W_nonneg_iff M hM μWl hμWl h15 μS e.pW hx).1 (h8.resolve_left hpW.ne')
  have b := (u2W_nonpos_iff M hM μWl hμWl h15 μS e.pW hx).1 (h9.resolve_left hpB.ne')
  rw [show M.lam * e.pW + M.lamE = M.lamE + e.pW * M.lam by ring]
  linarith

theorem proposition_2_1 (M : Model) (hM : M.Standing) (μWl : ℝ) (hμWl : 0 < μWl)
    (h15 : M.R - M.CW * M.w (M.lamE / μWl) = 0) :
    ∀ μS ∈ Set.Ico 0 M.mu, M.mu - μS ≤ μWl → ∀ e : ObsStrategy, M.IsObsEq μS e →
      e.pW = 0 ∧ e.δ = M.R / M.CD ∧ e.pB = blockProb M.lam (M.R / M.CD) μS := by
  intro μS hμS hle e he
  have hW : 0 < M.mu - μS := sub_pos.2 hμS.2
  have hlam : 0 < M.lam := hM.1
  have hlamE : 0 ≤ M.lamE := hM.2.1
  have hpW : e.pW = 0 := by
    obtain ⟨_, hpW0, _, hsum, _, _, _, h8, _⟩ := he
    by_contra hne
    have h0 : 0 < e.pW := lt_of_le_of_ne hpW0 (Ne.symm hne)
    have h := h8.resolve_left hne
    have hx : 0 ≤ (M.lamE + e.pW * M.lam) / (M.mu - μS) := div_nonneg (by positivity) hW.le
    have a := (u2W_nonneg_iff M hM μWl hμWl h15 μS e.pW hx).1 h
    have c1 : M.lamE / μWl ≤ M.lamE / (M.mu - μS) :=
      div_le_div_of_nonneg_left hlamE hW hle
    have c2 : M.lamE / (M.mu - μS) < (M.lamE + e.pW * M.lam) / (M.mu - μS) :=
      div_lt_div_of_pos_right (by nlinarith) hW
    linarith
  have hpB : 0 < e.pB := by
    have := he.2.2.2.1; rw [hpW] at this; simpa using this
  have hδ := delta_of_pB_pos M hM μS e he hpB
  refine ⟨hpW, hδ, ?_⟩
  have hsum := he.2.2.2.2.2.2.1
  rw [hpW, zero_add, hδ] at hsum
  exact hsum

end P6Aux

open OutpatientWalkIn.Triage

theorem solution (M : Model) (hM : M.Standing) (μWl : ℝ) (hμWl : 0 < μWl)
    (h15 : M.R - M.CW * M.w (M.lamE / μWl) = 0) :
    ∀ μS ∈ Set.Ico 0 M.mu, ∀ e : ObsStrategy, M.IsObsEq μS e → 0 < e.pW → 0 < e.pB →
      (M.lam * e.pW + M.lamE) / (M.mu - μS) = M.lamE / μWl :=
  P6Aux.walkin_intensity_SWB M hM μWl hμWl h15
