-- Prove2me | solution 1 for OutpatientWalkIn.Triage.proposition_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T12:45:23.491053+00:00
-- url     : https://prove2.me/submissions/b214422d-7dc8-49bd-a0d3-3ceaf0c0a957
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OutpatientWalkIn_Triage_Queue
import Definitions.Def_OutpatientWalkIn_Triage_Setting
import Theorems.Thm_OutpatientWalkIn_Triage_scheduling_rate_bound
import Theorems.Thm_OutpatientWalkIn_Triage_proposition_1_obs
import Theorems.Thm_OutpatientWalkIn_Triage_proposition_C_2_muS
import Theorems.Thm_OutpatientWalkIn_Triage_proposition_2_1
import Theorems.Thm_OutpatientWalkIn_Triage_walkin_intensity_SnW
import Theorems.Thm_OutpatientWalkIn_Triage_walkin_intensity_SWB

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

end P6Aux

open OutpatientWalkIn.Triage P6Aux

theorem solution (M : Model) (hM : M.Standing) (hCO : 0 < M.CO) (hlamE : 0 < M.lamE)
    (μWl : ℝ) (hμWl : 0 < μWl) (h15 : M.R - M.CW * M.w (M.lamE / μWl) = 0) (hμ : μWl < M.mu)
    (ho₁ : DifferentiableAt ℝ M.o (M.lamE / M.mu))
    (ho₂ : DifferentiableAt ℝ M.o (M.lamE / μWl)) :
    (M.CL / M.CO ≤ M.alphaLow →
      ∀ μS ∈ Set.Ico 0 M.mu, ∀ e : ObsStrategy, M.IsObsEq μS e →
        ∃ μS' ∈ Set.Ico 0 M.mu, M.triageCost μS' ≤ M.obsCost μS e) ∧
    (M.alphaHigh μWl ≤ M.CL / M.CO →
      ∀ μS ∈ Set.Ico 0 M.mu, ∃ μS' ∈ Set.Ico 0 M.mu, (∃ e : ObsStrategy, M.IsObsEq μS' e) ∧
        ∀ e : ObsStrategy, M.IsObsEq μS' e → M.obsCost μS' e ≤ M.triageCost μS) := by
  have hlam : 0 < M.lam := hM.1
  have hCL : 0 ≤ M.CL := hM.2.2.2.2.2.1
  have hmu : 0 < M.mu := hM.2.2.2.2.2.2.2.1
  have hoc : ConvexOn ℝ (Set.Ici 0) M.o := hM.2.2.2.2.2.2.2.2.2.2.2.1
  have hom : StrictMonoOn M.o (Set.Ici 0) := hM.2.2.2.2.2.2.2.2.2.2.2.2
  constructor
  · -- Part (1): compare with the triage model at the same allocation.
    intro hα μS hμS e he
    refine ⟨μS, hμS, ?_⟩
    have hW : 0 < M.mu - μS := sub_pos.2 hμS.2
    have hWle : M.mu - μS ≤ M.mu := by linarith [hμS.1]
    obtain ⟨hδ, hpW, hpB, hsum0, _, _, hsum, _, _⟩ := id he
    have srb := scheduling_rate_bound M hM μS hμS e he
    have hπ : blockProb M.lam (M.R / M.CD) μS ≤ e.pW + e.pB := by
      rw [hsum]
      have := le_of_mul_le_mul_left srb hlam
      linarith
    set d0 := deriv M.o (M.lamE / M.mu)
    have hd0 : 0 ≤ d0 := deriv_nonneg_of_mono hoc hom (div_pos hlamE hmu) ho₁
    have hCLle : M.CL ≤ M.CO * (d0 / M.mu) := by
      unfold Model.alphaLow at hα
      rw [div_le_iff₀ hCO] at hα; linarith
    set y := M.lamE / (M.mu - μS)
    set x := (e.pW * M.lam + M.lamE) / (M.mu - μS)
    have hx0y : M.lamE / M.mu ≤ y := div_le_div_of_nonneg_left hlamE.le hW hWle
    have hxy : x - y = e.pW * M.lam / (M.mu - μS) := by
      simp only [x, y]; field_simp; ring
    have hyx : y ≤ x := by
      have : 0 ≤ e.pW * M.lam / (M.mu - μS) := by positivity
      linarith
    have hcv := cvx_lower hoc (div_pos hlamE hmu).le hx0y hyx ho₁
    have hpl : e.pW * M.lam / M.mu ≤ e.pW * M.lam / (M.mu - μS) :=
      div_le_div_of_nonneg_left (by positivity) hW hWle
    -- CL pW λ ≤ CO d0 pW λ / μ ≤ CO d0 (x - y) ≤ CO (o x - o y)
    have k1 : M.CL * (e.pW * M.lam) ≤ M.CO * (d0 * (e.pW * M.lam / M.mu)) := by
      have := mul_le_mul_of_nonneg_right hCLle (by positivity : 0 ≤ e.pW * M.lam)
      calc M.CL * (e.pW * M.lam) ≤ M.CO * (d0 / M.mu) * (e.pW * M.lam) := this
        _ = M.CO * (d0 * (e.pW * M.lam / M.mu)) := by ring
    have k2 : d0 * (e.pW * M.lam / M.mu) ≤ d0 * (x - y) := by
      rw [hxy]; exact mul_le_mul_of_nonneg_left hpl hd0
    have k3 : M.CO * (d0 * (x - y)) ≤ M.CO * (M.o x - M.o y) :=
      mul_le_mul_of_nonneg_left hcv hCO.le
    have k4 : M.CO * (d0 * (e.pW * M.lam / M.mu)) ≤ M.CO * (d0 * (x - y)) :=
      mul_le_mul_of_nonneg_left k2 hCO.le
    have k5 : M.CL * blockProb M.lam (M.R / M.CD) μS * M.lam ≤ M.CL * (e.pW + e.pB) * M.lam := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hπ hCL) hlam.le
      linear_combination this
    unfold Model.triageCost Model.obsCost
    show M.CL * blockProb M.lam (M.R / M.CD) μS * M.lam + M.CO * M.o y ≤
      M.CL * e.pB * M.lam + M.CO * M.o x
    linear_combination k5 + k1 + k4 + k3
  · -- Part (2)
    intro hα μS hμS
    refine ⟨μS, hμS, proposition_1_obs M hM μS hμS, ?_⟩
    intro e he
    have hW : 0 < M.mu - μS := sub_pos.2 hμS.2
    set D := deriv M.o (M.lamE / μWl)
    set z := M.lamE / μWl
    have hz : 0 < z := div_pos hlamE hμWl
    have hD : 0 ≤ D := deriv_nonneg_of_mono hoc hom hz ho₂
    set π0 := blockProb M.lam (M.R / M.CD) (M.mu - μWl)
    set mx := max (M.lamE / (M.lam * π0)) 1
    have hCLA : M.CO * (D / μWl * mx) ≤ M.CL := by
      unfold Model.alphaHigh at hα
      rw [le_div_iff₀ hCO] at hα; linarith
    have hDm : 0 ≤ D / μWl := div_nonneg hD hμWl.le
    have hCL1 : M.CO * (D / μWl) ≤ M.CL := by
      have : D / μWl ≤ D / μWl * mx := le_mul_of_one_le_right hDm (le_max_right _ _)
      have := mul_le_mul_of_nonneg_left this hCO.le
      linarith
    by_cases hcase : M.mu - μS ≤ μWl
    · obtain ⟨h1, -, h3⟩ := proposition_2_1 M hM μWl hμWl h15 μS hμS hcase e he
      unfold Model.triageCost Model.obsCost
      rw [h1, h3]; simp
    · push_neg at hcase
      obtain ⟨hδ, hpW, hpB, hsum0, _, _, hsum, _, _⟩ := id he
      set y := M.lamE / (M.mu - μS)
      set x := (e.pW * M.lam + M.lamE) / (M.mu - μS)
      have hxy : x - y = e.pW * M.lam / (M.mu - μS) := by
        simp only [x, y]; field_simp; ring
      have hyx : y ≤ x := by
        have : 0 ≤ e.pW * M.lam / (M.mu - μS) := by positivity
        linarith
      have hy0 : 0 ≤ y := by positivity
      have hDW : D / (M.mu - μS) ≤ D / μWl := div_le_div_of_nonneg_left hD hμWl hcase.le
      unfold Model.triageCost Model.obsCost
      show M.CL * e.pB * M.lam + M.CO * M.o x ≤
        M.CL * blockProb M.lam (M.R / M.CD) μS * M.lam + M.CO * M.o y
      rcases eq_or_lt_of_le hpB with hpB0 | hpBpos
      · -- Regime SnW: nobody balks.
        have hpB0' : e.pB = 0 := hpB0.symm
        have hxz : x ≤ z := by
          have := walkin_intensity_SnW M hM μWl hμWl h15 μS hμS e he hpB0'
          simp only [x, z]; rwa [show e.pW * M.lam + M.lamE = M.lam * e.pW + M.lamE by ring]
        have hcv := cvx_upper hoc hy0 hyx hxz ho₂
        rw [hpB0']
        -- bound on the walk-in rate per unit capacity
        have hrate : e.pW * M.lam / (M.mu - μS) ≤ z := by
          have : y ≥ 0 := hy0
          linarith
        rcases eq_or_lt_of_le hμS.1 with h0 | hpos
        · -- μS = 0: π = 1
          have hb : ∀ δ, blockProb M.lam δ μS = 1 := by
            intro δ; unfold blockProb; simp [← h0]
          rw [hb] at hsum ⊢
          rw [hpB0', add_zero] at hsum
          rw [← h0, sub_zero] at hxy hDW
          have e1 : M.CO * (M.o x - M.o y) ≤ M.CO * (D * (x - y)) :=
            mul_le_mul_of_nonneg_left hcv hCO.le
          rw [hxy, hsum] at e1
          have e2 : M.CO * (D * (1 * M.lam / M.mu)) = M.CO * (D / M.mu) * M.lam := by ring
          rw [e2] at e1
          have e3 : M.CO * (D / M.mu) ≤ M.CL := by
            have := mul_le_mul_of_nonneg_left hDW hCO.le; linarith
          have := mul_le_mul_of_nonneg_right e3 hlam.le
          linear_combination e1 + this
        · -- 0 < μS < μ - μ̲_W
          have hs0 : μS < M.mu - μWl := by linarith
          have hmono := (proposition_C_2_muS M.lam (M.R / M.CD) hlam
            (div_nonneg hM.2.2.1.le hM.2.2.2.1.le)).1
          have hπ : π0 < blockProb M.lam (M.R / M.CD) μS :=
            hmono (Set.mem_Ioi.2 hpos) (Set.mem_Ioi.2 (by linarith)) hs0
          -- π0 > 0 from an equilibrium at μ - μ̲_W
          have hs0mem : M.mu - μWl ∈ Set.Ico 0 M.mu := ⟨by linarith, by linarith⟩
          obtain ⟨e0, he0⟩ := proposition_1_obs M hM (M.mu - μWl) hs0mem
          obtain ⟨g1, -, g3⟩ := proposition_2_1 M hM μWl hμWl h15 (M.mu - μWl) hs0mem
            (by linarith) e0 he0
          have hπ0 : 0 < π0 := by
            have := he0.2.2.2.1; rw [g1, g3, zero_add] at this; exact this
          -- CL * λ * π0 ≥ CO * D / μ̲_W * λ_E
          have hmx : M.lamE / (M.lam * π0) ≤ mx := le_max_left _ _
          have hk : M.CO * (D / μWl) * (M.lamE / (M.lam * π0)) ≤ M.CL := by
            have := mul_le_mul_of_nonneg_left hmx (mul_nonneg hCO.le hDm)
            linear_combination this + hCLA
          have hlp : 0 < M.lam * π0 := mul_pos hlam hπ0
          have hk' : M.CO * (D / μWl) * M.lamE ≤ M.CL * (M.lam * π0) := by
            have := mul_le_mul_of_nonneg_right hk hlp.le
            rwa [mul_assoc (M.CO * (D / μWl)), div_mul_cancel₀ _ hlp.ne'] at this
          have e1 : M.CO * (M.o x - M.o y) ≤ M.CO * (D * (x - y)) :=
            mul_le_mul_of_nonneg_left hcv hCO.le
          have e2 : M.CO * (D * (x - y)) ≤ M.CO * (D * z) := by
            rw [hxy]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrate hD) hCO.le
          have e3 : M.CO * (D * z) = M.CO * (D / μWl) * M.lamE := by simp only [z]; ring
          have e4 : M.CL * (M.lam * π0) ≤ M.CL * blockProb M.lam (M.R / M.CD) μS * M.lam := by
            have := mul_le_mul_of_nonneg_left hπ.le (mul_nonneg hCL hlam.le)
            linear_combination this
          linear_combination e1 + e2 + e3 + hk' + e4
      · -- Some patients balk: δ = R / C_D, so p_W + p_B = π(R/C_D, μ_S).
        have hδR := delta_of_pB_pos M hM μS e he hpBpos
        rw [hδR] at hsum
        rw [← hsum]
        rcases eq_or_lt_of_le hpW with hpW0 | hpWpos
        · have hx : x = y := by simp only [x, y]; rw [← hpW0]; ring_nf
          rw [hx, ← hpW0, zero_add]
        · have hxz : x ≤ z := by
            have := walkin_intensity_SWB M hM μWl hμWl h15 μS hμS e he hpWpos hpBpos
            simp only [x, z]; rw [show e.pW * M.lam + M.lamE = M.lam * e.pW + M.lamE by ring]
            exact this.le
          have hcv := cvx_upper hoc hy0 hyx hxz ho₂
          have e1 : M.CO * (M.o x - M.o y) ≤ M.CO * (D * (x - y)) :=
            mul_le_mul_of_nonneg_left hcv hCO.le
          rw [hxy] at e1
          have e2 : M.CO * (D * (e.pW * M.lam / (M.mu - μS))) =
              M.CO * (D / (M.mu - μS)) * (e.pW * M.lam) := by ring
          rw [e2] at e1
          have e3 : M.CO * (D / (M.mu - μS)) ≤ M.CL := by
            have := mul_le_mul_of_nonneg_left hDW hCO.le; linarith
          have := mul_le_mul_of_nonneg_right e3 (by positivity : 0 ≤ e.pW * M.lam)
          linear_combination e1 + this
