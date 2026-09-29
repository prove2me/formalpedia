-- Prove2me | solution 1 for StochasticOrders.Convex.convex_order_abs_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T05:46:38.429548+00:00
-- url     : https://prove2.me/submissions/a439c4c0-fbf2-423f-b071-23c4665aae65

import Mathlib
import Definitions.Def_StochasticOrders_Convex_ConvexOrder

set_option autoImplicit false

open MeasureTheory Filter Topology

theorem cxo_partC (v : ℕ → ℝ) : ∀ M k, k ≤ M →
    v k ≤ v 0 + ∑ i ∈ Finset.range M, max (v (i+1) - v i) 0 := by
  intro M
  induction M with
  | zero => intro k hk; rw [Nat.le_zero.1 hk]; simp
  | succ M ih =>
    intro k hk
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge k (M+1) with h | h
    · have h1 := ih k (by omega)
      have h2 := le_max_right (v (M+1) - v M) 0
      linarith
    · have hk' : k = M + 1 := by omega
      subst hk'
      have h1 := ih M le_rfl
      have h2 := le_max_left (v (M+1) - v M) 0
      linarith

theorem cxo_partA (v : ℕ → ℝ) : ∀ M, (∀ k < M, 0 ≤ v (k+1) - v k) →
    v 0 + ∑ i ∈ Finset.range M, max (v (i+1) - v i) 0 = v M := by
  intro M
  induction M with
  | zero => intro _; simp
  | succ M ih =>
    intro h
    rw [Finset.sum_range_succ, ← add_assoc, ih (fun k hk => h k (by omega)),
      max_eq_left (h M (by omega))]
    ring

theorem cxo_partB (v : ℕ → ℝ)
    (hP : ∀ k k', k < k' → v (k+1) - v k < 0 → v (k'+1) - v k' ≤ 0) : ∀ M, ∃ k ≤ M,
    v 0 + ∑ i ∈ Finset.range M, max (v (i+1) - v i) 0 = v k := by
  intro M
  induction M with
  | zero => exact ⟨0, le_rfl, by simp⟩
  | succ M ih =>
    obtain ⟨k, hk, hS⟩ := ih
    rw [Finset.sum_range_succ, ← add_assoc]
    rcases le_or_gt (v (M+1) - v M) 0 with h | h
    · refine ⟨k, by omega, ?_⟩
      rw [hS, max_eq_right h, add_zero]
    · have hall : ∀ k < M, 0 ≤ v (k+1) - v k := by
        intro k' hk'
        by_contra hneg
        push Not at hneg
        have := hP k' M hk' hneg
        linarith
      refine ⟨M+1, le_rfl, ?_⟩
      rw [cxo_partA v M hall, max_eq_left h.le]
      ring

theorem cxo_hinge {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ)
    (hsl : ∀ a : ℝ, ∫ ω, max (X ω - a) 0 ∂μ ≤ ∫ ω, max (Y ω - a) 0 ∂ν)
    (γ δ : ℝ) (hγ : 0 ≤ γ) :
    ∫ ω, max (γ * X ω + δ) 0 ∂μ ≤ ∫ ω, max (γ * Y ω + δ) 0 ∂ν := by
  rcases hγ.eq_or_lt with h | h
  · subst h
    simp
  · have key : ∀ z : ℝ, max (γ * z + δ) 0 = γ * max (z - (-δ / γ)) 0 := by
      intro z
      rw [mul_max_of_nonneg _ _ h.le, mul_zero]
      congr 1
      field_simp
      ring
    simp_rw [key]
    rw [integral_const_mul, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hsl _) h.le

theorem cxo_gen {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Integrable X μ) (hY : Integrable Y ν)
    (hmean : ∫ ω, X ω ∂μ = ∫ ω, Y ω ∂ν)
    (hsl : ∀ a : ℝ, ∫ ω, max (X ω - a) 0 ∂μ ≤ ∫ ω, max (Y ω - a) 0 ∂ν)
    (ψ : ℝ → ℝ) (A B : ℝ) (s : Finset ℕ) (γ δ : ℕ → ℝ) (hγ : ∀ k, 0 ≤ γ k)
    (hψ : ∀ z, ψ z = A + B * z + ∑ k ∈ s, max (γ k * z + δ k) 0) :
    ∫ ω, ψ (X ω) ∂μ ≤ ∫ ω, ψ (Y ω) ∂ν := by
  simp_rw [hψ]
  have iX : ∀ k, Integrable (fun ω => max (γ k * X ω + δ k) 0) μ := fun k =>
    ((hX.const_mul (γ k)).add (integrable_const (δ k))).pos_part
  have iY : ∀ k, Integrable (fun ω => max (γ k * Y ω + δ k) 0) ν := fun k =>
    ((hY.const_mul (γ k)).add (integrable_const (δ k))).pos_part
  have iAX : Integrable (fun ω => A + B * X ω) μ := (integrable_const A).add (hX.const_mul B)
  have iAY : Integrable (fun ω => A + B * Y ω) ν := (integrable_const A).add (hY.const_mul B)
  have iSX : Integrable (fun ω => ∑ k ∈ s, max (γ k * X ω + δ k) 0) μ :=
    integrable_finsetSum s fun k _ => iX k
  have iSY : Integrable (fun ω => ∑ k ∈ s, max (γ k * Y ω + δ k) 0) ν :=
    integrable_finsetSum s fun k _ => iY k
  have iBX : Integrable (fun ω => B * X ω) μ := hX.const_mul B
  have iBY : Integrable (fun ω => B * Y ω) ν := hY.const_mul B
  rw [integral_add iAX iSX, integral_add iAY iSY,
    integral_add (integrable_const A) iBX, integral_add (integrable_const A) iBY,
    integral_const_mul, integral_const_mul, integral_finsetSum s fun k _ => iX k,
    integral_finsetSum s fun k _ => iY k, hmean]
  simp only [integral_const, probReal_univ, one_smul]
  gcongr with k hk
  exact cxo_hinge μ ν X Y hsl (γ k) (δ k) (hγ k)

noncomputable def cxoD (φ : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin φ (Set.Ioi x) x

noncomputable def cxoT (N k : ℕ) : ℝ := ((k : ℝ) - ((N : ℝ) + 1) ^ 2) / ((N : ℝ) + 1)

noncomputable def cxoL (φ : ℝ → ℝ) (N k : ℕ) (x : ℝ) : ℝ :=
  φ (cxoT N k) + cxoD φ (cxoT N k) * (x - cxoT N k)

noncomputable def cxoPsi (φ : ℝ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  cxoL φ N 0 x + ∑ i ∈ Finset.range (2 * (N + 1) ^ 2), max (cxoL φ N (i+1) x - cxoL φ N i x) 0

theorem cxo_Dmono {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) : Monotone (cxoD φ) := by
  intro a b hab
  have h := hφ.monotoneOn_rightDeriv (by simp : a ∈ interior Set.univ)
    (by simp : b ∈ interior Set.univ) hab
  simpa [cxoD] using h

theorem cxo_sg {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) (x y : ℝ) :
    φ x + cxoD φ x * (y - x) ≤ φ y := by
  rcases lt_trichotomy x y with h | h | h
  · have h1 := hφ.rightDeriv_le_slope_of_mem_interior (x := x) (y := y) (by simp)
      (Set.mem_univ _) h
    rw [slope_def_field] at h1
    have h2 : 0 < y - x := sub_pos.2 h
    rw [le_div_iff₀ h2] at h1
    simp only [cxoD]
    linarith
  · subst h; simp
  · have h1 := hφ.slope_le_leftDeriv_of_mem_interior (x := y) (y := x) (Set.mem_univ _)
      (by simp) h
    have h3 := hφ.leftDeriv_le_rightDeriv_of_mem_interior (x := x) (by simp)
    rw [slope_def_field] at h1
    have h2 : 0 < x - y := sub_pos.2 h
    rw [div_le_iff₀ h2] at h1
    have h4 := mul_le_mul_of_nonneg_right h3 h2.le
    simp only [cxoD]
    nlinarith

theorem cxo_T_mono (N : ℕ) {k k' : ℕ} (h : k ≤ k') : cxoT N k ≤ cxoT N k' := by
  unfold cxoT
  have : (k : ℝ) ≤ k' := by exact_mod_cast h
  gcongr

theorem cxo_T_zero (N : ℕ) : cxoT N ((N + 1) ^ 2) = 0 := by
  unfold cxoT
  push_cast
  simp

theorem cxo_e_nonneg {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) {a b x : ℝ} (hab : a ≤ b)
    (hbx : b ≤ x) :
    0 ≤ (φ b + cxoD φ b * (x - b)) - (φ a + cxoD φ a * (x - a)) := by
  have h1 := cxo_sg hφ a b
  have h2 := mul_nonneg (sub_nonneg.2 (cxo_Dmono hφ hab)) (sub_nonneg.2 hbx)
  nlinarith

theorem cxo_e_nonpos {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) {a b x : ℝ} (hab : a ≤ b)
    (hxa : x ≤ a) :
    (φ b + cxoD φ b * (x - b)) - (φ a + cxoD φ a * (x - a)) ≤ 0 := by
  have h1 := cxo_sg hφ b a
  have h2 := mul_nonneg (sub_nonneg.2 (cxo_Dmono hφ hab)) (sub_nonneg.2 hxa)
  nlinarith

theorem cxo_psi_le {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) (N : ℕ) (x : ℝ) :
    cxoPsi φ N x ≤ φ x := by
  have hP : ∀ k k', k < k' → cxoL φ N (k+1) x - cxoL φ N k x < 0 →
      cxoL φ N (k'+1) x - cxoL φ N k' x ≤ 0 := by
    intro k k' hkk' hneg
    have hlt : x < cxoT N (k+1) := by
      by_contra hc
      push Not at hc
      have := cxo_e_nonneg hφ (cxo_T_mono N (Nat.le_succ k)) hc
      unfold cxoL at hneg
      linarith
    have hle : x ≤ cxoT N k' := hlt.le.trans (cxo_T_mono N (by omega))
    have := cxo_e_nonpos hφ (cxo_T_mono N (Nat.le_succ k')) hle
    unfold cxoL
    linarith
  obtain ⟨k, _, hk⟩ := cxo_partB (fun k => cxoL φ N k x) hP (2 * (N + 1) ^ 2)
  unfold cxoPsi
  rw [hk]
  exact cxo_sg hφ _ _

theorem cxo_psi_ge {φ : ℝ → ℝ} (N : ℕ) (x : ℝ) :
    φ 0 + cxoD φ 0 * x ≤ cxoPsi φ N x := by
  have h := cxo_partC (fun k => cxoL φ N k x) (2 * (N + 1) ^ 2) ((N + 1) ^ 2) (by nlinarith)
  unfold cxoPsi
  refine le_trans (le_of_eq ?_) h
  simp only [cxoL, cxo_T_zero, sub_zero]

theorem cxo_psi_cont (φ : ℝ → ℝ) (N : ℕ) : Continuous (cxoPsi φ N) := by
  unfold cxoPsi cxoL
  fun_prop

theorem cxo_psi_form (φ : ℝ → ℝ) (N : ℕ) (z : ℝ) :
    cxoPsi φ N z = (φ (cxoT N 0) - cxoD φ (cxoT N 0) * cxoT N 0) + cxoD φ (cxoT N 0) * z +
      ∑ k ∈ Finset.range (2 * (N + 1) ^ 2),
        max ((cxoD φ (cxoT N (k+1)) - cxoD φ (cxoT N k)) * z +
          (φ (cxoT N (k+1)) - cxoD φ (cxoT N (k+1)) * cxoT N (k+1) - φ (cxoT N k) +
            cxoD φ (cxoT N k) * cxoT N k)) 0 := by
  unfold cxoPsi cxoL
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    ring

theorem cxo_psi_tendsto {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) (x : ℝ) :
    Tendsto (fun N => cxoPsi φ N x) atTop (𝓝 (φ x)) := by
  have hc : Continuous φ := continuousOn_univ.1 (hφ.continuousOn isOpen_univ)
  set j : ℕ → ℕ := fun N => ⌊x * ((N : ℝ) + 1) + ((N : ℝ) + 1) ^ 2⌋₊ with hj
  have hev : ∀ᶠ N : ℕ in atTop, |x| < (N : ℝ) + 1 := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop |x|] with N hN
    linarith
  have hpos : ∀ N : ℕ, (0 : ℝ) < (N : ℝ) + 1 := fun N => by positivity
  -- basic floor facts
  have hfacts : ∀ᶠ N : ℕ in atTop, cxoT N (j N) ≤ x ∧ x - 1 / ((N : ℝ) + 1) < cxoT N (j N) ∧
      j N ≤ 2 * (N + 1) ^ 2 := by
    filter_upwards [hev] with N hN
    have hx1 : -((N : ℝ) + 1) < x := by linarith [neg_abs_le x]
    have hx2 : x < (N : ℝ) + 1 := by linarith [le_abs_self x]
    have ha : 0 ≤ x * ((N : ℝ) + 1) + ((N : ℝ) + 1) ^ 2 := by nlinarith [hpos N]
    have hfl := Nat.floor_le ha
    have hfl2 := Nat.lt_floor_add_one (x * ((N : ℝ) + 1) + ((N : ℝ) + 1) ^ 2)
    refine ⟨?_, ?_, ?_⟩
    · simp only [cxoT, hj]
      rw [div_le_iff₀ (hpos N)]
      linarith
    · simp only [cxoT, hj]
      rw [lt_div_iff₀ (hpos N), sub_mul, div_mul_cancel₀ _ (hpos N).ne']
      linarith
    · have : ((j N : ℕ) : ℝ) ≤ ((2 * (N + 1) ^ 2 : ℕ) : ℝ) := by
        push_cast
        simp only [hj]
        nlinarith [hpos N]
      exact_mod_cast this
  have hτ : Tendsto (fun N => cxoT N (j N)) atTop (𝓝 x) := by
    have hlow : Tendsto (fun N : ℕ => x - 1 / ((N : ℝ) + 1)) atTop (𝓝 x) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub x
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [hfacts] with N hN
      exact hN.2.1.le
    · filter_upwards [hfacts] with N hN
      exact hN.1
  have hglow : Tendsto (fun N => φ (cxoT N (j N)) + cxoD φ (x - 1) * (x - cxoT N (j N)))
      atTop (𝓝 (φ x)) := by
    have h1 := (hc.tendsto x).comp hτ
    have h2 : Tendsto (fun N => cxoD φ (x - 1) * (x - cxoT N (j N))) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := x)).sub hτ
      simpa using this.const_mul (cxoD φ (x - 1))
    simpa using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hglow tendsto_const_nhds ?_ ?_
  · filter_upwards [hfacts] with N hN
    obtain ⟨h1, h2, h3⟩ := hN
    have hC := cxo_partC (fun k => cxoL φ N k x) (2 * (N + 1) ^ 2) (j N) h3
    have hin : x - 1 ≤ cxoT N (j N) := by
      have : 1 / ((N : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (hpos N)]
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        linarith
      linarith
    have hD := cxo_Dmono hφ hin
    have hm := mul_le_mul_of_nonneg_right hD (sub_nonneg.2 h1)
    have : cxoL φ N (j N) x ≥ φ (cxoT N (j N)) + cxoD φ (x - 1) * (x - cxoT N (j N)) := by
      unfold cxoL
      linarith
    unfold cxoPsi
    linarith
  · exact Eventually.of_forall fun N => cxo_psi_le hφ N x

open StochasticOrders.Convex in
theorem cxo_key {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Integrable X μ) (hY : Integrable Y ν)
    (hmean : ∫ ω, X ω ∂μ = ∫ ω, Y ω ∂ν)
    (hsl : ∀ a : ℝ, ∫ ω, max (X ω - a) 0 ∂μ ≤ ∫ ω, max (Y ω - a) 0 ∂ν) :
    ConvexOrder μ ν X Y := by
  intro φ hφ hiX hiY
  have hbound : ∀ N z, ‖cxoPsi φ N z‖ ≤ |φ z| + |φ 0 + cxoD φ 0 * z| := by
    intro N z
    have h1 := cxo_psi_le hφ N z
    have h2 := cxo_psi_ge (φ := φ) N z
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [neg_abs_le (φ 0 + cxoD φ 0 * z), abs_nonneg (φ z)]
    · linarith [le_abs_self (φ z), abs_nonneg (φ 0 + cxoD φ 0 * z)]
  have tX : Tendsto (fun N => ∫ ω, cxoPsi φ N (X ω) ∂μ) atTop (𝓝 (∫ ω, φ (X ω) ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun ω => |φ (X ω)| + |φ 0 + cxoD φ 0 * X ω|)
      (fun N => (cxo_psi_cont φ N).comp_aestronglyMeasurable hX.aestronglyMeasurable)
      (hiX.abs.add ((integrable_const _).add (hX.const_mul _)).abs)
      (fun N => Eventually.of_forall fun ω => hbound N (X ω))
      (Eventually.of_forall fun ω => cxo_psi_tendsto hφ (X ω))
  have tY : Tendsto (fun N => ∫ ω, cxoPsi φ N (Y ω) ∂ν) atTop (𝓝 (∫ ω, φ (Y ω) ∂ν)) :=
    tendsto_integral_of_dominated_convergence (fun ω => |φ (Y ω)| + |φ 0 + cxoD φ 0 * Y ω|)
      (fun N => (cxo_psi_cont φ N).comp_aestronglyMeasurable hY.aestronglyMeasurable)
      (hiY.abs.add ((integrable_const _).add (hY.const_mul _)).abs)
      (fun N => Eventually.of_forall fun ω => hbound N (Y ω))
      (Eventually.of_forall fun ω => cxo_psi_tendsto hφ (Y ω))
  refine le_of_tendsto_of_tendsto' tX tY fun N => ?_
  refine cxo_gen μ ν X Y hX hY hmean hsl (cxoPsi φ N) _ _ _ _ _ ?_ (cxo_psi_form φ N)
  intro k
  exact sub_nonneg.2 (cxo_Dmono hφ (cxo_T_mono N (Nat.le_succ k)))

open MeasureTheory StochasticOrders.Convex in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Integrable X μ) (hY : Integrable Y ν)
    (hmean : ∫ ω, X ω ∂μ = ∫ ω, Y ω ∂ν) :
    ConvexOrder μ ν X Y ↔ ∀ a : ℝ, ∫ ω, |X ω - a| ∂μ ≤ ∫ ω, |Y ω - a| ∂ν := by
  constructor
  · intro h a
    have hconv : ConvexOn ℝ Set.univ (fun z : ℝ => |z - a|) := by
      refine ⟨convex_univ, fun x _ y _ p q hp hq hpq => ?_⟩
      simp only [smul_eq_mul]
      have e : p * x + q * y - a = p * (x - a) + q * (y - a) := by
        rw [show p * (x - a) + q * (y - a) = p * x + q * y - (p + q) * a by ring, hpq, one_mul]
      rw [e]
      calc |p * (x - a) + q * (y - a)| ≤ |p * (x - a)| + |q * (y - a)| := abs_add_le _ _
        _ = p * |x - a| + q * |y - a| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hq]
    exact h _ hconv (hX.sub (integrable_const a)).abs (hY.sub (integrable_const a)).abs
  · intro h
    refine cxo_key μ ν X Y hX hY hmean fun a => ?_
    have e : ∀ z : ℝ, max (z - a) 0 = (|z - a| + (z - a)) / 2 := by
      intro z
      rcases le_total 0 (z - a) with hz | hz
      · rw [max_eq_left hz, abs_of_nonneg hz]; ring
      · rw [max_eq_right hz, abs_of_nonpos hz]; ring
    simp_rw [e]
    have i1 : Integrable (fun ω => |X ω - a|) μ := (hX.sub (integrable_const a)).abs
    have i2 : Integrable (fun ω => X ω - a) μ := hX.sub (integrable_const a)
    have i3 : Integrable (fun ω => |Y ω - a|) ν := (hY.sub (integrable_const a)).abs
    have i4 : Integrable (fun ω => Y ω - a) ν := hY.sub (integrable_const a)
    rw [integral_div, integral_div, integral_add i1 i2, integral_add i3 i4,
      integral_sub hX (integrable_const a), integral_sub hY (integrable_const a)]
    have := h a
    simp only [integral_const, probReal_univ, one_smul] at *
    rw [hmean]
    linarith
