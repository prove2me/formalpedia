-- Prove2me | solution 1 for StochasticOrders.MonotoneConvex.icx_submartingale_coupling_iff_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T18:06:18.225995+00:00
-- url     : https://prove2.me/submissions/dfb74dd8-9138-40d3-a534-1e28fb6c2f83

import Mathlib
import Definitions.Def_StochasticOrders_Convex_ConvexOrder
import Definitions.Def_StochasticOrders_MonotoneConvex_IcxOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
section CXO

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
end CXO


section PartC2

open MeasureTheory ProbabilityTheory Finset

namespace Fin60

/-- hinge potential of a weight function `w` over the grid `G` at `a`. -/
noncomputable def HP (G : Finset ℝ) (w : ℝ → ℝ) (a : ℝ) : ℝ := ∑ x ∈ G, w x * max (x - a) 0

/-- contraction: move `p` from `ym`, `q` from `yp` to `a`. -/
noncomputable def contr (n : ℝ → ℝ) (ym yp a p q : ℝ) (y : ℝ) : ℝ :=
  n y - (if y = ym then p else 0) - (if y = yp then q else 0) + (if y = a then p + q else 0)

theorem sum_contr (G : Finset ℝ) (n f : ℝ → ℝ) (ym yp a p q : ℝ) (h1 : ym ∈ G) (h2 : yp ∈ G)
    (h3 : a ∈ G) :
    ∑ y ∈ G, contr n ym yp a p q y * f y
      = ∑ y ∈ G, n y * f y - p * f ym - q * f yp + (p + q) * f a := by
  have e : ∀ y, contr n ym yp a p q y * f y
      = n y * f y - (if y = ym then p * f y else 0) - (if y = yp then q * f y else 0)
        + (if y = a then (p + q) * f y else 0) := by
    intro y
    unfold contr
    simp only [sub_mul, add_mul, ite_mul, zero_mul]
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', h1, h2, h3,
    if_true]

/-- tent function of a contraction. -/
noncomputable def tent (ym yp a b : ℝ) : ℝ :=
  (yp - a) * max (ym - b) 0 + (a - ym) * max (yp - b) 0 - (yp - ym) * max (a - b) 0

theorem tent_nonneg {ym yp a : ℝ} (h1 : ym < a) (h2 : a < yp) (b : ℝ) : 0 ≤ tent ym yp a b := by
  unfold tent
  have p1 : 0 < yp - a := by linarith
  have p2 : 0 < a - ym := by linarith
  rcases le_total b ym with hb | hb
  · rw [max_eq_left (by linarith : (0:ℝ) ≤ ym - b), max_eq_left (by linarith : (0:ℝ) ≤ yp - b),
      max_eq_left (by linarith : (0:ℝ) ≤ a - b)]
    nlinarith
  · rcases le_total b a with hb2 | hb2
    · rw [max_eq_right (by linarith : ym - b ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ yp - b),
        max_eq_left (by linarith : (0:ℝ) ≤ a - b)]
      nlinarith
    · rcases le_total b yp with hb3 | hb3
      · rw [max_eq_right (by linarith : ym - b ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ yp - b),
          max_eq_right (by linarith : a - b ≤ 0)]
        nlinarith
      · rw [max_eq_right (by linarith : ym - b ≤ 0), max_eq_right (by linarith : yp - b ≤ 0),
          max_eq_right (by linarith : a - b ≤ 0)]
        nlinarith

theorem HP_contr (G : Finset ℝ) (n : ℝ → ℝ) (ym yp a ε : ℝ) (h1 : ym ∈ G) (h2 : yp ∈ G)
    (h3 : a ∈ G) (b : ℝ) :
    HP G (contr n ym yp a (ε * (yp - a)) (ε * (a - ym))) b = HP G n b - ε * tent ym yp a b := by
  unfold HP
  rw [sum_contr G n (fun x => max (x - b) 0) ym yp a _ _ h1 h2 h3]
  unfold tent
  ring


structure Hyp (G : Finset ℝ) (m n : ℝ → ℝ) : Prop where
  hm : ∀ x ∈ G, 0 ≤ m x
  hn : ∀ y ∈ G, 0 ≤ n y
  mass : ∑ x ∈ G, m x = ∑ y ∈ G, n y
  mean : ∑ x ∈ G, m x * x = ∑ y ∈ G, n y * y
  hing : ∀ a ∈ G, HP G m a ≤ HP G n a

structure Good (G : Finset ℝ) (m n : ℝ → ℝ) (P : ℝ → ℝ → ℝ) : Prop where
  nonneg : ∀ x ∈ G, ∀ y ∈ G, 0 ≤ P x y
  row : ∀ x ∈ G, ∑ y ∈ G, P x y = 1
  mean : ∀ x ∈ G, ∑ y ∈ G, y * P x y = x
  bal : ∀ y ∈ G, ∑ x ∈ G, m x * P x y = n y
  mono : ∀ x₁ ∈ G, ∀ x₂ ∈ G, 0 < m x₁ → 0 < m x₂ → x₁ ≤ x₂ → ∀ t : ℝ,
    ∑ y ∈ G.filter (fun y => t < y), P x₁ y ≤ ∑ y ∈ G.filter (fun y => t < y), P x₂ y

theorem hinge_conv_b {l r b x : ℝ} (hl : l ≤ b) (hb : b ≤ r) :
    (r - l) * max (x - b) 0 ≤ (r - b) * max (x - l) 0 + (b - l) * max (x - r) 0 := by
  rcases le_total x l with h1 | h1
  · rw [max_eq_right (by linarith : x - b ≤ 0), max_eq_right (by linarith : x - l ≤ 0),
      max_eq_right (by linarith : x - r ≤ 0)]
    simp
  · rcases le_total x b with h2 | h2
    · rw [max_eq_right (by linarith : x - b ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ x - l),
        max_eq_right (by linarith : x - r ≤ 0)]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ r - b) (by linarith : (0:ℝ) ≤ x - l)]
    · rcases le_total x r with h3 | h3
      · rw [max_eq_left (by linarith : (0:ℝ) ≤ x - b), max_eq_left (by linarith : (0:ℝ) ≤ x - l),
          max_eq_right (by linarith : x - r ≤ 0)]
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ r - x) (by linarith : (0:ℝ) ≤ b - l)]
      · rw [max_eq_left (by linarith : (0:ℝ) ≤ x - b), max_eq_left (by linarith : (0:ℝ) ≤ x - l),
          max_eq_left (by linarith : (0:ℝ) ≤ x - r)]
        nlinarith

theorem HP_affine (G : Finset ℝ) (n : ℝ → ℝ) (hn : ∀ y ∈ G, 0 ≤ n y) {l r b : ℝ}
    (hl : l ≤ b) (hb : b ≤ r) (hnone : ∀ y ∈ G, l < y → y < r → n y ≤ 0) :
    (r - l) * HP G n b = (r - b) * HP G n l + (b - l) * HP G n r := by
  unfold HP
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hyl : y ≤ l
  · rw [max_eq_right (by linarith : y - b ≤ 0), max_eq_right (by linarith : y - l ≤ 0),
      max_eq_right (by linarith : y - r ≤ 0)]
    simp
  · by_cases hyr : r ≤ y
    · rw [max_eq_left (by linarith : (0:ℝ) ≤ y - b), max_eq_left (by linarith : (0:ℝ) ≤ y - l),
        max_eq_left (by linarith : (0:ℝ) ≤ y - r)]
      ring
    · have h0 : n y = 0 := le_antisymm (hnone y hy (not_le.1 hyl) (not_le.1 hyr)) (hn y hy)
      simp [h0]

theorem HP_convex (G : Finset ℝ) (m : ℝ → ℝ) (hm : ∀ y ∈ G, 0 ≤ m y) {l r b : ℝ}
    (hl : l ≤ b) (hb : b ≤ r) :
    (r - l) * HP G m b ≤ (r - b) * HP G m l + (b - l) * HP G m r := by
  unfold HP
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro y hy
  have := mul_le_mul_of_nonneg_left (hinge_conv_b (x := y) hl hb) (hm y hy)
  nlinarith

theorem uniq (G : Finset ℝ) : ∀ (w w' : ℝ → ℝ), ∑ x ∈ G, w x = ∑ x ∈ G, w' x →
    (∀ a ∈ G, HP G w a = HP G w' a) → ∀ y ∈ G, w y = w' y := by
  induction G using Finset.induction_on_max with
  | empty => intro w w' _ _ y hy; simp at hy
  | insert t S hS ih =>
    intro w w' hmass hH y hy
    have htS : t ∉ S := fun h => lt_irrefl _ (hS t h)
    have hHS : ∀ w : ℝ → ℝ, ∀ a, HP (insert t S) w a = HP S w a + w t * max (t - a) 0 := by
      intro w a
      unfold HP
      rw [Finset.sum_insert htS]
      ring
    have hwt : w t = w' t := by
      rcases S.eq_empty_or_nonempty with he | hne
      · subst he
        simpa using hmass
      · set a := S.max' hne with ha
        have haS : a ∈ S := S.max'_mem hne
        have h1 := hH a (Finset.mem_insert_of_mem haS)
        rw [hHS, hHS] at h1
        have hz : ∀ w : ℝ → ℝ, HP S w a = 0 := by
          intro w
          unfold HP
          apply Finset.sum_eq_zero
          intro x hx
          have : x - a ≤ 0 := by linarith [S.le_max' x hx]
          rw [max_eq_right this]; simp
        rw [hz, hz] at h1
        have hta : 0 < t - a := by linarith [hS a haS]
        rw [max_eq_left hta.le] at h1
        have := mul_right_cancel₀ hta.ne' (by linarith : w t * (t - a) = w' t * (t - a))
        exact this
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact hwt
    · apply ih w w' _ _ y hy
      · rw [Finset.sum_insert htS, Finset.sum_insert htS] at hmass
        linarith
      · intro a ha
        have h1 := hH a (Finset.mem_insert_of_mem ha)
        rw [hHS, hHS, hwt] at h1
        linarith

theorem exists_below {G : Finset ℝ} {m n : ℝ → ℝ} (H : Hyp G m n) {a : ℝ}
    (hga : HP G m a < HP G n a) : ∃ y ∈ G, 0 < n y ∧ y < a := by
  by_contra hno
  simp only [not_exists, not_and, not_lt] at hno
  have h1 : HP G n a = ∑ y ∈ G, n y * (y - a) := by
    unfold HP
    apply Finset.sum_congr rfl
    intro y hy
    by_cases h0 : 0 < n y
    · rw [max_eq_left (by linarith [hno y hy h0])]
    · have : n y = 0 := le_antisymm (not_lt.1 h0) (H.hn y hy)
      simp [this]
  have h2 : ∑ y ∈ G, n y * (y - a) = ∑ x ∈ G, m x * (x - a) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, H.mean, H.mass]
  have h3 : ∑ x ∈ G, m x * (x - a) ≤ HP G m a := by
    unfold HP
    apply Finset.sum_le_sum
    intro x hx
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (H.hm x hx)
  linarith

theorem exists_above {G : Finset ℝ} {m n : ℝ → ℝ} (H : Hyp G m n) {a : ℝ}
    (hga : HP G m a < HP G n a) : ∃ y ∈ G, 0 < n y ∧ a < y := by
  by_contra hno
  simp only [not_exists, not_and, not_lt] at hno
  have h1 : HP G n a = 0 := by
    unfold HP
    apply Finset.sum_eq_zero
    intro y hy
    by_cases h0 : 0 < n y
    · rw [max_eq_right (by linarith [hno y hy h0])]; simp
    · have : n y = 0 := le_antisymm (not_lt.1 h0) (H.hn y hy)
      simp [this]
  have h3 : 0 ≤ HP G m a := by
    unfold HP
    apply Finset.sum_nonneg
    intro x hx
    exact mul_nonneg (H.hm x hx) (le_max_right _ _)
  linarith


theorem tent_zero {ym yp a : ℝ} (h1 : ym < a) (h2 : a < yp) {b : ℝ} (hb : b ≤ ym ∨ yp ≤ b) :
    tent ym yp a b = 0 := by
  unfold tent
  rcases hb with hb | hb
  · rw [max_eq_left (by linarith : (0:ℝ) ≤ ym - b), max_eq_left (by linarith : (0:ℝ) ≤ yp - b),
      max_eq_left (by linarith : (0:ℝ) ≤ a - b)]
    ring
  · rw [max_eq_right (by linarith : ym - b ≤ 0), max_eq_right (by linarith : yp - b ≤ 0),
      max_eq_right (by linarith : a - b ≤ 0)]
    ring

theorem tent_pos_mem {ym yp a : ℝ} (h1 : ym < a) (h2 : a < yp) {b : ℝ}
    (hb : 0 < tent ym yp a b) : ym < b ∧ b < yp := by
  by_contra hcon
  have : b ≤ ym ∨ yp ≤ b := by
    by_cases hx : ym < b
    · right; by_contra hy; exact hcon ⟨hx, not_le.1 hy⟩
    · left; exact not_lt.1 hx
  rw [tent_zero h1 h2 this] at hb
  exact lt_irrefl _ hb

theorem blocking {G : Finset ℝ} {m n : ℝ → ℝ} (H : Hyp G m n) {ym yp a b : ℝ}
    (hymG : ym ∈ G) (hypG : yp ∈ G) (h1 : ym < a) (h2 : a < yp)
    (hnone : ∀ y ∈ G, ym < y → y < yp → y ≠ a → n y ≤ 0)
    (hga : HP G m a < HP G n a) (hb1 : ym < b) (hb2 : b < yp) (hba : b ≠ a) :
    HP G m b < HP G n b := by
  by_contra hcon
  have hb0 : HP G n b ≤ HP G m b := not_lt.1 hcon
  rcases lt_or_gt_of_ne hba with hlt | hgt
  · have hA := HP_affine G n H.hn (l := ym) (r := a) (b := b) hb1.le hlt.le
      (fun y hy hy1 hy2 => hnone y hy hy1 (lt_trans hy2 h2) (ne_of_lt hy2))
    have hC := HP_convex G m H.hm (l := ym) (r := a) (b := b) hb1.le hlt.le
    have hy := H.hing ym hymG
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ a - b) (by linarith : 0 ≤ HP G n ym - HP G m ym),
      mul_pos (by linarith : (0:ℝ) < b - ym) (by linarith : 0 < HP G n a - HP G m a),
      mul_nonneg (by linarith : (0:ℝ) ≤ a - ym) (by linarith : 0 ≤ HP G m b - HP G n b)]
  · have hA := HP_affine G n H.hn (l := a) (r := yp) (b := b) hgt.le hb2.le
      (fun y hy hy1 hy2 => hnone y hy (lt_trans h1 hy1) hy2 (ne_of_gt hy1))
    have hC := HP_convex G m H.hm (l := a) (r := yp) (b := b) hgt.le hb2.le
    have hy := H.hing yp hypG
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ b - a) (by linarith : 0 ≤ HP G n yp - HP G m yp),
      mul_pos (by linarith : (0:ℝ) < yp - b) (by linarith : 0 < HP G n a - HP G m a),
      mul_nonneg (by linarith : (0:ℝ) ≤ yp - a) (by linarith : 0 ≤ HP G m b - HP G n b)]

theorem step_exists {G : Finset ℝ} {m n : ℝ → ℝ} (H : Hyp G m n) {a : ℝ}
    (hga : HP G m a < HP G n a) (haG : a ∈ G) :
    ∃ ym yp ε : ℝ, ym ∈ G ∧ yp ∈ G ∧ ym < a ∧ a < yp ∧ 0 < n ym ∧ 0 < n yp ∧
      (∀ y ∈ G, ym < y → y < yp → y ≠ a → n y ≤ 0) ∧ 0 < ε ∧
      ε * (yp - a) ≤ n ym ∧ ε * (a - ym) ≤ n yp ∧
      (∀ b ∈ G, ε * tent ym yp a b ≤ HP G n b - HP G m b) ∧
      (ε * (yp - a) = n ym ∨ ε * (a - ym) = n yp ∨
        ∃ b ∈ G, 0 < tent ym yp a b ∧ ε * tent ym yp a b = HP G n b - HP G m b) := by
  obtain ⟨y0, hy0G, hy0n, hy0a⟩ := exists_below H hga
  obtain ⟨y1, hy1G, hy1n, hy1a⟩ := exists_above H hga
  set A := G.filter (fun y => 0 < n y ∧ y < a) with hA
  set B := G.filter (fun y => 0 < n y ∧ a < y) with hB
  have hAne : A.Nonempty := ⟨y0, by simp [hA, hy0G, hy0n, hy0a]⟩
  have hBne : B.Nonempty := ⟨y1, by simp [hB, hy1G, hy1n, hy1a]⟩
  set ym := A.max' hAne with hym
  set yp := B.min' hBne with hyp
  have hymA : ym ∈ A := A.max'_mem hAne
  have hypB : yp ∈ B := B.min'_mem hBne
  have hymP := (Finset.mem_filter.1 hymA)
  have hypP := (Finset.mem_filter.1 hypB)
  have hymG : ym ∈ G := hymP.1
  have hypG : yp ∈ G := hypP.1
  have hymn : 0 < n ym := hymP.2.1
  have hypn : 0 < n yp := hypP.2.1
  have hyma : ym < a := hymP.2.2
  have hypa : a < yp := hypP.2.2
  have hnone : ∀ y ∈ G, ym < y → y < yp → y ≠ a → n y ≤ 0 := by
    intro y hy h1 h2 h3
    by_contra hpos
    have hpos' : 0 < n y := not_le.1 hpos
    rcases lt_or_gt_of_ne h3 with h4 | h4
    · have : y ∈ A := by simp [hA, hy, hpos', h4]
      have := A.le_max' y this
      linarith
    · have : y ∈ B := by simp [hB, hy, hpos', h4]
      have := B.min'_le y this
      linarith
  have hp1 : 0 < yp - a := by linarith
  have hp2 : 0 < a - ym := by linarith
  set S := G.filter (fun b => 0 < tent ym yp a b) with hS
  set cand : Finset ℝ := insert (n ym / (yp - a)) (insert (n yp / (a - ym))
    (S.image (fun b => (HP G n b - HP G m b) / tent ym yp a b))) with hcand
  have hcne : cand.Nonempty := ⟨_, Finset.mem_insert_self _ _⟩
  set ε := cand.min' hcne with hε
  have hεmem : ε ∈ cand := cand.min'_mem hcne
  have hεle : ∀ c ∈ cand, ε ≤ c := fun c hc => cand.min'_le c hc
  have hgpos : ∀ b ∈ S, 0 < HP G n b - HP G m b := by
    intro b hb
    have hbp := Finset.mem_filter.1 hb
    obtain ⟨hb1, hb2⟩ := tent_pos_mem hyma hypa hbp.2
    by_cases hba : b = a
    · subst hba; linarith
    · have := blocking H hymG hypG hyma hypa hnone hga hb1 hb2 hba
      linarith
  have hεpos : 0 < ε := by
    rcases Finset.mem_insert.1 hεmem with h | h
    · rw [h]; exact div_pos hymn hp1
    · rcases Finset.mem_insert.1 h with h | h
      · rw [h]; exact div_pos hypn hp2
      · obtain ⟨b, hb, hbe⟩ := Finset.mem_image.1 h
        rw [← hbe]
        exact div_pos (hgpos b hb) (Finset.mem_filter.1 hb).2
  have hc1 : ε * (yp - a) ≤ n ym := by
    have := hεle _ (Finset.mem_insert_self _ _)
    exact (le_div_iff₀ hp1).1 this
  have hc2 : ε * (a - ym) ≤ n yp := by
    have := hεle _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    exact (le_div_iff₀ hp2).1 this
  have hc3 : ∀ b ∈ G, ε * tent ym yp a b ≤ HP G n b - HP G m b := by
    intro b hb
    have hge : 0 ≤ HP G n b - HP G m b := by linarith [H.hing b hb]
    rcases (tent_nonneg hyma hypa b).eq_or_lt with h0 | h0
    · rw [← h0]; simpa using hge
    · have hbS : b ∈ S := by simp [hS, hb, h0]
      have := hεle _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ hbS)))
      exact (le_div_iff₀ h0).1 this
  refine ⟨ym, yp, ε, hymG, hypG, hyma, hypa, hymn, hypn, hnone, hεpos, hc1, hc2, hc3, ?_⟩
  rcases Finset.mem_insert.1 hεmem with h | h
  · left; rw [h]; exact div_mul_cancel₀ _ hp1.ne'
  · rcases Finset.mem_insert.1 h with h | h
    · right; left; rw [h]; exact div_mul_cancel₀ _ hp2.ne'
    · right; right
      obtain ⟨b, hb, hbe⟩ := Finset.mem_image.1 h
      have hbp := Finset.mem_filter.1 hb
      refine ⟨b, hbp.1, hbp.2, ?_⟩
      rw [← hbe]
      exact div_mul_cancel₀ _ hbp.2.ne'


noncomputable def Kfun (ym yp a p q na : ℝ) (z : ℝ) : ℝ :=
  (if z = ym then p / (na + p + q) else 0) + (if z = yp then q / (na + p + q) else 0)
    + (if z = a then na / (na + p + q) else 0)

theorem Kfun_sum (G : Finset ℝ) (f : ℝ → ℝ) {ym yp a : ℝ} (p q na : ℝ) (h1 : ym ∈ G)
    (h2 : yp ∈ G) (h3 : a ∈ G) :
    ∑ z ∈ G, Kfun ym yp a p q na z * f z
      = (p * f ym + q * f yp + na * f a) / (na + p + q) := by
  have e : ∀ z, Kfun ym yp a p q na z * f z
      = (if z = ym then p / (na + p + q) * f z else 0)
        + (if z = yp then q / (na + p + q) * f z else 0)
        + (if z = a then na / (na + p + q) * f z else 0) := by
    intro z; unfold Kfun; simp only [add_mul, ite_mul, zero_mul]
  simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', h1, h2, h3, if_true]
  ring

noncomputable def Pnew (P' : ℝ → ℝ → ℝ) (a : ℝ) (K : ℝ → ℝ) (x z : ℝ) : ℝ :=
  (if z = a then 0 else P' x z) + P' x a * K z

theorem Pnew_sum (G : Finset ℝ) (P' : ℝ → ℝ → ℝ) {a : ℝ} (haG : a ∈ G) (K f : ℝ → ℝ) (x : ℝ) :
    ∑ z ∈ G, Pnew P' a K x z * f z
      = ∑ z ∈ G, P' x z * f z - P' x a * f a + P' x a * ∑ z ∈ G, K z * f z := by
  have e : ∀ z, Pnew P' a K x z * f z
      = P' x z * f z - (if z = a then P' x z * f z else 0) + P' x a * (K z * f z) := by
    intro z
    unfold Pnew
    by_cases hz : z = a
    · subst hz; simp; ring
    · simp [hz]; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', haG, if_true,
    ← Finset.mul_sum]

noncomputable def tailF (G : Finset ℝ) (P : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∑ z ∈ G, P x z * (if t < z then 1 else 0)

theorem tail_filter (G : Finset ℝ) (P : ℝ → ℝ → ℝ) (t x : ℝ) :
    ∑ y ∈ G.filter (fun y => t < y), P x y = tailF G P t x := by
  unfold tailF
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> simp


theorem compose_good {G : Finset ℝ} {m n : ℝ → ℝ} (H : Hyp G m n) {a ym yp ε : ℝ}
    (hymG : ym ∈ G) (hypG : yp ∈ G) (haG : a ∈ G) (hyma : ym < a) (hypa : a < yp)
    (hnone : ∀ y ∈ G, ym < y → y < yp → y ≠ a → n y ≤ 0) (hε : 0 < ε)
    {P' : ℝ → ℝ → ℝ}
    (hP : Good G m (contr n ym yp a (ε * (yp - a)) (ε * (a - ym))) P') :
    ∃ P, Good G m n P := by
  set p := ε * (yp - a) with hp
  set q := ε * (a - ym) with hq
  have hp0 : 0 < p := mul_pos hε (by linarith)
  have hq0 : 0 < q := mul_pos hε (by linarith)
  have hna : 0 ≤ n a := H.hn a haG
  set D := n a + p + q with hD
  have hDpos : 0 < D := by linarith
  have hmy : ym ≠ a := ne_of_lt hyma
  have hay : a ≠ yp := ne_of_lt hypa
  have hmp : ym ≠ yp := ne_of_lt (lt_trans hyma hypa)
  have hn'a : contr n ym yp a p q a = D := by
    simp [contr, hmy.symm, hay, hD]
    ring
  have hn'ym : contr n ym yp a p q ym = n ym - p := by
    simp [contr, hmy, hmp]
  have hn'yp : contr n ym yp a p q yp = n yp - q := by
    simp [contr, hmp.symm, hay.symm]
  have hn'o : ∀ z, z ≠ ym → z ≠ yp → z ≠ a → contr n ym yp a p q z = n z := by
    intro z h1 h2 h3
    simp [contr, h1, h2, h3]
  set K := Kfun ym yp a p q (n a) with hK
  have hKnn : ∀ z, 0 ≤ K z := by
    intro z
    have h1 : 0 ≤ p / D := div_nonneg hp0.le hDpos.le
    have h2 : 0 ≤ q / D := div_nonneg hq0.le hDpos.le
    have h3 : 0 ≤ n a / D := div_nonneg hna hDpos.le
    simp only [hK, Kfun]
    split_ifs <;> linarith
  have hKym : K ym = p / D := by simp [hK, Kfun, hmy, hmp, hD]
  have hKyp : K yp = q / D := by simp [hK, Kfun, hmp.symm, hay.symm, hD]
  have hKa : K a = n a / D := by simp [hK, Kfun, hmy.symm, hay, hD]
  have hKo : ∀ z, z ≠ ym → z ≠ yp → z ≠ a → K z = 0 := by
    intro z h1 h2 h3
    simp [hK, Kfun, h1, h2, h3]
  have hrowzero : ∀ x ∈ G, 0 < m x → ∀ y ∈ G, ym < y → y < yp → y ≠ a → P' x y = 0 := by
    intro x hx hmx y hy h1 h2 h3
    have hb := hP.bal y hy
    rw [hn'o y (ne_of_gt h1) (ne_of_lt h2) h3] at hb
    have hle : m x * P' x y ≤ ∑ x' ∈ G, m x' * P' x' y := by
      apply Finset.single_le_sum (f := fun x' => m x' * P' x' y) _ hx
      intro x' hx'
      exact mul_nonneg (H.hm x' hx') (hP.nonneg x' hx' y hy)
    have h0 := hnone y hy h1 h2 h3
    have : m x * P' x y ≤ 0 := by linarith
    have hnn := hP.nonneg x hx y hy
    by_contra hne
    have : 0 < P' x y := lt_of_le_of_ne hnn (Ne.symm hne)
    nlinarith
  refine ⟨Pnew P' a K, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx z hz
    unfold Pnew
    have := hP.nonneg x hx z hz
    have := hP.nonneg x hx a haG
    have := hKnn z
    split_ifs <;> positivity
  · intro x hx
    have hK1 : ∑ z ∈ G, K z = 1 := by
      have h := Kfun_sum G (fun _ => (1:ℝ)) p q (n a) hymG hypG haG
      simp only [mul_one] at h
      rw [h, div_eq_one_iff_eq hDpos.ne']; ring
    have := Pnew_sum G P' haG K (fun _ => 1) x
    simp only [mul_one] at this
    rw [this, hK1, hP.row x hx]
    ring
  · intro x hx
    have := Pnew_sum G P' haG K (fun z => z) x
    have e1 : ∑ y ∈ G, y * Pnew P' a K x y = ∑ y ∈ G, Pnew P' a K x y * y := by
      apply Finset.sum_congr rfl; intros; ring
    have e2 : ∑ y ∈ G, y * P' x y = ∑ y ∈ G, P' x y * y := by
      apply Finset.sum_congr rfl; intros; ring
    rw [e1, this, ← e2, hP.mean x hx, Kfun_sum G (fun z => z) p q (n a) hymG hypG haG]
    have : (p * ym + q * yp + n a * a) / (n a + p + q) = a := by
      rw [div_eq_iff hDpos.ne']
      simp only [hp, hq]
      ring
    rw [show (p * ym + q * yp + n a * a) / (n a + p + q) = a from this]
    ring
  · intro z hz
    have hs : ∑ x ∈ G, m x * Pnew P' a K x z
        = (if z = a then 0 else ∑ x ∈ G, m x * P' x z) + (∑ x ∈ G, m x * P' x a) * K z := by
      unfold Pnew
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      · by_cases hza : z = a
        · simp [hza]
        · simp [hza]
      · rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intros; ring
    rw [hs, hP.bal a haG, hn'a]
    by_cases hza : z = a
    · subst hza
      rw [if_pos rfl, hKa]
      field_simp
      ring
    · rw [if_neg hza, hP.bal z hz]
      by_cases hzm : z = ym
      · subst hzm
        rw [hn'ym, hKym]
        field_simp
        ring
      · by_cases hzp : z = yp
        · subst hzp
          rw [hn'yp, hKyp]
          field_simp
          ring
        · rw [hn'o z hzm hzp hza, hKo z hzm hzp hza]
          ring
  · intro x₁ hx₁ x₂ hx₂ hm1 hm2 hle t
    rw [tail_filter, tail_filter]
    have hdiff : ∀ x ∈ G, 0 < m x → ∀ s t', ym ≤ s → s ≤ t' → t' < yp →
        tailF G P' s x - tailF G P' t' x = P' x a * (if s < a ∧ a ≤ t' then 1 else 0) := by
      intro x hx hmx s t' hs hst ht
      unfold tailF
      rw [← Finset.sum_sub_distrib]
      have hz : ∀ z ∈ G, P' x z * (if s < z then 1 else 0) - P' x z * (if t' < z then 1 else 0)
          = if z = a then P' x a * (if s < a ∧ a ≤ t' then 1 else 0) else 0 := by
        intro z hz
        by_cases hza : z = a
        · subst hza
          rw [if_pos rfl]
          by_cases h1 : s < z
          · by_cases h2 : t' < z
            · have h3 : ¬ z ≤ t' := not_le.2 h2
              simp [h1, h2, h3]
            · have h3 : z ≤ t' := not_lt.1 h2
              simp [h1, h2, h3]
          · have h2 : ¬ t' < z := by intro h; exact h1 (by linarith)
            simp [h1, h2]
        · rw [if_neg hza]
          by_cases hz1 : s < z ∧ z ≤ t'
          · have : P' x z = 0 :=
              hrowzero x hx hmx z hz (by linarith [hz1.1]) (by linarith [hz1.2]) hza
            simp [this]
          · have : (if s < z then (1:ℝ) else 0) = if t' < z then 1 else 0 := by
              by_cases h1 : s < z
              · have h2 : t' < z := by
                  by_contra h; exact hz1 ⟨h1, not_lt.1 h⟩
                simp [h1, h2]
              · have h2 : ¬ t' < z := by intro h; exact h1 (by linarith)
                simp [h1, h2]
            rw [this]; ring
      rw [Finset.sum_congr rfl hz, Finset.sum_ite_eq' G a, if_pos haG]
    have hNew : ∀ x t : ℝ, tailF G (Pnew P' a K) t x
        = tailF G P' t x - P' x a * (if t < a then 1 else 0)
          + P' x a * ((p * (if t < ym then 1 else 0) + q * (if t < yp then 1 else 0)
            + n a * (if t < a then 1 else 0)) / D) := by
      intro x t
      have h1 := Pnew_sum G P' haG K (fun z => if t < z then 1 else 0) x
      have h2 := Kfun_sum G (fun z => if t < z then (1:ℝ) else 0) p q (n a) hymG hypG haG
      unfold tailF
      rw [h1]
      rw [← hK] at h2
      rw [h2]
    have hform : ∃ c t1 t2 : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ x ∈ G, 0 < m x →
        tailF G (Pnew P' a K) t x = c * tailF G P' t1 x + (1 - c) * tailF G P' t2 x := by
      rcases lt_or_ge t ym with h1 | h1
      · refine ⟨1, t, t, by norm_num, le_refl _, ?_⟩
        intro x hx hmx
        have hD1 : (p * 1 + q * 1 + n a * 1) / D = 1 := by
          rw [div_eq_one_iff_eq hDpos.ne']; rw [hD]; ring
        rw [hNew x t, if_pos h1, if_pos (lt_trans h1 hyma),
          if_pos (lt_trans h1 (lt_trans hyma hypa)), hD1]
        ring
      · rcases lt_or_ge t a with h2 | h2
        · refine ⟨(q + n a) / D, t, a, div_nonneg (by linarith) hDpos.le, ?_, ?_⟩
          · rw [div_le_one hDpos]; rw [hD]; linarith
          · intro x hx hmx
            have hd := hdiff x hx hmx t a h1 h2.le hypa
            rw [if_pos ⟨h2, le_refl a⟩, mul_one] at hd
            rw [hNew x t, if_neg (not_lt.2 h1), if_pos (lt_trans h2 hypa), if_pos h2]
            have e : (p * 0 + q * 1 + n a * 1) / D = (q + n a) / D := by ring
            rw [e]
            have : tailF G P' t x = tailF G P' a x + P' x a := by linarith
            rw [this]; ring
        · rcases lt_or_ge t yp with h3 | h3
          · refine ⟨q / D, ym, t, div_nonneg hq0.le hDpos.le, ?_, ?_⟩
            · rw [div_le_one hDpos]; rw [hD]; linarith
            · intro x hx hmx
              have hd1 := hdiff x hx hmx ym a (le_refl _) hyma.le hypa
              rw [if_pos ⟨hyma, le_refl a⟩, mul_one] at hd1
              have hd2 := hdiff x hx hmx a t hyma.le h2 h3
              rw [if_neg (by intro h; exact lt_irrefl _ h.1), mul_zero] at hd2
              rw [hNew x t, if_neg (not_lt.2 h1), if_pos h3, if_neg (not_lt.2 h2)]
              have e : (p * 0 + q * 1 + n a * 0) / D = q / D := by ring
              rw [e]
              have e1 : tailF G P' ym x = tailF G P' a x + P' x a := by linarith
              have e2 : tailF G P' t x = tailF G P' a x := by linarith
              rw [e1, e2]; ring
          · refine ⟨1, t, t, by norm_num, le_refl _, ?_⟩
            intro x hx hmx
            rw [hNew x t, if_neg (not_lt.2 (le_trans hyma.le h2)), if_neg (not_lt.2 h3),
              if_neg (not_lt.2 h2)]
            ring
    obtain ⟨c, t1, t2, hc0, hc1, hfm⟩ := hform
    rw [hfm x₁ hx₁ hm1, hfm x₂ hx₂ hm2]
    have e1 := hP.mono x₁ hx₁ x₂ hx₂ hm1 hm2 hle t1
    have e2 := hP.mono x₁ hx₁ x₂ hx₂ hm1 hm2 hle t2
    rw [tail_filter, tail_filter] at e1 e2
    nlinarith [mul_le_mul_of_nonneg_left e1 hc0, mul_le_mul_of_nonneg_left e2 (sub_nonneg.2 hc1)]


noncomputable def badS (G : Finset ℝ) (m n : ℝ → ℝ) : Finset ℝ :=
  G.filter (fun b => HP G m b < HP G n b)
noncomputable def actS (G : Finset ℝ) (m n : ℝ → ℝ) : Finset ℝ :=
  G.filter (fun b => 0 < n b ∨ HP G m b < HP G n b)
noncomputable def supS (G : Finset ℝ) (n : ℝ → ℝ) : Finset ℝ :=
  G.filter (fun b => 0 < n b)
noncomputable def Phi (G : Finset ℝ) (m n : ℝ → ℝ) : ℕ :=
  (2 * G.card + 1) * (badS G m n).card + (actS G m n).card + (supS G n).card

theorem phi_arith (g B B' A A' S S' : ℕ) (hA' : A' ≤ g) (hS' : S' ≤ g)
    (h : (B' < B) ∨ (B' ≤ B ∧ A' ≤ A ∧ S' < S) ∨ (B' ≤ B ∧ A' < A ∧ S' ≤ S)) :
    (2 * g + 1) * B' + A' + S' < (2 * g + 1) * B + A + S := by
  rcases h with h | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have : (2 * g + 1) * (B' + 1) ≤ (2 * g + 1) * B := Nat.mul_le_mul_left _ h
    nlinarith
  · have : (2 * g + 1) * B' ≤ (2 * g + 1) * B := Nat.mul_le_mul_left _ h1
    omega
  · have : (2 * g + 1) * B' ≤ (2 * g + 1) * B := Nat.mul_le_mul_left _ h1
    omega

theorem phi_lt_bad {G : Finset ℝ} {m n n' : ℝ → ℝ}
    (hHP : ∀ b ∈ G, HP G n' b ≤ HP G n b) {b0 : ℝ} (hb0G : b0 ∈ G)
    (hb0 : HP G m b0 < HP G n b0) (hb0' : ¬ HP G m b0 < HP G n' b0) :
    Phi G m n' < Phi G m n := by
  unfold Phi
  apply phi_arith
  · exact Finset.card_filter_le _ _
  · exact Finset.card_filter_le _ _
  · left
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨b0, by simp [badS, hb0G, hb0], by simp [badS, hb0']⟩
    · intro b hb
      simp only [badS, Finset.mem_filter] at hb ⊢
      exact ⟨hb.1, lt_of_lt_of_le hb.2 (hHP b hb.1)⟩

theorem phi_lt_atom {G : Finset ℝ} {m n n' : ℝ → ℝ} {a y0 : ℝ} (haG : a ∈ G)
    (hga : HP G m a < HP G n a) (hy0G : y0 ∈ G) (hy0n : 0 < n y0) (hy0n' : n' y0 = 0)
    (hy0a : y0 ≠ a) (hle : ∀ b ∈ G, b ≠ a → n' b ≤ n b)
    (hHP : ∀ b ∈ G, HP G n' b ≤ HP G n b)
    (hprio : n a ≤ 0 → ∀ y ∈ G, 0 < n y → HP G n y ≤ HP G m y) :
    Phi G m n' < Phi G m n := by
  have hbadsub : badS G m n' ⊆ badS G m n := by
    intro b hb
    simp only [badS, Finset.mem_filter] at hb ⊢
    exact ⟨hb.1, lt_of_lt_of_le hb.2 (hHP b hb.1)⟩
  have hactsub : actS G m n' ⊆ actS G m n := by
    intro b hb
    simp only [actS, Finset.mem_filter] at hb ⊢
    refine ⟨hb.1, ?_⟩
    rcases hb.2 with h | h
    · by_cases hba : b = a
      · subst hba; right; exact hga
      · left; exact lt_of_lt_of_le h (hle b hb.1 hba)
    · right; exact lt_of_lt_of_le h (hHP b hb.1)
  unfold Phi
  apply phi_arith _ _ _ _ _ _ _ (Finset.card_filter_le _ _) (Finset.card_filter_le _ _)
  have hy0s : y0 ∈ supS G n := by simp [supS, hy0G, hy0n]
  by_cases ha : 0 < n a
  · right; left
    refine ⟨Finset.card_le_card hbadsub, Finset.card_le_card hactsub, ?_⟩
    have hsub : supS G n' ⊆ (supS G n).erase y0 := by
      intro b hb
      simp only [supS, Finset.mem_filter] at hb
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · rintro rfl; rw [hy0n'] at hb; exact lt_irrefl _ hb.2
      · simp only [supS, Finset.mem_filter]
        refine ⟨hb.1, ?_⟩
        by_cases hba : b = a
        · subst hba; exact ha
        · exact lt_of_lt_of_le hb.2 (hle b hb.1 hba)
    calc (supS G n').card ≤ ((supS G n).erase y0).card := Finset.card_le_card hsub
      _ < (supS G n).card := Finset.card_erase_lt_of_mem hy0s
  · right; right
    have han : n a ≤ 0 := not_lt.1 ha
    have hy0act : y0 ∈ actS G m n := by simp [actS, hy0G, hy0n]
    refine ⟨Finset.card_le_card hbadsub, ?_, ?_⟩
    · have hsub : actS G m n' ⊆ (actS G m n).erase y0 := by
        intro b hb
        have hb' := hactsub hb
        rw [Finset.mem_erase]
        refine ⟨?_, hb'⟩
        rintro rfl
        simp only [actS, Finset.mem_filter] at hb
        rcases hb.2 with h | h
        · rw [hy0n'] at h; exact lt_irrefl _ h
        · have := hprio han b hb.1 hy0n
          have := hHP b hb.1
          linarith
      calc (actS G m n').card ≤ ((actS G m n).erase y0).card := Finset.card_le_card hsub
        _ < (actS G m n).card := Finset.card_erase_lt_of_mem hy0act
    · have hsub : supS G n' ⊆ insert a ((supS G n).erase y0) := by
        intro b hb
        simp only [supS, Finset.mem_filter] at hb
        rw [Finset.mem_insert, Finset.mem_erase]
        by_cases hba : b = a
        · left; exact hba
        · right
          refine ⟨?_, ?_⟩
          · rintro rfl; rw [hy0n'] at hb; exact lt_irrefl _ hb.2
          · simp only [supS, Finset.mem_filter]
            exact ⟨hb.1, lt_of_lt_of_le hb.2 (hle b hb.1 hba)⟩
      calc (supS G n').card ≤ (insert a ((supS G n).erase y0)).card := Finset.card_le_card hsub
        _ ≤ ((supS G n).erase y0).card + 1 := Finset.card_insert_le _ _
        _ = (supS G n).card := by
          rw [Finset.card_erase_of_mem hy0s]
          have : 0 < (supS G n).card := Finset.card_pos.2 ⟨y0, hy0s⟩
          omega


theorem step_down {G : Finset ℝ} {m n : ℝ → ℝ} (H : Hyp G m n) {a : ℝ} (haG : a ∈ G)
    (hga : HP G m a < HP G n a)
    (hprio : n a ≤ 0 → ∀ y ∈ G, 0 < n y → HP G n y ≤ HP G m y) :
    ∃ n' : ℝ → ℝ, Hyp G m n' ∧ Phi G m n' < Phi G m n ∧
      ∀ P', Good G m n' P' → ∃ P, Good G m n P := by
  obtain ⟨ym, yp, ε, hymG, hypG, hyma, hypa, hymn, hypn, hnone, hε, hc1, hc2, hc3, hdis⟩ :=
    step_exists H hga haG
  have hmy : ym ≠ a := ne_of_lt hyma
  have hay : a ≠ yp := ne_of_lt hypa
  have hmp : ym ≠ yp := ne_of_lt (lt_trans hyma hypa)
  have hna : 0 ≤ n a := H.hn a haG
  have hp0 : 0 < ε * (yp - a) := mul_pos hε (by linarith)
  have hq0 : 0 < ε * (a - ym) := mul_pos hε (by linarith)
  have hn'a : contr n ym yp a (ε * (yp - a)) (ε * (a - ym)) a
      = n a + ε * (yp - a) + ε * (a - ym) := by
    simp [contr, hmy.symm, hay]
    ring
  have hn'ym : contr n ym yp a (ε * (yp - a)) (ε * (a - ym)) ym = n ym - ε * (yp - a) := by
    simp [contr, hmy, hmp]
  have hn'yp : contr n ym yp a (ε * (yp - a)) (ε * (a - ym)) yp = n yp - ε * (a - ym) := by
    simp [contr, hmp.symm, hay.symm]
  have hn'o : ∀ z, z ≠ ym → z ≠ yp → z ≠ a →
      contr n ym yp a (ε * (yp - a)) (ε * (a - ym)) z = n z := by
    intro z h1 h2 h3
    simp [contr, h1, h2, h3]
  have hHPeq : ∀ b, HP G (contr n ym yp a (ε * (yp - a)) (ε * (a - ym))) b
      = HP G n b - ε * tent ym yp a b := fun b => HP_contr G n ym yp a ε hymG hypG haG b
  have hHP : ∀ b ∈ G, HP G (contr n ym yp a (ε * (yp - a)) (ε * (a - ym))) b ≤ HP G n b := by
    intro b _
    rw [hHPeq b]
    have := tent_nonneg hyma hypa b
    nlinarith
  refine ⟨contr n ym yp a (ε * (yp - a)) (ε * (a - ym)), ?_, ?_, ?_⟩
  · refine ⟨H.hm, ?_, ?_, ?_, ?_⟩
    · intro y hy
      by_cases h1 : y = ym
      · subst h1; rw [hn'ym]; linarith
      · by_cases h2 : y = yp
        · subst h2; rw [hn'yp]; linarith
        · by_cases h3 : y = a
          · subst h3; rw [hn'a]; linarith
          · rw [hn'o y h1 h2 h3]; exact H.hn y hy
    · have h := sum_contr G n (fun _ => (1:ℝ)) ym yp a (ε * (yp - a)) (ε * (a - ym))
        hymG hypG haG
      simp only [mul_one] at h
      rw [H.mass, h]; ring
    · have h := sum_contr G n (fun y => y) ym yp a (ε * (yp - a)) (ε * (a - ym)) hymG hypG haG
      rw [H.mean, h]; ring
    · intro b hb
      rw [hHPeq b]
      have := hc3 b hb
      linarith
  · rcases hdis with h | h | ⟨b0, hb0G, htpos, hb0e⟩
    · apply phi_lt_atom (a := a) (y0 := ym) haG hga hymG hymn
      · rw [hn'ym]; linarith
      · exact hmy
      · intro b hb hba
        by_cases h1 : b = ym
        · subst h1; rw [hn'ym]; linarith
        · by_cases h2 : b = yp
          · subst h2; rw [hn'yp]; linarith
          · rw [hn'o b h1 h2 hba]
      · exact hHP
      · exact hprio
    · apply phi_lt_atom (a := a) (y0 := yp) haG hga hypG hypn
      · rw [hn'yp]; linarith
      · exact hay.symm
      · intro b hb hba
        by_cases h1 : b = ym
        · subst h1; rw [hn'ym]; linarith
        · by_cases h2 : b = yp
          · subst h2; rw [hn'yp]; linarith
          · rw [hn'o b h1 h2 hba]
      · exact hHP
      · exact hprio
    · apply phi_lt_bad hHP hb0G
      · have := mul_pos hε htpos
        linarith
      · rw [hHPeq b0]
        intro hlt
        linarith
  · intro P' hP
    exact compose_good H hymG hypG haG hyma hypa hnone hε hP

theorem terminal {G : Finset ℝ} {m n : ℝ → ℝ} (H : Hyp G m n)
    (hnb : ∀ a ∈ G, ¬ HP G m a < HP G n a) : ∃ P, Good G m n P := by
  have hHeq : ∀ a ∈ G, HP G m a = HP G n a := fun a ha =>
    le_antisymm (H.hing a ha) (not_lt.1 (hnb a ha))
  have hmn := uniq G m n H.mass hHeq
  refine ⟨fun x y => if y = x then 1 else 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro x _ y _; split_ifs <;> norm_num
  · intro x hx; simp [hx]
  · intro x hx; simp [hx]
  · intro y hy
    rw [← hmn y hy]
    simp [Finset.sum_ite_eq, hy]
  · intro x₁ hx₁ x₂ hx₂ _ _ hle t
    simp only [Finset.sum_ite_eq', Finset.mem_filter, hx₁, hx₂, true_and]
    by_cases h1 : t < x₁
    · have h2 : t < x₂ := lt_of_lt_of_le h1 hle
      simp [h1, h2]
    · simp only [h1, if_false]
      split_ifs <;> norm_num

theorem fin_main {G : Finset ℝ} {m : ℝ → ℝ} :
    ∀ (k : ℕ) (n : ℝ → ℝ), Hyp G m n → Phi G m n = k → ∃ P, Good G m n P := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n H hk
    by_cases hbad : ∃ a ∈ G, HP G m a < HP G n a
    · have hex : ∃ a ∈ G, HP G m a < HP G n a ∧
          (n a ≤ 0 → ∀ y ∈ G, 0 < n y → HP G n y ≤ HP G m y) := by
        by_cases hA : ∃ a ∈ G, 0 < n a ∧ HP G m a < HP G n a
        · obtain ⟨a, haG, han, hag⟩ := hA
          exact ⟨a, haG, hag, fun h => absurd han (not_lt.2 h)⟩
        · obtain ⟨a, haG, hag⟩ := hbad
          refine ⟨a, haG, hag, fun _ y hy hyn => ?_⟩
          by_contra hcon
          exact hA ⟨y, hy, hyn, not_le.1 hcon⟩
      obtain ⟨a, haG, hag, hprio⟩ := hex
      obtain ⟨n', Hn', hlt, hcomp⟩ := step_down H haG hag hprio
      obtain ⟨P', hP'⟩ := ih (Phi G m n') (lt_of_lt_of_eq hlt hk) n' Hn' rfl
      exact hcomp P' hP'
    · exact terminal H (fun a ha h => hbad ⟨a, ha, h⟩)

theorem fin_exists {G : Finset ℝ} {m n : ℝ → ℝ} (H : Hyp G m n) : ∃ P, Good G m n P :=
  fin_main _ n H rfl

end Fin60

namespace Fin60

/-- A measure vanishing off a finite set is a sum of weighted Diracs. -/
theorem meas_eq_sum (ρ : Measure ℝ) (G : Finset ℝ) (hG : ρ (↑G : Set ℝ)ᶜ = 0) :
    ρ = ∑ x ∈ G, ρ {x} • Measure.dirac x := by
  classical
  ext s hs
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
  rw [← measure_inter_conull (s := s) hG]
  have h1 : s ∩ (↑G : Set ℝ) = ↑(G.filter (· ∈ s)) := by ext x; simp [and_comm]
  rw [h1, ← sum_measure_singleton, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ s <;> simp [hx]

theorem integral_sumdirac (w : ℝ → ENNReal) (G : Finset ℝ) (hw : ∀ y ∈ G, w y ≠ ⊤) (f : ℝ → ℝ) :
    Integrable f (∑ y ∈ G, w y • Measure.dirac y) ∧
      ∫ x, f x ∂(∑ y ∈ G, w y • Measure.dirac y) = ∑ y ∈ G, (w y).toReal * f y := by
  have hint : ∀ y ∈ G, Integrable f (w y • Measure.dirac y) := fun y hy =>
    (integrable_dirac (by simp)).smul_measure (hw y hy)
  refine ⟨integrable_finsetSum_measure.2 hint, ?_⟩
  rw [integral_finsetSum_measure hint]
  apply Finset.sum_congr rfl
  intro y _
  rw [integral_smul_measure, integral_dirac]
  simp [smul_eq_mul]

theorem fin_integral (ρ : Measure ℝ) [IsFiniteMeasure ρ] (G : Finset ℝ)
    (hG : ρ (↑G : Set ℝ)ᶜ = 0) (f : ℝ → ℝ) :
    Integrable f ρ ∧ ∫ x, f x ∂ρ = ∑ x ∈ G, (ρ {x}).toReal * f x := by
  have h := integral_sumdirac (fun x => ρ {x}) G (fun y _ => measure_ne_top ρ _) f
  rw [← meas_eq_sum ρ G hG] at h
  exact h

theorem hyp_of_convex (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (G : Finset ℝ) (hμ : μ (↑G : Set ℝ)ᶜ = 0) (hν : ν (↑G : Set ℝ)ᶜ = 0)
    (hcx : StochasticOrders.Convex.ConvexOrder μ ν id id) :
    Hyp G (fun x => (μ {x}).toReal) (fun y => (ν {y}).toReal) := by
  have Iμ := fin_integral μ G hμ
  have Iν := fin_integral ν G hν
  have hlin : ∀ c : ℝ, ConvexOn ℝ Set.univ (fun x : ℝ => c * x) := by
    intro c
    refine ⟨convex_univ, fun x _ y _ s t _ _ hst => ?_⟩
    simp only [smul_eq_mul]
    nlinarith
  refine ⟨fun x _ => ENNReal.toReal_nonneg, fun y _ => ENNReal.toReal_nonneg, ?_, ?_, ?_⟩
  · have h1 := (Iμ (fun _ => 1)).2
    have h2 := (Iν (fun _ => 1)).2
    simp at h1 h2
    linarith
  · have h1 : ∫ x, (1:ℝ) * x ∂μ ≤ ∫ y, (1:ℝ) * y ∂ν :=
      hcx (fun x => 1 * x) (hlin 1) (Iμ _).1 (Iν _).1
    have h2 : ∫ x, (-1:ℝ) * x ∂μ ≤ ∫ y, (-1:ℝ) * y ∂ν :=
      hcx (fun x => -1 * x) (hlin (-1)) (Iμ _).1 (Iν _).1
    rw [(Iμ _).2, (Iν _).2] at h1 h2
    have e1 : ∑ x ∈ G, (μ {x}).toReal * (1 * x) = ∑ x ∈ G, (μ {x}).toReal * x := by
      apply Finset.sum_congr rfl; intros; ring
    have e2 : ∑ x ∈ G, (ν {x}).toReal * (1 * x) = ∑ x ∈ G, (ν {x}).toReal * x := by
      apply Finset.sum_congr rfl; intros; ring
    have e3 : ∑ x ∈ G, (μ {x}).toReal * (-1 * x) = - ∑ x ∈ G, (μ {x}).toReal * x := by
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intros; ring
    have e4 : ∑ x ∈ G, (ν {x}).toReal * (-1 * x) = - ∑ x ∈ G, (ν {x}).toReal * x := by
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intros; ring
    rw [e1, e2] at h1
    rw [e3, e4] at h2
    linarith
  · intro a _
    have h1 : ConvexOn ℝ Set.univ (fun x : ℝ => x - a) := by
      refine ⟨convex_univ, fun x _ y _ s t _ _ hst => ?_⟩
      simp only [smul_eq_mul]
      have : s * (x - a) + t * (y - a) = s * x + t * y - (s + t) * a := by ring
      rw [this, hst]; linarith
    have h2 : ConvexOn ℝ Set.univ (fun _ : ℝ => (0:ℝ)) := convexOn_const 0 convex_univ
    have hc : ConvexOn ℝ Set.univ (fun x : ℝ => max (x - a) 0) := h1.sup h2
    have := hcx (fun x => max (x - a) 0) hc (Iμ _).1 (Iν _).1
    have e := (Iμ (fun x => max (x - a) 0)).2
    have e' := (Iν (fun x => max (x - a) 0)).2
    unfold HP
    simp only [id] at this
    rw [e, e'] at this
    exact this

end Fin60

namespace Fin60

theorem meas_apply_fin (ρ : Measure ℝ) (G : Finset ℝ) (hG : ρ (↑G : Set ℝ)ᶜ = 0) {B : Set ℝ}
    (hB : MeasurableSet B) : ρ B = ∑ y ∈ G, ρ {y} * B.indicator 1 y := by
  conv_lhs => rw [meas_eq_sum ρ G hG]
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hB]

theorem lintegral_fin (ρ : Measure ℝ) (G : Finset ℝ) (hG : ρ (↑G : Set ℝ)ᶜ = 0)
    (g : ℝ → ENNReal) (hg : Measurable g) : ∫⁻ x, g x ∂ρ = ∑ x ∈ G, ρ {x} * g x := by
  conv_lhs => rw [meas_eq_sum ρ G hG]
  rw [lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro x _
  rw [lintegral_smul_measure, lintegral_dirac' _ hg]
  simp [smul_eq_mul]

noncomputable def flr (M : Finset ℝ) (x : ℝ) : ℝ :=
  if h : (M.filter (fun s => s ≤ x)).Nonempty then (M.filter (fun s => s ≤ x)).max' h
  else (if h2 : M.Nonempty then M.min' h2 else 0)

theorem flr_mem {M : Finset ℝ} (hM : M.Nonempty) (x : ℝ) : flr M x ∈ M := by
  by_cases h : (M.filter (fun s => s ≤ x)).Nonempty
  · rw [flr, dif_pos h]
    exact (Finset.mem_filter.1 ((M.filter (fun s => s ≤ x)).max'_mem h)).1
  · rw [flr, dif_neg h, dif_pos hM]
    exact M.min'_mem hM

theorem flr_self {M : Finset ℝ} {x : ℝ} (hx : x ∈ M) : flr M x = x := by
  have h : (M.filter (fun s => s ≤ x)).Nonempty := ⟨x, by simp [hx]⟩
  rw [flr, dif_pos h]
  apply le_antisymm
  · exact (Finset.mem_filter.1 ((M.filter (fun s => s ≤ x)).max'_mem h)).2
  · exact Finset.le_max' _ x (by simp [hx])

theorem flr_mono {M : Finset ℝ} (hM : M.Nonempty) : Monotone (flr M) := by
  intro x y hxy
  by_cases hx : (M.filter (fun s => s ≤ x)).Nonempty
  · have hy : (M.filter (fun s => s ≤ y)).Nonempty := by
      obtain ⟨z, hz⟩ := hx
      rw [Finset.mem_filter] at hz
      exact ⟨z, Finset.mem_filter.2 ⟨hz.1, le_trans hz.2 hxy⟩⟩
    rw [flr, dif_pos hx, flr, dif_pos hy]
    apply Finset.max'_le
    intro z hz
    rw [Finset.mem_filter] at hz
    apply Finset.le_max'
    exact Finset.mem_filter.2 ⟨hz.1, le_trans hz.2 hxy⟩
  · rw [flr, dif_neg hx, dif_pos hM]
    by_cases hy : (M.filter (fun s => s ≤ y)).Nonempty
    · rw [flr, dif_pos hy]
      exact M.min'_le _ (Finset.mem_filter.1 ((M.filter (fun s => s ≤ y)).max'_mem hy)).1
    · rw [flr, dif_neg hy, dif_pos hM]

noncomputable def kappa0 (G : Finset ℝ) (P : ℝ → ℝ → ℝ) (s : ℝ) : Measure ℝ :=
  ∑ y ∈ G, ENNReal.ofReal (P s y) • Measure.dirac y

theorem kappa0_apply (G : Finset ℝ) (P : ℝ → ℝ → ℝ) (s : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    kappa0 G P s B = ∑ y ∈ G, ENNReal.ofReal (P s y) * B.indicator 1 y := by
  unfold kappa0
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hB]

theorem kern_meas (G M : Finset ℝ) (P : ℝ → ℝ → ℝ) (hM : M.Nonempty) (B : Set ℝ) :
    Measurable fun x => kappa0 G P (flr M x) B := by
  have e : (fun x => kappa0 G P (flr M x) B)
      = fun x => ∑ s ∈ M, Set.indicator {x | flr M x = s} (fun _ => kappa0 G P s B) x := by
    ext x
    rw [Finset.sum_eq_single (flr M x)]
    · simp
    · intro s _ hs
      have : ¬ flr M x = s := fun h => hs h.symm
      simp [Set.indicator, this]
    · intro h; exact absurd (flr_mem hM x) h
  rw [e]
  apply Finset.measurable_sum
  intro s _
  exact Measurable.indicator measurable_const ((flr_mono hM).measurable (measurableSet_singleton s))

noncomputable def kern (G M : Finset ℝ) (hM : M.Nonempty) (P : ℝ → ℝ → ℝ) : Kernel ℝ ℝ where
  toFun x := kappa0 G P (flr M x)
  measurable' := Measure.measurable_of_measurable_coe _ (fun B _ => kern_meas G M P hM B)

theorem kern_apply (G M : Finset ℝ) (hM : M.Nonempty) (P : ℝ → ℝ → ℝ) (x : ℝ) :
    kern G M hM P x = kappa0 G P (flr M x) := rfl

theorem kern_markov (G M : Finset ℝ) (hM : M.Nonempty) (P : ℝ → ℝ → ℝ)
    (hrow : ∀ s ∈ M, ∑ y ∈ G, P s y = 1) (hnn : ∀ s ∈ M, ∀ y ∈ G, 0 ≤ P s y) :
    IsMarkovKernel (kern G M hM P) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [kern_apply, kappa0_apply G P _ MeasurableSet.univ]
  have hs := flr_mem hM x
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (hnn _ hs), hrow _ hs, ENNReal.ofReal_one]

end Fin60

open MeasureTheory ProbabilityTheory in
/-- A martingale coupling of `μ` and `ν` with a stochastically monotone kernel. -/
def IsMonoMartCoupling60 (μ ν : Measure ℝ) (κ : Kernel ℝ ℝ) : Prop :=
  IsMarkovKernel κ ∧
  (∀ᵐ x ∂μ, Integrable id (κ x) ∧ ∫ y, y ∂(κ x) = x) ∧
  (μ ⊗ₘ κ).snd = ν ∧
  ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → ∀ t : ℝ, κ x₁ {y : ℝ | t < y} ≤ κ x₂ {y : ℝ | t < y}

namespace Fin60

theorem kappa0_tail (G : Finset ℝ) (P : ℝ → ℝ → ℝ) (s t : ℝ) (hnn : ∀ y ∈ G, 0 ≤ P s y) :
    kappa0 G P s (Set.Ioi t) = ENNReal.ofReal (∑ y ∈ G.filter (fun y => t < y), P s y) := by
  rw [kappa0_apply G P s measurableSet_Ioi,
    ENNReal.ofReal_sum_of_nonneg (fun y hy => hnn y (Finset.mem_filter.1 hy).1),
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : t < y <;> simp [h]

theorem c2_core (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (G : Finset ℝ) (hμG : μ (↑G : Set ℝ)ᶜ = 0) (hνG : ν (↑G : Set ℝ)ᶜ = 0)
    (H : Hyp G (fun x => (μ {x}).toReal) (fun y => (ν {y}).toReal)) :
    ∃ κ : Kernel ℝ ℝ, IsMonoMartCoupling60 μ ν κ := by
  classical
  obtain ⟨P, hP⟩ := fin_exists H
  have hbal := hP.bal
  beta_reduce at hbal
  have hmono := hP.mono
  beta_reduce at hmono
  have hone := (fin_integral μ G hμG (fun _ => 1)).2
  simp at hone
  -- the atoms of μ
  obtain ⟨M, hMdef⟩ : ∃ M : Finset ℝ, M = G.filter (fun x => 0 < (μ {x}).toReal) := ⟨_, rfl⟩
  have hMmem : ∀ x ∈ M, x ∈ G ∧ 0 < (μ {x}).toReal := by
    intro x hx; rw [hMdef] at hx; exact Finset.mem_filter.1 hx
  have hMne : M.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hz : ∀ x ∈ G, (μ {x}).toReal = 0 := by
      intro x hx
      by_contra h
      have h1 : 0 < (μ {x}).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h)
      have : x ∈ M := by rw [hMdef]; exact Finset.mem_filter.2 ⟨hx, h1⟩
      rw [hne] at this; simp at this
    rw [Finset.sum_eq_zero (fun x hx => hz x hx)] at hone
    exact one_ne_zero hone
  have hrow : ∀ s ∈ M, ∑ y ∈ G, P s y = 1 := fun s hs => hP.row s (hMmem s hs).1
  have hnn : ∀ s ∈ M, ∀ y ∈ G, 0 ≤ P s y := fun s hs => hP.nonneg s (hMmem s hs).1
  have hmk : IsMarkovKernel (kern G M hMne P) := kern_markov G M hMne P hrow hnn
  have hMnull : μ (↑M : Set ℝ)ᶜ = 0 := by
    rw [meas_apply_fin μ G hμG (Finset.measurableSet M).compl]
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hxM : x ∈ M
    · simp [hxM]
    · have h0 : (μ {x}).toReal = 0 := by
        by_contra h
        apply hxM
        rw [hMdef]
        exact Finset.mem_filter.2 ⟨hx, lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h)⟩
      have : μ {x} = 0 := ((ENNReal.toReal_eq_zero_iff _).1 h0).resolve_right (measure_ne_top _ _)
      simp [this]
  have hae : ∀ᵐ x ∂μ, x ∈ M := by
    rw [ae_iff]
    have e : {a : ℝ | ¬ a ∈ M} = (↑M : Set ℝ)ᶜ := by ext; simp
    rw [e]; exact hMnull
  refine ⟨kern G M hMne P, hmk, ?_, ?_, ?_⟩
  · filter_upwards [hae] with x hx
    rw [kern_apply, flr_self hx]
    obtain ⟨hint, hval⟩ := integral_sumdirac (fun y => ENNReal.ofReal (P x y)) G
      (fun y _ => ENNReal.ofReal_ne_top) id
    refine ⟨hint, ?_⟩
    show ∫ y, id y ∂(kappa0 G P x) = x
    unfold kappa0
    rw [hval]
    have : ∀ y ∈ G, (ENNReal.ofReal (P x y)).toReal * id y = y * P x y := by
      intro y hy
      rw [ENNReal.toReal_ofReal (hP.nonneg x (hMmem x hx).1 y hy)]
      simp [mul_comm]
    rw [Finset.sum_congr rfl this]
    exact hP.mean x (hMmem x hx).1
  · rw [Measure.snd_compProd]
    ext B hB
    rw [Measure.bind_apply hB (kern G M hMne P).measurable.aemeasurable,
      lintegral_fin μ G hμG _ ((kern G M hMne P).measurable_coe hB),
      meas_apply_fin ν G hνG hB]
    have step : ∀ x ∈ G, μ {x} * (kern G M hMne P) x B
        = ENNReal.ofReal ((μ {x}).toReal) *
          ∑ y ∈ G, ENNReal.ofReal (P x y) * B.indicator 1 y := by
      intro x hx
      rw [ENNReal.ofReal_toReal (measure_ne_top μ _)]
      by_cases hxM : x ∈ M
      · rw [kern_apply, flr_self hxM, kappa0_apply G P x hB]
      · have h0 : (μ {x}).toReal = 0 := by
          by_contra h
          apply hxM
          rw [hMdef]
          exact Finset.mem_filter.2 ⟨hx, lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h)⟩
        have : μ {x} = 0 := ((ENNReal.toReal_eq_zero_iff _).1 h0).resolve_right (measure_ne_top _ _)
        simp [this]
    rw [Finset.sum_congr rfl step]
    have step2 : ∀ y ∈ G, ν {y} * B.indicator 1 y
        = ENNReal.ofReal (∑ x ∈ G, (μ {x}).toReal * P x y) * B.indicator 1 y := by
      intro y hy
      rw [hbal y hy, ENNReal.ofReal_toReal (measure_ne_top ν _)]
    rw [Finset.sum_congr rfl step2]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    rw [ENNReal.ofReal_sum_of_nonneg (fun x hx =>
      mul_nonneg ENNReal.toReal_nonneg (hP.nonneg x hx y hy)), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, mul_assoc]
  · intro x₁ x₂ hx t
    rw [kern_apply, kern_apply]
    have e : ({y : ℝ | t < y} : Set ℝ) = Set.Ioi t := rfl
    rw [e, kappa0_tail G P _ t (hnn _ (flr_mem hMne x₁)), kappa0_tail G P _ t (hnn _ (flr_mem hMne x₂))]
    apply ENNReal.ofReal_le_ofReal
    have h1 := flr_mem hMne x₁
    have h2 := flr_mem hMne x₂
    exact hmono _ (hMmem _ h1).1 _ (hMmem _ h2).1 (by have := (hMmem _ h1).2; exact this)
      (by have := (hMmem _ h2).2; exact this) (flr_mono hMne hx) t

theorem c2_finite_monoMart60 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (sμ sν : Finset ℝ) (hμ : μ (↑sμ : Set ℝ)ᶜ = 0) (hν : ν (↑sν : Set ℝ)ᶜ = 0)
    (hcx : StochasticOrders.Convex.ConvexOrder μ ν id id) :
    ∃ κ : Kernel ℝ ℝ, IsMonoMartCoupling60 μ ν κ := by
  have hμG : μ (↑(sμ ∪ sν) : Set ℝ)ᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.2 (Finset.coe_subset.2 Finset.subset_union_left)) hμ
  have hνG : ν (↑(sμ ∪ sν) : Set ℝ)ᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.2 (Finset.coe_subset.2 Finset.subset_union_right)) hν
  exact c2_core μ ν (sμ ∪ sν) hμG hνG (hyp_of_convex μ ν (sμ ∪ sν) hμG hνG hcx)

end Fin60

end PartC2

section PartC4
open MeasureTheory ProbabilityTheory Filter Topology Set

namespace C4L60

/-- Helly-type selection on a countable index set (compactness of `[0,1]^(ℕ × ℚ)`). -/
theorem helly60 (v : ℕ → ℕ × ℚ → ℝ) (hv : ∀ k i, v k i ∈ Icc (0 : ℝ) 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, ∃ a : ℝ, Tendsto (fun k => v (φ k) i) atTop (𝓝 a) := by
  let w : ℕ → (ℕ × ℚ → Icc (0 : ℝ) 1) := fun k i => ⟨v k i, hv k i⟩
  obtain ⟨a, φ, hφ, ht⟩ := CompactSpace.tendsto_subseq w
  refine ⟨φ, hφ, fun i => ⟨(a i : ℝ), ?_⟩⟩
  have h1 : Tendsto (fun k => (w ∘ φ) k i) atTop (𝓝 (a i)) :=
    ((continuous_apply i).tendsto a).comp ht
  exact (continuous_subtype_val.tendsto (a i)).comp h1

theorem bdd_le60 (u : ℕ → ℝ) (hu : ∀ k, u k ∈ Icc (0 : ℝ) 1) :
    IsBoundedUnder (· ≤ ·) atTop u :=
  ⟨1, Filter.eventually_map.2 (Eventually.of_forall fun k => (hu k).2)⟩

theorem cobdd_le60 (u : ℕ → ℝ) (hu : ∀ k, u k ∈ Icc (0 : ℝ) 1) :
    IsCoboundedUnder (· ≤ ·) atTop u :=
  isCoboundedUnder_le_of_le atTop (fun k => (hu k).1)

theorem limsup_mem60 (u : ℕ → ℝ) (hu : ∀ k, u k ∈ Icc (0 : ℝ) 1) :
    limsup u atTop ∈ Icc (0 : ℝ) 1 :=
  ⟨le_limsup_of_frequently_le (Frequently.of_forall fun k => (hu k).1) (bdd_le60 u hu),
    limsup_le_of_le (cobdd_le60 u hu) (Eventually.of_forall fun k => (hu k).2)⟩

theorem limsup_mono60 (u v : ℕ → ℝ) (hu : ∀ k, u k ∈ Icc (0 : ℝ) 1)
    (hv : ∀ k, v k ∈ Icc (0 : ℝ) 1) (h : ∀ k, u k ≤ v k) :
    limsup u atTop ≤ limsup v atTop :=
  limsup_le_limsup (Eventually.of_forall h) (cobdd_le60 u hu) (bdd_le60 v hv)

/-- A countable set without atoms is null. -/
theorem null_of_countable60 (μ : Measure ℝ) (B : Set ℝ) (hB : B.Countable)
    (h : ∀ x ∈ B, μ {x} = 0) : μ B = 0 := by
  rw [← Set.biUnion_of_singleton B]
  exact (measure_biUnion_null_iff hB).2 h

/-- Antitone functions converging on the rationals and at the atoms of `μ` converge `μ`-a.e. -/
theorem ae_tendsto_of_antitone60 (μ : Measure ℝ) (S : ℕ → ℝ → ℝ)
    (hS : ∀ k, Antitone (S k)) (hb : ∀ k x, S k x ∈ Icc (0 : ℝ) 1)
    (hq : ∀ q : ℚ, Tendsto (fun k => S k q) atTop (𝓝 (limsup (fun k => S k q) atTop)))
    (hat : ∀ x, μ {x} ≠ 0 → Tendsto (fun k => S k x) atTop (𝓝 (limsup (fun k => S k x) atTop))) :
    ∀ᵐ x ∂μ, Tendsto (fun k => S k x) atTop (𝓝 (limsup (fun k => S k x) atTop)) := by
  set G : ℝ → ℝ := fun x => limsup (fun k => S k x) atTop with hGdef
  have hG : Antitone G := fun x y hxy =>
    limsup_mono60 _ _ (fun k => hb k y) (fun k => hb k x) (fun k => hS k hxy)
  have hcount := hG.countable_not_continuousAt
  have hsub : {x | ¬ Tendsto (fun k => S k x) atTop (𝓝 (G x))} ⊆
      {x | ¬ ContinuousAt G x ∧ μ {x} = 0} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    by_cases hμ : μ {x} = 0
    · refine ⟨fun hc => hx ?_, hμ⟩
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨δ, hδ, hδG⟩ := Metric.continuousAt_iff.1 hc (ε / 2) (by linarith)
      obtain ⟨q1, hq1a, hq1b⟩ := exists_rat_btwn (show x - δ < x by linarith)
      obtain ⟨q2, hq2a, hq2b⟩ := exists_rat_btwn (show x < x + δ by linarith)
      have e1 : dist (q1 : ℝ) x < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
      have e2 : dist (q2 : ℝ) x < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
      have g1 := hδG e1
      have g2 := hδG e2
      rw [Real.dist_eq, abs_lt] at g1 g2
      obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.1 (hq q1) (ε / 2) (by linarith)
      obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.1 (hq q2) (ε / 2) (by linarith)
      refine ⟨max N1 N2, fun k hk => ?_⟩
      have h1 := hN1 k (le_of_max_le_left hk)
      have h2 := hN2 k (le_of_max_le_right hk)
      rw [Real.dist_eq, abs_lt] at h1 h2
      have m1 : S k x ≤ S k q1 := hS k hq1b.le
      have m2 : S k q2 ≤ S k x := hS k hq2a.le
      rw [Real.dist_eq, abs_lt]
      change -ε < S k x - G x ∧ S k x - G x < ε
      have : G (q1 : ℝ) = limsup (fun k => S k q1) atTop := rfl
      have : G (q2 : ℝ) = limsup (fun k => S k q2) atTop := rfl
      constructor <;> linarith
    · exact absurd (hat x hμ) hx
  refine measure_mono_null hsub (null_of_countable60 μ _ (hcount.mono fun x hx => hx.1)
    fun x hx => hx.2)

/-! ## Kernel from a regularised limit cdf -/

/-- Right-continuous regularisation over the rationals. -/
noncomputable def Fr60 (G : ℝ → ℚ → ℝ) (x : ℝ) (q : ℚ) : ℝ := ⨅ s : Ioi q, G x s

/-- Real-indexed version. -/
noncomputable def Gt60 (G : ℝ → ℚ → ℝ) (x : ℝ) (t : ℝ) : ℝ := ⨅ s : {s : ℚ // t < (s : ℝ)}, G x s

section Constr
variable (G : ℝ → ℚ → ℝ) (hG01 : ∀ x q, G x q ∈ Icc (0 : ℝ) 1)
include hG01

theorem Fr_le60 (x : ℝ) (q s : ℚ) (hs : q < s) : Fr60 G x q ≤ G x s :=
  ciInf_le ⟨0, by rintro _ ⟨r, rfl⟩; exact (hG01 x r).1⟩ (⟨s, hs⟩ : Ioi q)

theorem le_Fr60 (x : ℝ) (q : ℚ) (a : ℝ) (h : ∀ s : ℚ, q < s → a ≤ G x s) : a ≤ Fr60 G x q := by
  haveI : Nonempty (Ioi q) := (Set.nonempty_Ioi).to_subtype
  exact le_ciInf fun s => h s s.2

theorem Fr_nonneg60 (x : ℝ) (q : ℚ) : 0 ≤ Fr60 G x q :=
  le_Fr60 G hG01 x q 0 fun s _ => (hG01 x s).1

theorem Gt_le60 (x t : ℝ) (s : ℚ) (hs : t < s) : Gt60 G x t ≤ G x s :=
  ciInf_le ⟨0, by rintro _ ⟨r, rfl⟩; exact (hG01 x r).1⟩ (⟨s, hs⟩ : {s : ℚ // t < (s : ℝ)})

theorem le_Gt60 (x t : ℝ) (a : ℝ) (h : ∀ s : ℚ, t < s → a ≤ G x s) : a ≤ Gt60 G x t := by
  haveI : Nonempty {s : ℚ // t < (s : ℝ)} := by
    obtain ⟨q, hq, -⟩ := exists_rat_btwn (show t < t + 1 by linarith)
    exact ⟨⟨q, hq⟩⟩
  exact le_ciInf fun s => h s s.2

variable (hGq : ∀ x, Monotone (G x))
include hGq

theorem G_le_Fr60 (x : ℝ) (q : ℚ) : G x q ≤ Fr60 G x q :=
  le_Fr60 G hG01 x q _ fun s hs => hGq x hs.le

/-- The real-indexed infimum of the regularisation is the real-indexed infimum of `G`. -/
theorem iInf_Fr60 (x t : ℝ) :
    ⨅ r : {r' : ℚ // t < r'}, Fr60 G x r = Gt60 G x t := by
  haveI : Nonempty {s : ℚ // t < (s : ℝ)} := by
    obtain ⟨q, hq, -⟩ := exists_rat_btwn (show t < t + 1 by linarith)
    exact ⟨⟨q, hq⟩⟩
  apply le_antisymm
  · refine le_Gt60 G hG01 x t _ fun s hs => ?_
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hs
    exact (ciInf_le ⟨0, by rintro _ ⟨r, rfl⟩; exact Fr_nonneg60 G hG01 x r⟩
      (⟨r, hr1⟩ : {r' : ℚ // t < r'})).trans (Fr_le60 G hG01 x r s (by exact_mod_cast hr2))
  · exact le_ciInf fun r => le_Fr60 G hG01 x r _ fun s hs =>
      Gt_le60 G hG01 x t s (lt_trans r.2 (by exact_mod_cast hs))

variable (hGm : ∀ q : ℚ, Measurable fun x => G x q)
  (hGt : ∀ x, Tendsto (G x) atTop (𝓝 1) ∧ Tendsto (G x) atBot (𝓝 0))
include hGm hGt

theorem isMeasurableRatCDF_Fr60 : IsMeasurableRatCDF (Fr60 G) where
  isRatStieltjesPoint x :=
    { mono := fun q q' h => le_Fr60 G hG01 x q' _ fun s hs =>
        Fr_le60 G hG01 x q s (lt_of_le_of_lt h hs)
      tendsto_atTop_one := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le (hGt x).1 tendsto_const_nhds
          (fun q => G_le_Fr60 G hG01 hGq x q) (fun q => ?_)
        exact (Fr_le60 G hG01 x q (q + 1) (by linarith)).trans (hG01 x _).2
      tendsto_atBot_zero := by
        have h1 : Tendsto (fun q : ℚ => G x (q + 1)) atBot (𝓝 0) :=
          (hGt x).2.comp (tendsto_atBot_add_const_right _ 1 tendsto_id)
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
          (fun q => Fr_nonneg60 G hG01 x q) (fun q => Fr_le60 G hG01 x q (q + 1) (by linarith))
      iInf_rat_gt_eq := fun t => by
        haveI : Nonempty (Ioi t) := (Set.nonempty_Ioi).to_subtype
        apply le_antisymm
        · refine le_Fr60 G hG01 x t _ fun s hs => ?_
          obtain ⟨r, hr1, hr2⟩ := exists_between hs
          exact (ciInf_le ⟨0, by rintro _ ⟨r, rfl⟩; exact Fr_nonneg60 G hG01 x r⟩
            (⟨r, hr1⟩ : Ioi t)).trans (Fr_le60 G hG01 x r s hr2)
        · exact le_ciInf fun r => le_Fr60 G hG01 x r _ fun s hs =>
            Fr_le60 G hG01 x t s (lt_trans r.2 hs) }
  measurable := measurable_pi_iff.2 fun q => Measurable.iInf fun s => hGm s

/-- The limit kernel. -/
noncomputable def kern60 : Kernel ℝ ℝ :=
  ⟨fun x => ((isMeasurableRatCDF_Fr60 G hG01 hGq hGm hGt).stieltjesFunction x).measure,
    (isMeasurableRatCDF_Fr60 G hG01 hGq hGm hGt).measurable_measure_stieltjesFunction⟩

theorem kern_markov60 : IsMarkovKernel (kern60 G hG01 hGq hGm hGt) :=
  ⟨fun x => (isMeasurableRatCDF_Fr60 G hG01 hGq hGm hGt).instIsProbabilityMeasure_stieltjesFunction x⟩

theorem kern_Iic60 (x t : ℝ) :
    kern60 G hG01 hGq hGm hGt x (Iic t) = ENNReal.ofReal (Gt60 G x t) := by
  have hF := isMeasurableRatCDF_Fr60 G hG01 hGq hGm hGt
  show (hF.stieltjesFunction x).measure (Iic t) = _
  rw [hF.measure_stieltjesFunction_Iic]
  congr 1
  show IsMeasurableRatCDF.stieltjesFunctionAux (Fr60 G) x t = _
  rw [IsMeasurableRatCDF.stieltjesFunctionAux_def']
  exact iInf_Fr60 G hG01 hGq x t

theorem kern_mono60 (hGx : ∀ q, Antitone fun x => G x q) (x₁ x₂ : ℝ) (h : x₁ ≤ x₂) (t : ℝ) :
    kern60 G hG01 hGq hGm hGt x₁ {y : ℝ | t < y} ≤ kern60 G hG01 hGq hGm hGt x₂ {y : ℝ | t < y} := by
  haveI := kern_markov60 G hG01 hGq hGm hGt
  have e : {y : ℝ | t < y} = (Iic t)ᶜ := by ext y; simp
  rw [e, prob_compl_eq_one_sub measurableSet_Iic, prob_compl_eq_one_sub measurableSet_Iic,
    kern_Iic60, kern_Iic60]
  exact tsub_le_tsub_left (ENNReal.ofReal_le_ofReal (le_Gt60 G hG01 x₁ t _ fun s hs =>
    (Gt_le60 G hG01 x₂ t s hs).trans (hGx s h))) _

end Constr

/-! ## Marginal identity -/

theorem countable_atoms60 (ν : Measure ℝ) [IsFiniteMeasure ν] :
    {x : ℝ | 0 < ν {x}}.Countable :=
  Measure.countable_meas_pos_of_disjoint_iUnion (fun x => measurableSet_singleton x)
    (fun x y hxy => Set.disjoint_singleton.2 hxy)

theorem exists_nonatom60 (ν : Measure ℝ) [IsFiniteMeasure ν] (a b : ℝ) (h : a < b) :
    ∃ e ∈ Ioo a b, ν {e} = 0 := by
  have hd := (countable_atoms60 ν).dense_compl ℝ
  obtain ⟨e, he1, he2⟩ := hd.exists_mem_open isOpen_Ioo (nonempty_Ioo.2 h)
  refine ⟨e, he2, ?_⟩
  simpa [not_lt] using he1

theorem snd_real_Iic60 (μ : Measure ℝ) [IsProbabilityMeasure μ] (κ : Kernel ℝ ℝ)
    [IsMarkovKernel κ] (t : ℝ) :
    ((μ ⊗ₘ κ).snd).real (Iic t) = ∫ x, (κ x).real (Iic t) ∂μ := by
  rw [measureReal_def, Measure.snd_apply measurableSet_Iic, ← Set.univ_prod,
    Measure.compProd_apply_prod MeasurableSet.univ measurableSet_Iic, Measure.restrict_univ]
  simp only [measureReal_def]
  rw [integral_toReal ((κ.measurable_coe measurableSet_Iic).aemeasurable)
    (Eventually.of_forall fun x => measure_lt_top _ _)]

theorem Gt_tendsto60 (G : ℝ → ℚ → ℝ) (hG01 : ∀ x q, G x q ∈ Icc (0 : ℝ) 1)
    (hGq : ∀ x, Monotone (G x)) (x t : ℝ) (s : ℕ → ℚ) (hs1 : ∀ n, t < s n)
    (hs2 : Tendsto (fun n => (s n : ℝ)) atTop (𝓝 t)) :
    Tendsto (fun n => G x (s n)) atTop (𝓝 (Gt60 G x t)) := by
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n =>
    lt_of_lt_of_le ha (Gt_le60 G hG01 x t (s n) (hs1 n)), fun a ha => ?_⟩
  haveI : Nonempty {s : ℚ // t < (s : ℝ)} := ⟨⟨s 0, hs1 0⟩⟩
  obtain ⟨r, hr⟩ := exists_lt_of_ciInf_lt ha
  filter_upwards [hs2.eventually (gt_mem_nhds r.2)] with n hn
  exact lt_of_le_of_lt (hGq x (by exact_mod_cast hn.le)) hr

theorem marg60 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (L : ℕ → Kernel ℝ ℝ) [hL : ∀ k, IsMarkovKernel (L k)] (G : ℝ → ℚ → ℝ)
    (hG01 : ∀ x q, G x q ∈ Icc (0 : ℝ) 1) (hGq : ∀ x, Monotone (G x))
    (hGm : ∀ q : ℚ, Measurable fun x => G x q)
    (hconv : ∀ᵐ x ∂μ, ∀ q : ℚ, Tendsto (fun k => (L k x).real (Iic (q : ℝ))) atTop (𝓝 (G x q)))
    (hcdf : ∀ t, ν {t} = 0 →
      Tendsto (fun k => ((μ ⊗ₘ L k).snd).real (Iic t)) atTop (𝓝 (ν.real (Iic t))))
    (t : ℝ) : ∫ x, Gt60 G x t ∂μ = ν.real (Iic t) := by
  have hInt : ∀ s : ℚ, Tendsto (fun k => ∫ x, (L k x).real (Iic (s : ℝ)) ∂μ) atTop
      (𝓝 (∫ x, G x s ∂μ)) := by
    intro s
    refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun k => ?_)
      (integrable_const 1) (fun k => Eventually.of_forall fun x => ?_) (hconv.mono fun x hx => hx s)
    · exact ((L k).measurable_coe measurableSet_Iic).ennreal_toReal.aestronglyMeasurable
    · rw [Real.norm_of_nonneg measureReal_nonneg]; exact measureReal_le_one
  have up : ∀ s : ℚ, ∀ e : ℝ, (s : ℝ) < e → ν {e} = 0 → ∫ x, G x s ∂μ ≤ ν.real (Iic e) := by
    intro s e hse he
    refine le_of_tendsto_of_tendsto' (hInt s) (hcdf e he) fun k => ?_
    rw [← snd_real_Iic60]
    exact measureReal_mono (Iic_subset_Iic.2 hse.le)
  have lo : ∀ s : ℚ, ∀ e : ℝ, e < s → ν {e} = 0 → ν.real (Iic e) ≤ ∫ x, G x s ∂μ := by
    intro s e hse he
    refine le_of_tendsto_of_tendsto' (hcdf e he) (hInt s) fun k => ?_
    rw [← snd_real_Iic60]
    exact measureReal_mono (Iic_subset_Iic.2 hse.le)
  have hsx : ∀ n : ℕ, ∃ s : ℚ, t < s ∧ (s : ℝ) < t + 1 / ((n : ℝ) + 1) := fun n =>
    exists_rat_btwn (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                        linarith)
  choose s hs1 hs2 using hsx
  have hex : ∀ n, ∃ e : ℝ, e ∈ Ioo (s n : ℝ) (t + 1 / ((n : ℝ) + 1)) ∧ ν {e} = 0 :=
    fun n => exists_nonatom60 ν _ _ (hs2 n)
  choose e he1 he2 using hex
  have hex' : ∀ n, ∃ e : ℝ, e ∈ Ioo t (s n : ℝ) ∧ ν {e} = 0 :=
    fun n => exists_nonatom60 ν _ _ (hs1 n)
  choose e' he1' he2' using hex'
  have h0 : Tendsto (fun n : ℕ => t + 1 / ((n : ℝ) + 1)) atTop (𝓝 t) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add t
  have hsT : Tendsto (fun n => (s n : ℝ)) atTop (𝓝 t) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun n => (hs1 n).le)
      (fun n => (hs2 n).le)
  have heT : Tendsto e atTop (𝓝[≥] t) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
      (show t ≤ e n from ((hs1 n).trans (he1 n).1).le)⟩
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
      (fun n => ((hs1 n).trans (he1 n).1).le) (fun n => (he1 n).2.le)
  have hcdfT : Tendsto (fun n => ν.real (Iic (e n))) atTop (𝓝 (ν.real (Iic t))) := by
    have := ((cdf ν).right_continuous t).tendsto.comp heT
    simpa [Function.comp_def, cdf_eq_real] using this
  have hDCT : Tendsto (fun n => ∫ x, G x (s n) ∂μ) atTop (𝓝 (∫ x, Gt60 G x t ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun n => ?_)
      (integrable_const 1) (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => Gt_tendsto60 G hG01 hGq x t s hs1 hsT)
    · exact (hGm (s n)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (hG01 x _).1]; exact (hG01 x _).2
  have hsq : Tendsto (fun n => ∫ x, G x (s n) ∂μ) atTop (𝓝 (ν.real (Iic t))) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcdfT
      (fun n => (measureReal_mono (Iic_subset_Iic.2 (he1' n).1.le)).trans
        (lo (s n) (e' n) (he1' n).2 (he2' n)))
      (fun n => up (s n) (e n) (he1 n).1 (he2 n))
  exact tendsto_nhds_unique hDCT hsq

/-! ## Means pass to the limit -/

theorem real_Ioi60 (η : Measure ℝ) [IsProbabilityMeasure η] (t : ℝ) :
    η.real (Ioi t) = 1 - η.real (Iic t) := by
  rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ]

theorem layer60 (η : Measure ℝ) [IsProbabilityMeasure η] (h : Integrable id η) :
    ∫ y, y ∂η = (∫ t in Ioi 0, η.real (Ioi t)) - ∫ t in Ioi 0, η.real (Iic (-t)) := by
  have hp : Integrable (fun y : ℝ => max y 0) η := h.pos_part
  have hn : Integrable (fun y : ℝ => max (-y) 0) η := h.neg.pos_part
  have e : (fun y : ℝ => y) = fun y => max y 0 - max (-y) 0 := by
    funext y; rcases le_total y 0 with hy | hy
    · rw [max_eq_right hy, max_eq_left (by linarith)]; ring
    · rw [max_eq_left hy, max_eq_right (by linarith)]; ring
  rw [e, integral_sub hp hn,
    Integrable.integral_eq_integral_meas_lt hp (Eventually.of_forall fun y => le_max_right _ _),
    Integrable.integral_eq_integral_meas_le hn (Eventually.of_forall fun y => le_max_right _ _)]
  congr 1
  · refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    congr 1; ext y; simp only [Set.mem_ofPred_eq, mem_Ioi, lt_max_iff]
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd (h.trans ht) (lt_irrefl _)
    · exact Or.inl
  · refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    congr 1; ext y; simp only [Set.mem_ofPred_eq, mem_Iic, le_max_iff]
    constructor
    · rintro (h | h)
      · linarith
      · exact absurd h (not_le.2 ht)
    · intro h; left; linarith

theorem mean_lim60 (η : ℕ → Measure ℝ) [hη : ∀ k, IsProbabilityMeasure (η k)] (η0 : Measure ℝ)
    [IsProbabilityMeasure η0]
    (hconv : ∀ t, η0 {t} = 0 → Tendsto (fun k => (η k).real (Iic t)) atTop (𝓝 (η0.real (Iic t))))
    (hint : ∀ k, Integrable id (η k)) (g : ℝ → ℝ) (hg : IntegrableOn g (Ioi 0))
    (hdom : ∀ k t, 0 < t → (η k).real (Ioi t) ≤ g t ∧ (η k).real (Iic (-t)) ≤ g t) :
    Integrable id η0 ∧ Tendsto (fun k => ∫ y, y ∂(η k)) atTop (𝓝 (∫ y, y ∂η0)) := by
  have hN : (volume : Measure ℝ) {t | η0 {t} ≠ 0} = 0 :=
    ((countable_atoms60 η0).mono fun t (ht : η0 {t} ≠ 0) => pos_iff_ne_zero.2 ht).measure_zero _
  have hN' : (volume : Measure ℝ) {t | η0 {-t} ≠ 0} = 0 := by
    have : {t : ℝ | η0 {-t} ≠ 0} = Neg.neg ⁻¹' {t | η0 {t} ≠ 0} := rfl
    rw [this, Measure.measure_preimage_neg]; exact hN
  have aeA : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), η0 {t} = 0 :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hN |>.mono fun t ht => by
      simpa using ht)
  have aeB : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), η0 {-t} = 0 :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hN' |>.mono fun t ht => by
      simpa using ht)
  have limA : ∀ t, η0 {t} = 0 →
      Tendsto (fun k => (η k).real (Ioi t)) atTop (𝓝 (η0.real (Ioi t))) := by
    intro t ht
    simp only [real_Ioi60]
    exact (hconv t ht).const_sub 1
  have limB : ∀ t, η0 {-t} = 0 →
      Tendsto (fun k => (η k).real (Iic (-t))) atTop (𝓝 (η0.real (Iic (-t)))) :=
    fun t ht => hconv (-t) ht
  have bA : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), η0.real (Ioi t) ≤ g t := by
    filter_upwards [aeA, ae_restrict_mem measurableSet_Ioi] with t ht htp
    exact le_of_tendsto' (limA t ht) fun k => (hdom k t htp).1
  have bB : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), η0.real (Iic (-t)) ≤ g t := by
    filter_upwards [aeB, ae_restrict_mem measurableSet_Ioi] with t ht htp
    exact le_of_tendsto' (limB t ht) fun k => (hdom k t htp).2
  have hint0 : Integrable id η0 := by
    refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
    show ∫⁻ y, ‖id y‖ₑ ∂η0 < ⊤
    simp only [id, Real.enorm_eq_ofReal_abs]
    rw [lintegral_eq_lintegral_meas_lt η0 (Eventually.of_forall fun y => abs_nonneg y)
      measurable_id.abs.aemeasurable]
    have hgl : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (g t) < ⊤ := hg.lintegral_lt_top
    calc ∫⁻ t in Ioi (0 : ℝ), η0 {a | t < |a|}
        ≤ ∫⁻ t in Ioi (0 : ℝ), 2 * ENNReal.ofReal (g t) := by
          refine lintegral_mono_ae ?_
          filter_upwards [bA, bB, ae_restrict_mem measurableSet_Ioi] with t h1 h2 ht
          have hsub : {a : ℝ | t < |a|} ⊆ Ioi t ∪ Iic (-t) := by
            intro a ha
            simp only [Set.mem_ofPred_eq, lt_abs] at ha
            rcases ha with ha | ha
            · exact Or.inl ha
            · exact Or.inr (by simp only [mem_Iic]; linarith)
          calc η0 {a | t < |a|} ≤ η0 (Ioi t) + η0 (Iic (-t)) :=
                (measure_mono hsub).trans (measure_union_le _ _)
            _ = ENNReal.ofReal (η0.real (Ioi t)) + ENNReal.ofReal (η0.real (Iic (-t))) := by
                rw [ofReal_measureReal, ofReal_measureReal]
            _ ≤ ENNReal.ofReal (g t) + ENNReal.ofReal (g t) :=
                add_le_add (ENNReal.ofReal_le_ofReal h1) (ENNReal.ofReal_le_ofReal h2)
            _ = 2 * ENNReal.ofReal (g t) := by rw [two_mul]
      _ = 2 * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (g t) := lintegral_const_mul' _ _ (by simp)
      _ < ⊤ := ENNReal.mul_lt_top (by simp) hgl
  refine ⟨hint0, ?_⟩
  simp only [fun k => layer60 (η k) (hint k), layer60 η0 hint0]
  have mA : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ],
      AEStronglyMeasurable (fun t => ρ.real (Ioi t)) (volume.restrict (Ioi (0 : ℝ))) :=
    fun ρ _ => (Antitone.measurable fun a b hab =>
      measureReal_mono (Ioi_subset_Ioi hab)).aestronglyMeasurable
  have mB : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ],
      AEStronglyMeasurable (fun t => ρ.real (Iic (-t))) (volume.restrict (Ioi (0 : ℝ))) :=
    fun ρ _ => (Antitone.measurable fun a b hab =>
      measureReal_mono (Iic_subset_Iic.2 (neg_le_neg hab))).aestronglyMeasurable
  refine Tendsto.sub ?_ ?_
  · refine tendsto_integral_of_dominated_convergence g (fun k => mA (η k)) hg
      (fun k => ?_) (by filter_upwards [aeA] with t ht using limA t ht)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_of_nonneg measureReal_nonneg]; exact (hdom k t ht).1
  · refine tendsto_integral_of_dominated_convergence g (fun k => mB (η k)) hg
      (fun k => ?_) (by filter_upwards [aeB] with t ht using limB t ht)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_of_nonneg measureReal_nonneg]; exact (hdom k t ht).2

/-! ## Convergence at non-atoms and the assembled limit theorem -/

theorem conv_real60 (G : ℝ → ℚ → ℝ) (hG01 : ∀ x q, G x q ∈ Icc (0 : ℝ) 1) (x : ℝ)
    (C : ℕ → ℝ → ℝ) (hC : ∀ k, Monotone (C k))
    (hconv : ∀ q : ℚ, Tendsto (fun k => C k q) atTop (𝓝 (G x q))) (t : ℝ)
    (hleft : ∀ ε > 0, ∃ t' < t, Gt60 G x t - ε < Gt60 G x t') :
    Tendsto (fun k => C k t) atTop (𝓝 (Gt60 G x t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  haveI : Nonempty {s : ℚ // t < (s : ℝ)} := by
    obtain ⟨q, hq, -⟩ := exists_rat_btwn (show t < t + 1 by linarith)
    exact ⟨⟨q, hq⟩⟩
  obtain ⟨r, hr⟩ := exists_lt_of_ciInf_lt (show Gt60 G x t < Gt60 G x t + ε / 2 by linarith)
  obtain ⟨t', ht', hlt⟩ := hleft (ε / 2) (by linarith)
  obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn ht'
  have hGs : Gt60 G x t' ≤ G x s := Gt_le60 G hG01 x t' s hs1
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.1 (hconv r) (ε / 2) (by linarith)
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.1 (hconv s) (ε / 2) (by linarith)
  refine ⟨max N1 N2, fun k hk => ?_⟩
  have h1 := hN1 k (le_of_max_le_left hk)
  have h2 := hN2 k (le_of_max_le_right hk)
  rw [Real.dist_eq, abs_lt] at h1 h2 ⊢
  have m1 : C k t ≤ C k r := hC k r.2.le
  have m2 : C k s ≤ C k t := hC k hs2.le
  have : Gt60 G x t ≤ G x r := Gt_le60 G hG01 x t r r.2
  constructor <;> linarith

theorem Gt_nonneg60 (G : ℝ → ℚ → ℝ) (hG01 : ∀ x q, G x q ∈ Icc (0 : ℝ) 1) (x t : ℝ) :
    0 ≤ Gt60 G x t :=
  le_Gt60 G hG01 x t 0 fun s _ => (hG01 x s).1

section Left
variable (G : ℝ → ℚ → ℝ) (hG01 : ∀ x q, G x q ∈ Icc (0 : ℝ) 1) (hGq : ∀ x, Monotone (G x))
  (hGm : ∀ q : ℚ, Measurable fun x => G x q)
  (hGt : ∀ x, Tendsto (G x) atTop (𝓝 1) ∧ Tendsto (G x) atBot (𝓝 0))

theorem kern_real60 (x t : ℝ) :
    (kern60 G hG01 hGq hGm hGt x).real (Iic t) = Gt60 G x t := by
  rw [measureReal_def, kern_Iic60, ENNReal.toReal_ofReal (Gt_nonneg60 G hG01 x t)]

theorem kern_left60 (x t : ℝ) (h0 : kern60 G hG01 hGq hGm hGt x {t} = 0) :
    ∀ ε > 0, ∃ t' < t, Gt60 G x t - ε < Gt60 G x t' := by
  intro ε hε
  have hF := isMeasurableRatCDF_Fr60 G hG01 hGq hGm hGt
  set f := hF.stieltjesFunction x with hfdef
  have hfu : ∀ u, f u = Gt60 G x u := by
    intro u
    show IsMeasurableRatCDF.stieltjesFunctionAux (Fr60 G) x u = _
    rw [IsMeasurableRatCDF.stieltjesFunctionAux_def']
    exact iInf_Fr60 G hG01 hGq x u
  have hs : f.measure {t} = ENNReal.ofReal (f t - Function.leftLim f t) := f.measure_singleton t
  have h0' : f.measure {t} = 0 := h0
  rw [h0', eq_comm, ENNReal.ofReal_eq_zero] at hs
  have hT := f.mono.tendsto_leftLim t
  obtain ⟨u, hu1, hu2⟩ := ((hT.eventually (lt_mem_nhds (sub_lt_self _ hε))).and
    self_mem_nhdsWithin).exists
  refine ⟨u, hu2, ?_⟩
  rw [← hfu, ← hfu]
  linarith

end Left

theorem c4_core60 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (L : ℕ → Kernel ℝ ℝ) [hL : ∀ k, IsMarkovKernel (L k)]
    (hmono : ∀ k x₁ x₂, x₁ ≤ x₂ → ∀ t, (L k x₂).real (Iic t) ≤ (L k x₁).real (Iic t))
    (htight : ∀ x, ∀ ε > 0, ∃ R : ℝ, ∀ k, (L k x).real (Iic (-R)) ≤ ε ∧ 1 - ε ≤ (L k x).real (Iic R))
    (hcdf : ∀ t, ν {t} = 0 →
      Tendsto (fun k => ((μ ⊗ₘ L k).snd).real (Iic t)) atTop (𝓝 (ν.real (Iic t))))
    (hmean : ∀ᵐ x ∂μ, (∀ k, Integrable id (L k x)) ∧
      Tendsto (fun k => ∫ y, y ∂(L k x)) atTop (𝓝 x) ∧
      ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧
        ∀ k t, 0 < t → (L k x).real (Ioi t) ≤ g t ∧ (L k x).real (Iic (-t)) ≤ g t) :
    ∃ κ : Kernel ℝ ℝ, IsMonoMartCoupling60 μ ν κ := by
  classical
  have hA := countable_atoms60 μ
  set D : Set ℝ := {x : ℝ | 0 < μ {x}} ∪ range (fun q : ℚ => (q : ℝ)) with hDdef
  have hD : D.Countable := hA.union (countable_range _)
  have hDne : D.Nonempty := ⟨0, Or.inr ⟨0, by simp⟩⟩
  obtain ⟨dseq, hdseq⟩ := hD.exists_eq_range hDne
  obtain ⟨φ, hφ, hlim⟩ := helly60 (fun k i => (L k (dseq i.1)).real (Iic (i.2 : ℝ)))
    (fun k i => ⟨measureReal_nonneg, measureReal_le_one⟩)
  set C : ℕ → ℝ → ℚ → ℝ := fun k x q => (L (φ k) x).real (Iic (q : ℝ)) with hCdef
  set G : ℝ → ℚ → ℝ := fun x q => limsup (fun k => C k x q) atTop with hGdef
  have hC01 : ∀ k x q, C k x q ∈ Icc (0 : ℝ) 1 := fun k x q =>
    ⟨measureReal_nonneg, measureReal_le_one⟩
  have hG01 : ∀ x q, G x q ∈ Icc (0 : ℝ) 1 := fun x q => limsup_mem60 _ (fun k => hC01 k x q)
  have hGq : ∀ x, Monotone (G x) := fun x q q' h =>
    limsup_mono60 _ _ (fun k => hC01 k x q) (fun k => hC01 k x q') fun k =>
      measureReal_mono (Iic_subset_Iic.2 (by exact_mod_cast h))
  have hGx : ∀ q, Antitone fun x => G x q := fun q x y h =>
    limsup_mono60 _ _ (fun k => hC01 k y q) (fun k => hC01 k x q) fun k => hmono (φ k) x y h q
  have hGm : ∀ q : ℚ, Measurable fun x => G x q := fun q =>
    Measurable.limsup fun k => ((L (φ k)).measurable_coe measurableSet_Iic).ennreal_toReal
  have hGt : ∀ x, Tendsto (G x) atTop (𝓝 1) ∧ Tendsto (G x) atBot (𝓝 0) := by
    intro x
    constructor
    · refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha =>
        Eventually.of_forall fun q => lt_of_le_of_lt (hG01 x q).2 ha⟩
      obtain ⟨R, hR⟩ := htight x ((1 - a) / 2) (by linarith)
      obtain ⟨N, hN⟩ := exists_rat_gt R
      refine Filter.eventually_atTop.2 ⟨N, fun q hq => ?_⟩
      have hle : 1 - (1 - a) / 2 ≤ G x q :=
        le_limsup_of_frequently_le (Frequently.of_forall fun k => (hR (φ k)).2.trans
          (measureReal_mono (Iic_subset_Iic.2 (hN.le.trans (by exact_mod_cast hq)))))
          (bdd_le60 _ fun k => hC01 k x q)
      linarith
    · refine tendsto_order.2 ⟨fun a ha =>
        Eventually.of_forall fun q => lt_of_lt_of_le ha (hG01 x q).1, fun a ha => ?_⟩
      obtain ⟨R, hR⟩ := htight x (a / 2) (by linarith)
      obtain ⟨N, hN⟩ := exists_rat_lt (-R)
      refine Filter.eventually_atBot.2 ⟨N, fun q hq => ?_⟩
      have hle : G x q ≤ a / 2 :=
        limsup_le_of_le (cobdd_le60 _ fun k => hC01 k x q) (Eventually.of_forall fun k =>
          (measureReal_mono (Iic_subset_Iic.2 ((show ((q : ℚ) : ℝ) ≤ N by exact_mod_cast hq).trans
            hN.le))).trans (hR (φ k)).1)
      linarith
  have hD_conv : ∀ d ∈ D, ∀ q : ℚ, Tendsto (fun k => C k d q) atTop (𝓝 (G d q)) := by
    intro d hd q
    rw [hdseq] at hd
    obtain ⟨n, rfl⟩ := hd
    obtain ⟨a, ha⟩ := hlim (n, q)
    have e := ha.limsup_eq
    show Tendsto _ _ (𝓝 (limsup _ _))
    rw [e]; exact ha
  have hae : ∀ᵐ x ∂μ, ∀ q : ℚ, Tendsto (fun k => C k x q) atTop (𝓝 (G x q)) := by
    rw [ae_all_iff]
    intro q
    exact ae_tendsto_of_antitone60 μ (fun k x => C k x q)
      (fun k => fun x y h => hmono (φ k) x y h q) (fun k x => hC01 k x q)
      (fun q' => hD_conv q' (Or.inr ⟨q', rfl⟩) q)
      (fun x hx => hD_conv x (Or.inl (pos_iff_ne_zero.2 hx)) q)
  haveI hκ := kern_markov60 G hG01 hGq hGm hGt
  refine ⟨kern60 G hG01 hGq hGm hGt, hκ, ?_, ?_,
    fun x₁ x₂ h t => kern_mono60 G hG01 hGq hGm hGt hGx x₁ x₂ h t⟩
  · filter_upwards [hae, hmean] with x hx hm
    obtain ⟨hint, hlimx, g, hg, hdom⟩ := hm
    have hconvx : ∀ t, kern60 G hG01 hGq hGm hGt x {t} = 0 →
        Tendsto (fun k => (L (φ k) x).real (Iic t)) atTop
          (𝓝 ((kern60 G hG01 hGq hGm hGt x).real (Iic t))) := by
      intro t ht
      rw [kern_real60]
      exact conv_real60 G hG01 x (fun k u => (L (φ k) x).real (Iic u))
        (fun k a b h => measureReal_mono (Iic_subset_Iic.2 h)) hx t
        (kern_left60 G hG01 hGq hGm hGt x t ht)
    obtain ⟨hI, hT⟩ := mean_lim60 (fun k => L (φ k) x) (kern60 G hG01 hGq hGm hGt x) hconvx
      (fun k => hint (φ k)) g hg (fun k t ht => hdom (φ k) t ht)
    exact ⟨hI, tendsto_nhds_unique hT (hlimx.comp hφ.tendsto_atTop)⟩
  · refine Measure.ext_of_Iic _ _ fun t => ?_
    rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)]
    change ((μ ⊗ₘ kern60 G hG01 hGq hGm hGt).snd).real (Iic t) = ν.real (Iic t)
    rw [snd_real_Iic60]
    simp only [kern_real60]
    exact marg60 μ ν (fun k => L (φ k)) G hG01 hGq hGm hae
      (fun t ht => (hcdf t ht).comp hφ.tendsto_atTop) t

/-! ## Deriving tightness and domination from mean bounds -/

theorem snd_real60 (μ : Measure ℝ) [IsProbabilityMeasure μ] (κ : Kernel ℝ ℝ)
    [IsMarkovKernel κ] (s : Set ℝ) (hs : MeasurableSet s) :
    ((μ ⊗ₘ κ).snd).real s = ∫ x, (κ x).real s ∂μ := by
  rw [measureReal_def, Measure.snd_apply hs, ← Set.univ_prod,
    Measure.compProd_apply_prod MeasurableSet.univ hs, Measure.restrict_univ]
  simp only [measureReal_def]
  rw [integral_toReal ((κ.measurable_coe hs).aemeasurable)
    (Eventually.of_forall fun x => measure_lt_top _ _)]

theorem kint60 (μ : Measure ℝ) [IsProbabilityMeasure μ] (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (s : Set ℝ) (hs : MeasurableSet s) : Integrable (fun x => (κ x).real s) μ :=
  (integrable_const (1 : ℝ)).mono' ((κ.measurable_coe hs).ennreal_toReal.aestronglyMeasurable)
    (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg measureReal_nonneg]; exact measureReal_le_one)

theorem ae_pos_Ici60 (μ : Measure ℝ) [IsFiniteMeasure μ] : ∀ᵐ x ∂μ, μ (Ici x) ≠ 0 := by
  set S := {x : ℝ | μ (Ici x) = 0} with hS
  have up : ∀ x ∈ S, ∀ y : ℝ, x ≤ y → y ∈ S := fun x hx y hxy =>
    measure_mono_null (Ici_subset_Ici.2 hxy) hx
  set B := ⋃ q : ℚ, ⋃ (_ : (q : ℝ) ∈ S), Ici (q : ℝ) with hB
  have hB0 : μ B = 0 := measure_iUnion_null fun q => measure_iUnion_null fun hq => hq
  have hT : (S \ B).Subsingleton := by
    intro x hx y hy
    by_contra hne
    rcases lt_or_gt_of_ne hne with hxy | hxy
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hxy
      exact hy.2 (mem_iUnion₂.2 ⟨q, up x hx.1 q hq1.le, hq2.le⟩)
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hxy
      exact hx.2 (mem_iUnion₂.2 ⟨q, up y hy.1 q hq1.le, hq2.le⟩)
  have hT0 : μ (S \ B) = 0 := by
    rcases hT.eq_empty_or_singleton with h | ⟨x, h⟩
    · rw [h]; exact measure_empty
    · have hx : x ∈ S \ B := by rw [h]; exact mem_singleton x
      rw [h]
      exact measure_mono_null (singleton_subset_iff.2 (mem_Ici.2 le_rfl)) hx.1
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) (measure_union_null hB0 hT0)
  simp only [ne_eq, not_not, Set.mem_ofPred_eq] at hx
  by_cases hxB : x ∈ B
  · exact Or.inl hxB
  · exact Or.inr ⟨hx, hxB⟩

theorem ae_pos_Iic60 (μ : Measure ℝ) [IsFiniteMeasure μ] : ∀ᵐ x ∂μ, μ (Iic x) ≠ 0 := by
  set S := {x : ℝ | μ (Iic x) = 0} with hS
  have dn : ∀ x ∈ S, ∀ y : ℝ, y ≤ x → y ∈ S := fun x hx y hxy =>
    measure_mono_null (Iic_subset_Iic.2 hxy) hx
  set B := ⋃ q : ℚ, ⋃ (_ : (q : ℝ) ∈ S), Iic (q : ℝ) with hB
  have hB0 : μ B = 0 := measure_iUnion_null fun q => measure_iUnion_null fun hq => hq
  have hT : (S \ B).Subsingleton := by
    intro x hx y hy
    by_contra hne
    rcases lt_or_gt_of_ne hne with hxy | hxy
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hxy
      exact hx.2 (mem_iUnion₂.2 ⟨q, dn y hy.1 q hq2.le, hq1.le⟩)
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hxy
      exact hy.2 (mem_iUnion₂.2 ⟨q, dn x hx.1 q hq2.le, hq1.le⟩)
  have hT0 : μ (S \ B) = 0 := by
    rcases hT.eq_empty_or_singleton with h | ⟨x, h⟩
    · rw [h]; exact measure_empty
    · have hx : x ∈ S \ B := by rw [h]; exact mem_singleton x
      rw [h]
      exact measure_mono_null (singleton_subset_iff.2 (mem_Iic.2 le_rfl)) hx.1
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) (measure_union_null hB0 hT0)
  simp only [ne_eq, not_not, Set.mem_ofPred_eq] at hx
  by_cases hxB : x ∈ B
  · exact Or.inl hxB
  · exact Or.inr ⟨hx, hxB⟩

/-- Tail functions of an integrable law are integrable on `(0, ∞)`. -/
theorem tails_int60 (η : Measure ℝ) [IsProbabilityMeasure η] (h : Integrable id η) :
    IntegrableOn (fun t => η.real (Ioi t)) (Ioi 0) ∧
      IntegrableOn (fun t => η.real (Iic (-t))) (Ioi 0) := by
  have hp : Integrable (fun y : ℝ => max y 0) η := h.pos_part
  have hn : Integrable (fun y : ℝ => max (-y) 0) η := h.neg.pos_part
  have k1 := lintegral_eq_lintegral_meas_lt η (Eventually.of_forall fun y => le_max_right y 0)
    hp.aemeasurable
  have k2 := lintegral_eq_lintegral_meas_le η (Eventually.of_forall fun y => le_max_right (-y) 0)
    hn.aemeasurable
  have f1 : ∫⁻ y, ENNReal.ofReal (max y 0) ∂η < ⊤ := hp.lintegral_lt_top
  have f2 : ∫⁻ y, ENNReal.ofReal (max (-y) 0) ∂η < ⊤ := hn.lintegral_lt_top
  constructor
  · refine ⟨(Antitone.measurable fun a b hab =>
      measureReal_mono (Ioi_subset_Ioi hab)).aestronglyMeasurable, ?_⟩
    show ∫⁻ t in Ioi (0 : ℝ), ‖η.real (Ioi t)‖ₑ < ⊤
    have e : ∫⁻ t in Ioi (0 : ℝ), ‖η.real (Ioi t)‖ₑ = ∫⁻ t in Ioi (0 : ℝ), η {a | t < max a 0} := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
      rw [Real.enorm_of_nonneg measureReal_nonneg, ofReal_measureReal]
      congr 1; ext y; simp only [mem_Ioi, Set.mem_ofPred_eq, lt_max_iff]
      constructor
      · exact Or.inl
      · rintro (h | h)
        · exact h
        · exact absurd (h.trans ht) (lt_irrefl _)
    rw [e, ← k1]; exact f1
  · refine ⟨(Antitone.measurable fun a b hab =>
      measureReal_mono (Iic_subset_Iic.2 (neg_le_neg hab))).aestronglyMeasurable, ?_⟩
    show ∫⁻ t in Ioi (0 : ℝ), ‖η.real (Iic (-t))‖ₑ < ⊤
    have e : ∫⁻ t in Ioi (0 : ℝ), ‖η.real (Iic (-t))‖ₑ =
        ∫⁻ t in Ioi (0 : ℝ), η {a | t ≤ max (-a) 0} := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
      rw [Real.enorm_of_nonneg measureReal_nonneg, ofReal_measureReal]
      congr 1; ext y; simp only [mem_Iic, Set.mem_ofPred_eq, le_max_iff]
      constructor
      · intro h; left; linarith
      · rintro (h | h)
        · linarith
        · exact absurd h (not_le.2 ht)
    rw [e, ← k2]; exact f2

theorem c4_full60 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (L : ℕ → Kernel ℝ ℝ) [hL : ∀ k, IsMarkovKernel (L k)]
    (hmono : ∀ k x₁ x₂, x₁ ≤ x₂ → ∀ t, (L k x₂).real (Iic t) ≤ (L k x₁).real (Iic t))
    (hint : ∀ k x, Integrable id (L k x))
    (hM : ∀ x, ∃ M : ℝ, ∀ k, |∫ y, y ∂(L k x)| ≤ M)
    (hlimx : ∀ᵐ x ∂μ, Tendsto (fun k => ∫ y, y ∂(L k x)) atTop (𝓝 x))
    (g0 : ℝ → ℝ) (hg0 : IntegrableOn g0 (Ioi 0)) (hg0t : Tendsto g0 atTop (𝓝 0))
    (hνk : ∀ k t, 0 < t → ((μ ⊗ₘ L k).snd).real (Ioi t) ≤ g0 t ∧
      ((μ ⊗ₘ L k).snd).real (Iic (-t)) ≤ g0 t)
    (hcdf : ∀ t, ν {t} = 0 →
      Tendsto (fun k => ((μ ⊗ₘ L k).snd).real (Iic t)) atTop (𝓝 (ν.real (Iic t)))) :
    ∃ κ : Kernel ℝ ℝ, IsMonoMartCoupling60 μ ν κ := by
  have hmonoS : ∀ k x₁ x₂, x₁ ≤ x₂ → ∀ t, (L k x₁).real (Ioi t) ≤ (L k x₂).real (Ioi t) := by
    intro k x₁ x₂ h t; rw [real_Ioi60, real_Ioi60]; linarith [hmono k x₁ x₂ h t]
  have hup : ∀ k x t, μ.real (Ici x) * (L k x).real (Ioi t) ≤
      ((μ ⊗ₘ L k).snd).real (Ioi t) := by
    intro k x t
    rw [snd_real60 μ (L k) _ measurableSet_Ioi]
    calc μ.real (Ici x) * (L k x).real (Ioi t) = ∫ x' in Ici x, (L k x).real (Ioi t) ∂μ := by
          rw [setIntegral_const, smul_eq_mul]
      _ ≤ ∫ x' in Ici x, (L k x').real (Ioi t) ∂μ :=
          setIntegral_mono_on (integrable_const _).integrableOn
            (kint60 μ (L k) _ measurableSet_Ioi).integrableOn measurableSet_Ici
            (fun x' hx' => hmonoS k x x' hx' t)
      _ ≤ ∫ x', (L k x').real (Ioi t) ∂μ := setIntegral_le_integral
            (kint60 μ (L k) _ measurableSet_Ioi) (Eventually.of_forall fun _ => measureReal_nonneg)
  have hlow : ∀ k x t, μ.real (Iic x) * (L k x).real (Iic t) ≤
      ((μ ⊗ₘ L k).snd).real (Iic t) := by
    intro k x t
    rw [snd_real60 μ (L k) _ measurableSet_Iic]
    calc μ.real (Iic x) * (L k x).real (Iic t) = ∫ x' in Iic x, (L k x).real (Iic t) ∂μ := by
          rw [setIntegral_const, smul_eq_mul]
      _ ≤ ∫ x' in Iic x, (L k x').real (Iic t) ∂μ :=
          setIntegral_mono_on (integrable_const _).integrableOn
            (kint60 μ (L k) _ measurableSet_Iic).integrableOn measurableSet_Iic
            (fun x' hx' => hmono k x' x hx' t)
      _ ≤ ∫ x', (L k x').real (Iic t) ∂μ := setIntegral_le_integral
            (kint60 μ (L k) _ measurableSet_Iic) (Eventually.of_forall fun _ => measureReal_nonneg)
  set I := ∫ t in Ioi (0 : ℝ), g0 t with hI
  have hvolR : ∀ R : ℝ, 0 < R → (volume : Measure ℝ).real (Ioc 0 R) = R := by
    intro R hR
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]; ring
  have htight : ∀ x, ∀ ε > 0, ∃ R : ℝ, ∀ k, (L k x).real (Iic (-R)) ≤ ε ∧
      1 - ε ≤ (L k x).real (Iic R) := by
    intro x ε hε
    obtain ⟨M, hMx⟩ := hM x
    obtain ⟨R1, hR1⟩ := eventually_atTop.1 (hg0t.eventually (ge_mem_nhds (half_pos hε)))
    set R := max (max R1 1) ((2 * I + M) / ε + 1) with hRdef
    have hR1' : R1 ≤ R := (le_max_left _ _).trans (le_max_left _ _)
    have hR0 : 0 < R := lt_of_lt_of_le one_pos ((le_max_right _ _).trans (le_max_left _ _))
    have hRε : 2 * I + M < R * ε := by
      have h1 : (2 * I + M) / ε + 1 ≤ R := le_max_right _ _
      calc 2 * I + M = ((2 * I + M) / ε) * ε := by field_simp
        _ < ((2 * I + M) / ε + 1) * ε := by nlinarith
        _ ≤ R * ε := mul_le_mul_of_nonneg_right h1 hε.le
    have hg0R : g0 R ≤ ε / 2 := hR1 R hR1'
    have hsum : 1 ≤ μ.real (Ici x) + μ.real (Iic x) := by
      have e : (univ : Set ℝ) = Ici x ∪ Iic x := by
        ext y; simp only [mem_univ, mem_union, mem_Ici, mem_Iic, true_iff]; exact le_total x y
      calc (1 : ℝ) = μ.real univ := probReal_univ.symm
        _ ≤ μ.real (Ici x) + μ.real (Iic x) := by rw [e]; exact measureReal_union_le _ _
    refine ⟨R, fun k => ?_⟩
    obtain ⟨hA, hB⟩ := tails_int60 (L k x) (hint k x)
    have hlay := layer60 (L k x) (hint k x)
    have hmb := hMx k
    rw [hlay] at hmb
    have hmb' := abs_le.1 hmb
    set A := ∫ t in Ioi (0 : ℝ), (L k x).real (Ioi t) with hAdef
    set B := ∫ t in Ioi (0 : ℝ), (L k x).real (Iic (-t)) with hBdef
    have mA : R * (L k x).real (Ioi R) ≤ A := by
      calc R * (L k x).real (Ioi R) = ∫ t in Ioc 0 R, (L k x).real (Ioi R) := by
            rw [setIntegral_const, smul_eq_mul, hvolR R hR0]
        _ ≤ ∫ t in Ioc 0 R, (L k x).real (Ioi t) :=
            setIntegral_mono_on (integrableOn_const (by simp)) (hA.mono_set Ioc_subset_Ioi_self)
              measurableSet_Ioc (fun t ht => measureReal_mono (Ioi_subset_Ioi ht.2))
        _ ≤ A := setIntegral_mono_set hA (Eventually.of_forall fun _ => measureReal_nonneg)
            Ioc_subset_Ioi_self.eventuallyLE
    have mB : R * (L k x).real (Iic (-R)) ≤ B := by
      calc R * (L k x).real (Iic (-R)) = ∫ t in Ioc 0 R, (L k x).real (Iic (-R)) := by
            rw [setIntegral_const, smul_eq_mul, hvolR R hR0]
        _ ≤ ∫ t in Ioc 0 R, (L k x).real (Iic (-t)) :=
            setIntegral_mono_on (integrableOn_const (by simp)) (hB.mono_set Ioc_subset_Ioi_self)
              measurableSet_Ioc (fun t ht => measureReal_mono (Iic_subset_Iic.2 (neg_le_neg ht.2)))
        _ ≤ B := setIntegral_mono_set hB (Eventually.of_forall fun _ => measureReal_nonneg)
            Ioc_subset_Ioi_self.eventuallyLE
    have hvA := measureReal_nonneg (μ := L k x) (s := Ioi R)
    have hvB := measureReal_nonneg (μ := L k x) (s := Iic (-R))
    have hcR := real_Ioi60 (L k x) R
    rcases le_or_gt (1 / 2) (μ.real (Ici x)) with hc | hc
    · have tA : ∀ t, 0 < t → (L k x).real (Ioi t) ≤ 2 * g0 t := fun t ht => by
        have h1 := hup k x t
        have h2 := (hνk k t ht).1
        have h3 := measureReal_nonneg (μ := L k x) (s := Ioi t)
        nlinarith
      have hAle : A ≤ 2 * I := by
        calc A ≤ ∫ t in Ioi (0 : ℝ), 2 * g0 t :=
              setIntegral_mono_on hA (hg0.const_mul 2) measurableSet_Ioi (fun t ht => tA t ht)
          _ = 2 * I := integral_const_mul _ _
      have hv1 : (L k x).real (Iic (-R)) < ε := by
        by_contra hv
        rw [not_lt] at hv
        nlinarith
      have hv2 : (L k x).real (Ioi R) ≤ ε := by
        have := tA R hR0; linarith
      exact ⟨hv1.le, by linarith⟩
    · have hc2 : 1 / 2 ≤ μ.real (Iic x) := by linarith
      have tB : ∀ t, 0 < t → (L k x).real (Iic (-t)) ≤ 2 * g0 t := fun t ht => by
        have h1 := hlow k x (-t)
        have h2 := (hνk k t ht).2
        have h3 := measureReal_nonneg (μ := L k x) (s := Iic (-t))
        nlinarith
      have hBle : B ≤ 2 * I := by
        calc B ≤ ∫ t in Ioi (0 : ℝ), 2 * g0 t :=
              setIntegral_mono_on hB (hg0.const_mul 2) measurableSet_Ioi (fun t ht => tB t ht)
          _ = 2 * I := integral_const_mul _ _
      have hv1 : (L k x).real (Ioi R) < ε := by
        by_contra hv
        rw [not_lt] at hv
        nlinarith
      have hv2 : (L k x).real (Iic (-R)) ≤ ε := by
        have := tB R hR0; linarith
      exact ⟨hv2, by linarith⟩
  have hmean : ∀ᵐ x ∂μ, (∀ k, Integrable id (L k x)) ∧
      Tendsto (fun k => ∫ y, y ∂(L k x)) atTop (𝓝 x) ∧
      ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧
        ∀ k t, 0 < t → (L k x).real (Ioi t) ≤ g t ∧ (L k x).real (Iic (-t)) ≤ g t := by
    filter_upwards [hlimx, ae_pos_Ici60 μ, ae_pos_Iic60 μ] with x hx h1 h2
    have p1 : 0 < μ.real (Ici x) := ENNReal.toReal_pos h1 (measure_ne_top _ _)
    have p2 : 0 < μ.real (Iic x) := ENNReal.toReal_pos h2 (measure_ne_top _ _)
    set m := min (μ.real (Ici x)) (μ.real (Iic x)) with hm
    have hm0 : 0 < m := lt_min p1 p2
    refine ⟨fun k => hint k x, hx, fun t => g0 t / m, hg0.div_const _, fun k t ht => ⟨?_, ?_⟩⟩
    · rw [le_div_iff₀ hm0]
      have a1 := hup k x t
      have a2 := (hνk k t ht).1
      have a3 := measureReal_nonneg (μ := L k x) (s := Ioi t)
      have a4 : m ≤ μ.real (Ici x) := min_le_left _ _
      nlinarith
    · rw [le_div_iff₀ hm0]
      have a1 := hlow k x (-t)
      have a2 := (hνk k t ht).2
      have a3 := measureReal_nonneg (μ := L k x) (s := Iic (-t))
      have a4 : m ≤ μ.real (Iic x) := min_le_right _ _
      nlinarith
  exact c4_core60 μ ν L hmono htight hcdf hmean

/-! ## Integrability and mean comparison under the stochastic order -/

theorem st_integrable60 (η η1 η2 : Measure ℝ) [IsProbabilityMeasure η] [IsProbabilityMeasure η1]
    [IsProbabilityMeasure η2] (h1 : ∀ t, η.real (Iic t) ≤ η1.real (Iic t))
    (h2 : ∀ t, η2.real (Iic t) ≤ η.real (Iic t)) (i1 : Integrable id η1) (i2 : Integrable id η2) :
    Integrable id η := by
  obtain ⟨-, hB1⟩ := tails_int60 η1 i1
  obtain ⟨hA2, -⟩ := tails_int60 η2 i2
  refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
  show ∫⁻ y, ‖id y‖ₑ ∂η < ⊤
  simp only [id, Real.enorm_eq_ofReal_abs]
  rw [lintegral_eq_lintegral_meas_lt η (Eventually.of_forall fun y => abs_nonneg y)
    measurable_id.abs.aemeasurable]
  have hgl : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (η2.real (Ioi t) + η1.real (Iic (-t))) < ⊤ :=
    (hA2.add hB1).lintegral_lt_top
  refine lt_of_le_of_lt (lintegral_mono fun t => ?_) hgl
  have hsub : {a : ℝ | t < |a|} ⊆ Ioi t ∪ Iic (-t) := by
    intro a ha
    simp only [Set.mem_ofPred_eq, lt_abs] at ha
    rcases ha with ha | ha
    · exact Or.inl ha
    · exact Or.inr (by simp only [mem_Iic]; linarith)
  have e1 : η.real (Ioi t) ≤ η2.real (Ioi t) := by rw [real_Ioi60, real_Ioi60]; linarith [h2 t]
  calc η {a | t < |a|} ≤ η (Ioi t) + η (Iic (-t)) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ = ENNReal.ofReal (η.real (Ioi t)) + ENNReal.ofReal (η.real (Iic (-t))) := by
        rw [ofReal_measureReal, ofReal_measureReal]
    _ ≤ ENNReal.ofReal (η2.real (Ioi t)) + ENNReal.ofReal (η1.real (Iic (-t))) :=
        add_le_add (ENNReal.ofReal_le_ofReal e1) (ENNReal.ofReal_le_ofReal (h1 (-t)))
    _ = ENNReal.ofReal (η2.real (Ioi t) + η1.real (Iic (-t))) :=
        (ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg).symm

theorem st_mean_le60 (η1 η2 : Measure ℝ) [IsProbabilityMeasure η1] [IsProbabilityMeasure η2]
    (h : ∀ t, η2.real (Iic t) ≤ η1.real (Iic t)) (i1 : Integrable id η1)
    (i2 : Integrable id η2) : ∫ y, y ∂η1 ≤ ∫ y, y ∂η2 := by
  obtain ⟨hA1, hB1⟩ := tails_int60 η1 i1
  obtain ⟨hA2, hB2⟩ := tails_int60 η2 i2
  rw [layer60 η1 i1, layer60 η2 i2]
  have a : ∫ t in Ioi (0 : ℝ), η1.real (Ioi t) ≤ ∫ t in Ioi (0 : ℝ), η2.real (Ioi t) :=
    setIntegral_mono_on hA1 hA2 measurableSet_Ioi fun t _ => by
      rw [real_Ioi60, real_Ioi60]; linarith [h t]
  have b : ∫ t in Ioi (0 : ℝ), η2.real (Iic (-t)) ≤ ∫ t in Ioi (0 : ℝ), η1.real (Iic (-t)) :=
    setIntegral_mono_on hB2 hB1 measurableSet_Ioi fun t _ => h (-t)
  linarith

/-- Per-point integrability and mean bounds for clamped monotone kernel families. -/
theorem c4_bounds60 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (L : ℕ → Kernel ℝ ℝ) [hL : ∀ k, IsMarkovKernel (L k)]
    (hmono : ∀ k x₁ x₂, x₁ ≤ x₂ → ∀ t, (L k x₂).real (Iic t) ≤ (L k x₁).real (Iic t))
    (a b : ℕ → ℝ) (hab : ∀ k, a k ≤ b k)
    (hcl : ∀ k x, L k x = L k (max (a k) (min x (b k))))
    (ia : ∀ k, Integrable id (L k (a k))) (ib : ∀ k, Integrable id (L k (b k)))
    (ma : ∀ k, ∫ y, y ∂(L k (a k)) = a k) (mb : ∀ k, ∫ y, y ∂(L k (b k)) = b k)
    (hlo : ∀ k x, μ (Iic x) = 0 → x ≤ a k) (hhi : ∀ k x, μ (Ici x) = 0 → b k ≤ x)
    (hlimx : ∀ᵐ x ∂μ, Tendsto (fun k => ∫ y, y ∂(L k x)) atTop (𝓝 x)) :
    (∀ k x, Integrable id (L k x)) ∧ (∀ x, ∃ M : ℝ, ∀ k, |∫ y, y ∂(L k x)| ≤ M) := by
  have hint : ∀ k x, Integrable id (L k x) := by
    intro k x
    rw [hcl k x]
    have h1 : a k ≤ max (a k) (min x (b k)) := le_max_left _ _
    have h2 : max (a k) (min x (b k)) ≤ b k := max_le (hab k) (min_le_right _ _)
    exact st_integrable60 _ _ _ (fun t => hmono k _ _ h1 t) (fun t => hmono k _ _ h2 t)
      (ia k) (ib k)
  refine ⟨hint, fun x => ?_⟩
  have hmeanle : ∀ k x₁ x₂, x₁ ≤ x₂ → ∫ y, y ∂(L k x₁) ≤ ∫ y, y ∂(L k x₂) := fun k x₁ x₂ h =>
    st_mean_le60 _ _ (fun t => hmono k x₁ x₂ h t) (hint k x₁) (hint k x₂)
  -- lower bound
  have hlow : ∃ B : ℝ, ∀ k, B ≤ ∫ y, y ∂(L k x) := by
    by_cases h0 : μ (Iic x) = 0
    · refine ⟨x, fun k => ?_⟩
      have hx : x ≤ a k := hlo k x h0
      have e : max (a k) (min x (b k)) = a k := max_eq_left ((min_le_left _ _).trans hx)
      rw [hcl k x, e, ma k]; exact hx
    · haveI : NeBot (ae (μ.restrict (Iic x))) := ae_neBot.2 (by
        intro hr; apply h0; rw [← Measure.restrict_apply_univ, hr]; rfl)
      obtain ⟨z, hz, hzx⟩ := ((ae_restrict_of_ae (s := Iic x) hlimx).and
        (ae_restrict_mem (μ := μ) (measurableSet_Iic (a := x)))).exists
      obtain ⟨B, hB⟩ := hz.bddBelow_range
      exact ⟨B, fun k => (hB ⟨k, rfl⟩).trans (hmeanle k z x hzx)⟩
  have hup : ∃ B : ℝ, ∀ k, ∫ y, y ∂(L k x) ≤ B := by
    by_cases h0 : μ (Ici x) = 0
    · refine ⟨x, fun k => ?_⟩
      have hx : b k ≤ x := hhi k x h0
      have e : max (a k) (min x (b k)) = b k := by
        rw [min_eq_right hx]; exact max_eq_right (hab k)
      rw [hcl k x, e, mb k]; exact hx
    · haveI : NeBot (ae (μ.restrict (Ici x))) := ae_neBot.2 (by
        intro hr; apply h0; rw [← Measure.restrict_apply_univ, hr]; rfl)
      obtain ⟨z, hz, hzx⟩ := ((ae_restrict_of_ae (s := Ici x) hlimx).and
        (ae_restrict_mem (μ := μ) (measurableSet_Ici (a := x)))).exists
      obtain ⟨B, hB⟩ := hz.bddAbove_range
      exact ⟨B, fun k => (hmeanle k x z hzx).trans (hB ⟨k, rfl⟩)⟩
  obtain ⟨B1, hB1⟩ := hlow
  obtain ⟨B2, hB2⟩ := hup
  exact ⟨max |B1| |B2|, fun k => abs_le.2 ⟨by
    have := hB1 k; have := neg_abs_le B1; have := le_max_left |B1| |B2|; linarith, by
    have := hB2 k; have := le_abs_self B2; have := le_max_right |B1| |B2|; linarith⟩⟩

end C4L60

end PartC4

section PartA
open MeasureTheory ProbabilityTheory Filter Topology Set

namespace A60

/-! ## K1: the two-point spread onto the grid `h ℤ` -/

/-- Spread `w` onto its two neighbouring grid points of `h ℤ`, keeping the mean. -/
noncomputable def sp60 (h w : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - Int.fract (w / h)) • Measure.dirac (h * ⌊w / h⌋) +
  ENNReal.ofReal (Int.fract (w / h)) • Measure.dirac (h * (⌊w / h⌋ + 1))

theorem sp_apply60 (h w : ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    sp60 h w s = ENNReal.ofReal (1 - Int.fract (w / h)) * s.indicator 1 (h * ⌊w / h⌋) +
      ENNReal.ofReal (Int.fract (w / h)) * s.indicator 1 (h * (⌊w / h⌋ + 1)) := by
  simp only [sp60, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hs]

theorem sp_prob60 (h w : ℝ) : IsProbabilityMeasure (sp60 h w) := by
  constructor
  rw [sp_apply60 h w univ MeasurableSet.univ]
  simp only [indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_add (by linarith [Int.fract_lt_one (w / h)]) (Int.fract_nonneg _)]
  simp

theorem sp_meas60 (h : ℝ) : Measurable (sp60 h) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [sp_apply60 h _ s hs]
  have hfr : Measurable fun w : ℝ => Int.fract (w / h) :=
    measurable_fract.comp (measurable_id.div_const h)
  have hfl : Measurable fun w : ℝ => ((⌊w / h⌋ : ℤ) : ℝ) :=
    measurable_from_top.comp (Int.measurable_floor.comp (measurable_id.div_const h))
  refine Measurable.add (Measurable.mul ?_ ?_) (Measurable.mul ?_ ?_)
  · exact ENNReal.measurable_ofReal.comp (measurable_const.sub hfr)
  · exact (measurable_one.indicator hs).comp (measurable_const.mul hfl)
  · exact ENNReal.measurable_ofReal.comp hfr
  · exact (measurable_one.indicator hs).comp (measurable_const.mul (hfl.add measurable_const))

/-- The spread kernel. -/
noncomputable def spK60 (h : ℝ) : Kernel ℝ ℝ := ⟨sp60 h, sp_meas60 h⟩

instance spK_markov60 (h : ℝ) : IsMarkovKernel (spK60 h) := ⟨fun w => sp_prob60 h w⟩

theorem sp_integral60 (h w : ℝ) (φ : ℝ → ℝ) :
    ∫ y, φ y ∂(sp60 h w) = (1 - Int.fract (w / h)) * φ (h * ⌊w / h⌋) +
      Int.fract (w / h) * φ (h * (⌊w / h⌋ + 1)) := by
  have i1 : Integrable φ (ENNReal.ofReal (1 - Int.fract (w / h)) • Measure.dirac (h * ⌊w / h⌋)) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have i2 : Integrable φ (ENNReal.ofReal (Int.fract (w / h)) •
      Measure.dirac (h * (⌊w / h⌋ + 1))) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [sp60, integral_add_measure i1 i2, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, ENNReal.toReal_ofReal (by linarith [Int.fract_lt_one (w / h)]),
    ENNReal.toReal_ofReal (Int.fract_nonneg _), smul_eq_mul, smul_eq_mul]

theorem sp_mean60 (h w : ℝ) (hh : 0 < h) : ∫ y, y ∂(sp60 h w) = w := by
  rw [sp_integral60]
  have e := Int.floor_add_fract (w / h)
  have e2 : h * (w / h) = w := by field_simp
  nlinarith [e, e2]

theorem sp_stoploss60 (h w : ℝ) (hh : 0 < h) (j : ℤ) :
    ∫ y, max (y - h * j) 0 ∂(sp60 h w) = max (w - h * j) 0 := by
  rw [sp_integral60]
  have e := Int.floor_add_fract (w / h)
  have e2 : h * (w / h) = w := by field_simp
  have f0 := Int.fract_nonneg (w / h)
  have f1 := Int.fract_lt_one (w / h)
  set n := ⌊w / h⌋ with hn
  set f := Int.fract (w / h) with hf
  rcases le_or_gt j n with hjn | hjn
  · have c1 : (j : ℝ) ≤ n := by exact_mod_cast hjn
    have a1 : 0 ≤ h * n - h * j := by nlinarith
    have a2 : 0 ≤ h * (n + 1) - h * j := by nlinarith
    have a3 : 0 ≤ w - h * j := by nlinarith
    rw [max_eq_left a1, max_eq_left a2, max_eq_left a3]
    nlinarith
  · have c1 : (n : ℝ) + 1 ≤ j := by exact_mod_cast hjn
    have a1 : h * n - h * j ≤ 0 := by nlinarith
    have a2 : h * (n + 1) - h * j ≤ 0 := by nlinarith
    have a3 : w - h * j ≤ 0 := by nlinarith
    rw [max_eq_right a1, max_eq_right a2, max_eq_right a3]
    ring

/-- Linear interpolation of an antitone function on the grid is antitone. -/
theorem interp_anti60 (h : ℝ) (hh : 0 < h) (φ : ℝ → ℝ) (hφ : Antitone φ) :
    Antitone fun w : ℝ => (1 - Int.fract (w / h)) * φ (h * ⌊w / h⌋) +
      Int.fract (w / h) * φ (h * (⌊w / h⌋ + 1)) := by
  intro w w' hww
  have hn : ⌊w / h⌋ ≤ ⌊w' / h⌋ := Int.floor_mono (div_le_div_of_nonneg_right hww hh.le)
  have f0 := Int.fract_nonneg (w / h)
  have f1 := Int.fract_lt_one (w / h)
  have f0' := Int.fract_nonneg (w' / h)
  have f1' := Int.fract_lt_one (w' / h)
  have hd : ∀ m : ℤ, φ (h * (m + 1)) ≤ φ (h * m) := fun m => hφ (by nlinarith)
  rcases hn.lt_or_eq with hlt | heq
  · -- different cells
    have c : (⌊w / h⌋ : ℝ) + 1 ≤ ⌊w' / h⌋ := by exact_mod_cast hlt
    have m1 : φ (h * ⌊w' / h⌋) ≤ φ (h * (⌊w / h⌋ + 1)) := hφ (by nlinarith)
    have d1 := hd ⌊w / h⌋
    have d2 := hd ⌊w' / h⌋
    nlinarith
  · -- same cell
    have hf : Int.fract (w / h) ≤ Int.fract (w' / h) := by
      rw [Int.fract, Int.fract, heq]
      have : w / h ≤ w' / h := div_le_div_of_nonneg_right hww hh.le
      linarith
    dsimp only
    rw [← heq]
    have d1 := hd ⌊w / h⌋
    nlinarith

/-! ## K2: stop-loss functions and the clamp -/

/-- Upper stop-loss `E (X - a)⁺`. -/
noncomputable def SL60 (μ : Measure ℝ) (a : ℝ) : ℝ := ∫ x, max (x - a) 0 ∂μ
/-- Lower stop-loss `E (a - X)⁺`. -/
noncomputable def SLb60 (μ : Measure ℝ) (a : ℝ) : ℝ := ∫ x, max (a - x) 0 ∂μ

section SL
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
include hμ

theorem sl_int60 (a : ℝ) : Integrable (fun x : ℝ => max (x - a) 0) μ :=
  (hμ.sub (integrable_const a)).pos_part

theorem slb_int60 (a : ℝ) : Integrable (fun x : ℝ => max (a - x) 0) μ :=
  ((integrable_const a).sub hμ).pos_part

theorem sl_sub_slb60 (a : ℝ) : SL60 μ a - SLb60 μ a = ∫ x, x ∂μ - a := by
  rw [SL60, SLb60, ← integral_sub (sl_int60 μ hμ a) (slb_int60 μ hμ a)]
  have e : (fun x : ℝ => max (x - a) 0 - max (a - x) 0) = fun x => x - a := by
    funext x; rcases le_total x a with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  rw [e]
  have := integral_sub hμ (integrable_const (μ := μ) a)
  simp only [id] at this
  rw [this]; simp

theorem sl_anti60 : Antitone (SL60 μ) := fun a b hab =>
  integral_mono (sl_int60 μ hμ b) (sl_int60 μ hμ a) fun x => max_le_max (by linarith) le_rfl

theorem slb_mono60 : Monotone (SLb60 μ) := fun a b hab =>
  integral_mono (slb_int60 μ hμ a) (slb_int60 μ hμ b) fun x => max_le_max (by linarith) le_rfl

theorem sl_lip60 (a b : ℝ) : |SL60 μ a - SL60 μ b| ≤ |a - b| := by
  rw [SL60, SL60, ← integral_sub (sl_int60 μ hμ a) (sl_int60 μ hμ b)]
  have h := norm_integral_le_of_norm_le_const (μ := μ) (C := |a - b|)
    (f := fun x : ℝ => max (x - a) 0 - max (x - b) 0)
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      calc |max (x - a) 0 - max (x - b) 0| ≤ |x - a - (x - b)| := abs_max_sub_max_le_abs _ _ _
        _ = |a - b| := by rw [show x - a - (x - b) = -(a - b) by ring, abs_neg])
  simpa [Real.norm_eq_abs] using h

theorem slb_lip60 (a b : ℝ) : |SLb60 μ a - SLb60 μ b| ≤ |a - b| := by
  rw [SLb60, SLb60, ← integral_sub (slb_int60 μ hμ a) (slb_int60 μ hμ b)]
  have h := norm_integral_le_of_norm_le_const (μ := μ) (C := |a - b|)
    (f := fun x : ℝ => max (a - x) 0 - max (b - x) 0)
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      calc |max (a - x) 0 - max (b - x) 0| ≤ |a - x - (b - x)| := abs_max_sub_max_le_abs _ _ _
        _ = |a - b| := by rw [show a - x - (b - x) = a - b by ring])
  simpa [Real.norm_eq_abs] using h

theorem sl_cont60 : Continuous (SL60 μ) :=
  (LipschitzWith.of_dist_le' (K := 1) fun a b => by
    simpa [Real.dist_eq] using sl_lip60 μ hμ a b).continuous

theorem slb_cont60 : Continuous (SLb60 μ) :=
  (LipschitzWith.of_dist_le' (K := 1) fun a b => by
    simpa [Real.dist_eq] using slb_lip60 μ hμ a b).continuous

theorem sl_tendsto60 : Tendsto (SL60 μ) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
    (F := fun (a : ℝ) (x : ℝ) => max (x - a) 0) (f := fun _ => (0 : ℝ)) (fun x => |x|)
    (Eventually.of_forall fun a => (sl_int60 μ hμ a).aestronglyMeasurable)
    ((eventually_ge_atTop 0).mono fun a ha => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [le_abs_self x]) (abs_nonneg x))
    hμ.abs
    (Eventually.of_forall fun x => tendsto_const_nhds.congr' ((eventually_ge_atTop x).mono
      fun a ha => (max_eq_right (by linarith)).symm))
  have e : SL60 μ = fun a => ∫ x, max (x - a) 0 ∂μ := rfl
  rw [e]; simpa using h

theorem slb_tendsto60 : Tendsto (SLb60 μ) atBot (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atBot)
    (F := fun (a : ℝ) (x : ℝ) => max (a - x) 0) (f := fun _ => (0 : ℝ)) (fun x => |x|)
    (Eventually.of_forall fun a => (slb_int60 μ hμ a).aestronglyMeasurable)
    ((eventually_le_atBot 0).mono fun a ha => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [neg_abs_le x]) (abs_nonneg x))
    hμ.abs
    (Eventually.of_forall fun x => tendsto_const_nhds.congr' ((eventually_le_atBot x).mono
      fun a ha => (max_eq_right (by linarith)).symm))
  have e : SLb60 μ = fun a => ∫ x, max (a - x) 0 ∂μ := rfl
  rw [e]; simpa using h

theorem exists_beta60 (m d : ℝ) (hd0 : 0 < d) (hdD : d ≤ SL60 μ m) :
    ∃ β, m ≤ β ∧ SL60 μ β = d := by
  obtain ⟨M, hM1, hM2⟩ := ((sl_tendsto60 μ hμ).eventually (gt_mem_nhds hd0)).and
    (eventually_ge_atTop m) |>.exists
  obtain ⟨β, hβ, hβd⟩ := intermediate_value_Icc' hM2 (sl_cont60 μ hμ).continuousOn
    ⟨hM1.le, hdD⟩
  exact ⟨β, hβ.1, hβd⟩

theorem exists_alpha60 (m d : ℝ) (hd0 : 0 < d) (hdD : d ≤ SLb60 μ m) :
    ∃ α, α ≤ m ∧ SLb60 μ α = d := by
  obtain ⟨M, hM1, hM2⟩ := ((slb_tendsto60 μ hμ).eventually (gt_mem_nhds hd0)).and
    (eventually_le_atBot m) |>.exists
  obtain ⟨α, hα, hαd⟩ := intermediate_value_Icc hM2 (slb_cont60 μ hμ).continuousOn
    ⟨hM1.le, hdD⟩
  exact ⟨α, hα.2, hαd⟩

end SL

/-- The clamp `x ↦ max α (min x β)`. -/
noncomputable def cl60 (α β x : ℝ) : ℝ := max α (min x β)

theorem cl_cont60 (α β : ℝ) : Continuous (cl60 α β) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem cl_mono60 (α β : ℝ) : Monotone (cl60 α β) := fun x y h =>
  max_le_max le_rfl (min_le_min h le_rfl)

theorem cl_pt60 (α β x : ℝ) (h : α ≤ β) :
    cl60 α β x = x + max (α - x) 0 - max (x - β) 0 := by
  unfold cl60
  rcases le_total x α with h1 | h1
  · rw [min_eq_left (h1.trans h), max_eq_left h1, max_eq_left (by linarith),
      max_eq_right (by linarith)]; ring
  · rcases le_total x β with h2 | h2
    · rw [min_eq_left h2, max_eq_right h1, max_eq_right (by linarith), max_eq_right (by linarith)]
      ring
    · rw [min_eq_right h2, max_eq_right h, max_eq_right (by linarith), max_eq_left (by linarith)]
      ring

section Clamp
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ) (α β : ℝ) (hαβ : α ≤ β)
include hμ hαβ

theorem cl_int60 : Integrable (cl60 α β) μ := by
  have e : cl60 α β = fun x => x + max (α - x) 0 - max (x - β) 0 := funext fun x => cl_pt60 α β x hαβ
  rw [e]
  exact (hμ.add (slb_int60 μ hμ α)).sub (sl_int60 μ hμ β)

theorem cl_mean60 : ∫ x, cl60 α β x ∂μ = ∫ x, x ∂μ + SLb60 μ α - SL60 μ β := by
  simp_rw [fun x => cl_pt60 α β x hαβ]
  have i0 : Integrable (fun x : ℝ => x) μ := hμ
  have i1 : Integrable (fun x : ℝ => x + max (α - x) 0) μ := i0.add (slb_int60 μ hμ α)
  rw [integral_sub i1 (sl_int60 μ hμ β), integral_add i0 (slb_int60 μ hμ α)]
  rfl

/-- Stop-loss of the clamped law, above `α`. -/
theorem cl_sl60 (a : ℝ) (ha : α ≤ a) :
    ∫ x, max (cl60 α β x - a) 0 ∂μ = max (SL60 μ a - SL60 μ β) 0 := by
  rcases le_total a β with hb | hb
  · have e : (fun x => max (cl60 α β x - a) 0) = fun x => max (x - a) 0 - max (x - β) 0 := by
      funext x; unfold cl60
      rcases le_total x a with h1 | h1
      · rw [max_eq_right (show x - a ≤ 0 by linarith), max_eq_right (show x - β ≤ 0 by linarith)]
        refine max_eq_right ?_ |>.trans (by ring)
        have : min x β ≤ a := (min_le_left _ _).trans h1
        exact sub_nonpos.2 (max_le ha this)
      · rcases le_total x β with h2 | h2
        · rw [min_eq_left h2, max_eq_right (show α ≤ x by linarith), max_eq_left (by linarith),
            max_eq_right (show x - β ≤ 0 by linarith)]; ring
        · rw [min_eq_right h2, max_eq_right hαβ, max_eq_left (by linarith),
            max_eq_left (by linarith), max_eq_left (by linarith)]; ring
    rw [e, integral_sub (sl_int60 μ hμ a) (sl_int60 μ hμ β)]
    exact (max_eq_left (sub_nonneg.2 (sl_anti60 μ hμ hb))).symm
  · have e : (fun x => max (cl60 α β x - a) 0) = fun _ => (0 : ℝ) := by
      funext x; unfold cl60
      exact max_eq_right (sub_nonpos.2 (max_le ha ((min_le_right _ _).trans hb)))
    rw [e, integral_zero]
    exact (max_eq_right (sub_nonpos.2 (sl_anti60 μ hμ hb))).symm

/-- Stop-loss of the clamped law, below `α`. -/
theorem cl_sl_low60 (a : ℝ) (ha : a ≤ α) :
    ∫ x, max (cl60 α β x - a) 0 ∂μ = ∫ x, x ∂μ + SLb60 μ α - SL60 μ β - a := by
  have e : (fun x => max (cl60 α β x - a) 0) = fun x => cl60 α β x - a := by
    funext x; unfold cl60; exact max_eq_left (by linarith [le_max_left α (min x β)])
  rw [e, integral_sub (cl_int60 μ hμ α β hαβ) (integrable_const a), cl_mean60 μ hμ α β hαβ]
  simp

end Clamp

/-- The clamped laws keep the stop-loss order. -/
theorem cl_order60 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable id μ) (hν : Integrable id ν) (m : ℝ) (hmμ : ∫ x, x ∂μ = m)
    (hmν : ∫ x, x ∂ν = m) (hf : ∀ a, SL60 μ a ≤ SL60 ν a) (hg : ∀ a, SLb60 μ a ≤ SLb60 ν a)
    (d αμ βμ αν βν : ℝ) (h1 : αμ ≤ m) (h2 : m ≤ βμ) (h3 : αν ≤ m) (h4 : m ≤ βν)
    (e1 : SLb60 μ αμ = d) (e2 : SL60 μ βμ = d) (e3 : SLb60 ν αν = d) (e4 : SL60 ν βν = d)
    (a : ℝ) :
    ∫ x, max (cl60 αμ βμ x - a) 0 ∂μ ≤ ∫ x, max (cl60 αν βν x - a) 0 ∂ν := by
  have hμab : αμ ≤ βμ := h1.trans h2
  have hνab : αν ≤ βν := h3.trans h4
  have sμ := sl_sub_slb60 μ hμ a
  have sν := sl_sub_slb60 ν hν a
  rcases le_total αμ a with ha1 | ha1 <;> rcases le_total αν a with ha2 | ha2
  · rw [cl_sl60 μ hμ αμ βμ hμab a ha1, cl_sl60 ν hν αν βν hνab a ha2, e2, e4]
    exact max_le_max (by linarith [hf a]) le_rfl
  · rw [cl_sl60 μ hμ αμ βμ hμab a ha1, cl_sl_low60 ν hν αν βν hνab a ha2, e3, e4, hmν]
    have := slb_mono60 ν hν ha2
    have := hg a
    refine max_le (by linarith) (by linarith)
  · rw [cl_sl_low60 μ hμ αμ βμ hμab a ha1, cl_sl60 ν hν αν βν hνab a ha2, e1, e2, e4, hmμ]
    have := slb_mono60 ν hν ha2
    exact le_max_of_le_left (by linarith)
  · rw [cl_sl_low60 μ hμ αμ βμ hμab a ha1, cl_sl_low60 ν hν αν βν hνab a ha2, e1, e2, e3, e4,
      hmμ, hmν]

/-! ## K3: the grid laws and the finite hypothesis for C2 -/

/-- Grid points `h j` covering `[lo, hi]` with one extra point on the right. -/
noncomputable def gridF60 (h lo hi : ℝ) : Finset ℝ :=
  (Finset.Icc (⌊lo / h⌋) (⌊hi / h⌋ + 1)).image (fun j : ℤ => h * j)

theorem sp_supp60 (h : ℝ) (hh : 0 < h) (lo hi w : ℝ) (h1 : lo ≤ w) (h2 : w ≤ hi) :
    sp60 h w (↑(gridF60 h lo hi) : Set ℝ)ᶜ = 0 := by
  have hs : MeasurableSet ((↑(gridF60 h lo hi) : Set ℝ)ᶜ) := (Finset.measurableSet _).compl
  rw [sp_apply60 h w _ hs]
  have f1 : ⌊lo / h⌋ ≤ ⌊w / h⌋ := Int.floor_mono (div_le_div_of_nonneg_right h1 hh.le)
  have f2 : ⌊w / h⌋ ≤ ⌊hi / h⌋ := Int.floor_mono (div_le_div_of_nonneg_right h2 hh.le)
  have m1 : h * (⌊w / h⌋ : ℝ) ∈ (↑(gridF60 h lo hi) : Set ℝ) := by
    simp only [gridF60, Finset.coe_image, Finset.coe_Icc, mem_image, mem_Icc]
    exact ⟨⌊w / h⌋, ⟨f1, by omega⟩, rfl⟩
  have m2 : h * ((⌊w / h⌋ : ℝ) + 1) ∈ (↑(gridF60 h lo hi) : Set ℝ) := by
    simp only [gridF60, Finset.coe_image, Finset.coe_Icc, mem_image, mem_Icc]
    exact ⟨⌊w / h⌋ + 1, ⟨by omega, by omega⟩, by push_cast; ring⟩
  simp [indicator_of_notMem (notMem_compl_iff.2 m1), indicator_of_notMem (notMem_compl_iff.2 m2)]

/-- Integrals against the second marginal of a composition. -/
theorem int_snd60 (μ : Measure ℝ) [IsProbabilityMeasure μ] (K : Kernel ℝ ℝ) [IsMarkovKernel K]
    (f : ℝ → ℝ) (hfc : Continuous f) (hi : Integrable f (μ ⊗ₘ K).snd) :
    ∫ y, f y ∂(μ ⊗ₘ K).snd = ∫ x, ∫ y, f y ∂(K x) ∂μ := by
  rw [Measure.snd, integral_map measurable_snd.aemeasurable hfc.aestronglyMeasurable]
  exact Measure.integral_compProd (f := fun p : ℝ × ℝ => f p.2)
    ((integrable_map_measure hfc.aestronglyMeasurable measurable_snd.aemeasurable).1 hi)

/-- The clamp-then-spread kernel. -/
noncomputable def cK60 (h α β : ℝ) : Kernel ℝ ℝ :=
  (spK60 h).comap (cl60 α β) (cl_cont60 α β).measurable

instance cK_markov60 (h α β : ℝ) : IsMarkovKernel (cK60 h α β) := by
  unfold cK60; infer_instance

theorem cK_apply60 (h α β x : ℝ) : cK60 h α β x = sp60 h (cl60 α β x) := rfl

theorem cl_mem60 (α β x : ℝ) (h : α ≤ β) : α ≤ cl60 α β x ∧ cl60 α β x ≤ β :=
  ⟨le_max_left _ _, max_le h (min_le_right _ _)⟩

theorem grid_supp60 (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : ℝ) (hh : 0 < h) (α β lo hi : ℝ)
    (hαβ : α ≤ β) (hlo : lo ≤ α) (hhi : β ≤ hi) :
    (μ ⊗ₘ cK60 h α β).snd (↑(gridF60 h lo hi) : Set ℝ)ᶜ = 0 := by
  have hs : MeasurableSet ((↑(gridF60 h lo hi) : Set ℝ)ᶜ) := (Finset.measurableSet _).compl
  rw [Measure.snd_apply hs, ← Set.univ_prod, Measure.compProd_apply_prod MeasurableSet.univ hs,
    Measure.restrict_univ]
  refine lintegral_eq_zero_of_ae_eq_zero (Eventually.of_forall fun x => ?_)
  show cK60 h α β x _ = 0
  rw [cK_apply60]
  have := cl_mem60 α β x hαβ
  exact sp_supp60 h hh lo hi _ (hlo.trans this.1) (this.2.trans hhi)

theorem hyp_grid60 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable id μ) (hν : Integrable id ν) (m : ℝ) (hmμ : ∫ x, x ∂μ = m)
    (hmν : ∫ x, x ∂ν = m) (hf : ∀ a, SL60 μ a ≤ SL60 ν a) (hg : ∀ a, SLb60 μ a ≤ SLb60 ν a)
    (d αμ βμ αν βν : ℝ) (h1 : αμ ≤ m) (h2 : m ≤ βμ) (h3 : αν ≤ m) (h4 : m ≤ βν)
    (e1 : SLb60 μ αμ = d) (e2 : SL60 μ βμ = d) (e3 : SLb60 ν αν = d) (e4 : SL60 ν βν = d)
    (h : ℝ) (hh : 0 < h) (lo hi : ℝ) (hlo1 : lo ≤ αμ) (hlo2 : lo ≤ αν) (hhi1 : βμ ≤ hi)
    (hhi2 : βν ≤ hi) :
    Fin60.Hyp (gridF60 h lo hi) (fun x => ((μ ⊗ₘ cK60 h αμ βμ).snd {x}).toReal)
      (fun y => ((ν ⊗ₘ cK60 h αν βν).snd {y}).toReal) := by
  set G := gridF60 h lo hi with hG
  set μk := (μ ⊗ₘ cK60 h αμ βμ).snd with hμk
  set νk := (ν ⊗ₘ cK60 h αν βν).snd with hνk
  have sμ : μk (↑G : Set ℝ)ᶜ = 0 := grid_supp60 μ h hh αμ βμ lo hi (h1.trans h2) hlo1 hhi1
  have sν : νk (↑G : Set ℝ)ᶜ = 0 := grid_supp60 ν h hh αν βν lo hi (h3.trans h4) hlo2 hhi2
  have Iμ := Fin60.fin_integral μk G sμ
  have Iν := Fin60.fin_integral νk G sν
  have intμ : ∀ f : ℝ → ℝ, Continuous f →
      ∫ y, f y ∂μk = ∫ x, ∫ y, f y ∂(sp60 h (cl60 αμ βμ x)) ∂μ :=
    fun f hfc => int_snd60 μ _ f hfc (Iμ f).1
  have intν : ∀ f : ℝ → ℝ, Continuous f →
      ∫ y, f y ∂νk = ∫ x, ∫ y, f y ∂(sp60 h (cl60 αν βν x)) ∂ν :=
    fun f hfc => int_snd60 ν _ f hfc (Iν f).1
  refine ⟨fun x _ => ENNReal.toReal_nonneg, fun y _ => ENNReal.toReal_nonneg, ?_, ?_, ?_⟩
  · have a1 := (Iμ fun _ => 1).2
    have a2 := (Iν fun _ => 1).2
    simp only [mul_one, integral_const, smul_eq_mul, probReal_univ] at a1 a2
    rw [← a1, ← a2]
  · have a1 := (Iμ fun x => x).2
    have a2 := (Iν fun x => x).2
    beta_reduce
    rw [← a1, ← a2, intμ (fun x => x) continuous_id, intν (fun x => x) continuous_id]
    simp_rw [sp_mean60 h _ hh]
    rw [cl_mean60 μ hμ αμ βμ (h1.trans h2), cl_mean60 ν hν αν βν (h3.trans h4), hmμ, hmν,
      e1, e2, e3, e4]
  · intro a ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ha
    have a1 := (Iμ fun x => max (x - h * j) 0).2
    have a2 := (Iν fun x => max (x - h * j) 0).2
    have hc : Continuous fun x : ℝ => max (x - h * j) 0 :=
      (continuous_id.sub continuous_const).max continuous_const
    unfold Fin60.HP
    beta_reduce
    rw [← a1, ← a2, intμ _ hc, intν _ hc]
    simp_rw [sp_stoploss60 h _ hh j]
    exact cl_order60 μ ν hμ hν m hmμ hmν hf hg d αμ βμ αν βν h1 h2 h3 h4 e1 e2 e3 e4 _

/-! ## K4: the composed kernel `κ ∘ₖ cK60` -/

/-- The approximating kernel: clamp, spread to the grid, then the C2 kernel. -/
noncomputable def LK60 (κ : Kernel ℝ ℝ) (h α β : ℝ) : Kernel ℝ ℝ := κ ∘ₖ cK60 h α β

instance LK_markov60 (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (h α β : ℝ) :
    IsMarkovKernel (LK60 κ h α β) := by
  unfold LK60; infer_instance

theorem cl_idem60 (α β x : ℝ) (h : α ≤ β) : cl60 α β (cl60 α β x) = cl60 α β x := by
  obtain ⟨h1, h2⟩ := cl_mem60 α β x h
  unfold cl60 at *
  rw [min_eq_left h2, max_eq_right h1]

theorem LK_clamp60 (κ : Kernel ℝ ℝ) (h α β : ℝ) (hαβ : α ≤ β) (x : ℝ) :
    LK60 κ h α β x = LK60 κ h α β (cl60 α β x) := by
  simp only [LK60, Kernel.comp_apply, cK_apply60, cl_idem60 α β x hαβ]

theorem LK_real60 (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (h α β x : ℝ) (s : Set ℝ)
    (hs : MeasurableSet s) :
    (LK60 κ h α β x).real s = ∫ y, (κ y).real s ∂(sp60 h (cl60 α β x)) := by
  haveI := sp_prob60 h (cl60 α β x)
  rw [measureReal_def, LK60, Kernel.comp_apply' _ _ _ hs, cK_apply60]
  simp only [measureReal_def]
  rw [integral_toReal ((κ.measurable_coe hs).aemeasurable)
    (Eventually.of_forall fun y => measure_lt_top _ _)]

theorem LK_mono60 (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (h α β : ℝ) (hh : 0 < h)
    (hκ : ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → ∀ t : ℝ, κ x₁ {y : ℝ | t < y} ≤ κ x₂ {y : ℝ | t < y})
    (x₁ x₂ : ℝ) (hx : x₁ ≤ x₂) (t : ℝ) :
    (LK60 κ h α β x₂).real (Iic t) ≤ (LK60 κ h α β x₁).real (Iic t) := by
  rw [LK_real60 κ h α β x₂ _ measurableSet_Iic, LK_real60 κ h α β x₁ _ measurableSet_Iic,
    sp_integral60, sp_integral60]
  have hφ : Antitone fun y => (κ y).real (Iic t) := by
    intro y₁ y₂ hy
    have e : ∀ y, (κ y).real (Iic t) = 1 - (κ y).real {z : ℝ | t < z} := by
      intro y
      have : {z : ℝ | t < z} = (Iic t)ᶜ := by ext z; simp
      rw [this, measureReal_compl measurableSet_Iic, probReal_univ]; ring
    dsimp only
    rw [e, e]
    have := ENNReal.toReal_mono (measure_ne_top _ _) (hκ y₁ y₂ hy t)
    simp only [measureReal_def]
    linarith
  exact interp_anti60 h hh _ hφ (cl_mono60 α β hx)

theorem LK_marg60 (μ : Measure ℝ) [IsProbabilityMeasure μ] (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (h α β : ℝ) (νk : Measure ℝ) (hκ : ((μ ⊗ₘ cK60 h α β).snd ⊗ₘ κ).snd = νk) :
    (μ ⊗ₘ LK60 κ h α β).snd = νk := by
  rw [Measure.snd_compProd, LK60, ← Measure.comp_assoc, ← Measure.snd_compProd μ (cK60 h α β),
    ← Measure.snd_compProd]
  exact hκ

theorem atom_good60 (ρ : Measure ℝ) (P : ℝ → Prop) (hP : ∀ᵐ y ∂ρ, P y) (g : ℝ)
    (hg : 0 < ρ {g}) : P g := by
  by_contra hng
  rw [ae_iff] at hP
  exact (lt_irrefl 0) (hg.trans_le ((measure_mono (singleton_subset_iff.2 hng)).trans hP.le))

/-! NEW LEMMAS (session 4) -/

theorem LK_eq60 (κ : Kernel ℝ ℝ) (h α β x : ℝ) :
    LK60 κ h α β x = ENNReal.ofReal (1 - Int.fract (cl60 α β x / h)) • κ (h * ⌊cl60 α β x / h⌋) +
      ENNReal.ofReal (Int.fract (cl60 α β x / h)) • κ (h * (⌊cl60 α β x / h⌋ + 1)) := by
  ext s hs
  rw [LK60, Kernel.comp_apply' _ _ _ hs, cK_apply60, sp60, lintegral_add_measure,
    lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac, lintegral_dirac]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]

theorem sp_lo_pos60 (h w : ℝ) : 0 < sp60 h w {h * ⌊w / h⌋} := by
  rw [sp_apply60 h w _ (measurableSet_singleton _), indicator_of_mem (mem_singleton _)]
  simp only [Pi.one_apply, mul_one]
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by linarith [Int.fract_lt_one (w / h)])) le_self_add

theorem sp_hi_pos60 (h w : ℝ) (hf : 0 < Int.fract (w / h)) :
    0 < sp60 h w {h * ((⌊w / h⌋ : ℝ) + 1)} := by
  rw [sp_apply60 h w _ (measurableSet_singleton _), indicator_of_mem (mem_singleton _)]
  simp only [Pi.one_apply, mul_one]
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 hf) le_add_self

/-- Mean of the composed kernel when every charged grid point is good. -/
theorem LK_mean60 (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (h α β x : ℝ) (hh : 0 < h)
    (hgood : ∀ g : ℝ, 0 < sp60 h (cl60 α β x) {g} → Integrable id (κ g) ∧ ∫ y, y ∂(κ g) = g) :
    Integrable id (LK60 κ h α β x) ∧ ∫ y, y ∂(LK60 κ h α β x) = cl60 α β x := by
  rw [LK_eq60]
  have f0 := Int.fract_nonneg (cl60 α β x / h)
  have f1 := Int.fract_lt_one (cl60 α β x / h)
  have e := Int.floor_add_fract (cl60 α β x / h)
  have e2 : h * (cl60 α β x / h) = cl60 α β x := by field_simp
  have G1 := hgood _ (sp_lo_pos60 h (cl60 α β x))
  have i1 : Integrable id (ENNReal.ofReal (1 - Int.fract (cl60 α β x / h)) •
      κ (h * ⌊cl60 α β x / h⌋)) := G1.1.smul_measure ENNReal.ofReal_ne_top
  rcases f0.lt_or_eq with hf0 | hf0
  · have G2 := hgood _ (sp_hi_pos60 h (cl60 α β x) hf0)
    have i2 : Integrable id (ENNReal.ofReal (Int.fract (cl60 α β x / h)) •
        κ (h * ((⌊cl60 α β x / h⌋ : ℝ) + 1))) := G2.1.smul_measure ENNReal.ofReal_ne_top
    refine ⟨i1.add_measure i2, ?_⟩
    change ∫ y, id y ∂_ = _
    rw [integral_add_measure i1 i2, integral_smul_measure, integral_smul_measure,
      ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal f0, smul_eq_mul, smul_eq_mul]
    simp only [id]
    rw [G1.2, G2.2]
    linear_combination h * e + e2
  · rw [← hf0, ENNReal.ofReal_zero, zero_smul, add_zero, sub_zero, ENNReal.ofReal_one, one_smul]
    refine ⟨G1.1, ?_⟩
    rw [G1.2]
    rw [← hf0, add_zero] at e
    rw [e]
    exact e2

theorem snd_lint60 (ν : Measure ℝ) [SFinite ν] (K : Kernel ℝ ℝ) [IsSFiniteKernel K] (s : Set ℝ)
    (hs : MeasurableSet s) : (ν ⊗ₘ K).snd s = ∫⁻ x, K x s ∂ν := by
  rw [Measure.snd_apply hs, ← Set.univ_prod, Measure.compProd_apply_prod MeasurableSet.univ hs,
    Measure.restrict_univ]

theorem snd_realA60 (ν : Measure ℝ) [IsProbabilityMeasure ν] (K : Kernel ℝ ℝ) [IsMarkovKernel K]
    (s : Set ℝ) (hs : MeasurableSet s) :
    ((ν ⊗ₘ K).snd).real s = ∫ x, (K x).real s ∂ν := by
  rw [measureReal_def, snd_lint60 ν K s hs]
  simp only [measureReal_def]
  rw [integral_toReal ((K.measurable_coe hs).aemeasurable)
    (Eventually.of_forall fun y => measure_lt_top _ _)]

theorem snd_atom_lo60 (μ : Measure ℝ) [IsProbabilityMeasure μ] (h α β : ℝ) (g : ℝ) :
    μ (Iic α) * sp60 h α {g} ≤ (μ ⊗ₘ cK60 h α β).snd {g} := by
  rw [snd_lint60 μ _ _ (measurableSet_singleton g), mul_comm,
    ← lintegral_indicator_const measurableSet_Iic]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ Iic α
  · rw [indicator_of_mem hx, cK_apply60]
    have : cl60 α β x = α := max_eq_left ((min_le_left _ _).trans hx)
    rw [this]
  · rw [indicator_of_notMem hx]; exact zero_le

theorem snd_atom_hi60 (μ : Measure ℝ) [IsProbabilityMeasure μ] (h α β : ℝ) (hαβ : α ≤ β) (g : ℝ) :
    μ (Ici β) * sp60 h β {g} ≤ (μ ⊗ₘ cK60 h α β).snd {g} := by
  rw [snd_lint60 μ _ _ (measurableSet_singleton g), mul_comm,
    ← lintegral_indicator_const measurableSet_Ici]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ Ici β
  · rw [indicator_of_mem hx, cK_apply60]
    have : cl60 α β x = β := by
      unfold cl60; rw [min_eq_right (mem_Ici.1 hx), max_eq_right hαβ]
    rw [this]
  · rw [indicator_of_notMem hx]; exact zero_le

theorem Iic_pos60 (μ : Measure ℝ) [IsProbabilityMeasure μ] (α : ℝ) (h : 0 < SLb60 μ α) :
    0 < μ (Iic α) := by
  rw [pos_iff_ne_zero]; intro h0
  have hae : ∀ᵐ x ∂μ, α < x := by
    rw [ae_iff]; simp only [not_lt]; exact h0
  have : SLb60 μ α = 0 := by
    unfold SLb60
    have e : (fun x : ℝ => max (α - x) 0) =ᵐ[μ] fun _ => 0 := by
      filter_upwards [hae] with x hx
      exact max_eq_right (by linarith)
    rw [integral_congr_ae e, integral_zero]
  linarith

theorem Ici_pos60 (μ : Measure ℝ) [IsProbabilityMeasure μ] (β : ℝ) (h : 0 < SL60 μ β) :
    0 < μ (Ici β) := by
  rw [pos_iff_ne_zero]; intro h0
  have hae : ∀ᵐ x ∂μ, x < β := by
    rw [ae_iff]; simp only [not_lt]; exact h0
  have : SL60 μ β = 0 := by
    unfold SL60
    have e : (fun x : ℝ => max (x - β) 0) =ᵐ[μ] fun _ => 0 := by
      filter_upwards [hae] with x hx
      exact max_eq_right (by linarith)
    rw [integral_congr_ae e, integral_zero]
  linarith

theorem end_lo60 (μ : Measure ℝ) [IsProbabilityMeasure μ] (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (h α β : ℝ) (hh : 0 < h) (hαβ : α ≤ β) (hpos : 0 < μ (Iic α))
    (hκ : ∀ᵐ g ∂(μ ⊗ₘ cK60 h α β).snd, Integrable id (κ g) ∧ ∫ y, y ∂(κ g) = g) :
    Integrable id (LK60 κ h α β α) ∧ ∫ y, y ∂(LK60 κ h α β α) = α := by
  have hc : cl60 α β α = α := by unfold cl60; rw [min_eq_left hαβ, max_self]
  have := LK_mean60 κ h α β α hh fun g hg => by
    refine atom_good60 _ _ hκ g ?_
    rw [hc] at hg
    exact lt_of_lt_of_le (ENNReal.mul_pos hpos.ne' hg.ne') (snd_atom_lo60 μ h α β g)
  rwa [hc] at this

theorem end_hi60 (μ : Measure ℝ) [IsProbabilityMeasure μ] (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (h α β : ℝ) (hh : 0 < h) (hαβ : α ≤ β) (hpos : 0 < μ (Ici β))
    (hκ : ∀ᵐ g ∂(μ ⊗ₘ cK60 h α β).snd, Integrable id (κ g) ∧ ∫ y, y ∂(κ g) = g) :
    Integrable id (LK60 κ h α β β) ∧ ∫ y, y ∂(LK60 κ h α β β) = β := by
  have hc : cl60 α β β = β := by unfold cl60; rw [min_self, max_eq_right hαβ]
  have := LK_mean60 κ h α β β hh fun g hg => by
    refine atom_good60 _ _ hκ g ?_
    rw [hc] at hg
    exact lt_of_lt_of_le (ENNReal.mul_pos hpos.ne' hg.ne') (snd_atom_hi60 μ h α β hαβ g)
  rwa [hc] at this

/-- Almost every point: the composed kernel has mean `cl x`. -/
theorem ae_mean60 (μ : Measure ℝ) [IsProbabilityMeasure μ] (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (h α β lo hi : ℝ) (hh : 0 < h) (hαβ : α ≤ β) (hlo : lo ≤ α) (hhi : β ≤ hi)
    (hκ : ∀ᵐ g ∂(μ ⊗ₘ cK60 h α β).snd, Integrable id (κ g) ∧ ∫ y, y ∂(κ g) = g) :
    ∀ᵐ x ∂μ, Integrable id (LK60 κ h α β x) ∧ ∫ y, y ∂(LK60 κ h α β x) = cl60 α β x := by
  have hz : ∀ g ∈ gridF60 h lo hi, ∀ᵐ x ∂μ,
      (μ ⊗ₘ cK60 h α β).snd {g} = 0 → sp60 h (cl60 α β x) {g} = 0 := by
    intro g _
    by_cases h0 : (μ ⊗ₘ cK60 h α β).snd {g} = 0
    · have h0' := h0
      rw [snd_lint60 μ _ _ (measurableSet_singleton g),
        lintegral_eq_zero_iff (Kernel.measurable_coe _ (measurableSet_singleton g))] at h0'
      filter_upwards [h0'] with x hx _
      exact hx
    · exact Eventually.of_forall fun x hx => absurd hx h0
  have hall := (Filter.eventually_all_finset (gridF60 h lo hi)).2 hz
  filter_upwards [hall] with x hx
  refine LK_mean60 κ h α β x hh fun g hg => ?_
  have hgG : g ∈ gridF60 h lo hi := by
    by_contra hng
    have hs := sp_supp60 h hh lo hi (cl60 α β x) (hlo.trans (cl_mem60 α β x hαβ).1)
      ((cl_mem60 α β x hαβ).2.trans hhi)
    have hle : sp60 h (cl60 α β x) {g} ≤ 0 :=
      (measure_mono (singleton_subset_iff.2 (show g ∈ ((gridF60 h lo hi : Set ℝ))ᶜ from
        fun hm => hng (Finset.mem_coe.1 hm)))).trans hs.le
    exact absurd hg (not_lt.2 hle)
  have hpos : 0 < (μ ⊗ₘ cK60 h α β).snd {g} := by
    rw [pos_iff_ne_zero]; intro h0; exact absurd (hx g hgG h0) hg.ne'
  exact atom_good60 _ _ hκ g hpos

/-- Pointwise convergence of the clamps. -/
theorem cl_tendsto60 (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hρ : Integrable id ρ)
    (d a b : ℕ → ℝ) (hd : Tendsto d atTop (𝓝 0)) (ha : ∀ k, SLb60 ρ (a k) = d k)
    (hb : ∀ k, SL60 ρ (b k) = d k) (x : ℝ) (h1 : ρ (Ici x) ≠ 0) (h2 : ρ (Iic x) ≠ 0) :
    Tendsto (fun k => cl60 (a k) (b k) x) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hp1 : 0 < ρ.real (Iic x) := by
    rw [measureReal_def]; exact ENNReal.toReal_pos h2 (measure_ne_top _ _)
  have hp2 : 0 < ρ.real (Ici x) := by
    rw [measureReal_def]; exact ENNReal.toReal_pos h1 (measure_ne_top _ _)
  have q1 : 0 < SLb60 ρ (x + ε / 2) := by
    have key : ∀ y, (Iic x).indicator (fun _ => ε / 2) y ≤ max (x + ε / 2 - y) 0 := by
      intro y
      by_cases hy : y ∈ Iic x
      · rw [indicator_of_mem hy]; exact le_max_of_le_left (by rw [mem_Iic] at hy; linarith)
      · rw [indicator_of_notMem hy]; exact le_max_right _ _
    have := integral_mono ((integrable_const (ε / 2)).indicator measurableSet_Iic)
      (slb_int60 ρ hρ (x + ε / 2)) key
    rw [integral_indicator_const _ measurableSet_Iic, smul_eq_mul] at this
    unfold SLb60
    nlinarith
  have q2 : 0 < SL60 ρ (x - ε / 2) := by
    have key : ∀ y, (Ici x).indicator (fun _ => ε / 2) y ≤ max (y - (x - ε / 2)) 0 := by
      intro y
      by_cases hy : y ∈ Ici x
      · rw [indicator_of_mem hy]; exact le_max_of_le_left (by rw [mem_Ici] at hy; linarith)
      · rw [indicator_of_notMem hy]; exact le_max_right _ _
    have := integral_mono ((integrable_const (ε / 2)).indicator measurableSet_Ici)
      (sl_int60 ρ hρ (x - ε / 2)) key
    rw [integral_indicator_const _ measurableSet_Ici, smul_eq_mul] at this
    unfold SL60
    nlinarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((hd.eventually (gt_mem_nhds q1)).and (hd.eventually (gt_mem_nhds q2)))
  refine ⟨N, fun k hk => ?_⟩
  obtain ⟨hk1, hk2⟩ := hN k hk
  have ha' : a k < x + ε / 2 := by
    by_contra hc; push_neg at hc
    have := slb_mono60 ρ hρ hc; rw [ha k] at this; linarith
  have hb' : x - ε / 2 < b k := by
    by_contra hc; push_neg at hc
    have := sl_anti60 ρ hρ hc; rw [hb k] at this; linarith
  rw [Real.dist_eq, abs_lt]
  unfold cl60
  have u1 : x - ε / 2 ≤ max (a k) (min x (b k)) := le_max_of_le_right (le_min (by linarith) hb'.le)
  have u2 : max (a k) (min x (b k)) ≤ x + ε / 2 :=
    max_le ha'.le ((min_le_left _ _).trans (by linarith))
  constructor <;> linarith

theorem sp_low60 (h w : ℝ) (hh : 0 < h) :
    h * (⌊w / h⌋ : ℝ) ≤ w ∧ w - h < h * (⌊w / h⌋ : ℝ) := by
  have e := Int.floor_add_fract (w / h)
  have e2 : h * (w / h) = w := by field_simp
  have f0 := Int.fract_nonneg (w / h)
  have f1 := Int.fract_lt_one (w / h)
  have hn : h * (⌊w / h⌋ : ℝ) = w - h * Int.fract (w / h) := by linear_combination h * e + e2
  rw [hn]
  constructor
  · nlinarith
  · nlinarith

theorem sp_Ioi_zero60 (h w t : ℝ) (hh : 0 < h) (hw : w + h ≤ t) : sp60 h w (Ioi t) = 0 := by
  rw [sp_apply60 h w _ measurableSet_Ioi]
  obtain ⟨l1, l2⟩ := sp_low60 h w hh
  have n1 : h * (⌊w / h⌋ : ℝ) ∉ Ioi t := by simp only [mem_Ioi, not_lt]; linarith
  have n2 : h * ((⌊w / h⌋ : ℝ) + 1) ∉ Ioi t := by simp only [mem_Ioi, not_lt]; linarith
  simp [indicator_of_notMem n1, indicator_of_notMem n2]

theorem sp_Iic_zero60 (h w t : ℝ) (hh : 0 < h) (hw : t + h ≤ w) : sp60 h w (Iic t) = 0 := by
  rw [sp_apply60 h w _ measurableSet_Iic]
  obtain ⟨l1, l2⟩ := sp_low60 h w hh
  have n1 : h * (⌊w / h⌋ : ℝ) ∉ Iic t := by simp only [mem_Iic, not_le]; linarith
  have n2 : h * ((⌊w / h⌋ : ℝ) + 1) ∉ Iic t := by simp only [mem_Iic, not_le]; linarith
  simp [indicator_of_notMem n1, indicator_of_notMem n2]

theorem sp_real_one60 (h w t : ℝ) (hh : 0 < h) (hw : w + h ≤ t) : (sp60 h w).real (Iic t) = 1 := by
  haveI := sp_prob60 h w
  rw [measureReal_def, ← compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi,
    sp_Ioi_zero60 h w t hh hw]
  simp

theorem sp_real_zero60 (h w t : ℝ) (hh : 0 < h) (hw : t + h ≤ w) : (sp60 h w).real (Iic t) = 0 := by
  rw [measureReal_def, sp_Iic_zero60 h w t hh hw]
  simp

/-- Upper tail of the grid law. -/
theorem tail_hi60 (ν : Measure ℝ) [IsProbabilityMeasure ν] (h α β m t : ℝ) (hh : 0 < h)
    (h1 : h ≤ 1) (hα : α ≤ m) (ht : m + 1 ≤ t) :
    ((ν ⊗ₘ cK60 h α β).snd).real (Ioi t) ≤ ν.real (Ioi (t - 1)) := by
  have hle : (ν ⊗ₘ cK60 h α β).snd (Ioi t) ≤ ν (Ioi (t - 1)) := by
    rw [snd_lint60 ν _ _ measurableSet_Ioi, ← lintegral_indicator_one measurableSet_Ioi]
    refine lintegral_mono fun y => ?_
    rw [cK_apply60]
    by_cases hy : y ∈ Ioi (t - 1)
    · haveI := sp_prob60 h (cl60 α β y)
      rw [indicator_of_mem hy, Pi.one_apply]; exact prob_le_one
    · rw [indicator_of_notMem hy, sp_Ioi_zero60 h _ t hh ?_]
      simp only [mem_Ioi, not_lt] at hy
      unfold cl60
      have : max α (min y β) ≤ t - 1 := max_le (by linarith) ((min_le_left _ _).trans hy)
      linarith
  rw [measureReal_def, measureReal_def]
  exact ENNReal.toReal_mono (measure_ne_top _ _) hle

/-- Lower tail of the grid law. -/
theorem tail_lo60 (ν : Measure ℝ) [IsProbabilityMeasure ν] (h α β m t : ℝ) (hh : 0 < h)
    (h1 : h ≤ 1) (hβ : m ≤ β) (ht : 1 - t ≤ m) :
    ((ν ⊗ₘ cK60 h α β).snd).real (Iic (-t)) ≤ ν.real (Iic (-(t - 1))) := by
  have hle : (ν ⊗ₘ cK60 h α β).snd (Iic (-t)) ≤ ν (Iic (-(t - 1))) := by
    rw [snd_lint60 ν _ _ measurableSet_Iic, ← lintegral_indicator_one measurableSet_Iic]
    refine lintegral_mono fun y => ?_
    rw [cK_apply60]
    by_cases hy : y ∈ Iic (-(t - 1))
    · haveI := sp_prob60 h (cl60 α β y)
      rw [indicator_of_mem hy, Pi.one_apply]; exact prob_le_one
    · rw [indicator_of_notMem hy, sp_Iic_zero60 h _ (-t) hh ?_]
      simp only [mem_Iic, not_le] at hy
      unfold cl60
      have : 1 - t ≤ max α (min y β) := le_max_of_le_right (le_min (by linarith) (by linarith))
      linarith
  rw [measureReal_def, measureReal_def]
  exact ENNReal.toReal_mono (measure_ne_top _ _) hle

/-- Convergence of the grid cdfs at continuity points. -/
theorem cdf_conv60 (ν : Measure ℝ) [IsProbabilityMeasure ν] (h a b : ℕ → ℝ) (hh : ∀ k, 0 < h k)
    (hh0 : Tendsto h atTop (𝓝 0))
    (hcl : ∀ᵐ y ∂ν, Tendsto (fun k => cl60 (a k) (b k) y) atTop (𝓝 y))
    (t : ℝ) (ht : ν {t} = 0) :
    Tendsto (fun k => ((ν ⊗ₘ cK60 (h k) (a k) (b k)).snd).real (Iic t)) atTop
      (𝓝 (ν.real (Iic t))) := by
  have e : ∀ k, ((ν ⊗ₘ cK60 (h k) (a k) (b k)).snd).real (Iic t) =
      ∫ y, (cK60 (h k) (a k) (b k) y).real (Iic t) ∂ν := fun k =>
    snd_realA60 ν _ _ measurableSet_Iic
  simp only [e]
  rw [← integral_indicator_one measurableSet_Iic]
  have hne : ∀ᵐ y ∂ν, y ≠ t := by
    rw [ae_iff]; simpa using ht
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun k => ((Kernel.measurable_coe _ measurableSet_Iic).ennreal_toReal).aestronglyMeasurable)
    (integrable_const 1) (fun k => Eventually.of_forall fun y => ?_) ?_
  · rw [Real.norm_of_nonneg measureReal_nonneg]
    haveI := sp_prob60 (h k) (cl60 (a k) (b k) y)
    exact measureReal_le_one
  · filter_upwards [hcl, hne] with y hy hyt
    rcases lt_or_gt_of_ne hyt with hlt | hgt
    · rw [indicator_of_mem (mem_Iic.2 hlt.le), Pi.one_apply]
      have hδ : 0 < (t - y) / 2 := by linarith
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hy.eventually (gt_mem_nhds (show y < y + (t - y) / 2 by linarith)),
        hh0.eventually (gt_mem_nhds hδ)] with k hk1 hk2
      rw [cK_apply60, sp_real_one60 _ _ _ (hh k) (by linarith)]
    · rw [indicator_of_notMem (fun hm => absurd (mem_Iic.1 hm) (not_le.2 hgt)), ]
      have hδ : 0 < (y - t) / 2 := by linarith
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hy.eventually (lt_mem_nhds (show y - (y - t) / 2 < y by linarith)),
        hh0.eventually (gt_mem_nhds hδ)] with k hk1 hk2
      rw [cK_apply60, sp_real_zero60 _ _ _ (hh k) (by linarith)]

/-- Consequences of the convex order. -/
theorem cx_facts60 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable id μ) (hν : Integrable id ν)
    (hcx : StochasticOrders.Convex.ConvexOrder μ ν id id) :
    ∫ x, x ∂μ = ∫ x, x ∂ν ∧ (∀ a, SL60 μ a ≤ SL60 ν a) ∧ (∀ a, SLb60 μ a ≤ SLb60 ν a) := by
  have hlin : ∀ c : ℝ, ConvexOn ℝ Set.univ (fun x : ℝ => c * x) := by
    intro c
    refine ⟨convex_univ, fun x _ y _ s t _ _ hst => ?_⟩
    simp only [smul_eq_mul]
    nlinarith
  have haff : ∀ c e : ℝ, ConvexOn ℝ Set.univ (fun x : ℝ => max (c * x + e) 0) := by
    intro c e
    have h1 : ConvexOn ℝ Set.univ (fun x : ℝ => c * x + e) := by
      refine ⟨convex_univ, fun x _ y _ s t _ _ hst => ?_⟩
      simp only [smul_eq_mul]
      have : s * (c * x + e) + t * (c * y + e) = c * (s * x + t * y) + (s + t) * e := by ring
      rw [this, hst]; linarith
    exact h1.sup (convexOn_const 0 convex_univ)
  refine ⟨?_, fun a => ?_, fun a => ?_⟩
  · have h1 := hcx (fun x => 1 * x) (hlin 1) (hμ.const_mul 1) (hν.const_mul 1)
    have h2 := hcx (fun x => -1 * x) (hlin (-1)) (hμ.const_mul (-1)) (hν.const_mul (-1))
    simp only [id, one_mul, neg_one_mul] at h1 h2
    have n1 : ∫ ω, -ω ∂μ = -∫ ω, ω ∂μ := integral_neg (fun ω => ω)
    have n2 : ∫ ω, -ω ∂ν = -∫ ω, ω ∂ν := integral_neg (fun ω => ω)
    linarith
  · have h := hcx (fun x => max (1 * x + -a) 0) (haff 1 (-a))
      (by simpa [sub_eq_add_neg] using sl_int60 μ hμ a)
      (by simpa [sub_eq_add_neg] using sl_int60 ν hν a)
    simp only [id, one_mul, ← sub_eq_add_neg] at h
    exact h
  · have h := hcx (fun x => max (-1 * x + a) 0) (haff (-1) a)
      (by simpa [neg_add_eq_sub] using slb_int60 μ hμ a)
      (by simpa [neg_add_eq_sub] using slb_int60 ν hν a)
    simp only [id, neg_one_mul, neg_add_eq_sub] at h
    exact h

/-- Degenerate case: `μ` is a point mass. -/
theorem degen60 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable id μ) (hν : Integrable id ν) (m : ℝ) (hmμ : ∫ x, x ∂μ = m)
    (hmν : ∫ x, x ∂ν = m) (h0 : SL60 μ m = 0) : ∃ κ : Kernel ℝ ℝ, IsMonoMartCoupling60 μ ν κ := by
  have hb : SLb60 μ m = 0 := by
    have := sl_sub_slb60 μ hμ m; rw [hmμ] at this; linarith
  have hae : ∀ᵐ x ∂μ, x = m := by
    have i := (sl_int60 μ hμ m).add (slb_int60 μ hμ m)
    have hz : ∫ x, (max (x - m) 0 + max (m - x) 0) ∂μ = 0 := by
      rw [integral_add (sl_int60 μ hμ m) (slb_int60 μ hμ m)]
      unfold SL60 at h0; unfold SLb60 at hb; rw [h0, hb]; simp
    rw [integral_eq_zero_iff_of_nonneg
      (fun x => add_nonneg (le_max_right _ _) (le_max_right _ _)) i] at hz
    filter_upwards [hz] with x hx
    simp only [Pi.zero_apply] at hx
    have a1 := le_max_left (x - m) 0
    have a2 := le_max_left (m - x) 0
    have b1 := le_max_right (x - m) 0
    have b2 := le_max_right (m - x) 0
    linarith
  refine ⟨Kernel.const ℝ ν, inferInstance, ?_, ?_, fun _ _ _ _ => le_rfl⟩
  · filter_upwards [hae] with x hx
    rw [Kernel.const_apply, hx]
    exact ⟨hν, hmν⟩
  · rw [Measure.compProd_const, Measure.snd_prod]

theorem one_div_le60 (k : ℕ) : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
  rw [div_le_one (by positivity)]
  have := k.cast_nonneg (α := ℝ)
  linarith

/-- K: convex order of integrable laws gives a monotone martingale kernel. -/
theorem k_core60A (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable id μ) (hν : Integrable id ν)
    (hcx : StochasticOrders.Convex.ConvexOrder μ ν id id) :
    ∃ κ : Kernel ℝ ℝ, IsMonoMartCoupling60 μ ν κ := by
  obtain ⟨hmean, hf, hg⟩ := cx_facts60 μ ν hμ hν hcx
  obtain ⟨m, hmμ⟩ : ∃ m, ∫ x, x ∂μ = m := ⟨_, rfl⟩
  have hmν : ∫ x, x ∂ν = m := hmean ▸ hmμ
  obtain ⟨D0, hD0⟩ : ∃ D0, SL60 μ m = D0 := ⟨_, rfl⟩
  have hD0nn : 0 ≤ D0 := by
    rw [← hD0]; unfold SL60; exact integral_nonneg fun x => le_max_right _ _
  rcases hD0nn.lt_or_eq with hpos | hzero
  swap
  · exact degen60 μ ν hμ hν m hmμ hmν (hD0.trans hzero.symm)
  have hbμ : SLb60 μ m = D0 := by
    have := sl_sub_slb60 μ hμ m; rw [hmμ] at this; linarith
  have hbν : D0 ≤ SLb60 ν m := hbμ ▸ hg m
  have haν : D0 ≤ SL60 ν m := hD0 ▸ hf m
  -- the stop-loss levels and the mesh
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℝ, ∀ k, d k = D0 / 2 * (1 / ((k : ℝ) + 1)) := ⟨_, fun k => rfl⟩
  have hd0 : ∀ k, 0 < d k := fun k => by
    rw [hd]; exact mul_pos (half_pos hpos) (by positivity)
  have hdD : ∀ k, d k ≤ D0 := fun k => by
    rw [hd]; have := one_div_le60 k; have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    nlinarith
  have hdt : Tendsto d atTop (𝓝 0) := by
    have e : d = fun k : ℕ => D0 / 2 * (1 / ((k : ℝ) + 1)) := funext hd
    rw [e]
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (D0 / 2)
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → ℝ, ∀ k, δ k = 1 / ((k : ℝ) + 1) := ⟨_, fun k => rfl⟩
  have hδ0 : ∀ k, 0 < δ k := fun k => by rw [hδ]; positivity
  have hδ1 : ∀ k, δ k ≤ 1 := fun k => by rw [hδ]; exact one_div_le60 k
  have hδt : Tendsto δ atTop (𝓝 0) := by
    have e : δ = fun k : ℕ => 1 / ((k : ℝ) + 1) := funext hδ
    rw [e]; exact tendsto_one_div_add_atTop_nhds_zero_nat
  choose αμ hαμ1 hαμ2 using fun k => exists_alpha60 μ hμ m (d k) (hd0 k) (hbμ ▸ hdD k)
  choose βμ hβμ1 hβμ2 using fun k => exists_beta60 μ hμ m (d k) (hd0 k) (hD0 ▸ hdD k)
  choose αν hαν1 hαν2 using fun k => exists_alpha60 ν hν m (d k) (hd0 k) ((hdD k).trans hbν)
  choose βν hβν1 hβν2 using fun k => exists_beta60 ν hν m (d k) (hd0 k) ((hdD k).trans haν)
  have hab : ∀ k, αμ k ≤ βμ k := fun k => (hαμ1 k).trans (hβμ1 k)
  have habν : ∀ k, αν k ≤ βν k := fun k => (hαν1 k).trans (hβν1 k)
  -- the finite problems and their C2 kernels
  choose κ hκ using fun k => Fin60.c2_core ((μ ⊗ₘ cK60 (δ k) (αμ k) (βμ k)).snd)
    ((ν ⊗ₘ cK60 (δ k) (αν k) (βν k)).snd)
    (gridF60 (δ k) (min (αμ k) (αν k)) (max (βμ k) (βν k)))
    (grid_supp60 μ (δ k) (hδ0 k) _ _ _ _ (hab k) (min_le_left _ _) (le_max_left _ _))
    (grid_supp60 ν (δ k) (hδ0 k) _ _ _ _ (habν k) (min_le_right _ _) (le_max_right _ _))
    (hyp_grid60 μ ν hμ hν m hmμ hmν hf hg (d k) (αμ k) (βμ k) (αν k) (βν k) (hαμ1 k) (hβμ1 k)
      (hαν1 k) (hβν1 k) (hαμ2 k) (hβμ2 k) (hαν2 k) (hβν2 k) (δ k) (hδ0 k) _ _ (min_le_left _ _)
      (min_le_right _ _) (le_max_left _ _) (le_max_right _ _))
  haveI hκm : ∀ k, IsMarkovKernel (κ k) := fun k => (hκ k).1
  have hmarg : ∀ k, (μ ⊗ₘ LK60 (κ k) (δ k) (αμ k) (βμ k)).snd =
      (ν ⊗ₘ cK60 (δ k) (αν k) (βν k)).snd := fun k =>
    LK_marg60 μ (κ k) (δ k) _ _ _ (hκ k).2.2.1
  have hmono : ∀ k x₁ x₂, x₁ ≤ x₂ → ∀ t, (LK60 (κ k) (δ k) (αμ k) (βμ k) x₂).real (Iic t) ≤
      (LK60 (κ k) (δ k) (αμ k) (βμ k) x₁).real (Iic t) :=
    fun k x₁ x₂ hx t => LK_mono60 (κ k) (δ k) _ _ (hδ0 k) (hκ k).2.2.2 x₁ x₂ hx t
  have hmeanae : ∀ k, ∀ᵐ x ∂μ, Integrable id (LK60 (κ k) (δ k) (αμ k) (βμ k) x) ∧
      ∫ y, y ∂(LK60 (κ k) (δ k) (αμ k) (βμ k) x) = cl60 (αμ k) (βμ k) x :=
    fun k => ae_mean60 μ (κ k) (δ k) _ _ _ _ (hδ0 k) (hab k) le_rfl le_rfl (hκ k).2.1
  have hlimx : ∀ᵐ x ∂μ, Tendsto (fun k => ∫ y, y ∂(LK60 (κ k) (δ k) (αμ k) (βμ k) x)) atTop
      (𝓝 x) := by
    filter_upwards [ae_all_iff.2 hmeanae, C4L60.ae_pos_Ici60 μ, C4L60.ae_pos_Iic60 μ]
      with x hx h1 h2
    exact (cl_tendsto60 μ hμ d αμ βμ hdt hαμ2 hβμ2 x h1 h2).congr fun k => ((hx k).2).symm
  have hposlo : ∀ k, 0 < μ (Iic (αμ k)) := fun k =>
    Iic_pos60 μ _ (by rw [hαμ2 k]; exact hd0 k)
  have hposhi : ∀ k, 0 < μ (Ici (βμ k)) := fun k =>
    Ici_pos60 μ _ (by rw [hβμ2 k]; exact hd0 k)
  have elo := fun k => end_lo60 μ (κ k) (δ k) _ _ (hδ0 k) (hab k) (hposlo k) (hκ k).2.1
  have ehi := fun k => end_hi60 μ (κ k) (δ k) _ _ (hδ0 k) (hab k) (hposhi k) (hκ k).2.1
  obtain ⟨hint, hM⟩ := C4L60.c4_bounds60 μ (fun k => LK60 (κ k) (δ k) (αμ k) (βμ k)) hmono
    αμ βμ hab (fun k x => LK_clamp60 (κ k) (δ k) _ _ (hab k) x) (fun k => (elo k).1)
    (fun k => (ehi k).1) (fun k => (elo k).2) (fun k => (ehi k).2)
    (fun k x hx => by
      by_contra hc; push_neg at hc
      exact (hposlo k).ne' (measure_mono_null (Iic_subset_Iic.2 hc.le) hx))
    (fun k x hx => by
      by_contra hc; push_neg at hc
      exact (hposhi k).ne' (measure_mono_null (Ici_subset_Ici.2 hc.le) hx))
    hlimx
  -- the tail bound
  obtain ⟨t1, t2⟩ := C4L60.tails_int60 ν hν
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = (Ioi 0).indicator (fun s => ν.real (Ioi s)) := ⟨_, rfl⟩
  obtain ⟨F', hF'⟩ : ∃ F' : ℝ → ℝ, F' = (Ioi 0).indicator (fun s => ν.real (Iic (-s))) :=
    ⟨_, rfl⟩
  obtain ⟨T0, hT0⟩ : ∃ T0 : ℝ, T0 = |m| + 2 := ⟨_, rfl⟩
  obtain ⟨g0, hg0⟩ : ∃ g0 : ℝ → ℝ,
      g0 = fun t => (Ioc 0 T0).indicator 1 t + F (t - 1) + F' (t - 1) := ⟨_, rfl⟩
  have hF0 : ∀ s, 0 ≤ F s := fun s => by
    rw [hF]; exact indicator_nonneg (fun _ _ => measureReal_nonneg) s
  have hF0' : ∀ s, 0 ≤ F' s := fun s => by
    rw [hF']; exact indicator_nonneg (fun _ _ => measureReal_nonneg) s
  have hgi : IntegrableOn g0 (Ioi 0) := by
    have i1 : Integrable ((Ioc (0 : ℝ) T0).indicator (1 : ℝ → ℝ)) :=
      (integrable_indicator_iff measurableSet_Ioc).2
        (continuous_one.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    have i2 : Integrable F := by rw [hF]; exact (integrable_indicator_iff measurableSet_Ioi).2 t1
    have i3 : Integrable F' := by
      rw [hF']; exact (integrable_indicator_iff measurableSet_Ioi).2 t2
    rw [hg0]
    exact ((i1.add (i2.comp_sub_right 1)).add (i3.comp_sub_right 1)).integrableOn
  have hgt : Tendsto g0 atTop (𝓝 0) := by
    have l1 : Tendsto (fun s => ν.real (Ioi s)) atTop (𝓝 0) := by
      have e : (fun s => ν.real (Ioi s)) = fun s => 1 - cdf ν s := funext fun s => by
        rw [cdf_eq_real, ← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ]
      rw [e]; simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_cdf_atTop ν)
    have l2 : Tendsto (fun s => ν.real (Iic (-s))) atTop (𝓝 0) := by
      have e : (fun s => ν.real (Iic (-s))) = fun s => cdf ν (-s) := funext fun s => by
        rw [cdf_eq_real]
      rw [e]; exact (tendsto_cdf_atBot ν).comp tendsto_neg_atTop_atBot
    have hs : Tendsto (fun t : ℝ => t - 1) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id
    have l := (l1.comp hs).add (l2.comp hs)
    rw [add_zero] at l
    refine l.congr' ?_
    filter_upwards [eventually_gt_atTop (T0 + 1)] with t ht
    have ht1 : t - 1 ∈ Ioi (0 : ℝ) := by
      rw [mem_Ioi]; have : 0 ≤ |m| := abs_nonneg m; linarith
    have ht2 : t ∉ Ioc 0 T0 := fun hm => by linarith [hm.2]
    rw [hg0]
    simp only [Function.comp_apply, hF, hF', indicator_of_mem ht1, indicator_of_notMem ht2]
    ring
  have hνk : ∀ k t, 0 < t →
      ((μ ⊗ₘ LK60 (κ k) (δ k) (αμ k) (βμ k)).snd).real (Ioi t) ≤ g0 t ∧
      ((μ ⊗ₘ LK60 (κ k) (δ k) (αμ k) (βμ k)).snd).real (Iic (-t)) ≤ g0 t := by
    intro k t ht
    rw [hmarg k]
    have hFt := hF0 (t - 1)
    have hFt' := hF0' (t - 1)
    by_cases hT : t ≤ T0
    · have hi : (Ioc 0 T0).indicator (1 : ℝ → ℝ) t = 1 := by
        rw [indicator_of_mem (show t ∈ Ioc 0 T0 from ⟨ht, hT⟩), Pi.one_apply]
      have b1 : 1 ≤ g0 t := by rw [hg0]; dsimp only; rw [hi]; linarith
      exact ⟨measureReal_le_one.trans b1, measureReal_le_one.trans b1⟩
    · push_neg at hT
      have ht1 : t - 1 ∈ Ioi (0 : ℝ) := by
        rw [mem_Ioi]; have : 0 ≤ |m| := abs_nonneg m; linarith
      have hi : (Ioc 0 T0).indicator (1 : ℝ → ℝ) t = 0 :=
        indicator_of_notMem (fun hm => by linarith [hm.2]) _
      have eF : F (t - 1) = ν.real (Ioi (t - 1)) := by rw [hF, indicator_of_mem ht1]
      have eF' : F' (t - 1) = ν.real (Iic (-(t - 1))) := by rw [hF', indicator_of_mem ht1]
      have hm1 : m + 1 ≤ t := by have := le_abs_self m; linarith
      have hm2 : 1 - t ≤ m := by have := neg_abs_le m; linarith
      have u1 := tail_hi60 ν (δ k) (αν k) (βν k) m t (hδ0 k) (hδ1 k) (hαν1 k) hm1
      have u2 := tail_lo60 ν (δ k) (αν k) (βν k) m t (hδ0 k) (hδ1 k) (hβν1 k) hm2
      have eg : g0 t = F (t - 1) + F' (t - 1) := by rw [hg0]; dsimp only; rw [hi, zero_add]
      rw [eg, eF, eF']
      constructor <;> linarith
  have hclν : ∀ᵐ y ∂ν, Tendsto (fun k => cl60 (αν k) (βν k) y) atTop (𝓝 y) := by
    filter_upwards [C4L60.ae_pos_Ici60 ν, C4L60.ae_pos_Iic60 ν] with y h1 h2
    exact cl_tendsto60 ν hν d αν βν hdt hαν2 hβν2 y h1 h2
  have hcdf : ∀ t, ν {t} = 0 → Tendsto
      (fun k => ((μ ⊗ₘ LK60 (κ k) (δ k) (αμ k) (βμ k)).snd).real (Iic t)) atTop
      (𝓝 (ν.real (Iic t))) := by
    intro t ht
    simp only [hmarg]
    exact cdf_conv60 ν δ αν βν hδ0 hδt hclν t ht
  exact C4L60.c4_full60 μ ν (fun k => LK60 (κ k) (δ k) (αμ k) (βμ k)) hmono hint hM hlimx g0 hgi
    hgt hνk hcdf

end A60

end PartA

open MeasureTheory ProbabilityTheory in
/-- C1 (← direction of 60df9050): a martingale coupling gives the convex order. -/
theorem c1_convexOrder_of_martingale {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (Y : Ω' → ℝ)
    (hYint : Integrable Y ν)
    {Ω'' : Type} [MeasurableSpace Ω''] (ρ : Measure Ω'') [IsProbabilityMeasure ρ]
    (Xhat Yhat : Ω'' → ℝ) (hXh : Measurable Xhat)
    (hIX : IdentDistrib Xhat X ρ μ) (hIY : IdentDistrib Yhat Y ρ ν)
    (hmart : ρ[Yhat | MeasurableSpace.comap Xhat inferInstance] =ᵐ[ρ] Xhat) :
    StochasticOrders.Convex.ConvexOrder μ ν X Y := by
  intro φ hφ hφX hφY
  have hcont : Continuous φ := continuousOn_univ.1 (hφ.continuousOn isOpen_univ)
  have hm : MeasurableSpace.comap Xhat inferInstance ≤ (inferInstance : MeasurableSpace Ω'') :=
    hXh.comap_le
  have hIXφ := hIX.comp hcont.measurable
  have hIYφ := hIY.comp hcont.measurable
  have hYh : Integrable Yhat ρ := hIY.integrable_iff.2 hYint
  have hφYh : Integrable (φ ∘ Yhat) ρ := hIYφ.integrable_iff.2 hφY
  have hφXh : Integrable (φ ∘ Xhat) ρ := hIXφ.integrable_iff.2 hφX
  show ∫ ω, (φ ∘ X) ω ∂μ ≤ ∫ ω, (φ ∘ Y) ω ∂ν
  rw [← hIXφ.integral_eq, ← hIYφ.integral_eq]
  have hJ := hφ.map_condExp_le_univ hm hcont.lowerSemicontinuous hYh hφYh
  have h1 : (φ ∘ Xhat) ≤ᵐ[ρ] ρ[φ ∘ Yhat | MeasurableSpace.comap Xhat inferInstance] := by
    filter_upwards [hJ, hmart] with ω h1 h2
    simpa [Function.comp, h2] using h1
  calc ∫ ω, (φ ∘ Xhat) ω ∂ρ ≤ ∫ ω, (ρ[φ ∘ Yhat | MeasurableSpace.comap Xhat inferInstance]) ω ∂ρ :=
        integral_mono_ae hφXh integrable_condExp h1
    _ = ∫ ω, (φ ∘ Yhat) ω ∂ρ := integral_condExp hm

open MeasureTheory ProbabilityTheory in
/-- K (Kellerer / Müller–Rüschendorf core, OPEN): convex order of integrable laws gives a
monotone martingale kernel. -/
theorem k_core60 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable id μ) (hν : Integrable id ν)
    (hcx : StochasticOrders.Convex.ConvexOrder μ ν id id) :
    ∃ κ : Kernel ℝ ℝ, IsMonoMartCoupling60 μ ν κ := by
  exact A60.k_core60A μ ν hμ hν hcx

open MeasureTheory ProbabilityTheory in
/-- Transport of the convex order to the laws. -/
theorem cx_map60 {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (h : StochasticOrders.Convex.ConvexOrder μ ν X Y) :
    StochasticOrders.Convex.ConvexOrder (μ.map X) (ν.map Y) id id := by
  intro φ hφ hφX hφY
  have hcont : Continuous φ := continuousOn_univ.1 (hφ.continuousOn isOpen_univ)
  have e1 : Integrable (φ ∘ X) μ :=
    (integrable_map_measure hcont.aestronglyMeasurable hX.aemeasurable).1 hφX
  have e2 : Integrable (φ ∘ Y) ν :=
    (integrable_map_measure hcont.aestronglyMeasurable hY.aemeasurable).1 hφY
  have := h φ hφ e1 e2
  simp only [id]
  rw [integral_map hX.aemeasurable hcont.aestronglyMeasurable,
    integral_map hY.aemeasurable hcont.aestronglyMeasurable]
  exact this

open MeasureTheory ProbabilityTheory in
/-- C5: a monotone martingale kernel for the laws gives the random-variable witness. -/
theorem c5_witness60 {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXint : Integrable X μ) (hYint : Integrable Y ν) (κ : Kernel ℝ ℝ) (hκ : IsMonoMartCoupling60 (μ.map X) (ν.map Y) κ) :
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Xhat Yhat : Ω'' → ℝ),
        Measurable Xhat ∧ Measurable Yhat ∧
        IdentDistrib Xhat X ρ μ ∧ IdentDistrib Yhat Y ρ ν ∧
        ρ[Yhat | MeasurableSpace.comap Xhat inferInstance] =ᵐ[ρ] Xhat ∧
        ∃ κ : Kernel ℝ ℝ, IsMarkovKernel κ ∧
          ρ.map (fun ω => (Xhat ω, Yhat ω)) = (ρ.map Xhat) ⊗ₘ κ ∧
          ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → ∀ t : ℝ, κ x₁ {y : ℝ | t < y} ≤ κ x₂ {y : ℝ | t < y} := by
  obtain ⟨hmk, hmean, hsnd, hmono⟩ := hκ
  have := hmk
  have : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  set ρ : Measure (ℝ × ℝ) := (μ.map X) ⊗ₘ κ with hρ
  have hfst : ρ.map Prod.fst = μ.map X := by
    show ρ.fst = _
    exact Measure.fst_compProd _ _
  have hsnd' : ρ.map Prod.snd = ν.map Y := hsnd
  have hIX : IdentDistrib Prod.fst X ρ μ :=
    ⟨measurable_fst.aemeasurable, hX.aemeasurable, hfst⟩
  have hIY : IdentDistrib Prod.snd Y ρ ν :=
    ⟨measurable_snd.aemeasurable, hY.aemeasurable, hsnd'⟩
  have hsndint : Integrable Prod.snd ρ := hIY.integrable_iff.2 hYint
  have hfstint : Integrable Prod.fst ρ := hIX.integrable_iff.2 hXint
  have hm : MeasurableSpace.comap (Prod.fst : ℝ × ℝ → ℝ) inferInstance ≤
      (inferInstance : MeasurableSpace (ℝ × ℝ)) := measurable_fst.comap_le
  refine ⟨ℝ × ℝ, inferInstance, ρ, inferInstance, Prod.fst, Prod.snd, measurable_fst,
    measurable_snd, hIX, hIY, ?_, κ, hmk, ?_, hmono⟩
  · have hfm : Measurable[MeasurableSpace.comap (Prod.fst : ℝ × ℝ → ℝ) inferInstance]
        (Prod.fst : ℝ × ℝ → ℝ) := Measurable.of_comap_le le_rfl
    symm
    refine ae_eq_condExp_of_forall_setIntegral_eq hm hsndint ?_ ?_
      hfm.stronglyMeasurable.aestronglyMeasurable
    · intro s _ _
      exact hfstint.integrableOn
    · intro s hs _
      obtain ⟨B, hB, rfl⟩ := hs
      have hsB : Prod.fst ⁻¹' B = B ×ˢ (Set.univ : Set ℝ) := by ext; simp
      rw [hsB, Measure.setIntegral_compProd hB MeasurableSet.univ hfstint.integrableOn,
        Measure.setIntegral_compProd hB MeasurableSet.univ hsndint.integrableOn]
      simp only [Measure.restrict_univ]
      refine setIntegral_congr_ae hB ?_
      filter_upwards [hmean] with x hx _
      simp [hx.2]
  · rw [hfst]
    have hid : (fun ω : ℝ × ℝ => (ω.1, ω.2)) = id := rfl
    rw [hid, Measure.map_id]

section PartIcx8e
open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Icx8e

/-- T1: a floor `q` lifting the mean of `X` to any larger value `m`. -/
theorem exists_floor_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hXint : Integrable X μ)
    (m : ℝ) (hm : ∫ ω, X ω ∂μ < m) : ∃ q : ℝ, ∫ ω, max (X ω) q ∂μ = m := by
  have hint : ∀ a : ℝ, Integrable (fun ω => max (X ω) a) μ := fun a =>
    Integrable.mono' (hXint.abs.add (integrable_const |a|))
      ((continuous_id.max continuous_const).comp_aestronglyMeasurable hXint.aestronglyMeasurable)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        show |max (X ω) a| ≤ |X ω| + |a|
        exact (abs_max_le_max_abs_abs).trans
          (max_le (by linarith [abs_nonneg a]) (by linarith [abs_nonneg (X ω)])))
  set F : ℝ → ℝ := fun a => ∫ ω, max (X ω) a ∂μ with hF
  have hlim : Tendsto F atBot (𝓝 (∫ ω, X ω ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun ω => |X ω|) ?_ ?_ hXint.abs ?_
    · exact Eventually.of_forall fun a => (hint a).aestronglyMeasurable
    · filter_upwards [eventually_le_atBot (0:ℝ)] with a ha
      refine Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs]
      rcases le_total (X ω) a with h | h
      · rw [max_eq_right h]
        exact abs_le.2 ⟨by linarith [neg_abs_le (X ω)], by linarith [abs_nonneg (X ω)]⟩
      · rw [max_eq_left h]
    · refine Eventually.of_forall fun ω => tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_le_atBot (X ω)] with a ha
      exact (max_eq_left ha).symm
  obtain ⟨a0, ha0, ha0m⟩ := ((hlim.eventually (gt_mem_nhds hm)).and
    (eventually_le_atBot m)).exists
  have hFm : m ≤ F m := by
    have := integral_mono (integrable_const m) (hint m) (fun ω => le_max_right (X ω) m)
    simpa using this
  have hcont : ContinuousOn F (Icc a0 m) := by
    refine continuousOn_of_dominated (bound := fun ω => |X ω| + |a0| + |m|)
      (fun a _ => (hint a).aestronglyMeasurable) ?_
      ((hXint.abs.add (integrable_const _)).add (integrable_const _)) ?_
    · intro a ha
      refine Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have := le_max_right (X ω) a
        linarith [neg_abs_le a0, abs_nonneg (X ω), abs_nonneg m, ha.1]
      · exact max_le (by linarith [le_abs_self (X ω), abs_nonneg a0, abs_nonneg m])
          (by linarith [le_abs_self m, abs_nonneg a0, abs_nonneg (X ω), ha.2])
    · exact Eventually.of_forall fun ω => (continuous_const.max continuous_id).continuousOn
  obtain ⟨q, -, hq⟩ := intermediate_value_Icc ha0m hcont ⟨ha0.le, hFm⟩
  exact ⟨q, hq⟩

theorem hinge_convex (a : ℝ) : ConvexOn ℝ Set.univ (fun x : ℝ => max (x - a) 0) := by
  have h1 : ConvexOn ℝ Set.univ (fun x : ℝ => x - a) := by
    refine ⟨convex_univ, fun x _ y _ s t _ _ hst => ?_⟩
    simp only [smul_eq_mul]
    have : s * (x - a) + t * (y - a) = s * x + t * y - (s + t) * a := by ring
    rw [this, hst]; linarith
  have h2 : ConvexOn ℝ Set.univ (fun _ : ℝ => (0:ℝ)) := convexOn_const 0 convex_univ
  exact h1.sup h2

theorem hinge_mono (a : ℝ) : Monotone (fun x : ℝ => max (x - a) 0) :=
  fun x y h => max_le_max (by linarith) le_rfl

/-- stop-loss inequalities from the increasing convex order. -/
theorem sl_of_icx {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ)
    (hXint : Integrable X μ) (hYint : Integrable Y ν)
    (hicx : StochasticOrders.MonotoneConvex.IcxOrder μ ν X Y) (a : ℝ) :
    ∫ ω, max (X ω - a) 0 ∂μ ≤ ∫ ω, max (Y ω - a) 0 ∂ν :=
  hicx (fun x => max (x - a) 0) (hinge_mono a) (hinge_convex a)
    (hXint.sub (integrable_const a)).pos_part (hYint.sub (integrable_const a)).pos_part

/-- T2: a monotone lift `m ≥ id` with `m ∘ X ≤cx Y`. -/
theorem exists_lift {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hXint : Integrable X μ) (hYint : Integrable Y ν)
    (hicx : StochasticOrders.MonotoneConvex.IcxOrder μ ν X Y) :
    ∃ m : ℝ → ℝ, Measurable m ∧ Monotone m ∧ (∀ x, x ≤ m x) ∧ (∃ C : ℝ, ∀ x, |m x| ≤ |x| + C) ∧
      StochasticOrders.Convex.ConvexOrder μ ν (fun ω => m (X ω)) Y := by
  have hle : ∫ ω, X ω ∂μ ≤ ∫ ω, Y ω ∂ν := by
    have := hicx id monotone_id (convexOn_id convex_univ) hXint hYint
    simpa using this
  rcases hle.lt_or_eq with hlt | heq
  · obtain ⟨q, hq⟩ := exists_floor_mean μ X hXint _ hlt
    have hZint : Integrable (fun ω => max (X ω) q) μ :=
      Integrable.mono' (hXint.abs.add (integrable_const |q|))
        ((continuous_id.max continuous_const).comp_aestronglyMeasurable hXint.aestronglyMeasurable)
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs]
          show |max (X ω) q| ≤ |X ω| + |q|
          exact (abs_max_le_max_abs_abs).trans
            (max_le (by linarith [abs_nonneg q]) (by linarith [abs_nonneg (X ω)])))
    refine ⟨fun x => max x q, (continuous_id.max continuous_const).measurable,
      fun x y h => max_le_max h le_rfl, fun x => le_max_left x q, ⟨|q|, fun x =>
        (abs_max_le_max_abs_abs).trans
          (max_le (by linarith [abs_nonneg q]) (by linarith [abs_nonneg x]))⟩, ?_⟩
    refine cxo_key μ ν _ Y hZint hYint hq ?_
    intro a
    rcases le_total q a with hqa | haq
    · have e : ∀ x : ℝ, max (max x q - a) 0 = max (x - a) 0 := by
        intro x
        rcases le_total x q with h | h
        · rw [max_eq_right h, max_eq_right (by linarith : q - a ≤ 0),
            max_eq_right (by linarith : x - a ≤ 0)]
        · rw [max_eq_left h]
      simp only [e]
      exact sl_of_icx μ ν X Y hXint hYint hicx a
    · have e : ∀ x : ℝ, max (max x q - a) 0 = max x q - a := by
        intro x
        exact max_eq_left (by linarith [le_max_right x q])
      simp only [e]
      rw [integral_sub hZint (integrable_const a), hq]
      have h2 : ∫ ω, Y ω ∂ν - a = ∫ ω, (Y ω - a) ∂ν := by
        rw [integral_sub hYint (integrable_const a)]
        simp
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      rw [h2]
      exact integral_mono (hYint.sub (integrable_const a))
        (hYint.sub (integrable_const a)).pos_part (fun ω => le_max_left _ _)
  · refine ⟨id, measurable_id, monotone_id, fun x => le_rfl, ⟨0, fun x => by simp⟩, ?_⟩
    exact cxo_key μ ν X Y hXint hYint heq (sl_of_icx μ ν X Y hXint hYint hicx)

/-- kernel composition commutes with a lift. -/
theorem comp_comap (μ : Measure ℝ) (κ : Kernel ℝ ℝ) (m : ℝ → ℝ) (hm : Measurable m) :
    (κ.comap m hm) ∘ₘ μ = κ ∘ₘ (μ.map m) := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map (κ.measurable_coe hs) hm]
  rfl

/-- T3: a monotone martingale kernel for the lifted law gives the submartingale witness. -/
theorem witness {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXint : Integrable X μ) (hYint : Integrable Y ν)
    (m : ℝ → ℝ) (hmm : Measurable m) (hmono : Monotone m) (hge : ∀ x, x ≤ m x) (C : ℝ)
    (hC : ∀ x, |m x| ≤ |x| + C)
    (κ₂ : Kernel ℝ ℝ) (hκ : IsMonoMartCoupling60 ((μ.map X).map m) (ν.map Y) κ₂) :
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Xhat Yhat : Ω'' → ℝ),
        Measurable Xhat ∧ Measurable Yhat ∧
        IdentDistrib Xhat X ρ μ ∧ IdentDistrib Yhat Y ρ ν ∧
        Xhat ≤ᵐ[ρ] ρ[Yhat | MeasurableSpace.comap Xhat inferInstance] ∧
        ∃ κ : Kernel ℝ ℝ, IsMarkovKernel κ ∧
          ρ.map (fun ω => (Xhat ω, Yhat ω)) = (ρ.map Xhat) ⊗ₘ κ ∧
          ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → ∀ t : ℝ, κ x₁ {y : ℝ | t < y} ≤ κ x₂ {y : ℝ | t < y} := by
  obtain ⟨hmk, hmean, hsnd, hmono2⟩ := hκ
  have := hmk
  set κ : Kernel ℝ ℝ := κ₂.comap m hmm with hκdef
  have hmkκ : IsMarkovKernel κ := by rw [hκdef]; infer_instance
  have : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hmean' : ∀ᵐ x ∂(μ.map X), Integrable id (κ x) ∧ ∫ y, y ∂(κ x) = m x := by
    have h := ae_of_ae_map hmm.aemeasurable hmean
    filter_upwards [h] with x hx
    exact hx
  set ρ : Measure (ℝ × ℝ) := (μ.map X) ⊗ₘ κ with hρ
  have hfst : ρ.map Prod.fst = μ.map X := by
    show ρ.fst = _
    exact Measure.fst_compProd _ _
  have hsnd' : ρ.map Prod.snd = ν.map Y := by
    show ρ.snd = _
    rw [hρ, Measure.snd_compProd, hκdef, comp_comap, ← Measure.snd_compProd]
    exact hsnd
  have hIX : IdentDistrib Prod.fst X ρ μ :=
    ⟨measurable_fst.aemeasurable, hX.aemeasurable, hfst⟩
  have hIY : IdentDistrib Prod.snd Y ρ ν :=
    ⟨measurable_snd.aemeasurable, hY.aemeasurable, hsnd'⟩
  have hsndint : Integrable Prod.snd ρ := hIY.integrable_iff.2 hYint
  have h1 : Integrable id (μ.map X) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hX.aemeasurable).2 hXint
  have hmint : Integrable m (μ.map X) :=
    Integrable.mono' (h1.abs.add (integrable_const C)) hmm.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have hgint : Integrable (fun p : ℝ × ℝ => m p.1) ρ := by
    have := (integrable_map_measure (μ := ρ) hmm.aestronglyMeasurable
      measurable_fst.aemeasurable).1 (hfst ▸ hmint)
    exact this
  have hm : MeasurableSpace.comap (Prod.fst : ℝ × ℝ → ℝ) inferInstance ≤
      (inferInstance : MeasurableSpace (ℝ × ℝ)) := measurable_fst.comap_le
  refine ⟨ℝ × ℝ, inferInstance, ρ, inferInstance, Prod.fst, Prod.snd, measurable_fst,
    measurable_snd, hIX, hIY, ?_, κ, hmkκ, ?_, fun x₁ x₂ h t => hmono2 _ _ (hmono h) t⟩
  · have hfm : Measurable[MeasurableSpace.comap (Prod.fst : ℝ × ℝ → ℝ) inferInstance]
        (Prod.fst : ℝ × ℝ → ℝ) := Measurable.of_comap_le le_rfl
    have hce : (fun p : ℝ × ℝ => m p.1) =ᵐ[ρ]
        ρ[Prod.snd | MeasurableSpace.comap (Prod.fst : ℝ × ℝ → ℝ) inferInstance] := by
      refine ae_eq_condExp_of_forall_setIntegral_eq hm hsndint ?_ ?_
        (hmm.comp hfm).stronglyMeasurable.aestronglyMeasurable
      · intro s _ _
        exact hgint.integrableOn
      · intro s hs _
        obtain ⟨B, hB, rfl⟩ := hs
        have hsB : Prod.fst ⁻¹' B = B ×ˢ (Set.univ : Set ℝ) := by ext; simp
        rw [hsB, Measure.setIntegral_compProd hB MeasurableSet.univ hgint.integrableOn,
          Measure.setIntegral_compProd hB MeasurableSet.univ hsndint.integrableOn]
        simp only [Measure.restrict_univ]
        refine setIntegral_congr_ae hB ?_
        filter_upwards [hmean'] with x hx _
        simp [hx.2]
    filter_upwards [hce] with p hp
    rw [← hp]
    exact hge p.1
  · rw [hfst]
    have hid : (fun ω : ℝ × ℝ => (ω.1, ω.2)) = id := rfl
    rw [hid, Measure.map_id]

/-- T4 (⇐): a submartingale coupling gives the increasing convex order. -/
theorem icx_of_sub {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (Y : Ω' → ℝ)
    (hYint : Integrable Y ν)
    {Ω'' : Type} [MeasurableSpace Ω''] (ρ : Measure Ω'') [IsProbabilityMeasure ρ]
    (Xhat Yhat : Ω'' → ℝ) (hXh : Measurable Xhat)
    (hIX : IdentDistrib Xhat X ρ μ) (hIY : IdentDistrib Yhat Y ρ ν)
    (hsub : Xhat ≤ᵐ[ρ] ρ[Yhat | MeasurableSpace.comap Xhat inferInstance]) :
    StochasticOrders.MonotoneConvex.IcxOrder μ ν X Y := by
  intro φ hφm hφ hφX hφY
  have hcont : Continuous φ := continuousOn_univ.1 (hφ.continuousOn isOpen_univ)
  have hm : MeasurableSpace.comap Xhat inferInstance ≤ (inferInstance : MeasurableSpace Ω'') :=
    hXh.comap_le
  have hIXφ := hIX.comp hcont.measurable
  have hIYφ := hIY.comp hcont.measurable
  have hYh : Integrable Yhat ρ := hIY.integrable_iff.2 hYint
  have hφYh : Integrable (φ ∘ Yhat) ρ := hIYφ.integrable_iff.2 hφY
  have hφXh : Integrable (φ ∘ Xhat) ρ := hIXφ.integrable_iff.2 hφX
  show ∫ ω, (φ ∘ X) ω ∂μ ≤ ∫ ω, (φ ∘ Y) ω ∂ν
  rw [← hIXφ.integral_eq, ← hIYφ.integral_eq]
  have hJ := hφ.map_condExp_le_univ hm hcont.lowerSemicontinuous hYh hφYh
  have h1 : (φ ∘ Xhat) ≤ᵐ[ρ] ρ[φ ∘ Yhat | MeasurableSpace.comap Xhat inferInstance] := by
    filter_upwards [hJ, hsub] with ω h1 h2
    exact le_trans (hφm h2) h1
  calc ∫ ω, (φ ∘ Xhat) ω ∂ρ ≤ ∫ ω, (ρ[φ ∘ Yhat | MeasurableSpace.comap Xhat inferInstance]) ω ∂ρ :=
        integral_mono_ae hφXh integrable_condExp h1
    _ = ∫ ω, (φ ∘ Yhat) ω ∂ρ := integral_condExp hm

end Icx8e

end PartIcx8e

open StochasticOrders.MonotoneConvex MeasureTheory ProbabilityTheory in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXint : Integrable X μ) (hYint : Integrable Y ν) :
    IcxOrder μ ν X Y ↔
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Xhat Yhat : Ω'' → ℝ),
        Measurable Xhat ∧ Measurable Yhat ∧
        IdentDistrib Xhat X ρ μ ∧ IdentDistrib Yhat Y ρ ν ∧
        Xhat ≤ᵐ[ρ] ρ[Yhat | MeasurableSpace.comap Xhat inferInstance] ∧
        ∃ κ : Kernel ℝ ℝ, IsMarkovKernel κ ∧
          ρ.map (fun ω => (Xhat ω, Yhat ω)) = (ρ.map Xhat) ⊗ₘ κ ∧
          ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → ∀ t : ℝ, κ x₁ {y : ℝ | t < y} ≤ κ x₂ {y : ℝ | t < y} := by
  constructor
  · intro hicx
    obtain ⟨m, hmm, hmono, hge, ⟨C, hC⟩, hcx⟩ := Icx8e.exists_lift μ ν X Y hXint hYint hicx
    have hZ : Measurable (fun ω => m (X ω)) := hmm.comp hX
    have hZint : Integrable (fun ω => m (X ω)) μ :=
      Integrable.mono' (hXint.abs.add (integrable_const C)) hZ.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs]
          show |m (X ω)| ≤ |X ω| + C
          exact hC (X ω))
    have : IsProbabilityMeasure (μ.map fun ω => m (X ω)) :=
      Measure.isProbabilityMeasure_map hZ.aemeasurable
    have : IsProbabilityMeasure (ν.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
    have h1 : Integrable id (μ.map fun ω => m (X ω)) :=
      (integrable_map_measure measurable_id.aestronglyMeasurable hZ.aemeasurable).2 hZint
    have h2 : Integrable id (ν.map Y) :=
      (integrable_map_measure measurable_id.aestronglyMeasurable hY.aemeasurable).2 hYint
    obtain ⟨κ₂, hκ₂⟩ := k_core60 _ _ h1 h2 (cx_map60 μ ν _ Y hZ hY hcx)
    have hmapeq : μ.map (fun ω => m (X ω)) = (μ.map X).map m := by
      rw [Measure.map_map hmm hX]; rfl
    rw [hmapeq] at hκ₂
    exact Icx8e.witness μ ν X Y hX hY hXint hYint m hmm hmono hge C hC κ₂ hκ₂
  · rintro ⟨Ω'', _, ρ, _, Xh, Yh, hXm, -, hIX, hIY, hsub, -⟩
    exact Icx8e.icx_of_sub μ ν X Y hYint ρ Xh Yh hXm hIX hIY hsub
