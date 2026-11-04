-- Prove2me | solution 1 for SCInfoDesign.Disjoint.eq_C9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T14:06:52.788253+00:00
-- url     : https://prove2.me/submissions/e7c68ec1-bceb-4c0c-a158-70a1ad371cb6

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Disjoint_Setting

namespace SCDisjT3Aux

open SCInfoDesign.Disjoint

/-- Closed form of `E[(D - Q)⁺]` for `D ~ U[a, b]`. -/
noncomputable def Gc (a b Q : ℝ) : ℝ :=
  if Q ≤ a then (a + b) / 2 - Q else if Q ≤ b then (b - Q) ^ 2 / (2 * (b - a)) else 0

lemma integral_max_sub (a b Q : ℝ) (hab : a < b) :
    (∫ x in a..b, max (x - Q) 0) = (b - a) * Gc a b Q := by
  have hw : 0 < b - a := by linarith
  have hc : Continuous (fun x : ℝ => max (x - Q) 0) := by fun_prop
  unfold Gc
  split_ifs with h1 h2
  · have : Set.EqOn (fun x : ℝ => max (x - Q) 0) (fun x => x - Q) (Set.uIcc a b) := by
      intro x hx
      rw [Set.uIcc_of_le hab.le] at hx
      simp [max_eq_left (show (0:ℝ) ≤ x - Q by linarith [hx.1])]
    rw [intervalIntegral.integral_congr this]
    simp
    ring
  · have hQa : a ≤ Q := by linarith
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := Q)
      (hc.intervalIntegrable a Q) (hc.intervalIntegrable Q b)]
    have e1 : Set.EqOn (fun x : ℝ => max (x - Q) 0) (fun _ => (0:ℝ)) (Set.uIcc a Q) := by
      intro x hx
      rw [Set.uIcc_of_le hQa] at hx
      simp [max_eq_right (show x - Q ≤ 0 by linarith [hx.2])]
    have e2 : Set.EqOn (fun x : ℝ => max (x - Q) 0) (fun x => x - Q) (Set.uIcc Q b) := by
      intro x hx
      rw [Set.uIcc_of_le h2] at hx
      simp [max_eq_left (show (0:ℝ) ≤ x - Q by linarith [hx.1])]
    rw [intervalIntegral.integral_congr e1, intervalIntegral.integral_congr e2]
    simp
    field_simp
    ring
  · push Not at h2
    have e1 : Set.EqOn (fun x : ℝ => max (x - Q) 0) (fun _ => (0:ℝ)) (Set.uIcc a b) := by
      intro x hx
      rw [Set.uIcc_of_le hab.le] at hx
      simp [max_eq_right (show x - Q ≤ 0 by linarith [hx.2])]
    rw [intervalIntegral.integral_congr e1]
    simp

lemma mean_max (a b Q : ℝ) (hab : a < b) :
    SCInfoDesign.Nested.uniformMean a b (fun d => max (d - Q) 0) = Gc a b Q := by
  unfold SCInfoDesign.Nested.uniformMean
  rw [integral_max_sub a b Q hab]
  have hw : (b - a) ≠ 0 := by linarith
  field_simp

lemma mean_supp (a b Q ξ : ℝ) (hab : a < b) :
    SCInfoDesign.Nested.uniformMean a b (fun d => ξ * max (d - Q) 0 + (1 - ξ) * max (Q - d) 0)
      = Gc a b Q + (1 - ξ) * (Q - (a + b) / 2) := by
  have hpt : (fun d : ℝ => ξ * max (d - Q) 0 + (1 - ξ) * max (Q - d) 0)
      = fun d => max (d - Q) 0 + (1 - ξ) * (Q - d) := by
    funext d
    rcases le_total d Q with h | h
    · have e1 : max (d - Q) 0 = 0 := max_eq_right (by linarith)
      have e2 : max (Q - d) 0 = Q - d := max_eq_left (by linarith)
      rw [e1, e2]; ring
    · have e1 : max (d - Q) 0 = d - Q := max_eq_left (by linarith)
      have e2 : max (Q - d) 0 = 0 := max_eq_right (by linarith)
      rw [e1, e2]; ring
  rw [hpt]
  unfold SCInfoDesign.Nested.uniformMean
  have hc : Continuous (fun x : ℝ => max (x - Q) 0) := by fun_prop
  have hc2 : Continuous (fun x : ℝ => (1 - ξ) * (Q - x)) := by fun_prop
  rw [intervalIntegral.integral_add (hc.intervalIntegrable a b) (hc2.intervalIntegrable a b),
    integral_max_sub a b Q hab]
  have hI : (∫ x in a..b, (Q - x)) = Q * (b - a) - (b ^ 2 - a ^ 2) / 2 := by
    rw [intervalIntegral.integral_sub (f := fun _ => Q) (g := fun x => x) intervalIntegrable_const (continuous_id.intervalIntegrable (μ := MeasureTheory.volume) a b)]
    simp; ring
  rw [intervalIntegral.integral_const_mul, hI]
  have hw : (b - a) ≠ 0 := by linarith
  field_simp
  ring


lemma Gc_mul (a b Q : ℝ) (hab : a < b) :
    (b - a) * Gc a b Q =
      if Q ≤ a then (b - a) * ((a + b) / 2 - Q) else if Q ≤ b then (b - Q) ^ 2 / 2 else 0 := by
  unfold Gc
  have hw : (b - a) ≠ 0 := by linarith
  split_ifs <;> field_simp <;> simp

lemma Gc_nonneg (a b Q : ℝ) (hab : a < b) : 0 ≤ Gc a b Q := by
  have hw : 0 < b - a := by linarith
  have h := Gc_mul a b Q hab
  have : 0 ≤ (b - a) * Gc a b Q := by
    rw [h]; split_ifs <;> nlinarith [sq_nonneg (b - Q)]
  exact (mul_nonneg_iff_of_pos_left hw).mp this

lemma Gc_anti (a b Q Q' : ℝ) (hab : a < b) (hQ : Q ≤ Q') : Gc a b Q' ≤ Gc a b Q := by
  have hw : 0 < b - a := by linarith
  have h1 := Gc_mul a b Q hab
  have h2 := Gc_mul a b Q' hab
  have : (b - a) * Gc a b Q' ≤ (b - a) * Gc a b Q := by
    rw [h1, h2]; split_ifs <;> nlinarith [sq_nonneg (Q' - Q), sq_nonneg (Q - a), sq_nonneg (b - Q), sq_nonneg (Q' - a), sq_nonneg (b - Q')]
  exact le_of_mul_le_mul_left this hw

lemma Gc_sub1 (a b Q Q' : ℝ) (hab : a < b) (hQ : Q ≤ a) :
    Gc a b Q - (Q' - Q) ≤ Gc a b Q' := by
  have hw : 0 < b - a := by linarith
  have h1 := Gc_mul a b Q hab
  have h2 := Gc_mul a b Q' hab
  have : (b - a) * (Gc a b Q - (Q' - Q)) ≤ (b - a) * Gc a b Q' := by
    rw [mul_sub, h1, h2]; split_ifs <;> nlinarith [sq_nonneg (Q' - Q), sq_nonneg (Q - a), sq_nonneg (b - Q), sq_nonneg (Q' - a), sq_nonneg (b - Q')]
  exact le_of_mul_le_mul_left this hw

lemma Gc_sub2 (a b Q Q' : ℝ) (hab : a < b) (hQa : a ≤ Q) (hQb : Q ≤ b) :
    Gc a b Q - (b - Q) / (b - a) * (Q' - Q) ≤ Gc a b Q' := by
  have hw : 0 < b - a := by linarith
  have h1 := Gc_mul a b Q hab
  have h2 := Gc_mul a b Q' hab
  have e : (b - a) * ((b - Q) / (b - a) * (Q' - Q)) = (b - Q) * (Q' - Q) := by
    field_simp
  have : (b - a) * (Gc a b Q - (b - Q) / (b - a) * (Q' - Q)) ≤ (b - a) * Gc a b Q' := by
    rw [mul_sub, e, h1, h2]; split_ifs <;> nlinarith [sq_nonneg (Q' - Q), sq_nonneg (Q - a), sq_nonneg (b - Q), sq_nonneg (Q' - a), sq_nonneg (b - Q')]
  exact le_of_mul_le_mul_left this hw

lemma Gc_sub2s (a b Q Q' : ℝ) (hab : a < b) (hQa : a ≤ Q) (hQb : Q < b) (hQQ : Q < Q') :
    Gc a b Q - (b - Q) / (b - a) * (Q' - Q) < Gc a b Q' := by
  have hw : 0 < b - a := by linarith
  have h1 := Gc_mul a b Q hab
  have h2 := Gc_mul a b Q' hab
  have e : (b - a) * ((b - Q) / (b - a) * (Q' - Q)) = (b - Q) * (Q' - Q) := by
    field_simp
  have : (b - a) * (Gc a b Q - (b - Q) / (b - a) * (Q' - Q)) < (b - a) * Gc a b Q' := by
    rw [mul_sub, e, h1, h2]; split_ifs <;> nlinarith [sq_nonneg (Q' - Q), sq_nonneg (Q - a), sq_nonneg (b - Q), sq_nonneg (Q' - a), sq_nonneg (b - Q')]
  exact lt_of_mul_lt_mul_left this hw.le

lemma Gc_sub3 (a b Q Q' : ℝ) (hab : a < b) (hQ : b ≤ Q) : Gc a b Q ≤ Gc a b Q' := by
  have : Gc a b Q = 0 := by
    unfold Gc
    split_ifs with h1 h2
    · linarith
    · have : Q = b := by linarith
      subst this; simp
    · rfl
  rw [this]; exact Gc_nonneg a b Q' hab


lemma Gc_low (a b Q : ℝ) (hQ : Q ≤ a) : Gc a b Q = (a + b) / 2 - Q := by
  unfold Gc; rw [if_pos hQ]

lemma Gc_mid (a b Q : ℝ) (hab : a < b) (hQa : a ≤ Q) (hQb : Q ≤ b) :
    Gc a b Q = (b - Q) ^ 2 / (2 * (b - a)) := by
  unfold Gc
  split_ifs with h1
  · have : Q = a := le_antisymm h1 hQa
    subst this
    have hw : (b - Q) ≠ 0 := by linarith
    field_simp; ring
  · rfl

lemma Gc_high (a b Q : ℝ) (hab : a < b) (hQ : b ≤ Q) : Gc a b Q = 0 := by
  unfold Gc
  split_ifs with h1 h2
  · linarith
  · have : Q = b := by linarith
    subst this; simp
  · rfl

section Model

variable (P : Params)

noncomputable def Rc (p Q : ℝ) : ℝ := p * Gc P.a₀ P.b₀ Q + (1 - p) * Gc P.a₁ P.b₁ Q

noncomputable def Qbar (p : ℝ) : ℝ :=
  if p < 1 - P.ξ then P.a₁ + P.ξ * (P.b₁ - P.a₁) / (1 - p)
  else P.a₀ + (P.ξ - 1 + p) * (P.b₀ - P.a₀) / p

noncomputable def KL (p : ℝ) : ℝ :=
  p * ((P.a₀ + P.b₀) / 2 - P.a₁) + (P.b₁ - P.a₁) * (1 - p) / 2
    - (P.b₁ - P.a₁) * P.ξ * (2 - P.ξ) / (2 * (1 - p))

noncomputable def KR (p : ℝ) : ℝ := (P.b₀ - P.a₀) * (1 - P.ξ) ^ 2 / (2 * p)

noncomputable def Kc (p : ℝ) : ℝ := if p < 1 - P.ξ then KL P p else KR P p

variable {P}
variable (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hξ₀ : 0 < P.ξ) (hξ₁ : P.ξ < 1) (hdisj : P.b₁ < P.a₀)
include hab₀ hab₁

lemma retail_eq (p Q : ℝ) : P.retailerCost p Q = Rc P p Q := by
  unfold Params.retailerCost Rc
  rw [mean_max _ _ _ hab₀, mean_max _ _ _ hab₁]

lemma supp_eq (p Q : ℝ) : P.supplierCost p Q =
    Rc P p Q + (1 - P.ξ) * (Q - (p * ((P.a₀ + P.b₀) / 2) + (1 - p) * ((P.a₁ + P.b₁) / 2))) := by
  unfold Params.supplierCost Rc
  rw [mean_supp _ _ _ _ hab₀, mean_supp _ _ _ _ hab₁]
  ring

include ha₀ ha₁ hξ₀ hξ₁ hdisj

/-- `Qbar p` is optimal, and strictly better than every larger quantity. -/
lemma supp_sub (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) (Q' : ℝ) :
    P.supplierCost p (Qbar P p) ≤ P.supplierCost p Q' ∧
      (Qbar P p < Q' → P.supplierCost p (Qbar P p) < P.supplierCost p Q') := by
  obtain ⟨hp0, hp1⟩ := hp
  rw [supp_eq hab₀ hab₁, supp_eq hab₀ hab₁]
  unfold Rc Qbar
  split_ifs with hps
  · set q := P.a₁ + P.ξ * (P.b₁ - P.a₁) / (1 - p) with hq
    have h1p : 0 < 1 - p := by linarith
    have hqa : P.a₁ ≤ q := by
      have : 0 ≤ P.ξ * (P.b₁ - P.a₁) / (1 - p) := by
        apply div_nonneg; nlinarith; linarith
      linarith
    have hqb : q < P.b₁ := by
      have : P.ξ * (P.b₁ - P.a₁) / (1 - p) < P.b₁ - P.a₁ := by
        rw [div_lt_iff₀ h1p]; nlinarith
      linarith
    have hr : (1 - p) * ((P.b₁ - q) / (P.b₁ - P.a₁)) = 1 - p - P.ξ := by
      have : P.b₁ - P.a₁ ≠ 0 := by linarith
      have : 1 - p ≠ 0 := by linarith
      rw [hq]; field_simp; ring
    have h0 := Gc_sub1 P.a₀ P.b₀ q Q' hab₀ (by linarith)
    have h1 := Gc_sub2 P.a₁ P.b₁ q Q' hab₁ hqa hqb.le
    have h0' := mul_le_mul_of_nonneg_left h0 hp0
    have h1' := mul_le_mul_of_nonneg_left h1 h1p.le
    refine ⟨?_, fun hlt => ?_⟩
    · have : (1 - p) * ((P.b₁ - q) / (P.b₁ - P.a₁) * (Q' - q)) = (1 - p - P.ξ) * (Q' - q) := by
        rw [← mul_assoc, hr]
      nlinarith
    · have h1s := Gc_sub2s P.a₁ P.b₁ q Q' hab₁ hqa hqb hlt
      have h1s' := mul_lt_mul_of_pos_left h1s h1p
      have : (1 - p) * ((P.b₁ - q) / (P.b₁ - P.a₁) * (Q' - q)) = (1 - p - P.ξ) * (Q' - q) := by
        rw [← mul_assoc, hr]
      nlinarith
  · push Not at hps
    have hp : 0 < p := by linarith
    set q := P.a₀ + (P.ξ - 1 + p) * (P.b₀ - P.a₀) / p with hq
    have hqa : P.a₀ ≤ q := by
      have : 0 ≤ (P.ξ - 1 + p) * (P.b₀ - P.a₀) / p := by
        apply div_nonneg; nlinarith; linarith
      linarith
    have hqb : q < P.b₀ := by
      have : (P.ξ - 1 + p) * (P.b₀ - P.a₀) / p < P.b₀ - P.a₀ := by
        rw [div_lt_iff₀ hp]; nlinarith
      linarith
    have hr : p * ((P.b₀ - q) / (P.b₀ - P.a₀)) = 1 - P.ξ := by
      have : P.b₀ - P.a₀ ≠ 0 := by linarith
      have : p ≠ 0 := by linarith
      rw [hq]; field_simp; ring
    have h1 := Gc_sub3 P.a₁ P.b₁ q Q' hab₁ (by linarith)
    have h0 := Gc_sub2 P.a₀ P.b₀ q Q' hab₀ hqa hqb.le
    have h0' := mul_le_mul_of_nonneg_left h0 hp0
    have h1' := mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ 1 - p by linarith)
    have : p * ((P.b₀ - q) / (P.b₀ - P.a₀) * (Q' - q)) = (1 - P.ξ) * (Q' - q) := by
      rw [← mul_assoc, hr]
    refine ⟨?_, fun hlt => ?_⟩
    · nlinarith
    · have h0s := Gc_sub2s P.a₀ P.b₀ q Q' hab₀ hqa hqb hlt
      have h0s' := mul_lt_mul_of_pos_left h0s hp
      nlinarith

lemma Qbar_nonneg (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) : 0 ≤ Qbar P p := by
  obtain ⟨hp0, hp1⟩ := hp
  unfold Qbar
  split_ifs with hps
  · have : 0 ≤ P.ξ * (P.b₁ - P.a₁) / (1 - p) := by
      apply div_nonneg; nlinarith; linarith
    linarith
  · push Not at hps
    have : 0 ≤ (P.ξ - 1 + p) * (P.b₀ - P.a₀) / p := by
      apply div_nonneg; nlinarith; linarith
    linarith

lemma opt_Qbar (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) : P.IsOptimalQuantity p (Qbar P p) :=
  ⟨Qbar_nonneg hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p hp,
    fun Q' _ => (supp_sub hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p hp Q').1⟩

lemma opt_le (p Q : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) (hQ : P.IsOptimalQuantity p Q) :
    Q ≤ Qbar P p := by
  by_contra h
  push Not at h
  have h1 := (supp_sub hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p hp Q).2 h
  have h2 := hQ.2 (Qbar P p) (Qbar_nonneg hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p hp)
  linarith

lemma Rc_Qbar (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) : Rc P p (Qbar P p) = Kc P p := by
  obtain ⟨hp0, hp1⟩ := hp
  unfold Rc Qbar Kc
  split_ifs with hps
  · set q := P.a₁ + P.ξ * (P.b₁ - P.a₁) / (1 - p) with hq
    have h1p : 0 < 1 - p := by linarith
    have hqa : P.a₁ ≤ q := by
      have : 0 ≤ P.ξ * (P.b₁ - P.a₁) / (1 - p) := by
        apply div_nonneg; nlinarith; linarith
      linarith
    have hqb : q < P.b₁ := by
      have : P.ξ * (P.b₁ - P.a₁) / (1 - p) < P.b₁ - P.a₁ := by
        rw [div_lt_iff₀ h1p]; nlinarith
      linarith
    rw [Gc_low _ _ _ (by linarith), Gc_mid _ _ _ hab₁ hqa hqb.le, hq]
    unfold KL
    have : P.b₁ - P.a₁ ≠ 0 := by linarith
    have : 1 - p ≠ 0 := by linarith
    field_simp
    ring
  · push Not at hps
    have hp : 0 < p := by linarith
    set q := P.a₀ + (P.ξ - 1 + p) * (P.b₀ - P.a₀) / p with hq
    have hqa : P.a₀ ≤ q := by
      have : 0 ≤ (P.ξ - 1 + p) * (P.b₀ - P.a₀) / p := by
        apply div_nonneg; nlinarith; linarith
      linarith
    have hqb : q < P.b₀ := by
      have : (P.ξ - 1 + p) * (P.b₀ - P.a₀) / p < P.b₀ - P.a₀ := by
        rw [div_lt_iff₀ hp]; nlinarith
      linarith
    rw [Gc_high _ _ _ hab₁ (by linarith), Gc_mid _ _ _ hab₀ hqa hqb.le, hq]
    unfold KR
    have : P.b₀ - P.a₀ ≠ 0 := by linarith
    have : p ≠ 0 := by linarith
    field_simp
    ring

lemma K_le_retail (p Q : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) (hQ : P.IsOptimalQuantity p Q) :
    Kc P p ≤ P.retailerCost p Q := by
  rw [← Rc_Qbar hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p hp, retail_eq hab₀ hab₁]
  have hle := opt_le hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p Q hp hQ
  unfold Rc
  have := Gc_anti _ _ _ _ hab₀ hle
  have := Gc_anti _ _ _ _ hab₁ hle
  have := mul_le_mul_of_nonneg_left (Gc_anti _ _ _ _ hab₀ hle) hp.1
  have := mul_le_mul_of_nonneg_left (Gc_anti _ _ _ _ hab₁ hle) (show (0:ℝ) ≤ 1 - p by linarith [hp.2])
  linarith


lemma retail_Qbar (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) : P.retailerCost p (Qbar P p) = Kc P p := by
  rw [retail_eq hab₀ hab₁, Rc_Qbar hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p hp]

lemma bestResp : P.IsBestResponseProfile (Qbar P) :=
  fun p hp => opt_Qbar hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p hp

omit hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj in
lemma msgProb_nonneg {M : Type} [Fintype M] (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0:ℝ) 1) (π : Fin 2 → M → ℝ)
    (hπ : SCInfoDesign.Nested.IsPolicy π) (m : M) : 0 ≤ msgProb p₀ π m := by
  unfold msgProb
  have := hπ.1 0 m; have := hπ.1 1 m
  have := hp₀.1; have := hp₀.2
  nlinarith

omit hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj in
lemma post_mem {M : Type} [Fintype M] (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0:ℝ) 1) (π : Fin 2 → M → ℝ)
    (hπ : SCInfoDesign.Nested.IsPolicy π) (m : M) : posterior p₀ π m ∈ Set.Icc (0:ℝ) 1 := by
  have h0 := hπ.1 0 m; have h1 := hπ.1 1 m
  have := hp₀.1; have := hp₀.2
  have hn : 0 ≤ p₀ * π 0 m := mul_nonneg hp₀.1 h0
  have hd := msgProb_nonneg p₀ hp₀ π hπ m
  refine ⟨div_nonneg hn hd, div_le_one_of_le₀ ?_ hd⟩
  unfold msgProb
  nlinarith

omit hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj in
lemma msgProb_mul_post {M : Type} [Fintype M] (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0:ℝ) 1) (π : Fin 2 → M → ℝ)
    (hπ : SCInfoDesign.Nested.IsPolicy π) (m : M) :
    msgProb p₀ π m * posterior p₀ π m = p₀ * π 0 m := by
  unfold posterior
  by_cases h : msgProb p₀ π m = 0
  · rw [h]
    have h0 := hπ.1 0 m; have h1 := hπ.1 1 m
    have : 0 ≤ p₀ * π 0 m := mul_nonneg hp₀.1 h0
    have : 0 ≤ (1 - p₀) * π 1 m := mul_nonneg (by linarith [hp₀.2]) h1
    unfold msgProb at h
    simp only [zero_mul]
    linarith
  · field_simp

omit hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj in
lemma sum_msgProb {M : Type} [Fintype M] (p₀ : ℝ) (π : Fin 2 → M → ℝ)
    (hπ : SCInfoDesign.Nested.IsPolicy π) : ∑ m, msgProb p₀ π m = 1 := by
  unfold msgProb
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hπ.2 0, hπ.2 1]
  ring

lemma lower_bound (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0:ℝ) 1) (α β : ℝ)
    (hℓ : ∀ p ∈ Set.Icc (0:ℝ) 1, α + β * p ≤ Kc P p)
    (M' : Type) [Fintype M'] (π' : Fin 2 → M' → ℝ) (Qs' : ℝ → ℝ)
    (hπ' : SCInfoDesign.Nested.IsPolicy π') (hQs' : P.IsBestResponseProfile Qs') :
    α + β * p₀ ≤ expectedCost P p₀ π' Qs' := by
  unfold expectedCost
  calc α + β * p₀ = ∑ m, msgProb p₀ π' m * (α + β * posterior p₀ π' m) := by
        have : ∀ m, msgProb p₀ π' m * (α + β * posterior p₀ π' m)
            = α * msgProb p₀ π' m + β * (p₀ * π' 0 m) := by
          intro m
          rw [← msgProb_mul_post p₀ hp₀ π' hπ' m]; ring
        simp_rw [this]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
          sum_msgProb p₀ π' hπ', hπ'.2 0]
        ring
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro m _
        apply mul_le_mul_of_nonneg_left _ (msgProb_nonneg p₀ hp₀ π' hπ' m)
        have hm := post_mem p₀ hp₀ π' hπ' m
        exact (hℓ _ hm).trans
          (K_le_retail hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj _ _ hm (hQs' _ hm))


omit hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj in
lemma KL_form (p : ℝ) : KL P p = p * ((P.a₀ + P.b₀) / 2 - P.a₁) + (P.b₁ - P.a₁) * (1 - p) / 2
    - ((P.b₁ - P.a₁) * P.ξ * (2 - P.ξ) / 2) * (1 / (1 - p)) := by
  unfold KL; rw [← div_div]; ring

omit hab₀ hab₁ ha₀ ha₁ hdisj in
lemma inv_chord (p : ℝ) (hp0 : 0 ≤ p) (hps : p ≤ 1 - P.ξ) :
    (1 - P.ξ) * (1 / (1 - p)) ≤ (1 - P.ξ - p) * 1 + p * (1 / P.ξ) := by
  have h1p : 0 < 1 - p := by linarith
  have e : (1 - P.ξ - p) * 1 + p * (1 / P.ξ) - (1 - P.ξ) * (1 / (1 - p))
      = p * (1 - P.ξ) * (1 - P.ξ - p) / (P.ξ * (1 - p)) := by
    field_simp; ring
  have : 0 ≤ p * (1 - P.ξ) * (1 - P.ξ - p) / (P.ξ * (1 - p)) := by
    apply div_nonneg
    · apply mul_nonneg (mul_nonneg hp0 (by linarith)) (by linarith)
    · positivity
  linarith

omit ha₀ ha₁ hdisj in
lemma KL_chord (p : ℝ) (hp0 : 0 ≤ p) (hps : p ≤ 1 - P.ξ) :
    (1 - P.ξ - p) * KL P 0 + p * KL P (1 - P.ξ) ≤ (1 - P.ξ) * KL P p := by
  rw [KL_form, KL_form, KL_form]
  have hinv := inv_chord hξ₀ hξ₁ p hp0 hps
  have hC : 0 ≤ (P.b₁ - P.a₁) * P.ξ * (2 - P.ξ) / 2 := by
    apply div_nonneg _ (by norm_num)
    apply mul_nonneg (mul_nonneg (by linarith) hξ₀.le) (by linarith)
  have h1 := mul_le_mul_of_nonneg_left hinv hC
  have e1 : (1:ℝ) - (1 - P.ξ) = P.ξ := by ring
  rw [e1]
  simp only [sub_zero, div_one]
  nlinarith

noncomputable def K0v (P : Params) : ℝ := (P.b₁ - P.a₁) * (1 - P.ξ) ^ 2 / 2
noncomputable def Av (P : Params) : ℝ := (P.b₀ - P.a₀) * (1 - P.ξ) ^ 2 / 2

omit hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj in
lemma KL_zero : KL P 0 = K0v P := by
  unfold KL K0v; ring

omit hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj in
lemma KR_eq (p : ℝ) : KR P p = Av P / p := by
  unfold KR Av; ring

omit hab₀ hab₁ ha₀ ha₁ hdisj in
lemma KL_s : KL P (1 - P.ξ) = KR P (1 - P.ξ) + (1 - P.ξ) * (P.a₀ - P.b₁) := by
  unfold KL KR
  have : (1:ℝ) - (1 - P.ξ) = P.ξ := by ring
  rw [this]
  have : 1 - P.ξ ≠ 0 := by linarith
  have : P.ξ ≠ 0 := by linarith
  field_simp
  ring

lemma left_ok (α β : ℝ) (h0 : α ≤ KL P 0) (hs : α + β * (1 - P.ξ) ≤ KR P (1 - P.ξ))
    (p : ℝ) (hp0 : 0 ≤ p) (hps : p < 1 - P.ξ) : α + β * p ≤ KL P p := by
  have hch := KL_chord hab₀ hab₁ hξ₀ hξ₁ p hp0 hps.le
  have hKs := KL_s (P := P) hξ₀ hξ₁
  have hd : 0 ≤ (1 - P.ξ) * (P.a₀ - P.b₁) := mul_nonneg (by linarith) (by linarith)
  have hspos : 0 < 1 - P.ξ := by linarith
  have key : (1 - P.ξ) * (α + β * p) ≤ (1 - P.ξ) * KL P p := by
    have e : (1 - P.ξ) * (α + β * p) = (1 - P.ξ - p) * α + p * (α + β * (1 - P.ξ)) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left h0 (show (0:ℝ) ≤ 1 - P.ξ - p by linarith)
    have := mul_le_mul_of_nonneg_left hs hp0
    have := mul_le_mul_of_nonneg_left hd hp0
    nlinarith
  exact le_of_mul_le_mul_left key hspos

lemma lb_of (α β : ℝ) (hR : ∀ p, 1 - P.ξ ≤ p → p ≤ 1 → α + β * p ≤ Av P / p)
    (h0 : α ≤ K0v P) : ∀ p ∈ Set.Icc (0:ℝ) 1, α + β * p ≤ Kc P p := by
  intro p hp
  unfold Kc
  split_ifs with hps
  · apply left_ok hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj α β (by rw [KL_zero]; exact h0)
      (by rw [KR_eq]; exact hR _ le_rfl (by linarith)) p hp.1 hps
  · push Not at hps
    rw [KR_eq]; exact hR p hps hp.2


lemma cost_full (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0:ℝ) 1) :
    expectedCost P p₀ SCInfoDesign.Nested.fullDisclosure (Qbar P)
      = p₀ * Kc P 1 + (1 - p₀) * Kc P 0 := by
  unfold expectedCost
  rw [Fin.sum_univ_two]
  simp only [msgProb, posterior, SCInfoDesign.Nested.fullDisclosure]
  simp
  have h0 := retail_Qbar hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj 0 (by simp)
  have h1 := retail_Qbar hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj 1 (by simp)
  by_cases hz : p₀ = 0
  · subst hz; simp [h0]
  · rw [div_self hz, h0, h1]

lemma cost_none (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0:ℝ) 1) :
    expectedCost P p₀ SCInfoDesign.Nested.noDisclosure (Qbar P) = Kc P p₀ := by
  unfold expectedCost
  simp only [msgProb, posterior, SCInfoDesign.Nested.noDisclosure]
  simp
  exact retail_Qbar hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p₀ hp₀


lemma cost_gamma (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0:ℝ) 1) (hpt0 : 0 < P.ptilde) (hpt1 : P.ptilde < 1)
    (hlt : p₀ < P.ptilde) :
    expectedCost P p₀ (P.gammaStarDS p₀) (Qbar P)
      = p₀ / P.ptilde * Kc P P.ptilde + (1 - p₀ / P.ptilde) * Kc P 0 := by
  have h1p : 1 - p₀ ≠ 0 := by linarith
  have hptne : P.ptilde ≠ 0 := by linarith
  have e0 : msgProb p₀ (P.gammaStarDS p₀) 0 = p₀ / P.ptilde := by
    simp [msgProb, Params.gammaStarDS]
    field_simp; ring
  have e1 : msgProb p₀ (P.gammaStarDS p₀) 1 = 1 - p₀ / P.ptilde := by
    simp [msgProb, Params.gammaStarDS]
    field_simp; ring
  have q0 : p₀ * P.gammaStarDS p₀ 0 0 = p₀ := by simp [Params.gammaStarDS]
  have q1 : p₀ * P.gammaStarDS p₀ 0 1 = 0 := by simp [Params.gammaStarDS]
  have h0 := retail_Qbar hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj 0 (by simp)
  have hpt := retail_Qbar hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj P.ptilde ⟨hpt0.le, hpt1.le⟩
  unfold expectedCost
  rw [Fin.sum_univ_two]
  unfold posterior
  rw [e0, e1, q0, q1, zero_div, h0]
  by_cases hz : p₀ = 0
  · subst hz; simp
  · rw [show p₀ / (p₀ / P.ptilde) = P.ptilde by field_simp, hpt]

end Model

lemma R1 (A K0 p : ℝ) (hA : 0 ≤ A) (hK0 : 0 ≤ K0) (hK : K0 ≤ 2 * A) (hp : 0 < p) (hp1 : p ≤ 1) :
    K0 + (A - K0) * p ≤ A / p := by
  rw [le_div_iff₀ hp]
  have h1 : 0 ≤ A * (1 + p) - K0 * p := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hp1) h1]

lemma R2 (A p p₀ : ℝ) (hA : 0 ≤ A) (hp : 0 < p) (hp₀ : 0 < p₀) :
    2 * A / p₀ + (-(A / p₀ ^ 2)) * p ≤ A / p := by
  have e : A / p - (2 * A / p₀ + (-(A / p₀ ^ 2)) * p) = A * (p₀ - p) ^ 2 / (p * p₀ ^ 2) := by
    field_simp; ring
  have : 0 ≤ A * (p₀ - p) ^ 2 / (p * p₀ ^ 2) := by positivity
  linarith

lemma R3 (A K0 pt p : ℝ) (hA : 0 ≤ A) (hpt : 0 < pt) (hK : 2 * A ≤ K0 * pt)
    (hp : 0 < p) (hlt : p < pt → K0 * pt = 2 * A) :
    K0 + (A / pt - K0) / pt * p ≤ A / p := by
  have e : A / p - (K0 + (A / pt - K0) / pt * p)
      = (pt - p) * (A * (pt + p) - K0 * p * pt) / (p * pt ^ 2) := by
    field_simp; ring
  have : 0 ≤ (pt - p) * (A * (pt + p) - K0 * p * pt) := by
    rcases lt_or_ge p pt with h | h
    · have := hlt h
      have : A * (pt + p) - K0 * p * pt = A * (pt - p) := by nlinarith
      rw [this]; nlinarith [mul_nonneg hA (sq_nonneg (pt - p))]
    · have : A * (pt + p) - K0 * p * pt ≤ 0 := by nlinarith
      nlinarith
  have : 0 ≤ (pt - p) * (A * (pt + p) - K0 * p * pt) / (p * pt ^ 2) := by positivity
  linarith

theorem main (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀)
    (ha₁ : 0 ≤ P.a₁) (hξ₀ : 0 < P.ξ) (hξ₁ : P.ξ < 1) (hdisj : P.b₁ < P.a₀)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0 : ℝ) 1) :
    (P.b₁ - P.a₁ ≤ 2 * (P.b₀ - P.a₀) → IsOptimalPolicy P p₀ SCInfoDesign.Nested.fullDisclosure) ∧
    (2 * (P.b₀ - P.a₀) < P.b₁ - P.a₁ →
      (P.ptilde ≤ p₀ → IsOptimalPolicy P p₀ SCInfoDesign.Nested.noDisclosure) ∧
      (p₀ < P.ptilde → IsOptimalPolicy P p₀ (P.gammaStarDS p₀))) := by
  have hs : 0 < 1 - P.ξ := by linarith
  have hKc0 : Kc P 0 = K0v P := by
    unfold Kc; rw [if_pos hs, KL_zero]
  have hKcR : ∀ p, 1 - P.ξ ≤ p → Kc P p = Av P / p := by
    intro p hp; unfold Kc; rw [if_neg (not_lt.mpr hp), KR_eq]
  have hA : 0 ≤ Av P := by unfold Av; have := sq_nonneg (1 - P.ξ); nlinarith
  have hK0 : 0 ≤ K0v P := by unfold K0v; have := sq_nonneg (1 - P.ξ); nlinarith
  have hBR := bestResp hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · -- full disclosure
    have hpol : SCInfoDesign.Nested.IsPolicy SCInfoDesign.Nested.fullDisclosure := by
      refine ⟨fun ω m => ?_, fun ω => ?_⟩
      · unfold SCInfoDesign.Nested.fullDisclosure; split_ifs <;> norm_num
      · fin_cases ω <;> simp [Fin.sum_univ_two, SCInfoDesign.Nested.fullDisclosure]
    refine ⟨hpol, Qbar P, hBR, fun M' _ π' Qs' hπ' hQs' => ?_⟩
    rw [cost_full hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p₀ hp₀, hKc0, hKcR 1 (by linarith)]
    have hKA : K0v P ≤ 2 * Av P := by
      unfold K0v Av; have := sq_nonneg (1 - P.ξ); nlinarith
    have := lower_bound hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p₀ hp₀ (K0v P) (Av P - K0v P)
      (lb_of hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj _ _
        (fun p hsp hp1 => R1 _ _ p hA hK0 hKA (by linarith) hp1) le_rfl) M' π' Qs' hπ' hQs'
    have e : p₀ * (Av P / 1) + (1 - p₀) * K0v P = K0v P + (Av P - K0v P) * p₀ := by ring
    rw [e]; exact this
  · have hw1 : 0 < P.b₁ - P.a₁ := by linarith
    have hpt_s : 1 - P.ξ ≤ P.ptilde := le_max_left _ _
    have hpt_r : 2 * (P.b₀ - P.a₀) / (P.b₁ - P.a₁) ≤ P.ptilde := le_max_right _ _
    have hpt0 : 0 < P.ptilde := by linarith
    have hpt1 : P.ptilde < 1 := by
      apply max_lt (by linarith)
      rw [div_lt_one hw1]; exact hw
    have hKpt : 2 * Av P ≤ K0v P * P.ptilde := by
      have h2 : 2 * (P.b₀ - P.a₀) ≤ P.ptilde * (P.b₁ - P.a₁) := (div_le_iff₀ hw1).mp hpt_r
      unfold K0v Av
      have := sq_nonneg (1 - P.ξ)
      nlinarith
    refine ⟨fun hge => ?_, fun hlt => ?_⟩
    · -- no disclosure
      have hp0pos : 0 < p₀ := by linarith
      have hpol : SCInfoDesign.Nested.IsPolicy SCInfoDesign.Nested.noDisclosure :=
        ⟨fun _ _ => by simp [SCInfoDesign.Nested.noDisclosure],
         fun _ => by simp [SCInfoDesign.Nested.noDisclosure]⟩
      refine ⟨hpol, Qbar P, hBR, fun M' _ π' Qs' hπ' hQs' => ?_⟩
      rw [cost_none hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p₀ hp₀, hKcR p₀ (by linarith)]
      have h0 : 2 * Av P / p₀ ≤ K0v P := by
        rw [div_le_iff₀ hp0pos]
        nlinarith
      have := lower_bound hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p₀ hp₀ (2 * Av P / p₀) (-(Av P / p₀ ^ 2))
        (lb_of hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj _ _
          (fun p hsp hp1 => R2 _ p p₀ hA (by linarith) hp0pos) h0) M' π' Qs' hπ' hQs'
      have e : 2 * Av P / p₀ + -(Av P / p₀ ^ 2) * p₀ = Av P / p₀ := by
        field_simp; ring
      rw [← e]; exact this
    · -- partial disclosure
      have hq0 : 0 ≤ (1 - P.ptilde) / P.ptilde * (p₀ / (1 - p₀)) := by
        apply mul_nonneg (div_nonneg (by linarith) hpt0.le) (div_nonneg hp₀.1 (by linarith))
      have hq1 : (1 - P.ptilde) / P.ptilde * (p₀ / (1 - p₀)) ≤ 1 := by
        have h1p : 0 < 1 - p₀ := by linarith
        rw [div_mul_div_comm, div_le_one (mul_pos hpt0 h1p)]
        nlinarith
      have hpol : SCInfoDesign.Nested.IsPolicy (P.gammaStarDS p₀) := by
        refine ⟨fun ω m => ?_, fun ω => ?_⟩
        · unfold Params.gammaStarDS
          split_ifs <;> linarith
        · fin_cases ω <;> simp [Fin.sum_univ_two, Params.gammaStarDS]
      refine ⟨hpol, Qbar P, hBR, fun M' _ π' Qs' hπ' hQs' => ?_⟩
      rw [cost_gamma hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p₀ hp₀ hpt0 hpt1 hlt, hKc0,
        hKcR _ hpt_s]
      have hR : ∀ p, 1 - P.ξ ≤ p → p ≤ 1 →
          K0v P + (Av P / P.ptilde - K0v P) / P.ptilde * p ≤ Av P / p := by
        intro p hsp hp1
        apply R3 _ _ _ p hA hpt0 hKpt (by linarith)
        intro hlt'
        have hne : P.ptilde ≠ 1 - P.ξ := by intro h; linarith
        have heq : P.ptilde = 2 * (P.b₀ - P.a₀) / (P.b₁ - P.a₁) := by
          rcases max_choice (1 - P.ξ) (2 * (P.b₀ - P.a₀) / (P.b₁ - P.a₁)) with h | h
          · exact absurd h hne
          · exact h
        rw [heq]; unfold K0v Av
        field_simp
      have := lower_bound hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p₀ hp₀ (K0v P)
        ((Av P / P.ptilde - K0v P) / P.ptilde)
        (lb_of hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj _ _ hR le_rfl) M' π' Qs' hπ' hQs'
      have e : p₀ / P.ptilde * (Av P / P.ptilde) + (1 - p₀ / P.ptilde) * K0v P
          = K0v P + (Av P / P.ptilde - K0v P) / P.ptilde * p₀ := by
        field_simp; ring
      rw [e]; exact this


end SCDisjT3Aux


namespace SCDisjT3Aux

open SCInfoDesign.Disjoint

lemma Gc_sub2s' (a b Q Q' : ℝ) (hab : a < b) (hQa : a < Q) (hQb : Q ≤ b) (hQQ : Q' < Q) :
    Gc a b Q - (b - Q) / (b - a) * (Q' - Q) < Gc a b Q' := by
  have hw : 0 < b - a := by linarith
  have h1 := Gc_mul a b Q hab
  have h2 := Gc_mul a b Q' hab
  have e : (b - a) * ((b - Q) / (b - a) * (Q' - Q)) = (b - Q) * (Q' - Q) := by
    field_simp
  have : (b - a) * (Gc a b Q - (b - Q) / (b - a) * (Q' - Q)) < (b - a) * Gc a b Q' := by
    rw [mul_sub, e, h1, h2]
    split_ifs <;> nlinarith [sq_nonneg (Q' - Q), sq_nonneg (Q - a), sq_nonneg (b - Q),
      sq_nonneg (Q' - a), sq_nonneg (b - Q')]
  exact lt_of_mul_lt_mul_left this hw.le

section Extra

variable {P : Params}
variable (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hξ₀ : 0 < P.ξ) (hξ₁ : P.ξ < 1) (hdisj : P.b₁ < P.a₀)
include hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj

lemma supp_strict_left (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) (hps' : p ≠ 1 - P.ξ) (Q' : ℝ)
    (hQ' : Q' < Qbar P p) : P.supplierCost p (Qbar P p) < P.supplierCost p Q' := by
  obtain ⟨hp0, hp1⟩ := hp
  revert hQ'
  rw [supp_eq hab₀ hab₁, supp_eq hab₀ hab₁]
  unfold Rc Qbar
  split_ifs with hps
  · intro hlt
    set q := P.a₁ + P.ξ * (P.b₁ - P.a₁) / (1 - p) with hq
    have h1p : 0 < 1 - p := by linarith
    have hqa : P.a₁ < q := by
      have : 0 < P.ξ * (P.b₁ - P.a₁) / (1 - p) := by
        apply div_pos; nlinarith; linarith
      linarith
    have hqb : q < P.b₁ := by
      have : P.ξ * (P.b₁ - P.a₁) / (1 - p) < P.b₁ - P.a₁ := by
        rw [div_lt_iff₀ h1p]; nlinarith
      linarith
    have hr : (1 - p) * ((P.b₁ - q) / (P.b₁ - P.a₁)) = 1 - p - P.ξ := by
      have : P.b₁ - P.a₁ ≠ 0 := by linarith
      have : 1 - p ≠ 0 := by linarith
      rw [hq]; field_simp; ring
    have h0 := Gc_sub1 P.a₀ P.b₀ q Q' hab₀ (by linarith)
    have h0' := mul_le_mul_of_nonneg_left h0 hp0
    have h1s := Gc_sub2s' P.a₁ P.b₁ q Q' hab₁ hqa hqb.le hlt
    have h1s' := mul_lt_mul_of_pos_left h1s h1p
    have : (1 - p) * ((P.b₁ - q) / (P.b₁ - P.a₁) * (Q' - q)) = (1 - p - P.ξ) * (Q' - q) := by
      rw [← mul_assoc, hr]
    nlinarith
  · intro hlt
    push Not at hps
    have hps2 : 1 - P.ξ < p := lt_of_le_of_ne hps (Ne.symm hps')
    have hp : 0 < p := by linarith
    set q := P.a₀ + (P.ξ - 1 + p) * (P.b₀ - P.a₀) / p with hq
    have hqa : P.a₀ < q := by
      have : 0 < (P.ξ - 1 + p) * (P.b₀ - P.a₀) / p := by
        apply div_pos; nlinarith; linarith
      linarith
    have hqb : q < P.b₀ := by
      have : (P.ξ - 1 + p) * (P.b₀ - P.a₀) / p < P.b₀ - P.a₀ := by
        rw [div_lt_iff₀ hp]; nlinarith
      linarith
    have hr : p * ((P.b₀ - q) / (P.b₀ - P.a₀)) = 1 - P.ξ := by
      have : P.b₀ - P.a₀ ≠ 0 := by linarith
      have : p ≠ 0 := by linarith
      rw [hq]; field_simp; ring
    have h1 := Gc_sub3 P.a₁ P.b₁ q Q' hab₁ (by linarith)
    have h1' := mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ 1 - p by linarith)
    have h0s := Gc_sub2s' P.a₀ P.b₀ q Q' hab₀ hqa hqb.le hlt
    have h0s' := mul_lt_mul_of_pos_left h0s hp
    have : p * ((P.b₀ - q) / (P.b₀ - P.a₀) * (Q' - q)) = (1 - P.ξ) * (Q' - q) := by
      rw [← mul_assoc, hr]
    nlinarith

lemma opt_iff (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) (hps : p ≠ 1 - P.ξ) (Q : ℝ) :
    P.IsOptimalQuantity p Q ↔ Q = Qbar P p := by
  constructor
  · intro hQ
    apply le_antisymm (opt_le hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p Q hp hQ)
    by_contra h
    push Not at h
    have h1 := supp_strict_left hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p hp hps Q h
    have h2 := hQ.2 (Qbar P p) (Qbar_nonneg hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p hp)
    linarith
  · rintro rfl
    exact opt_Qbar hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p hp

omit hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj in
lemma Qbar_s : Qbar P (1 - P.ξ) = P.a₀ := by
  unfold Qbar
  rw [if_neg (lt_irrefl _)]
  have : P.ξ - 1 + (1 - P.ξ) = 0 := by ring
  rw [this]; simp

lemma opt_iff_s (Q : ℝ) : P.IsOptimalQuantity (1 - P.ξ) Q ↔ Q ∈ Set.Icc P.b₁ P.a₀ := by
  have hs : (1 - P.ξ) ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  constructor
  · intro hQ
    refine ⟨?_, ?_⟩
    · by_contra h
      push Not at h
      have h2 := hQ.2 P.b₁ (by linarith)
      rw [supp_eq hab₀ hab₁, supp_eq hab₀ hab₁] at h2
      unfold Rc at h2
      have h0 := Gc_sub1 P.a₀ P.b₀ P.b₁ Q hab₀ hdisj.le
      have h1 := Gc_sub2s' P.a₁ P.b₁ P.b₁ Q hab₁ hab₁ le_rfl h
      have h0' := mul_le_mul_of_nonneg_left h0 hs.1
      have h1' := mul_lt_mul_of_pos_left h1 (show (0:ℝ) < 1 - (1 - P.ξ) by linarith)
      simp only [sub_self, zero_div, zero_mul, sub_zero] at h1'
      nlinarith
    · have := opt_le hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj _ Q hs hQ
      rwa [Qbar_s] at this
  · rintro ⟨h1, h2⟩
    have hopt := opt_Qbar hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj _ hs
    rw [Qbar_s] at hopt
    refine ⟨by linarith, fun Q' hQ' => ?_⟩
    have hle := hopt.2 Q' hQ'
    have heq : P.supplierCost (1 - P.ξ) Q = P.supplierCost (1 - P.ξ) P.a₀ := by
      rw [supp_eq hab₀ hab₁, supp_eq hab₀ hab₁]
      unfold Rc
      rw [Gc_low _ _ _ h2, Gc_low _ _ _ le_rfl, Gc_high _ _ _ hab₁ h1,
        Gc_high _ _ _ hab₁ hdisj.le]
      ring
    linarith

lemma prefQ_eq (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) : P.prefQ p = Qbar P p := by
  unfold Params.prefQ
  exact IsGreatest.csSup_eq ⟨opt_Qbar hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p hp,
    fun Q hQ => opt_le hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p Q hp hQ⟩

lemma K_eq (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) : P.K p = Kc P p := by
  unfold Params.K
  rw [prefQ_eq hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p hp]
  exact retail_Qbar hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p hp

end Extra

end SCDisjT3Aux

theorem solution (P : SCInfoDesign.Disjoint.Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁)
    (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hξ₀ : 0 < P.ξ) (hξ₁ : P.ξ < 1) (hdisj : P.b₁ < P.a₀) :
    (∀ p ∈ Set.Ico (0 : ℝ) (1 - P.ξ),
      P.K p = p * ((P.a₀ + P.b₀) / 2 - (P.ξ * (P.b₁ - P.a₁) / (1 - p) + P.a₁)) +
        (1 - p) / (2 * (P.b₁ - P.a₁)) * (P.b₁ - (P.ξ * (P.b₁ - P.a₁) / (1 - p) + P.a₁)) ^ 2) ∧
    (∀ p ∈ Set.Icc (1 - P.ξ) 1,
      P.K p = p / (2 * (P.b₀ - P.a₀)) *
        (P.b₀ - ((P.ξ - 1 + p) * (P.b₀ - P.a₀) / p + P.a₀)) ^ 2) := by
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · have hp' : p ∈ Set.Icc (0:ℝ) 1 := ⟨hp.1, by linarith [hp.2]⟩
    rw [SCDisjT3Aux.K_eq hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p hp']
    unfold SCDisjT3Aux.Kc SCDisjT3Aux.KL
    rw [if_pos hp.2]
    have : 1 - p ≠ 0 := by linarith [hp.2]
    have : P.b₁ - P.a₁ ≠ 0 := by linarith
    field_simp
    ring
  · have hp' : p ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hp.1], hp.2⟩
    rw [SCDisjT3Aux.K_eq hab₀ hab₁ ha₀ ha₁ hξ₀ hξ₁ hdisj p hp']
    unfold SCDisjT3Aux.Kc SCDisjT3Aux.KR
    rw [if_neg (not_lt.mpr hp.1)]
    have : p ≠ 0 := by linarith [hp.1]
    have : P.b₀ - P.a₀ ≠ 0 := by linarith
    field_simp
    ring
