-- Prove2me | solution 1 for ThreeOpSplitting.ConvexRates.weighted_ergodic_rate
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T17:23:02.690063+00:00
-- url     : https://prove2.me/submissions/af8c70db-6fa0-4580-9851-54457c202aeb

import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_Nonexpansive
import Definitions.Def_ThreeOpSplitting_Convergence_ThreeOperatorIteration
import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_ThreeOpSplitting_ConvexRates_Algorithm

open InnerProductSpace Filter Topology
open InnerProductSpace Filter Topology ThreeOpSplitting.Convergence

namespace ThreeOpSplitting.ConvexRates

lemma cr_lemma_2_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U T₁ V : H → H) (hU : IsFirmlyNonexpansive U) (hT₁ : IsFirmlyNonexpansive T₁) :
    let S : H → H := fun x => U x + T₁ (V x)
    let W : H → H := fun x => x - ((2 : ℝ) • U x + V x)
    ∀ z w : H,
      ‖S z - S w‖ ^ 2 ≤ ‖z - w‖ ^ 2 - ‖(z - S z) - (w - S w)‖ ^ 2
        - 2 * ⟪T₁ (V z) - T₁ (V w), W z - W w⟫_ℝ := by
  intro S W z w
  set a := U z - U w with ha
  set b := T₁ (V z) - T₁ (V w) with hb
  set d := z - w with hd
  set v := V z - V w with hv
  have e1 : S z - S w = a + b := by simp only [S, ha, hb]; abel
  have e2 : (z - S z) - (w - S w) = d - (a + b) := by simp only [S, ha, hb, hd]; abel
  have e3 : W z - W w = d - (2 : ℝ) • a - v := by simp only [W, ha, hd, hv]; module
  have hUa : ‖a‖ ^ 2 ≤ ⟪a, d⟫_ℝ := hU z w
  have hTb : ‖b‖ ^ 2 ≤ ⟪b, v⟫_ℝ := hT₁ (V z) (V w)
  rw [e1, e2, e3]
  clear_value a b d v
  rw [norm_sub_sq_real d (a + b), norm_add_sq_real a b, inner_add_right d a b,
    inner_sub_right b (d - (2:ℝ) • a) v, inner_sub_right b d ((2:ℝ) • a),
    real_inner_smul_right b a 2]
  have s1 : ⟪d, a⟫_ℝ = ⟪a, d⟫_ℝ := real_inner_comm _ _
  have s2 : ⟪d, b⟫_ℝ = ⟪b, d⟫_ℝ := real_inner_comm _ _
  have s3 : ⟪b, a⟫_ℝ = ⟪a, b⟫_ℝ := real_inner_comm _ _
  nlinarith

/-- `I - T` is firmly nonexpansive when `T` is. -/
lemma cr_firm_compl {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (T : H → H)
    (hT : IsFirmlyNonexpansive T) : IsFirmlyNonexpansive (fun x => x - T x) := by
  intro x y
  have h := hT x y
  have e : (x - T x) - (y - T y) = (x - y) - (T x - T y) := by abel
  simp only
  rw [e, norm_sub_sq_real (x - y) (T x - T y), inner_sub_left (x - y) (T x - T y) (x - y),
    real_inner_self_eq_norm_sq]
  have := real_inner_comm (x - y) (T x - T y)
  linarith

/-- The key inequality for `T = threeOp γ T₁ T₂ C` with a Young parameter `ε > 0`. -/
lemma cr_key_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T₁ T₂ C : H → H) (β γ ε : ℝ)
    (hT₁ : IsFirmlyNonexpansive T₁) (hT₂ : IsFirmlyNonexpansive T₂)
    (hC : IsCocoercive β C) (hγ0 : 0 < γ) (hε : 0 < ε) (z w : H) :
    ‖threeOp γ T₁ T₂ C z - threeOp γ T₁ T₂ C w‖ ^ 2 ≤ ‖z - w‖ ^ 2
      - (1 - ε) * ‖(z - threeOp γ T₁ T₂ C z) - (w - threeOp γ T₁ T₂ C w)‖ ^ 2
      - γ * (2 * β - γ / ε) * ‖C (T₂ z) - C (T₂ w)‖ ^ 2 := by
  set T := threeOp γ T₁ T₂ C with hTdef
  set U : H → H := fun x => x - T₂ x with hUdef
  set V : H → H := fun x => (2 : ℝ) • T₂ x - x - γ • C (T₂ x) with hVdef
  have hS : ∀ x, U x + T₁ (V x) = T x := by
    intro x; simp only [hUdef, hVdef, hTdef, threeOp]; abel
  have hW : ∀ x, x - ((2 : ℝ) • U x + V x) = γ • C (T₂ x) := by
    intro x; simp only [hUdef, hVdef]; module
  have hT1V : ∀ x, T₁ (V x) = T x - x + T₂ x := by
    intro x; rw [← hS x]; simp only [hUdef]; abel
  have h23 := cr_lemma_2_3 U T₁ V (cr_firm_compl T₂ hT₂) hT₁ z w
  simp only [hS, hW] at h23
  rw [hT1V, hT1V] at h23
  set c := C (T₂ z) - C (T₂ w) with hc
  set p := T₂ z - T₂ w with hp
  set e := (T z - z) - (T w - w) with he
  have hsplit : (T z - z + T₂ z) - (T w - w + T₂ w) = e + p := by rw [he, hp]; abel
  have hWd : γ • C (T₂ z) - γ • C (T₂ w) = γ • c := by rw [hc, smul_sub]
  rw [hsplit, hWd, real_inner_smul_right, inner_add_left] at h23
  -- cocoercivity
  have hcoc : β * ‖c‖ ^ 2 ≤ ⟪c, p⟫_ℝ := hC (T₂ z) (T₂ w)
  have hcp : ⟪p, c⟫_ℝ = ⟪c, p⟫_ℝ := real_inner_comm _ _
  -- Young
  have hY0 : 0 ≤ ‖ε • e + γ • c‖ ^ 2 := sq_nonneg _
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hε, abs_of_pos hγ0] at hY0
  have hY : -2 * γ * ⟪e, c⟫_ℝ ≤ ε * ‖e‖ ^ 2 + γ ^ 2 / ε * ‖c‖ ^ 2 := by
    have h1 : 0 ≤ (ε * ‖e‖) ^ 2 + 2 * (ε * (γ * ⟪e, c⟫_ℝ)) + (γ * ‖c‖) ^ 2 := hY0
    have h2 : (ε * ‖e‖) ^ 2 + 2 * (ε * (γ * ⟪e, c⟫_ℝ)) + (γ * ‖c‖) ^ 2 =
        ε * (ε * ‖e‖ ^ 2 + 2 * γ * ⟪e, c⟫_ℝ + γ ^ 2 / ε * ‖c‖ ^ 2) := by
      field_simp
    rw [h2] at h1
    have h3 := (mul_nonneg_iff_of_pos_left hε).1 h1
    linarith
  have hnorm : ‖(z - T z) - (w - T w)‖ = ‖e‖ := by
    rw [he, ← norm_neg]; congr 1; abel
  rw [hnorm]
  rw [hnorm] at h23
  have hγc : γ * (2 * β - γ / ε) * ‖c‖ ^ 2 = 2 * γ * (β * ‖c‖ ^ 2) - γ ^ 2 / ε * ‖c‖ ^ 2 := by
    field_simp
  have hγcoc := mul_le_mul_of_nonneg_left hcoc (by linarith : (0:ℝ) ≤ 2 * γ)
  nlinarith


/-! ### Calculus facts for `h` -/

lemma line_deriv {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (h : H → ℝ) (hd : Differentiable ℝ h) (x v : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => h (x + s • v)) ⟪gradient h (x + t • v), v⟫_ℝ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hf := (hd (x + t • v)).hasFDerivAt
  have := hf.comp_hasDerivAt t hl
  have e : fderiv ℝ h (x + t • v) v = ⟪gradient h (x + t • v), v⟫_ℝ := by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  rw [← e]; exact this

lemma grad_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (h : H → ℝ) (hc : ConvexOn ℝ Set.univ h) (hd : Differentiable ℝ h) (x y : H) :
    h x + ⟪gradient h x, y - x⟫_ℝ ≤ h y := by
  have hder := line_deriv h hd x (y - x) 0
  simp only [zero_smul, add_zero] at hder
  have hs := hder.tendsto_slope_zero_right
  simp only [zero_add, smul_eq_mul, zero_smul, add_zero] at hs
  have hle : ∀ t ∈ Set.Ioo (0:ℝ) 1, t⁻¹ * (h (x + t • (y - x)) - h x) ≤ h y - h x := by
    intro t ht
    have hconv := hc.2 (Set.mem_univ x) (Set.mem_univ y) (by linarith [ht.2] : (0:ℝ) ≤ 1 - t)
      ht.1.le (by ring)
    have e : (1 - t) • x + t • y = x + t • (y - x) := by module
    rw [e, smul_eq_mul, smul_eq_mul] at hconv
    rw [inv_mul_le_iff₀ ht.1]
    linarith
  have := le_of_tendsto hs (by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    exact hle t ht)
  linarith

lemma descent_lemma {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (h : H → ℝ) (hd : Differentiable ℝ h) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ x y : H, ‖gradient h x - gradient h y‖ ≤ L * ‖x - y‖) (x y : H) :
    h y ≤ h x + ⟪gradient h x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  set v := y - x with hv
  set ψ : ℝ → ℝ := fun t => h (x + t • v) - t * ⟪gradient h x, v⟫_ℝ - L / 2 * t ^ 2 * ‖v‖ ^ 2
    with hψ
  have hψd : ∀ t, HasDerivAt ψ (⟪gradient h (x + t • v), v⟫_ℝ - ⟪gradient h x, v⟫_ℝ
      - L * t * ‖v‖ ^ 2) t := by
    intro t
    have h1 := line_deriv h hd x v t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪gradient h x, v⟫_ℝ) ⟪gradient h x, v⟫_ℝ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient h x, v⟫_ℝ
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖v‖ ^ 2) (L * t * ‖v‖ ^ 2) t := by
      have hp : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
      have := (hp.const_mul (L / 2)).mul_const (‖v‖ ^ 2)
      exact this.congr_deriv (by ring)
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hψd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hψd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hψd t).deriv]
      have hcs : ⟪gradient h (x + t • v) - gradient h x, v⟫_ℝ ≤
          ‖gradient h (x + t • v) - gradient h x‖ * ‖v‖ := real_inner_le_norm _ _
      have hlip := hL (x + t • v) x
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1] at hlip
      rw [inner_sub_left] at hcs
      have := mul_le_mul_of_nonneg_right hlip (norm_nonneg v)
      nlinarith
  have h01 := hanti ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [hψ, zero_smul, add_zero, zero_mul, sub_zero, one_smul, one_mul, one_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h01
  rw [hv, add_sub_cancel] at h01
  linarith

/-- Baillon–Haddad: `∇h` is `β`-cocoercive. -/
lemma baillon_haddad {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (β : ℝ) (hβ : 0 < β) (h : H → ℝ) (hh : IsSmoothConvex β h) :
    IsCocoercive β (gradient h) := by
  obtain ⟨hc, hd, hL⟩ := hh
  set L := β⁻¹ with hLdef
  have hL0 : 0 < L := inv_pos.2 hβ
  have half : ∀ x y : H, h x + ⟪gradient h x, y - x⟫_ℝ
      + 1 / (2 * L) * ‖gradient h y - gradient h x‖ ^ 2 ≤ h y := by
    intro x y
    set d := gradient h y - gradient h x with hd'
    set w := y - (1 / L) • d with hw
    have g1 := grad_ineq h hc hd x w
    have g2 := descent_lemma h hd L hL0.le hL y w
    have e1 : w - y = -((1 / L) • d) := by rw [hw]; abel
    have e2 : w - x = (y - x) - (1 / L) • d := by rw [hw]; abel
    rw [e1, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < 1 / L)] at g2
    rw [e2, inner_sub_right, real_inner_smul_right] at g1
    have hdd : ⟪gradient h y, d⟫_ℝ - ⟪gradient h x, d⟫_ℝ = ‖d‖ ^ 2 := by
      rw [← inner_sub_left, ← hd', real_inner_self_eq_norm_sq]
    have e3 : L / 2 * (1 / L * ‖d‖) ^ 2 = 1 / (2 * L) * ‖d‖ ^ 2 := by field_simp
    have e4 : 1 / L * ⟪gradient h y, d⟫_ℝ - 1 / L * ⟪gradient h x, d⟫_ℝ = 1 / L * ‖d‖ ^ 2 := by
      rw [← mul_sub, hdd]
    have e5 : 1 / L * ‖d‖ ^ 2 - 1 / (2 * L) * ‖d‖ ^ 2 = 1 / (2 * L) * ‖d‖ ^ 2 := by
      field_simp; ring
    linarith
  intro x y
  have h1 := half x y
  have h2 := half y x
  have n : ‖gradient h x - gradient h y‖ = ‖gradient h y - gradient h x‖ := norm_sub_rev _ _
  rw [n] at h2
  have e : ⟪gradient h x - gradient h y, x - y⟫_ℝ =
      -(⟪gradient h x, y - x⟫_ℝ + ⟪gradient h y, x - y⟫_ℝ) := by
    rw [inner_sub_left, show y - x = -(x - y) by abel, inner_neg_right]; ring
  rw [e, n]
  have e6 : 1 / (2 * L) + 1 / (2 * L) = β := by rw [hLdef]; field_simp; ring
  nlinarith

/-! ### Prox operators -/

lemma real_limit_le'' {A B C : ℝ} (h : ∀ t : ℝ, 0 < t → t ≤ 1 → A ≤ B + t * C) : A ≤ B := by
  have ht : Tendsto (fun t : ℝ => B + t * C) (𝓝[>] 0) (𝓝 (B + 0 * C)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    exact ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0)
  rw [zero_mul, add_zero] at ht
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t htt
  exact h t htt.1 htt.2.le

lemma prox_fin {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (f : H → EReal) (P : H → H) (hf : IsProperClosedConvex f) (hP : IsProx γ f P)
    (x : H) : f (P x) ≠ ⊤ := by
  obtain ⟨hbot, ⟨x0, hx0⟩, _, _⟩ := hf
  intro htop
  have h1 := hP x x0
  rw [htop, EReal.top_add_coe, ← EReal.coe_toReal hx0 (hbot x0), ← EReal.coe_add] at h1
  exact absurd h1 (not_le.2 (EReal.coe_lt_top _))

/-- Prox inequality: `⟪x - P x, y - P x⟫ ≤ γ (f y - f (P x))` in real form. -/
lemma prox_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (hγ : 0 < γ) (f : H → EReal) (P : H → H) (hf : IsProperClosedConvex f)
    (hP : IsProx γ f P) (x y : H) (a b : ℝ) (ha : f (P x) = a) (hb : f y = b) :
    ⟪x - P x, y - P x⟫_ℝ ≤ γ * (b - a) := by
  obtain ⟨hbot, _, _, hconv⟩ := hf
  have key : γ * (a - b) ≤ ⟪P x - x, y - P x⟫_ℝ := by
    have h := real_limit_le'' (A := a - b) (B := ⟪P x - x, y - P x⟫_ℝ / γ)
      (C := ‖y - P x‖ ^ 2 / (2 * γ)) (fun t ht0 ht1 => by
        set yt := (1 - t) • P x + t • y with hyt
        have hm1 : (P x, a) ∈ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)} := by
          simp only [Set.mem_ofPred_eq]; rw [ha]
        have hm2 : (y, b) ∈ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)} := by
          simp only [Set.mem_ofPred_eq]; rw [hb]
        have hc := hconv hm1 hm2 (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
        simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
          smul_eq_mul] at hc
        have hq := hP x yt
        rw [ha] at hq
        have hp2 : ((a + ‖P x - x‖ ^ 2 / (2 * γ) : ℝ) : EReal) ≤
            (((1 - t) * a + t * b + ‖yt - x‖ ^ 2 / (2 * γ) : ℝ) : EReal) := by
          rw [EReal.coe_add, EReal.coe_add]
          exact hq.trans (add_le_add hc le_rfl)
        rw [EReal.coe_le_coe_iff] at hp2
        have hexp : yt - x = (P x - x) + t • (y - P x) := by rw [hyt]; module
        rw [hexp, norm_add_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs,
          abs_of_pos ht0] at hp2
        have e : ‖P x - x‖ ^ 2 / (2 * γ) = ‖P x - x‖ ^ 2 / (2 * γ) := rfl
        have k1 : t * (a - b) ≤ t * (⟪P x - x, y - P x⟫_ℝ / γ + t * (‖y - P x‖ ^ 2 / (2 * γ))) := by
          have e2 : (‖P x - x‖ ^ 2 + 2 * (t * ⟪P x - x, y - P x⟫_ℝ) + (t * ‖y - P x‖) ^ 2) / (2 * γ)
              = ‖P x - x‖ ^ 2 / (2 * γ) + t * (⟪P x - x, y - P x⟫_ℝ / γ
                + t * (‖y - P x‖ ^ 2 / (2 * γ))) := by
            field_simp; ring
          rw [e2] at hp2
          nlinarith
        exact le_of_mul_le_mul_left k1 ht0)
    rw [le_div_iff₀ hγ] at h
    linarith
  have e : ⟪x - P x, y - P x⟫_ℝ = -⟪P x - x, y - P x⟫_ℝ := by
    rw [← inner_neg_left, neg_sub]
  linarith

lemma prox_firm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (hγ : 0 < γ) (f : H → EReal) (P : H → H) (hf : IsProperClosedConvex f)
    (hP : IsProx γ f P) : IsFirmlyNonexpansive P := by
  intro x y
  have hbot := hf.1
  have fx := EReal.coe_toReal (prox_fin γ f P hf hP x) (hbot _)
  have fy := EReal.coe_toReal (prox_fin γ f P hf hP y) (hbot _)
  have h1 := prox_ineq γ hγ f P hf hP x (P y) _ _ fx.symm fy.symm
  have h2 := prox_ineq γ hγ f P hf hP y (P x) _ _ fy.symm fx.symm
  have e1 : ⟪x - P x, P y - P x⟫_ℝ + ⟪y - P y, P x - P y⟫_ℝ =
      ‖P x - P y‖ ^ 2 - ⟪P x - P y, x - y⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    rw [real_inner_comm x (P x), real_inner_comm x (P y), real_inner_comm y (P x),
      real_inner_comm y (P y), real_inner_comm (P x) (P y)]
    ring
  linarith

lemma splitting_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (proxf proxg gradh : H → H) (γ : ℝ) :
    splittingOp proxf proxg gradh γ = threeOp γ proxf proxg gradh := rfl

lemma algZ_succ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (proxf proxg gradh : H → H) (γ : ℝ) (z0 : H) (k : ℕ) :
    algZ proxf proxg gradh γ z0 (k + 1) =
      splittingOp proxf proxg gradh γ (algZ proxf proxg gradh γ z0 k) := by
  simp only [algZ, splittingOp]; abel

/-- Nonexpansiveness of the splitting operator towards a fixed point, with the gradient term. -/
lemma split_key {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (h : H → ℝ) (β γ ε : ℝ) (hβ : 0 < β) (hγ : 0 < γ) (hε : 0 < ε)
    (hf : IsProperClosedConvex f) (hg : IsProperClosedConvex g) (hh : IsSmoothConvex β h)
    (proxf proxg : H → H) (hproxf : IsProx γ f proxf) (hproxg : IsProx γ g proxg) (z w : H) :
    ‖splittingOp proxf proxg (gradient h) γ z - splittingOp proxf proxg (gradient h) γ w‖ ^ 2
      ≤ ‖z - w‖ ^ 2 - (1 - ε) * ‖(z - splittingOp proxf proxg (gradient h) γ z)
          - (w - splittingOp proxf proxg (gradient h) γ w)‖ ^ 2
        - γ * (2 * β - γ / ε) * ‖gradient h (proxg z) - gradient h (proxg w)‖ ^ 2 := by
  rw [splitting_eq]
  exact cr_key_ineq proxf proxg (gradient h) β γ ε (prox_firm γ hγ f proxf hf hproxf)
    (prox_firm γ hγ g proxg hg hproxg) (baillon_haddad β hβ h hh) hγ hε z w

theorem fejer_monotone
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (h : H → ℝ) (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ) (hγβ : γ < 2 * β)
    (hf : IsProperClosedConvex f) (hg : IsProperClosedConvex g) (hh : IsSmoothConvex β h)
    (proxf proxg : H → H) (hproxf : IsProx γ f proxf) (hproxg : IsProx γ g proxg)
    (z0 zstar : H) (hfix : splittingOp proxf proxg (gradient h) γ zstar = zstar) :
    Antitone (fun j : ℕ => ‖algZ proxf proxg (gradient h) γ z0 j - zstar‖) := by
  apply antitone_nat_of_succ_le
  intro j
  have hε : 0 < γ / (2 * β) := by positivity
  have hk := split_key f g h β γ (γ / (2 * β)) hβ hγ hε hf hg hh proxf proxg hproxf hproxg
    (algZ proxf proxg (gradient h) γ z0 j) zstar
  rw [hfix] at hk
  have e : γ * (2 * β - γ / (γ / (2 * β))) = 0 := by field_simp; ring
  rw [e, zero_mul, sub_zero] at hk
  have h1 : 0 ≤ 1 - γ / (2 * β) := by rw [sub_nonneg, div_le_one (by positivity)]; linarith
  have h2 : ‖splittingOp proxf proxg (gradient h) γ (algZ proxf proxg (gradient h) γ z0 j)
      - zstar‖ ^ 2 ≤ ‖algZ proxf proxg (gradient h) γ z0 j - zstar‖ ^ 2 := by
    nlinarith [sq_nonneg ‖(algZ proxf proxg (gradient h) γ z0 j -
      splittingOp proxf proxg (gradient h) γ (algZ proxf proxg (gradient h) γ z0 j)) -
      (zstar - zstar)‖]
  show ‖algZ proxf proxg (gradient h) γ z0 (j + 1) - zstar‖ ≤ _
  rw [algZ_succ]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

lemma firm_nonexp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (P : H → H)
    (hP : IsFirmlyNonexpansive P) (x y : H) : ‖P x - P y‖ ≤ ‖x - y‖ := by
  have h := hP x y
  have hcs := real_inner_le_norm (P x - P y) (x - y)
  by_cases h0 : ‖P x - P y‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖P x - P y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

lemma firm_reflect {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (P : H → H)
    (hP : IsFirmlyNonexpansive P) (x y : H) :
    ‖((2 : ℝ) • P x - x) - ((2 : ℝ) • P y - y)‖ ≤ ‖x - y‖ := by
  have h := hP x y
  have e : ((2 : ℝ) • P x - x) - ((2 : ℝ) • P y - y) = (2 : ℝ) • (P x - P y) - (x - y) := by
    module
  rw [e]
  have hsq : ‖(2 : ℝ) • (P x - P y) - (x - y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_left, Real.norm_eq_abs]
    norm_num
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

theorem iterates_in_ball
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (h : H → ℝ) (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ) (hγβ : γ < 2 * β)
    (hf : IsProperClosedConvex f) (hg : IsProperClosedConvex g) (hh : IsSmoothConvex β h)
    (proxf proxg : H → H) (hproxf : IsProx γ f proxf) (hproxg : IsProx γ g proxg)
    (z0 zstar : H) (hfix : splittingOp proxf proxg (gradient h) γ zstar = zstar) :
    ∀ j : ℕ, algXf proxf proxg (gradient h) γ z0 j ∈ Metric.closedBall (proxg zstar) ((1 + γ / β) * ‖z0 - zstar‖) ∧
      algXg proxf proxg (gradient h) γ z0 j ∈ Metric.closedBall (proxg zstar) ((1 + γ / β) * ‖z0 - zstar‖) := by
  intro j
  have hfej := fejer_monotone f g h β γ hβ hγ hγβ hf hg hh proxf proxg hproxf hproxg z0 zstar hfix
  have hdj : ‖algZ proxf proxg (gradient h) γ z0 j - zstar‖ ≤ ‖z0 - zstar‖ :=
    hfej (Nat.zero_le j)
  set zj := algZ proxf proxg (gradient h) γ z0 j with hzj
  have hPf := prox_firm γ hγ f proxf hf hproxf
  have hPg := prox_firm γ hγ g proxg hg hproxg
  have hlip := hh.2.2
  have hg1 : ‖proxg zj - proxg zstar‖ ≤ ‖zj - zstar‖ := firm_nonexp proxg hPg zj zstar
  have hfixf : proxf ((2 : ℝ) • proxg zstar - zstar - γ • gradient h (proxg zstar)) = proxg zstar := by
    have := hfix
    simp only [splittingOp] at this
    calc proxf ((2 : ℝ) • proxg zstar - zstar - γ • gradient h (proxg zstar))
        = (proxf ((2 : ℝ) • proxg zstar - zstar - γ • gradient h (proxg zstar)) + zstar
            - proxg zstar) - zstar + proxg zstar := by abel
      _ = proxg zstar := by rw [this]; abel
  have hnn : 0 ≤ ‖z0 - zstar‖ := norm_nonneg _
  have hγβ' : 0 ≤ γ / β := by positivity
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_eq_norm]
    show ‖proxf ((2 : ℝ) • proxg zj - zj - γ • gradient h (proxg zj)) - proxg zstar‖ ≤ _
    rw [← hfixf]
    have h1 := firm_nonexp proxf hPf ((2 : ℝ) • proxg zj - zj - γ • gradient h (proxg zj))
      ((2 : ℝ) • proxg zstar - zstar - γ • gradient h (proxg zstar))
    have e : ((2 : ℝ) • proxg zj - zj - γ • gradient h (proxg zj)) -
        ((2 : ℝ) • proxg zstar - zstar - γ • gradient h (proxg zstar)) =
        (((2 : ℝ) • proxg zj - zj) - ((2 : ℝ) • proxg zstar - zstar))
          - γ • (gradient h (proxg zj) - gradient h (proxg zstar)) := by module
    rw [e] at h1
    have h2 := norm_sub_le (((2 : ℝ) • proxg zj - zj) - ((2 : ℝ) • proxg zstar - zstar))
      (γ • (gradient h (proxg zj) - gradient h (proxg zstar)))
    have h3 := firm_reflect proxg hPg zj zstar
    have h4 : ‖γ • (gradient h (proxg zj) - gradient h (proxg zstar))‖ ≤ γ / β * ‖zj - zstar‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
      have := hlip (proxg zj) (proxg zstar)
      have h5 : β⁻¹ * ‖proxg zj - proxg zstar‖ ≤ β⁻¹ * ‖zj - zstar‖ :=
        mul_le_mul_of_nonneg_left hg1 (inv_nonneg.2 hβ.le)
      calc γ * ‖gradient h (proxg zj) - gradient h (proxg zstar)‖ ≤ γ * (β⁻¹ * ‖zj - zstar‖) :=
            mul_le_mul_of_nonneg_left (this.trans h5) hγ.le
        _ = γ / β * ‖zj - zstar‖ := by ring
    have h6 : γ / β * ‖zj - zstar‖ ≤ γ / β * ‖z0 - zstar‖ := mul_le_mul_of_nonneg_left hdj hγβ'
    nlinarith
  · rw [Metric.mem_closedBall, dist_eq_norm]
    show ‖proxg zj - proxg zstar‖ ≤ _
    nlinarith [mul_nonneg hγβ' hnn]

theorem gradient_tail_sum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (h : H → ℝ) (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ) (hγβ : γ < 2 * β)
    (hf : IsProperClosedConvex f) (hg : IsProperClosedConvex g) (hh : IsSmoothConvex β h)
    (proxf proxg : H → H) (hproxf : IsProx γ f proxf) (hproxg : IsProx γ g proxg)
    (z0 zstar : H) (hfix : splittingOp proxf proxg (gradient h) γ zstar = zstar)
    (ε : ℝ) (hε₁ : γ / (2 * β) < ε) (hε₂ : ε < 1) :
    Summable (fun i : ℕ => ‖gradient h (algXg proxf proxg (gradient h) γ z0 i) - gradient h (proxg zstar)‖ ^ 2) ∧
      ∀ k : ℕ, ∑' i : ℕ, ‖gradient h (algXg proxf proxg (gradient h) γ z0 (i + k)) - gradient h (proxg zstar)‖ ^ 2 ≤
        ‖algZ proxf proxg (gradient h) γ z0 k - zstar‖ ^ 2 / (γ * (2 * β - γ / ε)) := by
  have hε0 : 0 < ε := lt_trans (by positivity) hε₁
  have hκ' : 0 < 2 * β - γ / ε := by
    rw [sub_pos, div_lt_iff₀ hε0]
    rw [div_lt_iff₀ (by positivity)] at hε₁
    linarith
  set κ := γ * (2 * β - γ / ε) with hκ
  have hκpos : 0 < κ := mul_pos hγ hκ'
  set z := algZ proxf proxg (gradient h) γ z0 with hz
  set c : ℕ → ℝ := fun i =>
    ‖gradient h (algXg proxf proxg (gradient h) γ z0 i) - gradient h (proxg zstar)‖ ^ 2 with hc
  have hc0 : ∀ i, 0 ≤ c i := fun i => sq_nonneg _
  have hdesc : ∀ i, κ * c i ≤ ‖z i - zstar‖ ^ 2 - ‖z (i + 1) - zstar‖ ^ 2 := by
    intro i
    have hk := split_key f g h β γ ε hβ hγ hε0 hf hg hh proxf proxg hproxf hproxg (z i) zstar
    rw [hfix] at hk
    have hzs : z (i + 1) = splittingOp proxf proxg (gradient h) γ (z i) := algZ_succ _ _ _ _ _ _
    rw [← hzs] at hk
    have h1 : 0 ≤ (1 - ε) * ‖(z i - z (i + 1)) - (zstar - zstar)‖ ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    have hci : c i = ‖gradient h (proxg (z i)) - gradient h (proxg zstar)‖ ^ 2 := rfl
    rw [hci]
    linarith
  have hpartial : ∀ k n, ∑ i ∈ Finset.range n, c (i + k) ≤ ‖z k - zstar‖ ^ 2 / κ := by
    intro k n
    have htel : ∀ n, κ * ∑ i ∈ Finset.range n, c (i + k) ≤
        ‖z k - zstar‖ ^ 2 - ‖z (n + k) - zstar‖ ^ 2 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, mul_add]
        have := hdesc (n + k)
        rw [show n + 1 + k = n + k + 1 by ring]
        linarith
    rw [le_div_iff₀ hκpos]
    have := htel n
    nlinarith [sq_nonneg ‖z (n + k) - zstar‖]
  refine ⟨?_, fun k => ?_⟩
  · have := summable_of_sum_range_le hc0 (hpartial 0)
    simpa using this
  · exact Real.tsum_le_of_sum_range_le (fun i => hc0 (i + k)) (hpartial k)

theorem one_step_inequality
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (h : H → ℝ) (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ) (hγβ : γ < 2 * β)
    (hf : IsProperClosedConvex f) (hg : IsProperClosedConvex g) (hh : IsSmoothConvex β h)
    (proxf proxg : H → H) (hproxf : IsProx γ f proxf) (hproxg : IsProx γ g proxg)
    (z0 zstar : H) (hfix : splittingOp proxf proxg (gradient h) γ zstar = zstar) :
    ∀ k : ℕ,
      ((2 * γ : ℝ) : EReal) *
          (f (algXf proxf proxg (gradient h) γ z0 k) + g (algXg proxf proxg (gradient h) γ z0 k) + ((h (algXg proxf proxg (gradient h) γ z0 k) : ℝ) : EReal)
            - objective f g h (proxg zstar)) ≤
        ((‖algZ proxf proxg (gradient h) γ z0 k - proxg zstar‖ ^ 2 - ‖algZ proxf proxg (gradient h) γ z0 (k + 1) - proxg zstar‖ ^ 2
            - ‖algZ proxf proxg (gradient h) γ z0 k - algZ proxf proxg (gradient h) γ z0 (k + 1)‖ ^ 2
            + 2 * γ * ⟪algZ proxf proxg (gradient h) γ z0 k - algZ proxf proxg (gradient h) γ z0 (k + 1), gradient h (algXg proxf proxg (gradient h) γ z0 k)⟫_ℝ : ℝ) : EReal) := by
  intro k
  set x := proxg zstar with hx
  set z := algZ proxf proxg (gradient h) γ z0 k with hz
  set xg := algXg proxf proxg (gradient h) γ z0 k with hxg
  set xf := algXf proxf proxg (gradient h) γ z0 k with hxf
  have hxg' : xg = proxg z := rfl
  have hxf' : xf = proxf ((2 : ℝ) • xg - z - γ • gradient h xg) := rfl
  have hz1 : algZ proxf proxg (gradient h) γ z0 (k + 1) = z + (xf - xg) := rfl
  rw [hz1]
  have hff := prox_fin γ f proxf hf hproxf ((2 : ℝ) • xg - z - γ • gradient h xg)
  have hgf := prox_fin γ g proxg hg hproxg z
  rw [← hxf'] at hff
  rw [← hxg'] at hgf
  have hfb := hf.1
  have hgb := hg.1
  set a := (f xf).toReal with ha
  set b := (g xg).toReal with hb
  have efa : f xf = a := (EReal.coe_toReal hff (hfb _)).symm
  have egb : g xg = b := (EReal.coe_toReal hgf (hgb _)).symm
  by_cases hfin : f x ≠ ⊤ ∧ g x ≠ ⊤
  · obtain ⟨hfx, hgx⟩ := hfin
    set c := (f x).toReal with hc
    set d := (g x).toReal with hd
    have efc : f x = c := (EReal.coe_toReal hfx (hfb _)).symm
    have egd : g x = d := (EReal.coe_toReal hgx (hgb _)).symm
    unfold objective
    rw [efa, egb, efc, egd, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add,
      ← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_le_coe_iff]
    -- the three inequalities
    have pg := prox_ineq γ hγ g proxg hg hproxg z x b d (by rw [← hxg']; exact egb) egd
    have pf := prox_ineq γ hγ f proxf hf hproxf ((2 : ℝ) • xg - z - γ • gradient h xg) x a c
      (by rw [← hxf']; exact efa) efc
    rw [← hxg'] at pg
    rw [← hxf'] at pf
    have ph := grad_ineq h hh.1 hh.2.1 xg x
    -- algebra
    set δ := z - (z + (xf - xg)) with hδ
    have eδ : δ = xg - xf := by rw [hδ]; abel
    have e1 : (2 : ℝ) • xg - z - γ • gradient h xg - xf = δ - (z - xg) - γ • gradient h xg := by
      rw [eδ]; module
    have e2 : x - xf = (x - xg) + δ := by rw [eδ]; abel
    rw [e1, e2] at pf
    have e3 : z + (xf - xg) - x = ((z - xg) - (x - xg)) - δ := by rw [eδ]; abel
    rw [e3, show z - x = (z - xg) - (x - xg) by abel]
    clear_value δ
    set w := z - xg with hw
    set u := x - xg with hu
    set G := gradient h xg with hG
    clear_value w u G
    rw [norm_sub_sq_real (w - u) δ, inner_sub_left w u δ]
    rw [inner_add_right, inner_sub_left, inner_sub_left, inner_sub_left, inner_sub_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at pf
    have c1 : ⟪w, δ⟫_ℝ = ⟪δ, w⟫_ℝ := real_inner_comm _ _
    have c2 : ⟪u, δ⟫_ℝ = ⟪δ, u⟫_ℝ := real_inner_comm _ _
    have c3 : ⟪δ, G⟫_ℝ = ⟪G, δ⟫_ℝ := real_inner_comm _ _
    have c4 : ⟪w, u⟫_ℝ = ⟪w, u⟫_ℝ := rfl
    nlinarith [mul_le_mul_of_nonneg_left ph hγ.le]
  · -- the objective at x is infinite
    have htop : objective f g h x = ⊤ := by
      unfold objective
      rcases not_and_or.1 hfin with h1 | h1 <;> push Not at h1
      · rw [h1, EReal.top_add_of_ne_bot (hgb x), EReal.top_add_coe]
      · rw [h1, EReal.add_top_of_ne_bot (hfb x), EReal.top_add_coe]
    rw [htop, efa, egb, ← EReal.coe_add, ← EReal.coe_add, EReal.sub_top,
      EReal.coe_mul_bot_of_pos (by positivity)]
    exact bot_le

lemma abel_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (z : ℕ → H) (zs : H) (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i : ℝ) + 1) • (z (i + 1) - z i) =
      (n : ℝ) • (z n - zs) - ∑ i ∈ Finset.range n, (z i - zs) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    push_cast
    module

theorem weighted_ergodic_distance
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (h : H → ℝ) (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ) (hγβ : γ < 2 * β)
    (hf : IsProperClosedConvex f) (hg : IsProperClosedConvex g) (hh : IsSmoothConvex β h)
    (proxf proxg : H → H) (hproxf : IsProx γ f proxf) (hproxg : IsProx γ g proxg)
    (z0 zstar : H) (hfix : splittingOp proxf proxg (gradient h) γ zstar = zstar) :
    ∀ k : ℕ, ‖weightedErgodic (algXf proxf proxg (gradient h) γ z0) k - weightedErgodic (algXg proxf proxg (gradient h) γ z0) k‖ ≤
      5 * ‖z0 - zstar‖ / ((k : ℝ) + 1) := by
  intro k
  have hfej := fejer_monotone f g h β γ hβ hγ hγβ hf hg hh proxf proxg hproxf hproxg z0 zstar hfix
  set z := algZ proxf proxg (gradient h) γ z0 with hz
  have hdist : ∀ j, ‖z j - zstar‖ ≤ ‖z0 - zstar‖ := fun j => hfej (Nat.zero_le j)
  have hstep : ∀ i, algXf proxf proxg (gradient h) γ z0 i - algXg proxf proxg (gradient h) γ z0 i
      = z (i + 1) - z i := by
    intro i
    have : z (i + 1) = z i + (algXf proxf proxg (gradient h) γ z0 i
        - algXg proxf proxg (gradient h) γ z0 i) := rfl
    rw [this]; abel
  have hdiff : weightedErgodic (algXf proxf proxg (gradient h) γ z0) k
      - weightedErgodic (algXg proxf proxg (gradient h) γ z0) k =
      (2 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) •
        ∑ i ∈ Finset.range (k + 1), ((i : ℝ) + 1) • (z (i + 1) - z i) := by
    simp only [weightedErgodic]
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← smul_sub, hstep]
  rw [hdiff, abel_sum z zstar (k + 1), norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hsum : ‖((k + 1 : ℕ) : ℝ) • (z (k + 1) - zstar) - ∑ i ∈ Finset.range (k + 1), (z i - zstar)‖
      ≤ 2 * ((k : ℝ) + 1) * ‖z0 - zstar‖ := by
    have h1 := norm_sub_le (((k + 1 : ℕ) : ℝ) • (z (k + 1) - zstar))
      (∑ i ∈ Finset.range (k + 1), (z i - zstar))
    have h2 : ‖((k + 1 : ℕ) : ℝ) • (z (k + 1) - zstar)‖ ≤ ((k : ℝ) + 1) * ‖z0 - zstar‖ := by
      rw [norm_smul, Real.norm_eq_abs]; push_cast
      rw [abs_of_pos hk1]
      exact mul_le_mul_of_nonneg_left (hdist _) hk1.le
    have h3 : ‖∑ i ∈ Finset.range (k + 1), (z i - zstar)‖ ≤ ((k : ℝ) + 1) * ‖z0 - zstar‖ := by
      calc ‖∑ i ∈ Finset.range (k + 1), (z i - zstar)‖
          ≤ ∑ i ∈ Finset.range (k + 1), ‖z i - zstar‖ := norm_sum_le _ _
        _ ≤ ∑ _i ∈ Finset.range (k + 1), ‖z0 - zstar‖ := Finset.sum_le_sum (fun i _ => hdist i)
        _ = ((k : ℝ) + 1) * ‖z0 - zstar‖ := by simp
    linarith
  have hn : 0 ≤ ‖z0 - zstar‖ := norm_nonneg _
  rw [le_div_iff₀ hk1]
  have hc : 2 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) * (2 * ((k : ℝ) + 1) * ‖z0 - zstar‖) * ((k : ℝ) + 1)
      ≤ 5 * ‖z0 - zstar‖ := by
    have e : 2 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) * (2 * ((k : ℝ) + 1) * ‖z0 - zstar‖) * ((k : ℝ) + 1)
        = 4 * ‖z0 - zstar‖ * (((k : ℝ) + 1) / ((k : ℝ) + 2)) := by
      field_simp
      ring
    rw [e]
    have : ((k : ℝ) + 1) / ((k : ℝ) + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith
  have hpos : 0 ≤ 2 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by positivity
  calc 2 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) *
        ‖((k + 1 : ℕ) : ℝ) • (z (k + 1) - zstar) - ∑ i ∈ Finset.range (k + 1), (z i - zstar)‖ *
          ((k : ℝ) + 1)
      ≤ 2 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) * (2 * ((k : ℝ) + 1) * ‖z0 - zstar‖) * ((k : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_right _ hk1.le
        exact mul_le_mul_of_nonneg_left hsum hpos
    _ ≤ 5 * ‖z0 - zstar‖ := hc
/-- `n f(n) → 0` for antitone nonnegative summable sequences. -/
lemma little_o_of_antitone {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n) (hfa : Antitone f)
    (hs : Summable f) : Tendsto (fun k : ℕ => ((k : ℝ) + 1) * f k) atTop (𝓝 0) := by
  set S := fun n => ∑ i ∈ Finset.range n, f i with hS
  have hSlim : Tendsto S atTop (𝓝 (∑' i, f i)) := hs.hasSum.tendsto_sum_nat
  have hdiv : Tendsto (fun k : ℕ => k / 2) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b; exact ⟨2 * b, fun a ha => by omega⟩
  have h1 : Tendsto (fun k : ℕ => S (k + 1)) atTop (𝓝 (∑' i, f i)) :=
    hSlim.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun k : ℕ => S (k / 2)) atTop (𝓝 (∑' i, f i)) := hSlim.comp hdiv
  have h3 : Tendsto (fun k : ℕ => 2 * (S (k + 1) - S (k / 2))) atTop (𝓝 (2 * (∑' i, f i - ∑' i, f i))) :=
    (h1.sub h2).const_mul 2
  rw [sub_self, mul_zero] at h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun k => ?_) (fun k => ?_)
  · exact mul_nonneg (by positivity) (hf0 k)
  · have hle : k / 2 ≤ k + 1 := by omega
    have hsum : S (k + 1) - S (k / 2) = ∑ i ∈ Finset.Ico (k / 2) (k + 1), f i := by
      simp only [hS]; rw [Finset.sum_Ico_eq_sub _ hle]
    rw [hsum]
    have hcard := Finset.card_nsmul_le_sum (Finset.Ico (k / 2) (k + 1)) f (f k)
      (fun i hi => hfa (Finset.mem_Ico.1 hi).2.le |> fun h => by
        have := Finset.mem_Ico.1 hi; exact hfa (Nat.lt_succ_iff.1 this.2))
    rw [Nat.card_Ico, nsmul_eq_mul] at hcard
    have hc : ((k : ℝ) + 1) ≤ 2 * (((k + 1 - k / 2 : ℕ) : ℝ)) := by
      have : 2 * (k / 2) ≤ k := Nat.mul_div_le k 2
      have h' : (k + 1 - k / 2 : ℕ) = k + 1 - k / 2 := rfl
      rw [Nat.cast_sub hle]
      push_cast
      have : (2 : ℝ) * ((k / 2 : ℕ) : ℝ) ≤ k := by exact_mod_cast this
      linarith
    nlinarith [hf0 k]


lemma ereal_real {e : EReal} (h1 : e ≠ ⊤) (h2 : e ≠ ⊥) : ∃ r : ℝ, e = r :=
  ⟨e.toReal, (EReal.coe_toReal h1 h2).symm⟩

theorem last_iterate_rate
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (h : H → ℝ) (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ) (hγβ : γ < 2 * β)
    (hf : IsProperClosedConvex f) (hg : IsProperClosedConvex g) (hh : IsSmoothConvex β h)
    (proxf proxg : H → H) (hproxf : IsProx γ f proxf) (hproxg : IsProx γ g proxg)
    (z0 zstar : H) (hfix : splittingOp proxf proxg (gradient h) γ zstar = zstar)
    (L : NNReal)
    (hfin : ∀ x ∈ Metric.closedBall (proxg zstar) ((1 + γ / β) * ‖z0 - zstar‖), f x ≠ ⊤)
    (hLip : LipschitzOnWith L (fun x => (f x).toReal)
      (Metric.closedBall (proxg zstar) ((1 + γ / β) * ‖z0 - zstar‖))) :
    objective f g h (proxg zstar) ≠ ⊤ ∧
      (∀ k : ℕ, objective f g h (algXg proxf proxg (gradient h) γ z0 k) ≠ ⊤) ∧
      Tendsto (fun k : ℕ => Real.sqrt ((k : ℝ) + 1) *
          ((objective f g h (algXg proxf proxg (gradient h) γ z0 k)).toReal - (objective f g h (proxg zstar)).toReal))
        atTop (𝓝 0) := by
  set x := proxg zstar with hx
  set r := (1 + γ / β) * ‖z0 - zstar‖ with hr
  have hr0 : 0 ≤ r := by positivity
  have hball := iterates_in_ball f g h β γ hβ hγ hγβ hf hg hh proxf proxg hproxf hproxg z0 zstar hfix
  have hfej := fejer_monotone f g h β γ hβ hγ hγβ hf hg hh proxf proxg hproxf hproxg z0 zstar hfix
  set z := algZ proxf proxg (gradient h) γ z0 with hz
  set xg := algXg proxf proxg (gradient h) γ z0 with hxg
  set xf := algXf proxf proxg (gradient h) γ z0 with hxf
  have hfb := hf.1
  have hgb := hg.1
  -- finiteness
  have fx : f x ≠ ⊤ := hfin x (Metric.mem_closedBall_self hr0)
  have gx : g x ≠ ⊤ := prox_fin γ g proxg hg hproxg zstar
  have fxg : ∀ k, f (xg k) ≠ ⊤ := fun k => hfin _ (hball k).2
  have fxf : ∀ k, f (xf k) ≠ ⊤ := fun k => hfin _ (hball k).1
  have gxg : ∀ k, g (xg k) ≠ ⊤ := fun k => prox_fin γ g proxg hg hproxg (z k)
  have hobj : ∀ y, f y ≠ ⊤ → g y ≠ ⊤ →
      objective f g h y = (((f y).toReal + (g y).toReal + h y : ℝ) : EReal) := by
    intro y h1 h2
    obtain ⟨a, ha⟩ := ereal_real h1 (hfb y)
    obtain ⟨b, hb⟩ := ereal_real h2 (hgb y)
    unfold objective
    rw [ha, hb, EReal.toReal_coe, EReal.toReal_coe, ← EReal.coe_add, ← EReal.coe_add]
  refine ⟨by rw [hobj x fx gx]; exact EReal.coe_ne_top _,
    fun k => by rw [hobj _ (fxg k) (gxg k)]; exact EReal.coe_ne_top _, ?_⟩
  simp_rw [hobj _ (fxg _) (gxg _), hobj x fx gx, EReal.toReal_coe]
  set Fs := (f x).toReal + (g x).toReal + h x with hFs
  -- optimality: F(y) ≥ F(x) on the finite domain
  have hfixf : proxf ((2 : ℝ) • x - zstar - γ • gradient h x) = x := by
    have := hfix
    simp only [splittingOp] at this
    calc proxf ((2 : ℝ) • x - zstar - γ • gradient h x)
        = (proxf ((2 : ℝ) • x - zstar - γ • gradient h x) + zstar - x) - zstar + x := by abel
      _ = x := by rw [this]; abel
  have hopt : ∀ y, f y ≠ ⊤ → g y ≠ ⊤ → Fs ≤ (f y).toReal + (g y).toReal + h y := by
    intro y h1 h2
    have p1 := prox_ineq γ hγ f proxf hf hproxf ((2 : ℝ) • x - zstar - γ • gradient h x) y
      (f x).toReal (f y).toReal (by rw [hfixf]; exact (EReal.coe_toReal fx (hfb x)).symm)
      (EReal.coe_toReal h1 (hfb y)).symm
    have p2 := prox_ineq γ hγ g proxg hg hproxg zstar y (g x).toReal (g y).toReal
      (EReal.coe_toReal gx (hgb x)).symm (EReal.coe_toReal h2 (hgb y)).symm
    rw [hfixf] at p1
    have p3 := grad_ineq h hh.1 hh.2.1 x y
    have e : ((2 : ℝ) • x - zstar - γ • gradient h x - x) + (zstar - x) = -(γ • gradient h x) := by
      module
    have hsum : ⟪(2 : ℝ) • x - zstar - γ • gradient h x - x, y - x⟫_ℝ + ⟪zstar - x, y - x⟫_ℝ
        = -(γ * ⟪gradient h x, y - x⟫_ℝ) := by
      rw [← inner_add_left, e, inner_neg_left, real_inner_smul_left]
    have := mul_le_mul_of_nonneg_left p3 hγ.le
    rw [hFs]
    nlinarith
  -- the nonexpansive estimate for T
  set ε := γ / (2 * β) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : 0 < 1 - ε := by rw [hε, sub_pos, div_lt_one (by positivity)]; linarith
  have hκ0 : γ * (2 * β - γ / ε) = 0 := by rw [hε]; field_simp; ring
  have hzs : ∀ k, z (k + 1) = splittingOp proxf proxg (gradient h) γ (z k) :=
    fun k => algZ_succ _ _ _ _ _ _
  set R : ℕ → ℝ := fun k => ‖z k - z (k + 1)‖ ^ 2 with hR
  have hR0 : ∀ k, 0 ≤ R k := fun k => sq_nonneg _
  have hRdesc : ∀ k, (1 - ε) * R k ≤ ‖z k - zstar‖ ^ 2 - ‖z (k + 1) - zstar‖ ^ 2 := by
    intro k
    have hk := split_key f g h β γ ε hβ hγ hε0 hf hg hh proxf proxg hproxf hproxg (z k) zstar
    rw [hfix, hκ0, zero_mul, sub_zero, ← hzs, sub_self, sub_zero] at hk
    simp only [hR]; linarith
  have hRanti : Antitone R := by
    apply antitone_nat_of_succ_le
    intro k
    have hk := split_key f g h β γ ε hβ hγ hε0 hf hg hh proxf proxg hproxf hproxg (z k) (z (k + 1))
    rw [hκ0, zero_mul, sub_zero, ← hzs, ← hzs] at hk
    have : 0 ≤ (1 - ε) * ‖z k - z (k + 1) - (z (k + 1) - z (k + 1 + 1))‖ ^ 2 :=
      mul_nonneg hε1.le (sq_nonneg _)
    simp only [hR]; linarith
  have hRsum : Summable R := by
    apply summable_of_sum_range_le hR0 (c := ‖z 0 - zstar‖ ^ 2 / (1 - ε))
    intro n
    rw [le_div_iff₀ hε1]
    have htel : ∀ n, (1 - ε) * ∑ i ∈ Finset.range n, R i ≤ ‖z 0 - zstar‖ ^ 2 - ‖z n - zstar‖ ^ 2 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ, mul_add]; linarith [hRdesc n]
    nlinarith [htel n, sq_nonneg ‖z n - zstar‖]
  have hlo := little_o_of_antitone hR0 hRanti hRsum
  have hsq : Tendsto (fun k : ℕ => Real.sqrt ((k : ℝ) + 1) * ‖z k - z (k + 1)‖) atTop (𝓝 0) := by
    have := hlo.sqrt
    rw [Real.sqrt_zero] at this
    refine this.congr (fun k => ?_)
    simp only [hR]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  -- bounds
  set M1 := ‖z0 - zstar‖ + ‖zstar - x‖ with hM1
  set M2 := β⁻¹ * r + ‖gradient h x‖ with hM2
  have hzx : ∀ k, ‖z k - x‖ ≤ M1 := by
    intro k
    have h1 : ‖z k - zstar‖ ≤ ‖z0 - zstar‖ := hfej (Nat.zero_le k)
    have h2 := norm_sub_le_norm_sub_add_norm_sub (z k) zstar x
    linarith
  have hgrad : ∀ k, ‖gradient h (xg k)‖ ≤ M2 := by
    intro k
    have h1 := hh.2.2 (xg k) x
    have h2 : ‖xg k - x‖ ≤ r := by
      have := (hball k).2; rwa [Metric.mem_closedBall, dist_eq_norm] at this
    have h3 : ‖gradient h (xg k)‖ ≤ ‖gradient h (xg k) - gradient h x‖ + ‖gradient h x‖ := by
      have := norm_add_le (gradient h (xg k) - gradient h x) (gradient h x)
      rwa [sub_add_cancel] at this
    have h4 : β⁻¹ * ‖xg k - x‖ ≤ β⁻¹ * r := mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hβ.le)
    linarith
  set K := (L : ℝ) + M1 / γ + M2 with hK
  have hupper : ∀ k, (f (xg k)).toReal + (g (xg k)).toReal + h (xg k) - Fs ≤ K * ‖z k - z (k + 1)‖ := by
    intro k
    have hos := one_step_inequality f g h β γ hβ hγ hγβ hf hg hh proxf proxg hproxf hproxg z0 zstar hfix k
    obtain ⟨a, ha⟩ := ereal_real (fxf k) (hfb _)
    obtain ⟨b, hb⟩ := ereal_real (gxg k) (hgb _)
    have hobx := hobj x fx gx
    rw [← hFs] at hobx
    change ((2 * γ : ℝ) : EReal) * (f (xf k) + g (xg k) + ((h (xg k) : ℝ) : EReal)
      - objective f g h x) ≤ _ at hos
    rw [ha, hb, hobx, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_mul,
      EReal.coe_le_coe_iff] at hos
    have hδ : z k - z (k + 1) = xg k - xf k := by
      have : z (k + 1) = z k + (xf k - xg k) := rfl
      rw [this]; abel
    -- Lipschitz
    have hL := hLip.dist_le_mul (xg k) (hball k).2 (xf k) (hball k).1
    rw [Real.dist_eq, dist_eq_norm, ← hδ] at hL
    have hfa : (f (xf k)).toReal = a := by rw [ha, EReal.toReal_coe]
    have hgb' : (g (xg k)).toReal = b := by rw [hb, EReal.toReal_coe]
    rw [hfa] at hL
    rw [hgb']
    -- norm difference bound
    set δ := z k - z (k + 1) with hδdef
    have hdiff : ‖z k - x‖ ^ 2 - ‖z (k + 1) - x‖ ^ 2 ≤ ‖δ‖ * (2 * M1) := by
      have e1 : z (k + 1) - x = (z k - x) - δ := by rw [hδdef]; abel
      rw [e1, norm_sub_sq_real (z k - x) δ]
      have hcs := real_inner_le_norm (z k - x) δ
      have := hzx k
      have := hzx (k + 1)
      have hnn := norm_nonneg δ
      have h5 : ‖z k - x‖ * ‖δ‖ ≤ M1 * ‖δ‖ := mul_le_mul_of_nonneg_right (hzx k) hnn
      nlinarith
    have hgi : ⟪δ, gradient h (xg k)⟫_ℝ ≤ ‖δ‖ * M2 := by
      have := real_inner_le_norm δ (gradient h (xg k))
      have := mul_le_mul_of_nonneg_left (hgrad k) (norm_nonneg δ)
      linarith
    have hab : |(f (xg k)).toReal - a| ≤ L * ‖δ‖ := hL
    have hab' := (abs_le.1 hab).2
    have hδsq : 0 ≤ ‖δ‖ ^ 2 := sq_nonneg _
    have key : 2 * γ * ((f (xg k)).toReal + b + h (xg k) - Fs) ≤
        2 * γ * (L * ‖δ‖) + ‖δ‖ * (2 * M1) + 2 * γ * (‖δ‖ * M2) := by
      nlinarith
    have hK' : 2 * γ * (K * ‖δ‖) = 2 * γ * (L * ‖δ‖) + ‖δ‖ * (2 * M1) + 2 * γ * (‖δ‖ * M2) := by
      rw [hK]; field_simp
    rw [← hK'] at key
    exact le_of_mul_le_mul_left key (by positivity)
  have hlow : ∀ k, 0 ≤ (f (xg k)).toReal + (g (xg k)).toReal + h (xg k) - Fs := by
    intro k; have := hopt (xg k) (fxg k) (gxg k); linarith
  have hlim : Tendsto (fun k : ℕ => K * (Real.sqrt ((k : ℝ) + 1) * ‖z k - z (k + 1)‖)) atTop (𝓝 (K * 0)) :=
    hsq.const_mul K
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => ?_) (fun k => ?_)
  · exact mul_nonneg (Real.sqrt_nonneg _) (hlow k)
  · have := mul_le_mul_of_nonneg_left (hupper k) (Real.sqrt_nonneg ((k : ℝ) + 1))
    simp only
    linarith

lemma jensen_ereal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hconv : Convex ℝ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)})
    (s : Finset ℕ) (w : ℕ → ℝ) (y : ℕ → H) (a : ℕ → ℝ)
    (hw0 : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) (ha : ∀ i ∈ s, f (y i) = a i) :
    f (∑ i ∈ s, w i • y i) ≤ ((∑ i ∈ s, w i * a i : ℝ) : EReal) := by
  have hmem := hconv.sum_mem hw0 hw1 (z := fun i => (y i, a i)) (fun i hi => by
    simp only [Set.mem_ofPred_eq]; rw [ha i hi])
  simp only [Set.mem_ofPred_eq, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hmem
  exact hmem

lemma gauss_real (n : ℕ) : ∑ i ∈ Finset.range n, ((i : ℝ) + 1) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma telescope_weighted (D : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * (D i - D (i + 1)) =
      ∑ i ∈ Finset.range n, D i - (n : ℝ) * D n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]; push_cast; ring

theorem weighted_ergodic_rate
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (h : H → ℝ) (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ) (hγβ : γ < 2 * β)
    (hf : IsProperClosedConvex f) (hg : IsProperClosedConvex g) (hh : IsSmoothConvex β h)
    (proxf proxg : H → H) (hproxf : IsProx γ f proxf) (hproxg : IsProx γ g proxg)
    (z0 zstar : H) (hfix : splittingOp proxf proxg (gradient h) γ zstar = zstar)
    (L : NNReal)
    (hfin : ∀ x ∈ Metric.closedBall (proxg zstar) ((1 + γ / β) * ‖z0 - zstar‖), f x ≠ ⊤)
    (hLip : LipschitzOnWith L (fun x => (f x).toReal)
      (Metric.closedBall (proxg zstar) ((1 + γ / β) * ‖z0 - zstar‖))) :
    objective f g h (proxg zstar) ≠ ⊤ ∧
      ∃ C : ℝ, ∀ k : ℕ,
        objective f g h (weightedErgodic (algXg proxf proxg (gradient h) γ z0) k) ≤
          objective f g h (proxg zstar) + ((C / ((k : ℝ) + 1) : ℝ) : EReal) := by
  set x := proxg zstar with hx
  set r := (1 + γ / β) * ‖z0 - zstar‖ with hr
  have hr0 : 0 ≤ r := by positivity
  have hball := iterates_in_ball f g h β γ hβ hγ hγβ hf hg hh proxf proxg hproxf hproxg z0 zstar hfix
  have hfej := fejer_monotone f g h β γ hβ hγ hγβ hf hg hh proxf proxg hproxf hproxg z0 zstar hfix
  have hwed := weighted_ergodic_distance f g h β γ hβ hγ hγβ hf hg hh proxf proxg hproxf hproxg
    z0 zstar hfix
  set z := algZ proxf proxg (gradient h) γ z0 with hz
  set xg := algXg proxf proxg (gradient h) γ z0 with hxg
  set xf := algXf proxf proxg (gradient h) γ z0 with hxf
  obtain ⟨hfb, _, _, hfconv⟩ := hf
  obtain ⟨hgb, _, _, hgconv⟩ := hg
  have hf' : IsProperClosedConvex f := ⟨hfb, ‹_›, ‹_›, hfconv⟩
  have hg' : IsProperClosedConvex g := ⟨hgb, ‹_›, ‹_›, hgconv⟩
  have fx : f x ≠ ⊤ := hfin x (Metric.mem_closedBall_self hr0)
  have gx : g x ≠ ⊤ := prox_fin γ g proxg hg' hproxg zstar
  have fxf : ∀ k, f (xf k) ≠ ⊤ := fun k => hfin _ (hball k).1
  have gxg : ∀ k, g (xg k) ≠ ⊤ := fun k => prox_fin γ g proxg hg' hproxg (z k)
  have hobj : ∀ y, f y ≠ ⊤ → g y ≠ ⊤ →
      objective f g h y = (((f y).toReal + (g y).toReal + h y : ℝ) : EReal) := by
    intro y h1 h2
    obtain ⟨a, ha⟩ := ereal_real h1 (hfb y)
    obtain ⟨b, hb⟩ := ereal_real h2 (hgb y)
    unfold objective
    rw [ha, hb, EReal.toReal_coe, EReal.toReal_coe, ← EReal.coe_add, ← EReal.coe_add]
  refine ⟨by rw [hobj x fx gx]; exact EReal.coe_ne_top _, ?_⟩
  set Fs := (f x).toReal + (g x).toReal + h x with hFs
  -- constants
  set M1 := ‖z0 - zstar‖ + ‖zstar - x‖ with hM1
  have hzx : ∀ k, ‖z k - x‖ ≤ M1 := by
    intro k
    have h1 : ‖z k - zstar‖ ≤ ‖z0 - zstar‖ := hfej (Nat.zero_le k)
    have h2 := norm_sub_le_norm_sub_add_norm_sub (z k) zstar x
    linarith
  set ε := (γ / (2 * β) + 1) / 2 with hε
  have hε1 : γ / (2 * β) < ε := by
    have : γ / (2 * β) < 1 := by rw [div_lt_one (by positivity)]; linarith
    rw [hε]; linarith
  have hε2 : ε < 1 := by
    have : γ / (2 * β) < 1 := by rw [div_lt_one (by positivity)]; linarith
    rw [hε]; linarith
  obtain ⟨hcsum, _⟩ := gradient_tail_sum f g h β γ hβ hγ hγβ hf' hg' hh proxf proxg hproxf hproxg
    z0 zstar hfix ε hε1 hε2
  set c : ℕ → ℝ := fun i => ‖gradient h (xg i) - gradient h x‖ ^ 2 with hc
  set S := ∑' i, c i with hS
  have hc0 : ∀ i, 0 ≤ c i := fun i => sq_nonneg _
  have hpart : ∀ n, ∑ i ∈ Finset.range n, c i ≤ S := fun n => hcsum.sum_le_tsum _ (fun i _ => hc0 i)
  set gs := gradient h x with hgs
  set Q := M1 ^ 2 + γ ^ 2 * S + 4 * γ * ‖z0 - zstar‖ * ‖gs‖ with hQ
  refine ⟨Q / γ + 5 * L * ‖z0 - zstar‖, fun k => ?_⟩
  -- per-step real inequality
  set a : ℕ → ℝ := fun i => (f (xf i)).toReal with ha
  set b : ℕ → ℝ := fun i => (g (xg i)).toReal with hb
  have efa : ∀ i, f (xf i) = a i := fun i => (EReal.coe_toReal (fxf i) (hfb _)).symm
  have egb : ∀ i, g (xg i) = b i := fun i => (EReal.coe_toReal (gxg i) (hgb _)).symm
  set E : ℕ → ℝ := fun i => a i + b i + h (xg i) - Fs with hE
  have hstep : ∀ i, 2 * γ * E i ≤ ‖z i - x‖ ^ 2 - ‖z (i + 1) - x‖ ^ 2 + γ ^ 2 * c i
      + 2 * γ * ⟪z i - z (i + 1), gs⟫_ℝ := by
    intro i
    have hos := one_step_inequality f g h β γ hβ hγ hγβ hf' hg' hh proxf proxg hproxf hproxg z0
      zstar hfix i
    have hobx := hobj x fx gx
    rw [← hFs] at hobx
    change ((2 * γ : ℝ) : EReal) * (f (xf i) + g (xg i) + ((h (xg i) : ℝ) : EReal)
      - objective f g h x) ≤ _ at hos
    rw [efa, egb, hobx, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_mul,
      EReal.coe_le_coe_iff] at hos
    set δ := z i - z (i + 1) with hδ
    set e := gradient h (xg i) - gs with he
    have hsplit : ⟪δ, gradient h (xg i)⟫_ℝ = ⟪δ, e⟫_ℝ + ⟪δ, gs⟫_ℝ := by
      rw [← inner_add_right, he, sub_add_cancel]
    have hsq : 0 ≤ ‖δ - γ • e‖ ^ 2 := sq_nonneg _
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs, abs_of_pos hγ]
      at hsq
    have hci : c i = ‖e‖ ^ 2 := rfl
    change 2 * γ * (a i + b i + h (xg i) - Fs) ≤ _
    rw [hci]
    nlinarith
  -- weighted sum
  set n := k + 1 with hn
  have hsumE : 2 * γ * ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * E i ≤ (n : ℝ) * Q := by
    have h1 : 2 * γ * ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * E i ≤
        ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * (‖z i - x‖ ^ 2 - ‖z (i + 1) - x‖ ^ 2)
        + γ ^ 2 * ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * c i
        + 2 * γ * ⟪∑ i ∈ Finset.range n, ((i : ℝ) + 1) • (z i - z (i + 1)), gs⟫_ℝ := by
      rw [Finset.mul_sum, Finset.mul_sum, sum_inner, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      rw [real_inner_smul_left]
      have := mul_le_mul_of_nonneg_left (hstep i) (by positivity : (0:ℝ) ≤ (i : ℝ) + 1)
      nlinarith
    have h2 := telescope_weighted (fun i => ‖z i - x‖ ^ 2) n
    have h3 : ∑ i ∈ Finset.range n, ‖z i - x‖ ^ 2 ≤ (n : ℝ) * M1 ^ 2 := by
      calc ∑ i ∈ Finset.range n, ‖z i - x‖ ^ 2 ≤ ∑ _i ∈ Finset.range n, M1 ^ 2 :=
            Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hzx i) 2)
        _ = (n : ℝ) * M1 ^ 2 := by simp
    have h4 : ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * c i ≤ (n : ℝ) * S := by
      calc ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * c i ≤ ∑ i ∈ Finset.range n, (n : ℝ) * c i := by
            apply Finset.sum_le_sum; intro i hi
            apply mul_le_mul_of_nonneg_right _ (hc0 i)
            have := Finset.mem_range.1 hi
            have : (i : ℝ) + 1 ≤ n := by exact_mod_cast this
            linarith
        _ = (n : ℝ) * ∑ i ∈ Finset.range n, c i := by rw [Finset.mul_sum]
        _ ≤ (n : ℝ) * S := mul_le_mul_of_nonneg_left (hpart n) (by positivity)
    have h5 : ∑ i ∈ Finset.range n, ((i : ℝ) + 1) • (z i - z (i + 1)) =
        -((n : ℝ) • (z n - zstar) - ∑ i ∈ Finset.range n, (z i - zstar)) := by
      rw [← abel_sum z zstar n, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro i _; rw [← smul_neg, neg_sub]
    have h6 : ‖(n : ℝ) • (z n - zstar) - ∑ i ∈ Finset.range n, (z i - zstar)‖ ≤
        2 * (n : ℝ) * ‖z0 - zstar‖ := by
      have hd : ∀ j, ‖z j - zstar‖ ≤ ‖z0 - zstar‖ := fun j => hfej (Nat.zero_le j)
      have q1 := norm_sub_le ((n : ℝ) • (z n - zstar)) (∑ i ∈ Finset.range n, (z i - zstar))
      have q2 : ‖(n : ℝ) • (z n - zstar)‖ ≤ (n : ℝ) * ‖z0 - zstar‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (hd n) (by positivity)
      have q3 : ‖∑ i ∈ Finset.range n, (z i - zstar)‖ ≤ (n : ℝ) * ‖z0 - zstar‖ := by
        calc ‖∑ i ∈ Finset.range n, (z i - zstar)‖ ≤ ∑ i ∈ Finset.range n, ‖z i - zstar‖ :=
              norm_sum_le _ _
          _ ≤ ∑ _i ∈ Finset.range n, ‖z0 - zstar‖ := Finset.sum_le_sum (fun i _ => hd i)
          _ = (n : ℝ) * ‖z0 - zstar‖ := by simp
      linarith
    have h7 : ⟪∑ i ∈ Finset.range n, ((i : ℝ) + 1) • (z i - z (i + 1)), gs⟫_ℝ ≤
        2 * (n : ℝ) * ‖z0 - zstar‖ * ‖gs‖ := by
      rw [h5, inner_neg_left]
      have := abs_real_inner_le_norm ((n : ℝ) • (z n - zstar) - ∑ i ∈ Finset.range n, (z i - zstar)) gs
      have := (abs_le.1 this).1
      have := mul_le_mul_of_nonneg_right h6 (norm_nonneg gs)
      linarith
    have hDn : 0 ≤ (n : ℝ) * ‖z n - x‖ ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left h4 (sq_nonneg γ)
    have := mul_le_mul_of_nonneg_left h7 (by positivity : (0:ℝ) ≤ 2 * γ)
    rw [hQ]
    nlinarith
  -- weights
  have hn0 : (0 : ℝ) < n := by rw [hn]; positivity
  set W := 2 / ((n : ℝ) * ((n : ℝ) + 1)) with hW
  have hWpos : 0 < W := by positivity
  have hwe : ∀ y : ℕ → H, weightedErgodic y k = ∑ i ∈ Finset.range n, (W * ((i : ℝ) + 1)) • y i := by
    intro y
    simp only [weightedErgodic, Finset.smul_sum, smul_smul]
    have e : ((k : ℝ) + 1) * ((k : ℝ) + 2) = (n : ℝ) * ((n : ℝ) + 1) := by rw [hn]; push_cast; ring
    rw [e]
  have hw0 : ∀ i ∈ Finset.range n, 0 ≤ W * ((i : ℝ) + 1) := fun i _ => by positivity
  have hw1 : ∑ i ∈ Finset.range n, W * ((i : ℝ) + 1) = 1 := by
    rw [← Finset.mul_sum, gauss_real, hW]; field_simp
  -- averages lie in the ball
  have hconvB := convex_closedBall x r
  have hxgbar : weightedErgodic xg k ∈ Metric.closedBall x r := by
    rw [hwe]; exact hconvB.sum_mem hw0 hw1 (fun i _ => (hball i).2)
  have hxfbar : weightedErgodic xf k ∈ Metric.closedBall x r := by
    rw [hwe]; exact hconvB.sum_mem hw0 hw1 (fun i _ => (hball i).1)
  -- Jensen
  have jf := jensen_ereal f hfconv (Finset.range n) (fun i => W * ((i : ℝ) + 1)) xf a hw0 hw1
    (fun i _ => efa i)
  have jg := jensen_ereal g hgconv (Finset.range n) (fun i => W * ((i : ℝ) + 1)) xg b hw0 hw1
    (fun i _ => egb i)
  rw [← hwe] at jf jg
  have jh := hh.1.map_sum_le (t := Finset.range n) (w := fun i => W * ((i : ℝ) + 1)) (p := xg)
    hw0 hw1 (fun i _ => Set.mem_univ _)
  rw [← hwe] at jh
  simp only [smul_eq_mul] at jh
  -- finiteness at the averages
  have fbar : f (weightedErgodic xg k) ≠ ⊤ := hfin _ hxgbar
  have fbar' : f (weightedErgodic xf k) ≠ ⊤ := hfin _ hxfbar
  have gbar : g (weightedErgodic xg k) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) jg
  rw [hobj _ fbar gbar, hobj x fx gx, ← hFs, ← EReal.coe_add, EReal.coe_le_coe_iff]
  -- real inequalities
  have jf' : (f (weightedErgodic xf k)).toReal ≤ ∑ i ∈ Finset.range n, W * ((i : ℝ) + 1) * a i := by
    rw [← EReal.coe_le_coe_iff, EReal.coe_toReal fbar' (hfb _)]; exact jf
  have jg' : (g (weightedErgodic xg k)).toReal ≤ ∑ i ∈ Finset.range n, W * ((i : ℝ) + 1) * b i := by
    rw [← EReal.coe_le_coe_iff, EReal.coe_toReal gbar (hgb _)]; exact jg
  have hL := hLip.dist_le_mul _ hxgbar _ hxfbar
  rw [Real.dist_eq, dist_eq_norm] at hL
  have hL' := (abs_le.1 hL).2
  have hdist := hwed k
  rw [norm_sub_rev] at hdist
  have hLd : (L : ℝ) * ‖weightedErgodic xg k - weightedErgodic xf k‖ ≤
      (L : ℝ) * (5 * ‖z0 - zstar‖ / ((k : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left hdist L.coe_nonneg
  -- combine
  have hsumW : ∑ i ∈ Finset.range n, W * ((i : ℝ) + 1) * a i
      + ∑ i ∈ Finset.range n, W * ((i : ℝ) + 1) * b i
      + ∑ i ∈ Finset.range n, W * ((i : ℝ) + 1) * h (xg i) - Fs
      = W * ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * E i := by
    have hF : Fs = ∑ i ∈ Finset.range n, W * ((i : ℝ) + 1) * Fs := by
      rw [← Finset.sum_mul, hw1, one_mul]
    rw [hF, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    simp only [hE]; ring
  have hWE : W * ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * E i ≤ Q / γ / ((k : ℝ) + 1) := by
    have h1 : ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * E i ≤ (n : ℝ) * Q / (2 * γ) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hWpos.le
    have e : W * ((n : ℝ) * Q / (2 * γ)) = Q / γ / ((n : ℝ) + 1) := by
      rw [hW]; field_simp
    rw [e] at h2
    have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
    have h3 : Q / γ / ((n : ℝ) + 1) ≤ Q / γ / ((k : ℝ) + 1) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      rw [hn]; push_cast; linarith
    linarith
  have hfin' : Fs + (Q / γ + 5 * ↑L * ‖z0 - zstar‖) / ((k : ℝ) + 1) =
      Fs + Q / γ / ((k : ℝ) + 1) + (L : ℝ) * (5 * ‖z0 - zstar‖ / ((k : ℝ) + 1)) := by
    field_simp; ring
  rw [hfin']
  linarith

end ThreeOpSplitting.ConvexRates

open ThreeOpSplitting.ConvexRates

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (h : H → ℝ) (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ) (hγβ : γ < 2 * β)
    (hf : IsProperClosedConvex f) (hg : IsProperClosedConvex g) (hh : IsSmoothConvex β h)
    (proxf proxg : H → H) (hproxf : IsProx γ f proxf) (hproxg : IsProx γ g proxg)
    (z0 zstar : H) (hfix : splittingOp proxf proxg (gradient h) γ zstar = zstar)
    (L : NNReal)
    (hfin : ∀ x ∈ Metric.closedBall (proxg zstar) ((1 + γ / β) * ‖z0 - zstar‖), f x ≠ ⊤)
    (hLip : LipschitzOnWith L (fun x => (f x).toReal)
      (Metric.closedBall (proxg zstar) ((1 + γ / β) * ‖z0 - zstar‖))) :
    objective f g h (proxg zstar) ≠ ⊤ ∧
      ∃ C : ℝ, ∀ k : ℕ,
        objective f g h (weightedErgodic (algXg proxf proxg (gradient h) γ z0) k) ≤
          objective f g h (proxg zstar) + ((C / ((k : ℝ) + 1) : ℝ) : EReal) := by
  exact weighted_ergodic_rate f g h β γ hβ hγ hγβ hf hg hh proxf proxg hproxf hproxg z0 zstar hfix L hfin hLip
