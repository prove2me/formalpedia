-- Prove2me | solution 1 for TradingFavors.Existence.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T04:48:15.173134+00:00
-- url     : https://prove2.me/submissions/faf310eb-6c0d-46aa-979f-bdcaa06e601b

import Mathlib
import Definitions.Def_TradingFavors_Existence_Model

namespace TradingFavors.Existence
namespace P5

open Matrix

lemma fr_cases (b : Fin 2) : fr b = 0 ∨ fr b = 1 := by
  fin_cases b <;> simp [fr]

lemma fr_nonneg (b : Fin 2) : 0 ≤ fr b := by
  rcases fr_cases b with h | h <;> rw [h] <;> norm_num

lemma fr_le_one (b : Fin 2) : fr b ≤ 1 := by
  rcases fr_cases b with h | h <;> rw [h] <;> norm_num

lemma one_sub_fr_nonneg (b : Fin 2) : 0 ≤ 1 - fr b := by
  have := fr_le_one b; linarith

variable {θ : Params}

lemma Lam_pos (hθ : θ.Standing) : 0 < Lam θ := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hθ; unfold Lam; linarith

lemma gam_pos (hθ : θ.Standing) : 0 < θ.gam := hθ.2.2.2.2.1

lemma outRate_le (hθ : θ.Standing) (σ : Profile) (s : State) :
    outRate θ σ s ≤ Lam θ := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hθ
  unfold outRate Lam
  rcases fr_cases s.1 with a | a <;> rcases fr_cases s.2.1 with b | b <;>
    rcases fr_cases (σ.s1 s.2.2) with c | c <;> rcases fr_cases (σ.s2 s.2.2) with d | d <;>
    simp only [a, b, c, d] <;> nlinarith

/-- `Lam * step f s` written out. -/
lemma Lam_mul_step (hθ : θ.Standing) (σ : Profile) (f : State → ℝ) (s : State) :
    Lam θ * step θ σ f s =
      θ.lam1 * (1 - fr s.1) * f (1, s.2.1, s.2.2)
      + θ.lam1 * fr s.1 * (1 - fr s.2.1) * (1 - fr (σ.s2 s.2.2)) * f (1, 1, s.2.2 - 1)
      + θ.lam2 * (1 - fr s.2.1) * f (s.1, 1, s.2.2)
      + θ.lam2 * fr s.2.1 * (1 - fr s.1) * (1 - fr (σ.s1 s.2.2)) * f (1, 1, s.2.2 + 1)
      + θ.mu1 * fr s.1 * f (0, s.2.1, s.2.2)
      + θ.mu2 * fr s.2.1 * f (s.1, 0, s.2.2)
      + (Lam θ - outRate θ σ s) * f s := by
  have hL := (Lam_pos hθ).ne'
  unfold step
  field_simp

lemma step_nonneg (hθ : θ.Standing) (σ : Profile) (f : State → ℝ) (hf : ∀ t, 0 ≤ f t)
    (s : State) : 0 ≤ step θ σ f s := by
  have hL := Lam_pos hθ
  have hout := sub_nonneg.mpr (outRate_le hθ σ s)
  have key : 0 ≤ Lam θ * step θ σ f s := by
    rw [Lam_mul_step hθ]
    obtain ⟨h1, h2, h3, h4, -⟩ := hθ
    have a1 := one_sub_fr_nonneg s.1
    have a2 := one_sub_fr_nonneg s.2.1
    have a3 := one_sub_fr_nonneg (σ.s1 s.2.2)
    have a4 := one_sub_fr_nonneg (σ.s2 s.2.2)
    have b1 := fr_nonneg s.1
    have b2 := fr_nonneg s.2.1
    have := hf (1, s.2.1, s.2.2)
    have := hf (1, 1, s.2.2 - 1)
    have := hf (s.1, 1, s.2.2)
    have := hf (1, 1, s.2.2 + 1)
    have := hf (0, s.2.1, s.2.2)
    have := hf (s.1, 0, s.2.2)
    have := hf s
    apply_rules [add_nonneg, mul_nonneg, h1.le, h2.le, h3.le, h4.le]
  exact (mul_nonneg_iff_of_pos_left hL).mp key

lemma step_sub (σ : Profile) (f g : State → ℝ) (s : State) :
    step θ σ (fun t => f t - g t) s = step θ σ f s - step θ σ g s := by
  simp only [step]; ring

lemma step_smul (σ : Profile) (a : ℝ) (f : State → ℝ) (s : State) :
    step θ σ (fun t => a * f t) s = a * step θ σ f s := by
  simp only [step]; ring

lemma step_const (hθ : θ.Standing) (σ : Profile) (a : ℝ) (s : State) :
    step θ σ (fun _ => a) s = a := by
  have hL := (Lam_pos hθ).ne'
  simp only [step, outRate]
  field_simp
  simp only [Lam]
  ring

lemma step_mono (hθ : θ.Standing) (σ : Profile) (f g : State → ℝ) (h : ∀ t, f t ≤ g t)
    (s : State) : step θ σ f s ≤ step θ σ g s := by
  have := step_nonneg hθ σ (fun t => g t - f t) (fun t => sub_nonneg.mpr (h t)) s
  rw [step_sub] at this; linarith

lemma step_abs_le (hθ : θ.Standing) (σ : Profile) (f : State → ℝ) (M : ℝ)
    (h : ∀ t, |f t| ≤ M) (s : State) : |step θ σ f s| ≤ M := by
  have h1 := step_mono hθ σ f (fun _ => M) (fun t => (abs_le.mp (h t)).2) s
  have h2 := step_mono hθ σ (fun _ => -M) f (fun t => (abs_le.mp (h t)).1) s
  rw [step_const hθ] at h1 h2
  exact abs_le.mpr ⟨h2, h1⟩

lemma iter_abs_le (hθ : θ.Standing) (σ : Profile) (f : State → ℝ) (M : ℝ)
    (h : ∀ t, |f t| ≤ M) (n : ℕ) (s : State) : |(step θ σ)^[n] f s| ≤ M := by
  induction n generalizing s with
  | zero => simpa using h s
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact step_abs_le hθ σ _ M ih s

/-- The discount factor of the uniformized chain. -/
noncomputable def cc (θ : Params) : ℝ := Lam θ / (Lam θ + θ.gam)

lemma cc_nonneg (hθ : θ.Standing) : 0 ≤ cc θ := by
  have := Lam_pos hθ; have := gam_pos hθ; unfold cc; positivity

lemma cc_lt_one (hθ : θ.Standing) : cc θ < 1 := by
  have := Lam_pos hθ; have := gam_pos hθ; unfold cc
  rw [div_lt_one (by linarith)]; linarith

/-- Generic discounted payoff. -/
noncomputable def gpay (θ : Params) (σ : Profile) (r : State → ℝ) (s : State) : ℝ :=
  ∑' n : ℕ, cc θ ^ n * ((step θ σ)^[n] r) s

lemma gpay_hasSum (hθ : θ.Standing) (σ : Profile) (r : State → ℝ) (M : ℝ)
    (hr : ∀ t, |r t| ≤ M) (s : State) :
    HasSum (fun n : ℕ => cc θ ^ n * ((step θ σ)^[n] r) s)
      (gpay θ σ r s) := by
  apply Summable.hasSum
  have hc0 := cc_nonneg hθ
  have hc1 := cc_lt_one hθ
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hc0 hc1).mul_left M) ?_
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hc0]
  have h1 := iter_abs_le hθ σ r M hr n s
  have h2 : 0 ≤ cc θ ^ n := pow_nonneg hc0 n
  rw [mul_comm M]
  exact mul_le_mul_of_nonneg_left h1 h2

lemma hasSum_step (σ : Profile) (G : ℕ → State → ℝ) (g : State → ℝ)
    (h : ∀ t, HasSum (fun n => G n t) (g t)) (s : State) :
    HasSum (fun n => step θ σ (G n) s) (step θ σ g s) := by
  simp only [step]
  exact (((((((h _).mul_left _).add ((h _).mul_left _)).add ((h _).mul_left _)).add
    ((h _).mul_left _)).add ((h _).mul_left _)).add ((h _).mul_left _)).add
    ((h _).mul_left _) |>.div_const _

lemma gpay_bellman (hθ : θ.Standing) (σ : Profile) (r : State → ℝ) (M : ℝ)
    (hr : ∀ t, |r t| ≤ M) (s : State) :
    gpay θ σ r s = r s + cc θ * step θ σ (gpay θ σ r) s := by
  have h1 := hasSum_step (θ := θ) σ _ _ (gpay_hasSum hθ σ r M hr) s
  have h2 : HasSum (fun n : ℕ => cc θ ^ (n + 1) * ((step θ σ)^[n + 1] r) s)
      (cc θ * step θ σ (gpay θ σ r) s) := by
    have := h1.mul_left (cc θ)
    have e : (fun n : ℕ => cc θ ^ (n + 1) * ((step θ σ)^[n + 1] r) s) =
        fun n => cc θ * step θ σ (fun t => cc θ ^ n * (step θ σ)^[n] r t) s := by
      funext n
      rw [step_smul, Function.iterate_succ_apply', pow_succ]
      ring
    rw [e]; exact this
  have h3 : HasSum (fun n : ℕ => cc θ ^ n * ((step θ σ)^[n] r) s)
      (r s + cc θ * step θ σ (gpay θ σ r) s) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa using h2
  exact (gpay_hasSum hθ σ r M hr s).unique h3

lemma gpay_abs_le (hθ : θ.Standing) (σ : Profile) (r : State → ℝ) (M : ℝ)
    (hr : ∀ t, |r t| ≤ M) (s : State) : |gpay θ σ r s| ≤ M / (1 - cc θ) := by
  have hc0 := cc_nonneg hθ
  have hc1 := cc_lt_one hθ
  have hg := (hasSum_geometric_of_lt_one hc0 hc1).mul_left M
  have hs := gpay_hasSum hθ σ r M hr s
  have hb : ∀ n : ℕ, |cc θ ^ n * ((step θ σ)^[n] r) s| ≤ M * cc θ ^ n := by
    intro n
    have h1 := iter_abs_le hθ σ r M hr n s
    have h2 : 0 ≤ cc θ ^ n := pow_nonneg hc0 n
    rw [abs_mul, abs_of_nonneg h2, mul_comm M]
    exact mul_le_mul_of_nonneg_left h1 h2
  rw [abs_le]
  constructor
  · have := hasSum_le (fun n => (abs_le.mp (hb n)).1) hg.neg hs
    rw [div_eq_mul_inv]; linarith
  · have := hasSum_le (fun n => (abs_le.mp (hb n)).2) hs hg
    rw [div_eq_mul_inv]; linarith

/-- Comparison principle: a bounded supersolution dominates the payoff. -/
lemma gpay_le_of_super (hθ : θ.Standing) (σ : Profile) (r : State → ℝ) (M : ℝ)
    (hr : ∀ t, |r t| ≤ M) (w : State → ℝ) (B : ℝ) (hwB : ∀ t, |w t| ≤ B)
    (hw : ∀ t, r t + cc θ * step θ σ w t ≤ w t) (s : State) : gpay θ σ r s ≤ w s := by
  set e : State → ℝ := fun t => w t - gpay θ σ r t with he
  have hc0 := cc_nonneg hθ
  have hc1 := cc_lt_one hθ
  have hK : ∀ t, -(B + M / (1 - cc θ)) ≤ e t := by
    intro t
    have := abs_le.mp (hwB t); have := abs_le.mp (gpay_abs_le hθ σ r M hr t)
    simp only [he]; linarith
  have hsup : ∀ t, cc θ * step θ σ e t ≤ e t := by
    intro t
    have hb := gpay_bellman hθ σ r M hr t
    have := hw t
    simp only [he]
    rw [step_sub]
    linarith
  have key : ∀ n : ℕ, ∀ t, -(cc θ ^ n * (B + M / (1 - cc θ))) ≤ e t := by
    intro n
    induction n with
    | zero => intro t; simpa using hK t
    | succ n ih =>
      intro t
      have hm := step_mono hθ σ (fun _ => -(cc θ ^ n * (B + M / (1 - cc θ)))) e ih t
      rw [step_const hθ] at hm
      have := hsup t
      have := mul_le_mul_of_nonneg_left hm hc0
      rw [pow_succ]
      nlinarith
  have hlim : Filter.Tendsto (fun n : ℕ => -(cc θ ^ n * (B + M / (1 - cc θ))))
      Filter.atTop (nhds (-(0 * (B + M / (1 - cc θ))))) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const _).neg
  have := le_of_tendsto hlim (Filter.Eventually.of_forall (fun n => key n s))
  simp only [zero_mul, neg_zero, he] at this
  linarith

/-! ### A generic four-state cluster system (maximum principle) -/

/-- The balance system of one cluster, relative to the no-collaboration values. -/
def SysG (a b m n c a' b' S1 S2 d0 d1 d2 d3 : ℝ) : Prop :=
  (c + a + b) * d0 = a * d1 + b * d2 ∧
  (c + m + b + a') * d1 = m * d0 + b * d3 + a' * S1 ∧
  (c + n + a + b') * d2 = n * d0 + a * d3 + b' * S2 ∧
  (c + m + n) * d3 = n * d1 + m * d2

lemma sysG_lower {a b m n c a' b' S1 S2 d0 d1 d2 d3 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hc : 0 < c) (ha' : 0 ≤ a') (hb' : 0 ≤ b')
    (h : SysG a b m n c a' b' S1 S2 d0 d1 d2 d3) :
    let L := min 0 (min (a' / (c + a') * S1) (b' / (c + b') * S2))
    L ≤ d0 ∧ L ≤ d1 ∧ L ≤ d2 ∧ L ≤ d3 := by
  intro L
  obtain ⟨e0, e1, e2, e3⟩ := h
  set μ := min (min d0 d1) (min d2 d3) with hμ
  have m0 : μ ≤ d0 := le_trans (min_le_left _ _) (min_le_left _ _)
  have m1 : μ ≤ d1 := le_trans (min_le_left _ _) (min_le_right _ _)
  have m2 : μ ≤ d2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have m3 : μ ≤ d3 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hL0 : L ≤ 0 := min_le_left _ _
  have hL1 : L ≤ a' / (c + a') * S1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hL2 : L ≤ b' / (c + b') * S2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have key : L ≤ μ := by
    rcases min_choice (min d0 d1) (min d2 d3) with h1 | h1 <;> rw [h1] at hμ
    · rcases min_choice d0 d1 with h2 | h2 <;> rw [h2] at hμ
      · -- μ = d0
        have := mul_le_mul_of_nonneg_left m1 ha
        have := mul_le_mul_of_nonneg_left m2 hb
        have : c * μ ≥ 0 := by rw [hμ] at *; nlinarith
        have : 0 ≤ μ := by nlinarith
        linarith
      · -- μ = d1
        have := mul_le_mul_of_nonneg_left m0 hm
        have := mul_le_mul_of_nonneg_left m3 hb
        have h5 : (c + a') * μ ≥ a' * S1 := by rw [hμ] at *; nlinarith
        have hca : 0 < c + a' := by linarith
        have : a' / (c + a') * S1 ≤ μ := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hca]; linarith
        linarith
    · rcases min_choice d2 d3 with h2 | h2 <;> rw [h2] at hμ
      · -- μ = d2
        have := mul_le_mul_of_nonneg_left m0 hn
        have := mul_le_mul_of_nonneg_left m3 ha
        have h5 : (c + b') * μ ≥ b' * S2 := by rw [hμ] at *; nlinarith
        have hcb : 0 < c + b' := by linarith
        have : b' / (c + b') * S2 ≤ μ := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hcb]; linarith
        linarith
      · -- μ = d3
        have := mul_le_mul_of_nonneg_left m1 hn
        have := mul_le_mul_of_nonneg_left m2 hm
        have : c * μ ≥ 0 := by rw [hμ] at *; nlinarith
        have : 0 ≤ μ := by nlinarith
        linarith
  exact ⟨key.trans m0, key.trans m1, key.trans m2, key.trans m3⟩

lemma sysG_neg {a b m n c a' b' S1 S2 d0 d1 d2 d3 : ℝ}
    (h : SysG a b m n c a' b' S1 S2 d0 d1 d2 d3) :
    SysG a b m n c a' b' (-S1) (-S2) (-d0) (-d1) (-d2) (-d3) := by
  obtain ⟨e0, e1, e2, e3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

lemma sysG_upper {a b m n c a' b' S1 S2 d0 d1 d2 d3 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hc : 0 < c) (ha' : 0 ≤ a') (hb' : 0 ≤ b')
    (h : SysG a b m n c a' b' S1 S2 d0 d1 d2 d3) :
    let U := max 0 (max (a' / (c + a') * S1) (b' / (c + b') * S2))
    d0 ≤ U ∧ d1 ≤ U ∧ d2 ≤ U ∧ d3 ≤ U := by
  intro U
  have := sysG_lower ha hb hm hn hc ha' hb' (sysG_neg h)
  simp only at this
  have hU : min 0 (min (a' / (c + a') * -S1) (b' / (c + b') * -S2)) = -U := by
    simp only [U, mul_neg]
    rw [min_neg_neg, ← neg_zero, min_neg_neg, neg_zero]
  rw [hU] at this
  obtain ⟨h0, h1, h2, h3⟩ := this
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma sysG_zero {a b m n c a' b' d0 d1 d2 d3 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hc : 0 < c) (ha' : 0 ≤ a') (hb' : 0 ≤ b')
    (h : SysG a b m n c a' b' 0 0 d0 d1 d2 d3) :
    d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ d3 = 0 := by
  have l := sysG_lower ha hb hm hn hc ha' hb' h
  have u := sysG_upper ha hb hm hn hc ha' hb' h
  simp only [mul_zero, min_self, max_self] at l u
  obtain ⟨l0, l1, l2, l3⟩ := l
  obtain ⟨u0, u1, u2, u3⟩ := u
  exact ⟨le_antisymm u0 l0, le_antisymm u1 l1, le_antisymm u2 l2, le_antisymm u3 l3⟩

/-- Properties of the first-passage vector solving the system with source `a·1` in row 1. -/
lemma phi_props {a b m n c x0 x1 x2 x3 : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hm : 0 < m) (hn : 0 ≤ n) (hc : 0 < c)
    (h : SysG a b m n c a 0 1 0 x0 x1 x2 x3) :
    0 ≤ x0 ∧ 0 ≤ x1 ∧ 0 ≤ x2 ∧ 0 ≤ x3 ∧
    x0 ≤ a / (c + a) ∧ x1 ≤ a / (c + a) ∧ x2 ≤ a / (c + a) ∧ x3 ≤ a / (c + a) ∧
    x3 ^ 2 ≤ x2 := by
  have l := sysG_lower ha.le hb hm.le hn hc ha.le le_rfl h
  have u := sysG_upper ha.le hb hm.le hn hc ha.le le_rfl h
  have hK0 : 0 ≤ a / (c + a) := by positivity
  have hK1 : a / (c + a) < 1 := by rw [div_lt_one (by linarith)]; linarith
  simp only [mul_one, zero_div, zero_mul, mul_zero] at l u
  have e1 : min (a / (c + a)) 0 = 0 := min_eq_right hK0
  have e2 : max (a / (c + a)) 0 = a / (c + a) := max_eq_left hK0
  rw [e1, min_self] at l
  rw [e2, max_eq_right hK0] at u
  obtain ⟨l0, l1, l2, l3⟩ := l
  obtain ⟨u0, u1, u2, u3⟩ := u
  refine ⟨l0, l1, l2, l3, u0, u1, u2, u3, ?_⟩
  obtain ⟨e0, e1, e2, e3⟩ := h
  set K := a / (c + a) with hK
  have hcK : (c + a) * K = a := by rw [hK]; field_simp
  -- z = min x0 x2 ≥ K * min x1 x3
  set μ := min x1 x3 with hμ
  have hμ1 : μ ≤ x1 := min_le_left _ _
  have hμ3 : μ ≤ x3 := min_le_right _ _
  have hμ0 : 0 ≤ μ := le_min l1 l3
  have hz : K * μ ≤ x2 := by
    rcases le_total x0 x2 with h02 | h02
    · -- min is x0
      have : (c + a) * x0 ≥ a * μ := by
        have := mul_le_mul_of_nonneg_left hμ1 ha.le
        have := mul_le_mul_of_nonneg_left h02 hb
        nlinarith
      have : K * μ ≤ x0 := by
        have hca : 0 < c + a := by linarith
        rw [hK, div_mul_eq_mul_div, div_le_iff₀ hca]; linarith
      linarith
    · have : (c + a) * x2 ≥ a * μ := by
        have := mul_le_mul_of_nonneg_left hμ3 ha.le
        have := mul_le_mul_of_nonneg_left h02 hn
        nlinarith
      have hca : 0 < c + a := by linarith
      rw [hK, div_mul_eq_mul_div, div_le_iff₀ hca]; linarith
  rcases le_total x3 x1 with h31 | h31
  · have : μ = x3 := min_eq_right h31
    rw [this] at hz
    have : x3 * x3 ≤ K * x3 := mul_le_mul_of_nonneg_right u3 l3
    nlinarith
  · -- x1 ≤ x3 : then x3 ≤ x2
    have : x3 ≤ x2 := by
      have := mul_le_mul_of_nonneg_left h31 hn
      by_contra hcon
      push_neg at hcon
      have := mul_lt_mul_of_pos_left hcon hm
      nlinarith
    have : x3 * x3 ≤ x3 := by nlinarith
    nlinarith

/-! ### The no-collaboration values -/

lemma piNC1_zero : piNC1 θ 0 =
    (θ.mu1 + θ.gam) * θ.lam1 * (θ.p1 - θ.l1) / ((θ.lam1 + θ.mu1 + θ.gam) * θ.gam) := by
  simp [piNC1]
lemma piNC1_one : piNC1 θ 1 =
    θ.lam1 * θ.mu1 * (θ.p1 - θ.l1) / ((θ.lam1 + θ.mu1 + θ.gam) * θ.gam) := by
  simp [piNC1]
lemma piNC2_zero : piNC2 θ 0 =
    (θ.mu2 + θ.gam) * θ.lam2 * (θ.p2 - θ.l2) / ((θ.lam2 + θ.mu2 + θ.gam) * θ.gam) := by
  simp [piNC2]
lemma piNC2_one : piNC2 θ 1 =
    θ.lam2 * θ.mu2 * (θ.p2 - θ.l2) / ((θ.lam2 + θ.mu2 + θ.gam) * θ.gam) := by
  simp [piNC2]

lemma nc1a (hθ : θ.Standing) :
    (θ.gam + θ.lam1) * piNC1 θ 0 = θ.lam1 * (θ.p1 - θ.l1) + θ.lam1 * piNC1 θ 1 := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hθ
  rw [piNC1_zero, piNC1_one]
  field_simp
  ring

lemma nc1b (hθ : θ.Standing) :
    (θ.gam + θ.mu1) * piNC1 θ 1 = θ.mu1 * piNC1 θ 0 := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hθ
  rw [piNC1_zero, piNC1_one]
  field_simp
  ring

lemma nc2a (hθ : θ.Standing) :
    (θ.gam + θ.lam2) * piNC2 θ 0 = θ.lam2 * (θ.p2 - θ.l2) + θ.lam2 * piNC2 θ 1 := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hθ
  rw [piNC2_zero, piNC2_one]
  field_simp
  ring

lemma nc2b (hθ : θ.Standing) :
    (θ.gam + θ.mu2) * piNC2 θ 1 = θ.mu2 * piNC2 θ 0 := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hθ
  rw [piNC2_zero, piNC2_one]
  field_simp
  ring

lemma nc1_gap (hθ : θ.Standing) :
    rhoHat1 θ * (θ.p1 - θ.l1) = piNC1 θ 0 - piNC1 θ 1 := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hθ
  rw [rhoHat1, piNC1_zero, piNC1_one]
  field_simp
  ring

lemma nc2_gap (hθ : θ.Standing) :
    rhoHat2 θ * (θ.p2 - θ.l2) = piNC2 θ 0 - piNC2 θ 1 := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hθ
  rw [rhoHat2, piNC2_zero, piNC2_one]
  field_simp
  ring

lemma rhoHat1_mem (hθ : θ.Standing) : 0 < rhoHat1 θ ∧ rhoHat1 θ < 1 := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hθ
  unfold rhoHat1
  exact ⟨by positivity, by rw [div_lt_one (by linarith)]; linarith⟩

lemma rhoHat2_mem (hθ : θ.Standing) : 0 < rhoHat2 θ ∧ rhoHat2 θ < 1 := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hθ
  unfold rhoHat2
  exact ⟨by positivity, by rw [div_lt_one (by linarith)]; linarith⟩

/-! ### Payoffs as generic payoffs; Bellman equations -/

lemma R1_abs (hθ : θ.Standing) (σ : Profile) (s : State) :
    |R1 θ σ s| ≤ θ.lam1 * |θ.p1 - θ.l1| + θ.lam1 * θ.q1 + θ.lam2 * θ.l1 := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, hq1, -, hl1, -⟩ := hθ
  have hp := abs_le.mp (le_refl |θ.p1 - θ.l1|)
  have := abs_nonneg (θ.p1 - θ.l1)
  unfold R1
  rw [abs_le]
  rcases fr_cases s.1 with a | a <;> rcases fr_cases s.2.1 with b | b <;>
    rcases fr_cases (σ.s1 s.2.2) with c | c <;> rcases fr_cases (σ.s2 s.2.2) with d | d <;>
    simp only [a, b, c, d] <;> constructor <;> nlinarith

lemma R2_abs (hθ : θ.Standing) (σ : Profile) (s : State) :
    |R2 θ σ s| ≤ θ.lam2 * |θ.p2 - θ.l2| + θ.lam2 * θ.q2 + θ.lam1 * θ.l2 := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, -, hq2, -, hl2, -⟩ := hθ
  have hp := abs_le.mp (le_refl |θ.p2 - θ.l2|)
  have := abs_nonneg (θ.p2 - θ.l2)
  unfold R2
  rw [abs_le]
  rcases fr_cases s.1 with a | a <;> rcases fr_cases s.2.1 with b | b <;>
    rcases fr_cases (σ.s1 s.2.2) with c | c <;> rcases fr_cases (σ.s2 s.2.2) with d | d <;>
    simp only [a, b, c, d] <;> constructor <;> nlinarith

lemma r1_abs (hθ : θ.Standing) (σ : Profile) (s : State) :
    |R1 θ σ s / (Lam θ + θ.gam)| ≤
      (θ.lam1 * |θ.p1 - θ.l1| + θ.lam1 * θ.q1 + θ.lam2 * θ.l1) / (Lam θ + θ.gam) := by
  have := Lam_pos hθ; have := gam_pos hθ
  rw [abs_div, abs_of_pos (by linarith : 0 < Lam θ + θ.gam)]
  exact div_le_div_of_nonneg_right (R1_abs hθ σ s) (by linarith)

lemma r2_abs (hθ : θ.Standing) (σ : Profile) (s : State) :
    |R2 θ σ s / (Lam θ + θ.gam)| ≤
      (θ.lam2 * |θ.p2 - θ.l2| + θ.lam2 * θ.q2 + θ.lam1 * θ.l2) / (Lam θ + θ.gam) := by
  have := Lam_pos hθ; have := gam_pos hθ
  rw [abs_div, abs_of_pos (by linarith : 0 < Lam θ + θ.gam)]
  exact div_le_div_of_nonneg_right (R2_abs hθ σ s) (by linarith)

lemma pay1_eq_gpay (σ : Profile) :
    pay1 θ σ = gpay θ σ (fun u => R1 θ σ u / (Lam θ + θ.gam)) := rfl

lemma pay2_eq_gpay (σ : Profile) :
    pay2 θ σ = gpay θ σ (fun u => R2 θ σ u / (Lam θ + θ.gam)) := rfl

lemma bell1 (hθ : θ.Standing) (σ : Profile) (s : State) :
    (Lam θ + θ.gam) * pay1 θ σ s = R1 θ σ s + Lam θ * step θ σ (pay1 θ σ) s := by
  have h := gpay_bellman hθ σ _ _ (r1_abs hθ σ) s
  rw [← pay1_eq_gpay] at h
  have := Lam_pos hθ; have := gam_pos hθ
  rw [h, cc]
  field_simp

lemma bell2 (hθ : θ.Standing) (σ : Profile) (s : State) :
    (Lam θ + θ.gam) * pay2 θ σ s = R2 θ σ s + Lam θ * step θ σ (pay2 θ σ) s := by
  have h := gpay_bellman hθ σ _ _ (r2_abs hθ σ) s
  rw [← pay2_eq_gpay] at h
  have := Lam_pos hθ; have := gam_pos hθ
  rw [h, cc]
  field_simp

@[simp] lemma fr_zero : fr 0 = 0 := by simp [fr]
@[simp] lemma fr_one : fr 1 = 1 := by simp [fr]

/-- The cluster system for firm 1 at balance `k` (relative to no-collaboration values). -/
lemma cluster1 (hθ : θ.Standing) (σ : Profile) (k : ℤ) :
    SysG θ.lam1 θ.lam2 θ.mu1 θ.mu2 θ.gam (θ.lam1 * (1 - fr (σ.s2 k)))
      (θ.lam2 * (1 - fr (σ.s1 k)))
      (θ.q1 + pay1 θ σ (1, 1, k - 1) - piNC1 θ 1) (pay1 θ σ (1, 1, k + 1) - θ.l1 - piNC1 θ 0)
      (pay1 θ σ (0, 0, k) - piNC1 θ 0) (pay1 θ σ (1, 0, k) - piNC1 θ 1)
      (pay1 θ σ (0, 1, k) - piNC1 θ 0) (pay1 θ σ (1, 1, k) - piNC1 θ 1) := by
  have b00 := bell1 hθ σ (0, 0, k)
  have b10 := bell1 hθ σ (1, 0, k)
  have b01 := bell1 hθ σ (0, 1, k)
  have b11 := bell1 hθ σ (1, 1, k)
  have na := nc1a hθ
  have nb := nc1b hθ
  simp only [Lam_mul_step hθ, R1, outRate, fr_zero, fr_one] at b00 b10 b01 b11
  unfold Lam at b00 b10 b01 b11
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- The cluster system for firm 2 at balance `k`, in physical coordinates. -/
lemma cluster2 (hθ : θ.Standing) (σ : Profile) (k : ℤ) :
    SysG θ.lam1 θ.lam2 θ.mu1 θ.mu2 θ.gam (θ.lam1 * (1 - fr (σ.s2 k)))
      (θ.lam2 * (1 - fr (σ.s1 k)))
      (pay2 θ σ (1, 1, k - 1) - θ.l2 - piNC2 θ 0) (θ.q2 + pay2 θ σ (1, 1, k + 1) - piNC2 θ 1)
      (pay2 θ σ (0, 0, k) - piNC2 θ 0) (pay2 θ σ (1, 0, k) - piNC2 θ 0)
      (pay2 θ σ (0, 1, k) - piNC2 θ 1) (pay2 θ σ (1, 1, k) - piNC2 θ 1) := by
  have b00 := bell2 hθ σ (0, 0, k)
  have b10 := bell2 hθ σ (1, 0, k)
  have b01 := bell2 hθ σ (0, 1, k)
  have b11 := bell2 hθ σ (1, 1, k)
  have na := nc2a hθ
  have nb := nc2b hθ
  simp only [Lam_mul_step hθ, R2, outRate, fr_zero, fr_one] at b00 b10 b01 b11
  unfold Lam at b00 b10 b01 b11
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

lemma sysG_lin {a b m n c a' b' S1 S2 T1 T2 d0 d1 d2 d3 x0 x1 x2 x3 : ℝ} (e : ℝ)
    (h : SysG a b m n c a' b' S1 S2 d0 d1 d2 d3) (h' : SysG a b m n c a' b' T1 T2 x0 x1 x2 x3) :
    SysG a b m n c a' b' (S1 - e * T1) (S2 - e * T2) (d0 - e * x0) (d1 - e * x1)
      (d2 - e * x2) (d3 - e * x3) := by
  obtain ⟨e0, e1, e2, e3⟩ := h
  obtain ⟨f0, f1, f2, f3⟩ := h'
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination e0 - e * f0
  · linear_combination e1 - e * f1
  · linear_combination e2 - e * f2
  · linear_combination e3 - e * f3

lemma sysG_zero_rates {a b m n c S1 S2 d0 d1 d2 d3 : ℝ}
    (h : SysG a b m n c 0 0 S1 S2 d0 d1 d2 d3) : SysG a b m n c 0 0 0 0 d0 d1 d2 d3 := by
  obtain ⟨e0, e1, e2, e3⟩ := h
  exact ⟨e0, by linarith, by linarith, e3⟩

/-! ### The matrices `B₁` and the first-passage vectors -/

lemma B1_det_ne (hθ : θ.Standing) (s1 s2 : ℝ) (h1 : s1 ≤ 1) (h2 : s2 ≤ 1) :
    (B1 θ s1 s2).det ≠ 0 := by
  obtain ⟨l1, l2, m1, m2, g, -⟩ := hθ
  intro h
  obtain ⟨v, hv, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  apply hv
  have e0 := congrFun hBv 0
  have e1 := congrFun hBv 1
  have e2 := congrFun hBv 2
  have e3 := congrFun hBv 3
  simp [mulVec, dotProduct, Fin.sum_univ_four, B1, Bmat] at e0 e1 e2 e3
  have hs : SysG θ.lam1 θ.lam2 θ.mu1 θ.mu2 θ.gam (θ.lam1 * (1 - s2)) (θ.lam2 * (1 - s1)) 0 0
      (v 0) (v 1) (v 2) (v 3) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  have z := sysG_zero l1.le l2.le m1.le m2.le g (mul_nonneg l1.le (by linarith))
    (mul_nonneg l2.le (by linarith)) hs
  funext i
  fin_cases i <;> simp [z.1, z.2.1, z.2.2.1, z.2.2.2]

/-- `φ = λ₁ B₁(1,0)⁻¹ e₂`: discounted first passage to a type-1 transfer. -/
noncomputable def phiv (θ : Params) : Fin 4 → ℝ :=
  θ.lam1 • ((B1 θ 1 0)⁻¹ *ᵥ Pi.single 1 1)

/-- `φ' = λ₂ B₁(0,1)⁻¹ e₃`: discounted first passage to a type-2 transfer. -/
noncomputable def phiw (θ : Params) : Fin 4 → ℝ :=
  θ.lam2 • ((B1 θ 0 1)⁻¹ *ᵥ Pi.single 2 1)

lemma phiv_sys (hθ : θ.Standing) :
    SysG θ.lam1 θ.lam2 θ.mu1 θ.mu2 θ.gam θ.lam1 0 1 0
      (phiv θ 0) (phiv θ 1) (phiv θ 2) (phiv θ 3) := by
  have hdet := B1_det_ne hθ 1 0 le_rfl zero_le_one
  have hB : B1 θ 1 0 *ᵥ phiv θ = θ.lam1 • Pi.single 1 1 := by
    rw [phiv, mulVec_smul, mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      one_mulVec]
  have e0 := congrFun hB 0
  have e1 := congrFun hB 1
  have e2 := congrFun hB 2
  have e3 := congrFun hB 3
  simp [mulVec, dotProduct, Fin.sum_univ_four, B1, Bmat] at e0 e1 e2 e3
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

lemma phiw_sys (hθ : θ.Standing) :
    SysG θ.lam1 θ.lam2 θ.mu1 θ.mu2 θ.gam 0 θ.lam2 0 1
      (phiw θ 0) (phiw θ 1) (phiw θ 2) (phiw θ 3) := by
  have hdet := B1_det_ne hθ 0 1 zero_le_one le_rfl
  have hB : B1 θ 0 1 *ᵥ phiw θ = θ.lam2 • Pi.single 2 1 := by
    rw [phiw, mulVec_smul, mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      one_mulVec]
  have e0 := congrFun hB 0
  have e1 := congrFun hB 1
  have e2 := congrFun hB 2
  have e3 := congrFun hB 3
  simp [mulVec, dotProduct, Fin.sum_univ_four, B1, Bmat] at e0 e1 e2 e3
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

lemma beta2_eq : beta2 θ = phiv θ 3 := by
  simp [phiv, beta2, mulVec, dotProduct, Fin.sum_univ_four]

lemma alpha1_eq : alpha1 θ = phiw θ 3 := by
  simp [phiw, alpha1, mulVec, dotProduct, Fin.sum_univ_four]

lemma phiv_props (hθ : θ.Standing) :
    0 ≤ phiv θ 0 ∧ 0 ≤ phiv θ 1 ∧ 0 ≤ phiv θ 2 ∧ 0 ≤ phiv θ 3 ∧
    phiv θ 0 < 1 ∧ phiv θ 1 < 1 ∧ phiv θ 2 < 1 ∧ phiv θ 3 < 1 ∧
    phiv θ 3 ^ 2 ≤ phiv θ 2 := by
  have hs := phiv_sys hθ
  obtain ⟨l1, l2, m1, m2, g, -⟩ := hθ
  have := phi_props l1 l2.le m1 m2.le g hs
  have hK : θ.lam1 / (θ.gam + θ.lam1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3, c⟩ := this
  exact ⟨a0, a1, a2, a3, by linarith, by linarith, by linarith, by linarith, c⟩

lemma phiw_props (hθ : θ.Standing) :
    0 ≤ phiw θ 0 ∧ 0 ≤ phiw θ 1 ∧ 0 ≤ phiw θ 2 ∧ 0 ≤ phiw θ 3 ∧
    phiw θ 0 < 1 ∧ phiw θ 1 < 1 ∧ phiw θ 2 < 1 ∧ phiw θ 3 < 1 ∧
    phiw θ 3 ^ 2 ≤ phiw θ 1 := by
  obtain ⟨e0, e1, e2, e3⟩ := phiw_sys hθ
  obtain ⟨l1, l2, m1, m2, g, -⟩ := hθ
  have hs : SysG θ.lam2 θ.lam1 θ.mu2 θ.mu1 θ.gam θ.lam2 0 1 0
      (phiw θ 0) (phiw θ 2) (phiw θ 1) (phiw θ 3) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  have := phi_props l2 l1.le m2 m1.le g hs
  have hK : θ.lam2 / (θ.gam + θ.lam2) < 1 := by rw [div_lt_one (by linarith)]; linarith
  obtain ⟨a0, a2, a1, a3, b0, b2, b1, b3, c⟩ := this
  exact ⟨a0, a1, a2, a3, by linarith, by linarith, by linarith, by linarith, c⟩

/-! ### Geometric weights -/

noncomputable def Sg (β : ℝ) (k : ℤ) : ℝ := ∑ j ∈ Finset.range k.toNat, β ^ j

lemma Sg_nonpos {β : ℝ} {k : ℤ} (hk : k ≤ 0) : Sg β k = 0 := by
  simp [Sg, Int.toNat_eq_zero.mpr hk]

lemma Sg_succ (β : ℝ) {k : ℤ} (hk : 1 ≤ k) : Sg β k = 1 + β * Sg β (k - 1) := by
  have : k.toNat = (k - 1).toNat + 1 := by omega
  rw [Sg, Sg, this, Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_succ, pow_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _; ring

lemma Sg_nonneg {β : ℝ} (hβ : 0 ≤ β) (k : ℤ) : 0 ≤ Sg β k :=
  Finset.sum_nonneg (fun j _ => pow_nonneg hβ j)

lemma Sg_le {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) (k : ℤ) : Sg β k ≤ 1 / (1 - β) := by
  rw [Sg, one_div, ← tsum_geometric_of_lt_one hβ hβ1]
  exact Summable.sum_le_tsum _ (fun j _ => pow_nonneg hβ j)
    (summable_geometric_of_lt_one hβ hβ1)

lemma Sg_succ_le {β : ℝ} (hβ : 0 ≤ β) (k : ℤ) : Sg β (k + 1) ≤ 1 + β * Sg β k := by
  rcases le_or_gt 0 k with hk | hk
  · rw [Sg_succ β (by omega)]; simp
  · rw [Sg_nonpos (by omega)]
    have := Sg_nonneg hβ k
    nlinarith

lemma Sg_one (β : ℝ) : Sg β 1 = 1 := by simp [Sg]

lemma fr_eq_zero {b : Fin 2} (h : fr b = 0) : b = 0 := by
  fin_cases b
  · rfl
  · simp at h

lemma fr_eq_one {b : Fin 2} (h : fr b = 1) : b = 1 := by
  fin_cases b
  · simp at h
  · rfl

lemma fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

/-- Reading a 4-vector at the physical state `(x₁, x₂)`. -/
noncomputable def ph (v : Fin 4 → ℝ) (x1 x2 : Fin 2) : ℝ :=
  if x1 = 0 then (if x2 = 0 then v 0 else v 2) else (if x2 = 0 then v 1 else v 3)

/-! ### Upper bound for firm 1 (supersolution) -/

/-- Firm 1's supersolution: no-collaboration value plus the value of the favors it can
still call in, each worth at most `q₁` discounted by `φ`. -/
noncomputable def W1 (θ : Params) (s : State) : ℝ :=
  piNC1 θ s.1 + θ.q1 * Sg (phiv θ 3) s.2.2 * ph (phiv θ) s.1 s.2.1

lemma W1_00 (k : ℤ) : W1 θ (0, 0, k) = piNC1 θ 0 + θ.q1 * Sg (phiv θ 3) k * phiv θ 0 := by
  simp [W1, ph]
lemma W1_10 (k : ℤ) : W1 θ (1, 0, k) = piNC1 θ 1 + θ.q1 * Sg (phiv θ 3) k * phiv θ 1 := by
  simp [W1, ph]
lemma W1_01 (k : ℤ) : W1 θ (0, 1, k) = piNC1 θ 0 + θ.q1 * Sg (phiv θ 3) k * phiv θ 2 := by
  simp [W1, ph]
lemma W1_11 (k : ℤ) : W1 θ (1, 1, k) = piNC1 θ 1 + θ.q1 * Sg (phiv θ 3) k * phiv θ 3 := by
  simp [W1, ph]

lemma W1_abs (hθ : θ.Standing) (s : State) :
    |W1 θ s| ≤ |piNC1 θ 0| + |piNC1 θ 1| + θ.q1 * (1 / (1 - phiv θ 3)) := by
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3, -⟩ := phiv_props hθ
  have hq : 0 ≤ θ.q1 := hθ.2.2.2.2.2.2.2.1
  have hS0 := Sg_nonneg a3 s.2.2
  have hS1 := Sg_le a3 b3 s.2.2
  have hph : 0 ≤ ph (phiv θ) s.1 s.2.1 ∧ ph (phiv θ) s.1 s.2.1 ≤ 1 := by
    unfold ph; split_ifs <;> constructor <;> linarith
  have h1 : 0 ≤ θ.q1 * Sg (phiv θ 3) s.2.2 * ph (phiv θ) s.1 s.2.1 := by
    have := hph.1; positivity
  have h2 : θ.q1 * Sg (phiv θ 3) s.2.2 * ph (phiv θ) s.1 s.2.1 ≤ θ.q1 * (1 / (1 - phiv θ 3)) := by
    have hpos : 0 ≤ 1 / (1 - phiv θ 3) := one_div_nonneg.mpr (by linarith)
    calc θ.q1 * Sg (phiv θ 3) s.2.2 * ph (phiv θ) s.1 s.2.1
        = θ.q1 * (Sg (phiv θ 3) s.2.2 * ph (phiv θ) s.1 s.2.1) := by ring
      _ ≤ θ.q1 * (1 / (1 - phiv θ 3) * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hS1 hph.2 hph.1 hpos) hq
      _ = θ.q1 * (1 / (1 - phiv θ 3)) := by ring
  have h3 : |piNC1 θ s.1| ≤ |piNC1 θ 0| + |piNC1 θ 1| := by
    have := abs_nonneg (piNC1 θ 0); have := abs_nonneg (piNC1 θ 1)
    obtain ⟨x, -⟩ := s
    fin_cases x <;> simp <;> linarith
  unfold W1
  calc |piNC1 θ s.1 + θ.q1 * Sg (phiv θ 3) s.2.2 * ph (phiv θ) s.1 s.2.1|
      ≤ |piNC1 θ s.1| + |θ.q1 * Sg (phiv θ 3) s.2.2 * ph (phiv θ) s.1 s.2.1| := abs_add_le _ _
    _ ≤ _ := by rw [abs_of_nonneg h1]; linarith

lemma W1_gen (hθ : θ.Standing) (σ : Profile) (hσ : ∀ k, σ.s2 k = 0 → 1 ≤ k)
    (hC : phiv θ 3 * θ.q1 ≤ piNC1 θ 0 - piNC1 θ 1 + θ.l1) (s : State) :
    R1 θ σ s + Lam θ * step θ σ (W1 θ) s ≤ (Lam θ + θ.gam) * W1 θ s := by
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3, c⟩ := phiv_props hθ
  obtain ⟨e0, e1, e2, e3⟩ := phiv_sys hθ
  have na := nc1a hθ
  have nb := nc1b hθ
  have hq : 0 ≤ θ.q1 := hθ.2.2.2.2.2.2.2.1
  have hl1 : 0 ≤ θ.l1 := hθ.2.2.2.2.2.2.2.2.2.1
  have l1 := hθ.1
  have l2 := hθ.2.1
  obtain ⟨x1, x2, k⟩ := s
  suffices key : ∀ k : ℤ,
      (R1 θ σ (0, 0, k) + Lam θ * step θ σ (W1 θ) (0, 0, k) ≤ (Lam θ + θ.gam) * W1 θ (0, 0, k)) ∧
      (R1 θ σ (0, 1, k) + Lam θ * step θ σ (W1 θ) (0, 1, k) ≤ (Lam θ + θ.gam) * W1 θ (0, 1, k)) ∧
      (R1 θ σ (1, 0, k) + Lam θ * step θ σ (W1 θ) (1, 0, k) ≤ (Lam θ + θ.gam) * W1 θ (1, 0, k)) ∧
      (R1 θ σ (1, 1, k) + Lam θ * step θ σ (W1 θ) (1, 1, k) ≤ (Lam θ + θ.gam) * W1 θ (1, 1, k)) by
    rcases fin2_cases x1 with rfl | rfl <;> rcases fin2_cases x2 with rfl | rfl
    exacts [(key k).1, (key k).2.1, (key k).2.2.1, (key k).2.2.2]
  intro k
  set β := phiv θ 3 with hβ
  have hS := Sg_nonneg a3 k
  have hqS : 0 ≤ θ.q1 * Sg β k := mul_nonneg hq hS
  have r0 : (θ.gam + θ.lam1 + θ.lam2) * (θ.q1 * Sg β k * phiv θ 0) =
      θ.lam1 * (θ.q1 * Sg β k * phiv θ 1) + θ.lam2 * (θ.q1 * Sg β k * phiv θ 2) := by
    linear_combination (θ.q1 * Sg β k) * e0
  have r1 : (θ.gam + θ.mu1 + θ.lam2 + θ.lam1) * (θ.q1 * Sg β k * phiv θ 1) =
      θ.mu1 * (θ.q1 * Sg β k * phiv θ 0) + θ.lam2 * (θ.q1 * Sg β k * β) +
        θ.lam1 * (θ.q1 * Sg β k) := by
    linear_combination (θ.q1 * Sg β k) * e1
  have r2 : (θ.gam + θ.mu2 + θ.lam1 + 0) * (θ.q1 * Sg β k * phiv θ 2) =
      θ.mu2 * (θ.q1 * Sg β k * phiv θ 0) + θ.lam1 * (θ.q1 * Sg β k * β) := by
    linear_combination (θ.q1 * Sg β k) * e2
  have r3 : (θ.gam + θ.mu1 + θ.mu2) * (θ.q1 * Sg β k * β) =
      θ.mu2 * (θ.q1 * Sg β k * phiv θ 1) + θ.mu1 * (θ.q1 * Sg β k * phiv θ 2) := by
    linear_combination (θ.q1 * Sg β k) * e3
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (0,0,k)
    simp only [Lam_mul_step hθ, R1, outRate, W1_00, W1_10, W1_01, W1_11, fr_zero, fr_one]
    unfold Lam
    linarith
  · -- (0,1,k)
    have hSp := Sg_succ_le a3 k
    have h1 : θ.q1 * β * Sg β (k + 1) ≤ θ.q1 * β * (1 + β * Sg β k) :=
      mul_le_mul_of_nonneg_left hSp (mul_nonneg hq a3)
    have h2 : θ.q1 * Sg β k * β ^ 2 ≤ θ.q1 * Sg β k * phiv θ 2 :=
      mul_le_mul_of_nonneg_left c hqS
    have h3 : 0 ≤ (θ.q1 * Sg β k * phiv θ 2 + (piNC1 θ 0 - piNC1 θ 1 + θ.l1))
        - θ.q1 * Sg β (k + 1) * β := by nlinarith
    simp only [Lam_mul_step hθ, R1, outRate, W1_00, W1_10, W1_01, W1_11, fr_zero, fr_one]
    unfold Lam
    rcases fr_cases (σ.s1 k) with t | t <;> rw [t]
    · have := mul_nonneg l2.le h3
      linarith
    · linarith
  · -- (1,0,k)
    simp only [Lam_mul_step hθ, R1, outRate, W1_00, W1_10, W1_01, W1_11, fr_zero, fr_one]
    unfold Lam
    rcases fr_cases (σ.s2 k) with t | t
    · have hk := hσ k (fr_eq_zero t)
      have hs := Sg_succ β hk
      rw [t]
      have : θ.lam1 * (θ.q1 * Sg β k) = θ.lam1 * θ.q1 + θ.lam1 * (θ.q1 * Sg β (k - 1) * β) := by
        rw [hs]; ring
      linarith
    · rw [t]
      have := mul_nonneg (mul_nonneg hqS l1.le) (sub_nonneg.mpr b1.le)
      linarith
  · -- (1,1,k)
    simp only [Lam_mul_step hθ, R1, outRate, W1_00, W1_10, W1_01, W1_11, fr_zero, fr_one]
    unfold Lam
    linarith

lemma super_of_gen (hθ : θ.Standing) (σ : Profile) (R w : State → ℝ) (t : State)
    (h : R t + Lam θ * step θ σ w t ≤ (Lam θ + θ.gam) * w t) :
    R t / (Lam θ + θ.gam) + cc θ * step θ σ w t ≤ w t := by
  have := Lam_pos hθ; have := gam_pos hθ
  have hp : 0 < Lam θ + θ.gam := by linarith
  have e : R t / (Lam θ + θ.gam) + cc θ * step θ σ w t =
      (R t + Lam θ * step θ σ w t) / (Lam θ + θ.gam) := by
    rw [cc]; field_simp
  rw [e, div_le_iff₀ hp]; linarith

lemma pay1_le_W1 (hθ : θ.Standing) (σ : Profile) (hσ : ∀ k, σ.s2 k = 0 → 1 ≤ k)
    (hC : phiv θ 3 * θ.q1 ≤ piNC1 θ 0 - piNC1 θ 1 + θ.l1) (s : State) :
    pay1 θ σ s ≤ W1 θ s := by
  rw [pay1_eq_gpay]
  exact gpay_le_of_super hθ σ _ _ (r1_abs hθ σ) (W1 θ) _ (W1_abs hθ)
    (fun t => super_of_gen hθ σ (R1 θ σ) (W1 θ) t (W1_gen hθ σ hσ hC t)) s

/-! ### Upper bound for firm 2 (supersolution) -/

noncomputable def W2 (θ : Params) (L : ℤ) (s : State) : ℝ :=
  piNC2 θ s.2.1 + θ.q2 * Sg (phiw θ 3) (L - s.2.2) * ph (phiw θ) s.1 s.2.1

lemma W2_00 (L k : ℤ) :
    W2 θ L (0, 0, k) = piNC2 θ 0 + θ.q2 * Sg (phiw θ 3) (L - k) * phiw θ 0 := by
  simp [W2, ph]
lemma W2_10 (L k : ℤ) :
    W2 θ L (1, 0, k) = piNC2 θ 0 + θ.q2 * Sg (phiw θ 3) (L - k) * phiw θ 1 := by
  simp [W2, ph]
lemma W2_01 (L k : ℤ) :
    W2 θ L (0, 1, k) = piNC2 θ 1 + θ.q2 * Sg (phiw θ 3) (L - k) * phiw θ 2 := by
  simp [W2, ph]
lemma W2_11 (L k : ℤ) :
    W2 θ L (1, 1, k) = piNC2 θ 1 + θ.q2 * Sg (phiw θ 3) (L - k) * phiw θ 3 := by
  simp [W2, ph]

lemma W2_abs (hθ : θ.Standing) (L : ℤ) (s : State) :
    |W2 θ L s| ≤ |piNC2 θ 0| + |piNC2 θ 1| + θ.q2 * (1 / (1 - phiw θ 3)) := by
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3, -⟩ := phiw_props hθ
  have hq : 0 ≤ θ.q2 := hθ.2.2.2.2.2.2.2.2.1
  have hS0 := Sg_nonneg a3 (L - s.2.2)
  have hS1 := Sg_le a3 b3 (L - s.2.2)
  have hph : 0 ≤ ph (phiw θ) s.1 s.2.1 ∧ ph (phiw θ) s.1 s.2.1 ≤ 1 := by
    unfold ph; split_ifs <;> constructor <;> linarith
  have h1 : 0 ≤ θ.q2 * Sg (phiw θ 3) (L - s.2.2) * ph (phiw θ) s.1 s.2.1 := by
    have := hph.1; positivity
  have h2 : θ.q2 * Sg (phiw θ 3) (L - s.2.2) * ph (phiw θ) s.1 s.2.1 ≤
      θ.q2 * (1 / (1 - phiw θ 3)) := by
    have hpos : 0 ≤ 1 / (1 - phiw θ 3) := one_div_nonneg.mpr (by linarith)
    calc θ.q2 * Sg (phiw θ 3) (L - s.2.2) * ph (phiw θ) s.1 s.2.1
        = θ.q2 * (Sg (phiw θ 3) (L - s.2.2) * ph (phiw θ) s.1 s.2.1) := by ring
      _ ≤ θ.q2 * (1 / (1 - phiw θ 3) * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hS1 hph.2 hph.1 hpos) hq
      _ = θ.q2 * (1 / (1 - phiw θ 3)) := by ring
  have h3 : |piNC2 θ s.2.1| ≤ |piNC2 θ 0| + |piNC2 θ 1| := by
    have := abs_nonneg (piNC2 θ 0); have := abs_nonneg (piNC2 θ 1)
    rcases fin2_cases s.2.1 with h | h <;> rw [h] <;> linarith
  unfold W2
  calc |piNC2 θ s.2.1 + θ.q2 * Sg (phiw θ 3) (L - s.2.2) * ph (phiw θ) s.1 s.2.1|
      ≤ |piNC2 θ s.2.1| + |θ.q2 * Sg (phiw θ 3) (L - s.2.2) * ph (phiw θ) s.1 s.2.1| :=
        abs_add_le _ _
    _ ≤ _ := by rw [abs_of_nonneg h1]; linarith

lemma W2_gen (hθ : θ.Standing) (σ : Profile) (L : ℤ) (hσ : ∀ k, σ.s1 k = 0 → k + 1 ≤ L)
    (hC : phiw θ 3 * θ.q2 ≤ piNC2 θ 0 - piNC2 θ 1 + θ.l2) (s : State) :
    R2 θ σ s + Lam θ * step θ σ (W2 θ L) s ≤ (Lam θ + θ.gam) * W2 θ L s := by
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3, c⟩ := phiw_props hθ
  obtain ⟨e0, e1, e2, e3⟩ := phiw_sys hθ
  have na := nc2a hθ
  have nb := nc2b hθ
  have hq : 0 ≤ θ.q2 := hθ.2.2.2.2.2.2.2.2.1
  have l1 := hθ.1
  have l2 := hθ.2.1
  obtain ⟨x1, x2, k⟩ := s
  suffices key : ∀ k : ℤ,
      (R2 θ σ (0, 0, k) + Lam θ * step θ σ (W2 θ L) (0, 0, k) ≤
        (Lam θ + θ.gam) * W2 θ L (0, 0, k)) ∧
      (R2 θ σ (0, 1, k) + Lam θ * step θ σ (W2 θ L) (0, 1, k) ≤
        (Lam θ + θ.gam) * W2 θ L (0, 1, k)) ∧
      (R2 θ σ (1, 0, k) + Lam θ * step θ σ (W2 θ L) (1, 0, k) ≤
        (Lam θ + θ.gam) * W2 θ L (1, 0, k)) ∧
      (R2 θ σ (1, 1, k) + Lam θ * step θ σ (W2 θ L) (1, 1, k) ≤
        (Lam θ + θ.gam) * W2 θ L (1, 1, k)) by
    rcases fin2_cases x1 with rfl | rfl <;> rcases fin2_cases x2 with rfl | rfl
    exacts [(key k).1, (key k).2.1, (key k).2.2.1, (key k).2.2.2]
  intro k
  set α := phiw θ 3 with hα
  set S := Sg α (L - k) with hSdef
  have hS := Sg_nonneg a3 (L - k)
  have hqS : 0 ≤ θ.q2 * S := mul_nonneg hq hS
  have r0 : (θ.gam + θ.lam1 + θ.lam2) * (θ.q2 * S * phiw θ 0) =
      θ.lam1 * (θ.q2 * S * phiw θ 1) + θ.lam2 * (θ.q2 * S * phiw θ 2) := by
    linear_combination (θ.q2 * S) * e0
  have r1 : (θ.gam + θ.mu1 + θ.lam2 + 0) * (θ.q2 * S * phiw θ 1) =
      θ.mu1 * (θ.q2 * S * phiw θ 0) + θ.lam2 * (θ.q2 * S * α) := by
    linear_combination (θ.q2 * S) * e1
  have r2 : (θ.gam + θ.mu2 + θ.lam1 + θ.lam2) * (θ.q2 * S * phiw θ 2) =
      θ.mu2 * (θ.q2 * S * phiw θ 0) + θ.lam1 * (θ.q2 * S * α) + θ.lam2 * (θ.q2 * S) := by
    linear_combination (θ.q2 * S) * e2
  have r3 : (θ.gam + θ.mu1 + θ.mu2) * (θ.q2 * S * α) =
      θ.mu2 * (θ.q2 * S * phiw θ 1) + θ.mu1 * (θ.q2 * S * phiw θ 2) := by
    linear_combination (θ.q2 * S) * e3
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (0,0,k)
    simp only [Lam_mul_step hθ, R2, outRate, W2_00, W2_10, W2_01, W2_11, fr_zero, fr_one]
    unfold Lam
    linarith
  · -- (0,1,k): firm 2 may hand a customer to firm 1
    simp only [Lam_mul_step hθ, R2, outRate, W2_00, W2_10, W2_01, W2_11, fr_zero, fr_one]
    unfold Lam
    rcases fr_cases (σ.s1 k) with t | t
    · have hk := hσ k (fr_eq_zero t)
      have hs := Sg_succ α (show 1 ≤ L - k by omega)
      have e : L - k - 1 = L - (k + 1) := by ring
      rw [e] at hs
      rw [t]
      have : θ.lam2 * (θ.q2 * S) = θ.lam2 * θ.q2 + θ.lam2 * (θ.q2 * Sg α (L - (k + 1)) * α) := by
        rw [hSdef, hs]; ring
      linarith
    · rw [t]
      have := mul_nonneg (mul_nonneg hqS l2.le) (sub_nonneg.mpr b2.le)
      linarith
  · -- (1,0,k): firm 2 may accept a customer from firm 1
    have hSm : Sg α (L - (k - 1)) ≤ 1 + α * S := by
      have := Sg_succ_le a3 (L - k)
      rwa [show L - k + 1 = L - (k - 1) by ring] at this
    have h1 : θ.q2 * α * Sg α (L - (k - 1)) ≤ θ.q2 * α * (1 + α * S) :=
      mul_le_mul_of_nonneg_left hSm (mul_nonneg hq a3)
    have h2 : θ.q2 * S * α ^ 2 ≤ θ.q2 * S * phiw θ 1 :=
      mul_le_mul_of_nonneg_left c hqS
    have h3 : 0 ≤ (θ.q2 * S * phiw θ 1 + (piNC2 θ 0 - piNC2 θ 1 + θ.l2))
        - θ.q2 * Sg α (L - (k - 1)) * α := by nlinarith
    simp only [Lam_mul_step hθ, R2, outRate, W2_00, W2_10, W2_01, W2_11, fr_zero, fr_one]
    unfold Lam
    rcases fr_cases (σ.s2 k) with t | t <;> rw [t]
    · have := mul_nonneg l1.le h3
      linarith
    · linarith
  · -- (1,1,k)
    simp only [Lam_mul_step hθ, R2, outRate, W2_00, W2_10, W2_01, W2_11, fr_zero, fr_one]
    unfold Lam
    linarith

lemma pay2_le_W2 (hθ : θ.Standing) (σ : Profile) (L : ℤ) (hσ : ∀ k, σ.s1 k = 0 → k + 1 ≤ L)
    (hC : phiw θ 3 * θ.q2 ≤ piNC2 θ 0 - piNC2 θ 1 + θ.l2) (s : State) :
    pay2 θ σ s ≤ W2 θ L s := by
  rw [pay2_eq_gpay]
  exact gpay_le_of_super hθ σ _ _ (r2_abs hθ σ) (W2 θ L) _ (W2_abs hθ L)
    (fun t => super_of_gen hθ σ (R2 θ σ) (W2 θ L) t (W2_gen hθ σ L hσ hC t)) s

lemma sysG_zero' {a b m n c a' b' S1 S2 d0 d1 d2 d3 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hc : 0 < c) (ha' : 0 ≤ a') (hb' : 0 ≤ b')
    (h : SysG a b m n c a' b' S1 S2 d0 d1 d2 d3) (h1 : a' * S1 = 0) (h2 : b' * S2 = 0) :
    d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ d3 = 0 := by
  obtain ⟨e0, e1, e2, e3⟩ := h
  exact sysG_zero ha hb hm hn hc ha' hb' ⟨e0, by rw [mul_zero]; linarith,
    by rw [mul_zero]; linarith, e3⟩


end P5
end TradingFavors.Existence

open TradingFavors.Existence TradingFavors.Existence.P5 in
theorem solution (θ : Params) (hθ : θ.Standing) : IsTFE θ sigmaNC := by
  have l1 := hθ.1; have l2 := hθ.2.1; have m1 := hθ.2.2.1; have m2 := hθ.2.2.2.1
  have gp := hθ.2.2.2.2.1
  have hp1 : 0 ≤ θ.p1 := hθ.2.2.2.2.2.1
  have hp2 : 0 ≤ θ.p2 := hθ.2.2.2.2.2.2.1
  have hl1 : 0 ≤ θ.l1 := hθ.2.2.2.2.2.2.2.2.2.1
  have hl2 : 0 ≤ θ.l2 := hθ.2.2.2.2.2.2.2.2.2.2.1
  have hg1 : 0 ≤ piNC1 θ 0 - piNC1 θ 1 + θ.l1 := by
    rw [← nc1_gap hθ]; obtain ⟨r0, r1⟩ := rhoHat1_mem hθ; nlinarith
  have hg2 : 0 ≤ piNC2 θ 0 - piNC2 θ 1 + θ.l2 := by
    rw [← nc2_gap hθ]; obtain ⟨r0, r1⟩ := rhoHat2_mem hθ; nlinarith
  have hs1 : ∀ k, sigmaNC.s1 k = 1 := fun _ => rfl
  have hs2 : ∀ k, sigmaNC.s2 k = 1 := fun _ => rfl
  have z1 : ∀ k, pay1 θ sigmaNC (0, 1, k) = piNC1 θ 0 ∧ pay1 θ sigmaNC (1, 1, k) = piNC1 θ 1 := by
    intro k
    have c := cluster1 hθ sigmaNC k
    rw [hs1, hs2, fr_one] at c
    simp only [sub_self, mul_zero] at c
    have z := sysG_zero l1.le l2.le m1.le m2.le gp le_rfl le_rfl (sysG_zero_rates c)
    exact ⟨by linarith [z.2.2.1], by linarith [z.2.2.2]⟩
  have z2 : ∀ k, pay2 θ sigmaNC (1, 0, k) = piNC2 θ 0 ∧ pay2 θ sigmaNC (1, 1, k) = piNC2 θ 1 := by
    intro k
    have c := cluster2 hθ sigmaNC k
    rw [hs1, hs2, fr_one] at c
    simp only [sub_self, mul_zero] at c
    have z := sysG_zero l1.le l2.le m1.le m2.le gp le_rfl le_rfl (sysG_zero_rates c)
    exact ⟨by linarith [z.2.1], by linarith [z.2.2.2]⟩
  intro k
  refine ⟨?_, ?_⟩
  · unfold Cond4Firm1 pi1
    rw [hs1, (z1 (k + 1)).2, (z1 k).1]
    constructor
    · intro h; exact absurd h (by decide)
    · intro h; linarith
  · unfold Cond4Firm2 pi2
    rw [hs2, (z2 (k - 1)).2, (z2 k).1]
    constructor
    · intro h; exact absurd h (by decide)
    · intro h; linarith
