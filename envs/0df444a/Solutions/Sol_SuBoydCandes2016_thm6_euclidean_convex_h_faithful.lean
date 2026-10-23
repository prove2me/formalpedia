-- Prove2me | solution 1 for SuBoydCandes2016.thm6_euclidean_convex_h_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T04:50:06.382886+00:00
-- url     : https://prove2.me/submissions/6cf86222-9f92-44f3-952c-27515325006c

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_NesterovFB_Rates_Algorithm
import Definitions.Def_NesterovODE_GenScheme_Run

open Filter Topology InnerProductSpace
open Filter Topology InnerProductSpace NNReal

namespace SB86

open ThreeOpSplitting.ConvexRates NesterovFB.Rates

/-- Proper convex (epigraph) without the closedness condition. -/
def PCC86 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (f : H → EReal) : Prop :=
  (∀ x : H, f x ≠ ⊥) ∧ (∃ x : H, f x ≠ ⊤) ∧ True ∧ Convex ℝ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)}

lemma nfb_line_deriv {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (h : H → ℝ) (hd : Differentiable ℝ h) (x v : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => h (x + s • v)) ⟪gradient h (x + t • v), v⟫_ℝ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hf := (hd (x + t • v)).hasFDerivAt
  have := hf.comp_hasDerivAt t hl
  have e : fderiv ℝ h (x + t • v) v = ⟪gradient h (x + t • v), v⟫_ℝ := by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  rw [← e]; exact this

lemma nfb_grad_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (h : H → ℝ) (hc : ConvexOn ℝ Set.univ h) (hd : Differentiable ℝ h) (x y : H) :
    h x + ⟪gradient h x, y - x⟫_ℝ ≤ h y := by
  have hder := nfb_line_deriv h hd x (y - x) 0
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

lemma nfb_descent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (h : H → ℝ) (hd : Differentiable ℝ h) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ x y : H, ‖gradient h x - gradient h y‖ ≤ L * ‖x - y‖) (x y : H) :
    h y ≤ h x + ⟪gradient h x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  set v := y - x with hv
  set ψ : ℝ → ℝ := fun t => h (x + t • v) - t * ⟪gradient h x, v⟫_ℝ - L / 2 * t ^ 2 * ‖v‖ ^ 2
    with hψ
  have hψd : ∀ t, HasDerivAt ψ (⟪gradient h (x + t • v), v⟫_ℝ - ⟪gradient h x, v⟫_ℝ
      - L * t * ‖v‖ ^ 2) t := by
    intro t
    have h1 := nfb_line_deriv h hd x v t
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

lemma nfb_real_limit_le {A B C : ℝ} (h : ∀ t : ℝ, 0 < t → t ≤ 1 → A ≤ B + t * C) : A ≤ B := by
  have ht : Tendsto (fun t : ℝ => B + t * C) (𝓝[>] 0) (𝓝 (B + 0 * C)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    exact ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0)
  rw [zero_mul, add_zero] at ht
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t htt
  exact h t htt.1 htt.2.le

lemma nfb_prox_fin {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (f : H → EReal) (P : H → H) (hf : PCC86 f) (hP : IsProx γ f P)
    (x : H) : f (P x) ≠ ⊤ := by
  obtain ⟨hbot, ⟨x0, hx0⟩, _, _⟩ := hf
  intro htop
  have h1 := hP x x0
  rw [htop, EReal.top_add_coe, ← EReal.coe_toReal hx0 (hbot x0), ← EReal.coe_add] at h1
  exact absurd h1 (not_le.2 (EReal.coe_lt_top _))

lemma nfb_prox_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (hγ : 0 < γ) (f : H → EReal) (P : H → H) (hf : PCC86 f)
    (hP : IsProx γ f P) (x y : H) (a b : ℝ) (ha : f (P x) = a) (hb : f y ≤ b) :
    ⟪x - P x, y - P x⟫_ℝ ≤ γ * (b - a) := by
  obtain ⟨hbot, _, _, hconv⟩ := hf
  have key : γ * (a - b) ≤ ⟪P x - x, y - P x⟫_ℝ := by
    have h := nfb_real_limit_le (A := a - b) (B := ⟪P x - x, y - P x⟫_ℝ / γ)
      (C := ‖y - P x‖ ^ 2 / (2 * γ)) (fun t ht0 ht1 => by
        set yt := (1 - t) • P x + t • y with hyt
        have hm1 : (P x, a) ∈ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)} := by
          simp only [Set.mem_ofPred_eq]; rw [ha]
        have hm2 : (y, b) ∈ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)} := by
          simp only [Set.mem_ofPred_eq]; exact hb
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

/-- Forward-backward inequality. -/
lemma nfb_fb_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (L : ℝ≥0) (s : ℝ) (P : H → H)
    (hΨ : PCC86 Ψ)
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL : s * (L : ℝ) ≤ 1)
    (hP : IsProx s Ψ P) (y z : H) (a b : ℝ)
    (ha : Ψ (P (y - s • gradient Φ y)) = a) (hb : Ψ z ≤ b) :
    a + Φ (P (y - s • gradient Φ y)) + 1 / (2 * s) * ‖P (y - s • gradient Φ y) - z‖ ^ 2 ≤
      b + Φ z + 1 / (2 * s) * ‖y - z‖ ^ 2 := by
  have hd : Differentiable ℝ Φ := hΦd.differentiable (by norm_num)
  set g := gradient Φ y with hg
  set p := P (y - s • g) with hp
  have h1 := nfb_prox_ineq s hs Ψ P hΨ hP (y - s • g) z a b ha hb
  rw [← hp] at h1
  have hLip : ∀ u v : H, ‖gradient Φ u - gradient Φ v‖ ≤ (L:ℝ) * ‖u - v‖ := by
    intro u v; have := hL.dist_le_mul u v; rwa [dist_eq_norm, dist_eq_norm] at this
  have h2 := nfb_descent Φ hd L L.2 hLip y p
  have h3 := nfb_grad_ineq Φ hΦc hd y z
  rw [← hg] at h2 h3
  have e1 : y - s • g - p = (y - p) - s • g := by abel
  rw [e1, inner_sub_left, real_inner_smul_left] at h1
  have e2 : ‖y - z‖ ^ 2 = ‖y - p‖ ^ 2 - 2 * ⟪y - p, z - p⟫_ℝ + ‖p - z‖ ^ 2 := by
    have : y - z = (y - p) - (z - p) := by abel
    rw [this, norm_sub_sq_real, norm_sub_rev z p]
  have e3 : ⟪g, z - p⟫_ℝ = ⟪g, z - y⟫_ℝ - ⟪g, p - y⟫_ℝ := by
    rw [← inner_sub_right]; congr 1; abel
  have hpy : ‖p - y‖ = ‖y - p‖ := norm_sub_rev _ _
  rw [hpy] at h2
  have hq : 0 ≤ ‖y - p‖ ^ 2 := sq_nonneg _
  have hLs : s * (L:ℝ) * ‖y - p‖ ^ 2 ≤ ‖y - p‖ ^ 2 := by nlinarith
  rw [e2]
  have key : s * (a + Φ p) ≤ s * (b + Φ z) - ⟪y - p, z - p⟫_ℝ + s * ((L:ℝ) / 2) * ‖y - p‖ ^ 2 := by
    nlinarith
  have : s * (a + Φ p + 1 / (2 * s) * ‖p - z‖ ^ 2) ≤
      s * (b + Φ z + 1 / (2 * s) * (‖y - p‖ ^ 2 - 2 * ⟪y - p, z - p⟫_ℝ + ‖p - z‖ ^ 2)) := by
    have e4 : s * (1 / (2 * s)) = 1 / 2 := by field_simp
    nlinarith
  exact le_of_mul_le_mul_left this hs


lemma nfb_theta_le {H : Type*} (Ψ : H → EReal) (Φ : H → ℝ) (u v : H)
    (hu : Ψ u ≠ ⊤) (hu' : Ψ u ≠ ⊥) (hv : Ψ v ≠ ⊤) (hv' : Ψ v ≠ ⊥)
    (h : theta Ψ Φ u ≤ theta Ψ Φ v) :
    (Ψ u).toReal + Φ u ≤ (Ψ v).toReal + Φ v := by
  unfold theta at h
  rw [← EReal.coe_toReal hu hu', ← EReal.coe_toReal hv hv', ← EReal.coe_add,
    ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  exact h

lemma nfb_star_fin {H : Type*} (Ψ : H → EReal) (Φ : H → ℝ)
    (hΨ1 : ∀ x, Ψ x ≠ ⊥) (hΨ2 : ∃ x, Ψ x ≠ ⊤) (xstar : H)
    (hxstar : ∀ y, theta Ψ Φ xstar ≤ theta Ψ Φ y) : Ψ xstar ≠ ⊤ := by
  obtain ⟨u, hu⟩ := hΨ2
  intro htop
  have h := hxstar u
  unfold theta at h
  rw [htop, EReal.top_add_coe, ← EReal.coe_toReal hu (hΨ1 u), ← EReal.coe_add] at h
  exact absurd h (not_le.2 (EReal.coe_lt_top _))

lemma nfb_iter_fin {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (s α : ℝ) (P : H → H) (x : ℕ → H)
    (hΨ : PCC86 Ψ) (hP : IsProx s Ψ P)
    (hrun : IsAccelFBRun Φ P α s x) (k : ℕ) (hk : 2 ≤ k) : Ψ (x k) ≠ ⊤ := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [hrun j (by omega)]
  exact nfb_prox_fin s Ψ P hΨ hP _

/-- norm identity for extrapolation -/
lemma nfb_extrap_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u d : H) (β : ℝ) :
    ‖u + β • d‖ ^ 2 = ‖u‖ ^ 2 + β * (‖u‖ ^ 2 - ‖u - d‖ ^ 2) + (β + β ^ 2) * ‖d‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  ring

lemma nfb_epi {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ψ : H → EReal) (hΨ : PCC86 Ψ) (u v : H) (a b t : ℝ)
    (ha : Ψ u ≤ a) (hb : Ψ v ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ψ ((1 - t) • u + t • v) ≤ (((1 - t) * a + t * b : ℝ) : EReal) := by
  have hm1 : (u, a) ∈ {p : H × ℝ | Ψ p.1 ≤ (p.2 : EReal)} := ha
  have hm2 : (v, b) ∈ {p : H × ℝ | Ψ p.1 ≤ (p.2 : EReal)} := hb
  have hc := hΨ.2.2.2 hm1 hm2 (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
  simpa only [Set.mem_ofPred_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
    smul_eq_mul] using hc

/-- Energy step. -/
lemma nfb_energy_step
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (L : ℝ≥0) (s α : ℝ) (P : H → H) (x : ℕ → H)
    (hΨ : PCC86 Ψ)
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL : s * (L : ℝ) ≤ 1)
    (hP : IsProx s Ψ P) (hα : 1 < α)
    (hrun : IsAccelFBRun Φ P α s x)
    (xstar : H) (hsf : Ψ xstar ≠ ⊤) (k : ℕ) (hk : 1 ≤ k) (hkf : Ψ (x k) ≠ ⊤) :
    2 * s / (α - 1) * ((k:ℝ) + α - 1) ^ 2 *
        ((Ψ (x (k + 1))).toReal + Φ (x (k + 1)) - ((Ψ xstar).toReal + Φ xstar))
      + (α - 1) * ‖zSeq α x (k + 1) - xstar‖ ^ 2
      + 2 * s / (α - 1) * ((α - 3) * k + (α - 2) ^ 2) *
        ((Ψ (x k)).toReal + Φ (x k) - ((Ψ xstar).toReal + Φ xstar)) ≤
    2 * s / (α - 1) * ((k:ℝ) + α - 2) ^ 2 *
        ((Ψ (x k)).toReal + Φ (x k) - ((Ψ xstar).toReal + Φ xstar))
      + (α - 1) * ‖zSeq α x k - xstar‖ ^ 2 := by
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  set T : ℝ := (k:ℝ) + α - 1 with hT
  have hT0 : 0 < T := by linarith
  set τ : ℝ := (α - 1) / T with hτ
  have hτT : τ * T = α - 1 := by rw [hτ]; field_simp
  have hτ0 : 0 ≤ τ := div_nonneg (by linarith) hT0.le
  have hτ1 : τ ≤ 1 := (div_le_one hT0).2 (by linarith)
  have hk1f : Ψ (x (k + 1)) ≠ ⊤ := nfb_iter_fin Ψ Φ s α P x hΨ hP hrun (k + 1) (by omega)
  set w := (1 - τ) • x k + τ • xstar with hw
  have hΨw := nfb_epi Ψ hΨ (x k) xstar (Ψ (x k)).toReal (Ψ xstar).toReal τ
    (EReal.coe_toReal hkf (hΨ.1 _)).ge (EReal.coe_toReal hsf (hΨ.1 _)).ge hτ0 hτ1
  have hΦw : Φ w ≤ (1 - τ) * Φ (x k) + τ * Φ xstar := by
    have := hΦc.2 (Set.mem_univ (x k)) (Set.mem_univ xstar) (by linarith : (0:ℝ) ≤ 1 - τ) hτ0
      (by ring)
    simpa only [smul_eq_mul] using this
  have hfb := nfb_fb_ineq Ψ Φ L s P hΨ hΦc hΦd hL hs hsL hP (extrap α x k) w
    (Ψ (x (k + 1))).toReal _
    (by rw [← hrun k (by omega)]; exact (EReal.coe_toReal hk1f (hΨ.1 _)).symm) hΨw
  rw [← hrun k (by omega)] at hfb
  have hα1 : (0:ℝ) < α - 1 := by linarith
  clear_value T τ
  have hTne : T ≠ 0 := hT0.ne'
  have hαne : α - 1 ≠ 0 := hα1.ne'
  have c1 : τ * ((k:ℝ) / (α - 1)) = 1 - τ := by
    rw [hτ]; field_simp; rw [hT]; ring
  have c2 : τ * (((k:ℝ) - 1) / (α - 1)) = ((k:ℝ) - 1) / T := by
    rw [hτ]; field_simp
  have e1 : x (k + 1) - w = τ • (zSeq α x (k + 1) - xstar) := by
    unfold zSeq
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Nat.add_sub_cancel]
    rw [hw]
    linear_combination (norm := module) c1 • (x k - x (k + 1))
  have e2 : extrap α x k - w = τ • (zSeq α x k - xstar) := by
    unfold zSeq extrap
    rw [hw, ← hT]
    linear_combination (norm := module) c2 • (x (k - 1) - x k)
  rw [e1, e2, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ0, mul_pow, mul_pow] at hfb
  set F1 := (Ψ (x (k + 1))).toReal + Φ (x (k + 1))
  set Fk := (Ψ (x k)).toReal + Φ (x k)
  set Fs := (Ψ xstar).toReal + Φ xstar
  set Z1 := ‖zSeq α x (k + 1) - xstar‖ ^ 2
  set Zk := ‖zSeq α x k - xstar‖ ^ 2
  have key : F1 - Fs + 1 / (2 * s) * (τ ^ 2 * Z1) ≤ (1 - τ) * (Fk - Fs) + 1 / (2 * s) * (τ ^ 2 * Zk) := by
    simp only [F1, Fk, Fs] at *
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left key (by positivity : (0:ℝ) ≤ 2 * s * T ^ 2 / (α - 1))
  have hkT : 1 - τ = (k:ℝ) / T := by rw [hτ]; field_simp; rw [hT]; ring
  rw [hkT] at hmul
  have r1 : 2 * s * T ^ 2 / (α - 1) * (F1 - Fs + 1 / (2 * s) * (τ ^ 2 * Z1)) =
      2 * s / (α - 1) * T ^ 2 * (F1 - Fs) + (α - 1) * Z1 := by
    rw [hτ]; field_simp
  have r2 : 2 * s * T ^ 2 / (α - 1) * ((k:ℝ) / T * (Fk - Fs) + 1 / (2 * s) * (τ ^ 2 * Zk)) =
      2 * s / (α - 1) * (k * T) * (Fk - Fs) + (α - 1) * Zk := by
    rw [hτ]; field_simp
  rw [r1, r2] at hmul
  have r3 : ((k:ℝ) + α - 2) ^ 2 = k * T + ((α - 3) * k + (α - 2) ^ 2) := by rw [hT]; ring
  rw [r3]
  linarith



lemma theta_coe {H : Type*} (Ψ : H → EReal) (Φ : H → ℝ) (u : H) (hu : Ψ u ≠ ⊤) (hu' : Ψ u ≠ ⊥) :
    theta Ψ Φ u = (((Ψ u).toReal + Φ u : ℝ) : EReal) := by
  unfold theta; rw [← EReal.coe_toReal hu hu', EReal.coe_add, EReal.toReal_coe]

lemma ereal_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, ((f i : ℝ) : EReal) = ((∑ i ∈ s, f i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, EReal.coe_add]

end SB86

open InnerProductSpace NesterovFB.Rates ThreeOpSplitting.ConvexRates SB86 in
theorem solution {n : ℕ}
    (Ψ : EuclideanSpace ℝ (Fin n) → EReal) (Φ : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal) (s r : ℝ)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (xstar : EuclideanSpace ℝ (Fin n))
    (hΨbot : ∀ y : EuclideanSpace ℝ (Fin n), Ψ y ≠ ⊥)
    (hΨdom : ∃ y : EuclideanSpace ℝ (Fin n), Ψ y ≠ ⊤)
    (hΨcvx : Convex ℝ {p : EuclideanSpace ℝ (Fin n) × ℝ | Ψ p.1 ≤ (p.2 : EReal)})
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL0 : 0 < L) (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL : s * L ≤ 1)
    (hP : IsProx s Ψ P)
    (hr : 3 < r)
    (hrun : NesterovODE.GenScheme.IsGenNesterovRun Φ P r s x)
    (hmin : ∀ y : EuclideanSpace ℝ (Fin n), theta Ψ Φ xstar ≤ theta Ψ Φ y) :
    (∀ k : ℕ, 1 ≤ k →
      theta Ψ Φ (x k) - theta Ψ Φ xstar
        ≤ (((r - 1) ^ 2 * ‖x 0 - xstar‖ ^ 2 / (2 * s * ((k : ℝ) + r - 2) ^ 2) : ℝ) : EReal)) ∧
    (∀ K : ℕ,
      ∑ k ∈ Finset.Icc 1 K, (((k : ℝ) + r - 1 : ℝ) : EReal) * (theta Ψ Φ (x k) - theta Ψ Φ xstar)
        ≤ (((r - 1) ^ 2 * ‖x 0 - xstar‖ ^ 2 / (2 * s * (r - 3)) : ℝ) : EReal)) := by
  have hΨ : PCC86 Ψ := ⟨hΨbot, hΨdom, trivial, hΨcvx⟩
  have hacc : IsAccelFBRun Φ P r s x := fun k _ => hrun k
  have hsf : Ψ xstar ≠ ⊤ := nfb_star_fin Ψ Φ hΨbot hΨdom xstar hmin
  have hfin : ∀ k, 1 ≤ k → Ψ (x k) ≠ ⊤ := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hrun j]; exact nfb_prox_fin s Ψ P hΨ hP _
  set Fs := (Ψ xstar).toReal + Φ xstar
  set θ : ℕ → ℝ := fun k => (Ψ (x k)).toReal + Φ (x k) - Fs with hθ
  have hθnn : ∀ k, 1 ≤ k → 0 ≤ θ k := fun k hk => by
    have := nfb_theta_le Ψ Φ xstar (x k) hsf (hΨbot _) (hfin k hk) (hΨbot _) (hmin _)
    simp only [θ, Fs]; linarith
  have hθe : ∀ k, 1 ≤ k → theta Ψ Φ (x k) - theta Ψ Φ xstar = ((θ k : ℝ) : EReal) := by
    intro k hk
    rw [theta_coe Ψ Φ _ (hfin k hk) (hΨbot _), theta_coe Ψ Φ _ hsf (hΨbot _), ← EReal.coe_sub]
  set E : ℕ → ℝ := fun k => 2 * s / (r - 1) * ((k : ℝ) + r - 2) ^ 2 * θ k
    + (r - 1) * ‖zSeq r x k - xstar‖ ^ 2 with hE
  have hr1 : (0 : ℝ) < r - 1 := by linarith
  have hstep : ∀ k, 1 ≤ k → E (k + 1) + 2 * s / (r - 1) * ((r - 3) * k + (r - 2) ^ 2) * θ k ≤ E k := by
    intro k hk
    have h := nfb_energy_step Ψ Φ L s r P x hΨ hΦc hΦd hL hs hsL hP (by linarith) hacc xstar hsf k hk
      (hfin k hk)
    simp only [E, θ, Fs]
    push_cast
    have e : ((k : ℝ) + 1 + r - 2) = (k : ℝ) + r - 1 := by ring
    rw [e]; linarith
  -- first step
  have hE1 : E 1 ≤ (r - 1) * ‖x 0 - xstar‖ ^ 2 := by
    have hx1 : x 1 = P (x 0 - s • gradient Φ (x 0)) := by
      have := hrun 0
      simpa [extrap] using this
    have hfb := nfb_fb_ineq Ψ Φ L s P hΨ hΦc hΦd hL hs hsL hP (x 0) xstar (Ψ (x 1)).toReal
      (Ψ xstar).toReal (by rw [← hx1]; exact (EReal.coe_toReal (hfin 1 le_rfl) (hΨbot _)).symm)
      (EReal.coe_toReal hsf (hΨbot _)).ge
    rw [← hx1] at hfb
    have hz1 : zSeq r x 1 = x 1 := by simp [zSeq]
    simp only [E, θ, Fs, hz1]
    have e : ((1 : ℕ) : ℝ) + r - 2 = r - 1 := by push_cast; ring
    rw [e]
    have : 2 * s / (r - 1) * (r - 1) ^ 2 = 2 * s * (r - 1) := by field_simp
    rw [this]
    have h2 : 2 * s * (r - 1) * (1 / (2 * s)) = r - 1 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hfb (by positivity : (0:ℝ) ≤ 2 * s * (r - 1))]
  have hEnn : ∀ k, 1 ≤ k → 0 ≤ E k := fun k hk => by
    simp only [E]; have := hθnn k hk; positivity
  have htele : ∀ K, E (K + 1) + ∑ k ∈ Finset.Icc 1 K, 2 * s / (r - 1) * ((r - 3) * k + (r - 2) ^ 2) * θ k
      ≤ E 1 := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have := hstep (K + 1) (by omega)
      linarith
  constructor
  · intro k hk
    rw [hθe k hk, EReal.coe_le_coe_iff]
    have hEk : E k ≤ E 1 := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have := htele j
      have : 0 ≤ ∑ k ∈ Finset.Icc 1 j, 2 * s / (r - 1) * ((r - 3) * k + (r - 2) ^ 2) * θ k :=
        Finset.sum_nonneg (fun i hi => by
          have := hθnn i (Finset.mem_Icc.mp hi).1
          have : (0:ℝ) ≤ (r - 3) * i + (r - 2) ^ 2 := by positivity
          positivity)
      linarith
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hD : 0 < (k : ℝ) + r - 2 := by linarith
    have hz := sq_nonneg ‖zSeq r x k - xstar‖
    have hmain : 2 * s / (r - 1) * ((k : ℝ) + r - 2) ^ 2 * θ k ≤ (r - 1) * ‖x 0 - xstar‖ ^ 2 := by
      have : E k ≤ (r - 1) * ‖x 0 - xstar‖ ^ 2 := hEk.trans hE1
      simp only [E] at this; nlinarith [mul_nonneg hr1.le hz]
    rw [le_div_iff₀ (by positivity)]
    have e : θ k * (2 * s * ((k : ℝ) + r - 2) ^ 2) =
        (r - 1) * (2 * s / (r - 1) * ((k : ℝ) + r - 2) ^ 2 * θ k) := by field_simp
    rw [e]
    nlinarith
  · intro K
    rw [Finset.sum_congr rfl (fun k hk => by rw [hθe k (Finset.mem_Icc.mp hk).1, ← EReal.coe_mul]),
      ereal_sum, EReal.coe_le_coe_iff]
    have h1 := htele K
    have h2 := hEnn (K + 1) (by omega)
    have h3 : ∑ k ∈ Finset.Icc 1 K, 2 * s / (r - 1) * ((r - 3) * ((k : ℝ) + r - 1)) * θ k ≤
        ∑ k ∈ Finset.Icc 1 K, 2 * s / (r - 1) * ((r - 3) * k + (r - 2) ^ 2) * θ k := by
      apply Finset.sum_le_sum
      intro k hk
      have := hθnn k (Finset.mem_Icc.mp hk).1
      apply mul_le_mul_of_nonneg_right _ this
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    have h4 : ∑ k ∈ Finset.Icc 1 K, 2 * s / (r - 1) * ((r - 3) * ((k : ℝ) + r - 1)) * θ k =
        2 * s * (r - 3) / (r - 1) * ∑ k ∈ Finset.Icc 1 K, ((k : ℝ) + r - 1) * θ k := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    have hr3 : (0 : ℝ) < r - 3 := by linarith
    rw [le_div_iff₀ (by positivity)]
    have h5 : 2 * s * (r - 3) / (r - 1) * ∑ k ∈ Finset.Icc 1 K, ((k : ℝ) + r - 1) * θ k
        ≤ (r - 1) * ‖x 0 - xstar‖ ^ 2 := by linarith
    have e : (∑ k ∈ Finset.Icc 1 K, ((k : ℝ) + r - 1) * θ k) * (2 * s * (r - 3)) =
        (r - 1) * (2 * s * (r - 3) / (r - 1) * ∑ k ∈ Finset.Icc 1 K, ((k : ℝ) + r - 1) * θ k) := by
      field_simp
    rw [e]
    nlinarith
