-- Prove2me | solution 1 for TwoSidedExp.DemandLimit.Supplement.theorem_1_gas
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:28:59.831384+00:00
-- url     : https://prove2.me/submissions/2a8e6864-7c07-4b08-b55f-c698164c837f

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting
import Definitions.Def_TwoSidedExp_DemandLimit_Supplement_Dynamics

open Filter Topology MeasureTheory

open TwoSidedExp
open TwoSidedExp.DemandLimit
open TwoSidedExp.DemandLimit.Supplement

/-- The stability sentence of Theorem 1, p. 12, including boundary initial conditions. -/
theorem solution {Γ Θ : Type} [Fintype Γ] [Fintype Θ]
    (M : Model Γ Θ) (hM : M.Standing) (lam tau : ℝ)
    (hlam : 0 < lam) (htau : 0 < tau) (sstar : Θ → ℝ)
    (hstar : M.sys.IsSteady lam tau sstar) (s : ℝ → Θ → ℝ)
    (hs : Trajectory M.sys lam tau s) :
    Tendsto s atTop (𝓝 sstar) := by
      -- algebraic key inequality
      have alg : ∀ (x y σ : Θ → ℝ) (ε : ℝ), 0 < ε → (∀ θ, 0 ≤ x θ) → (∀ θ, 0 ≤ y θ) →
          (∀ θ, σ θ * (x θ - y θ) = |x θ - y θ|) → (∀ θ, |σ θ| ≤ 1) →
          0 ≤ ∑ θ, σ θ * (x θ / (ε + ∑ θ', x θ') - y θ / (ε + ∑ θ', y θ')) := by
        intro x y σ ε hε hx hy hσ hσ1
        set X := ∑ θ', x θ' with hX
        set Y := ∑ θ', y θ' with hY
        have hX0 : 0 ≤ X := Finset.sum_nonneg (fun θ _ => hx θ)
        have hY0 : 0 ≤ Y := Finset.sum_nonneg (fun θ _ => hy θ)
        have hXp : 0 < ε + X := by linarith
        have hYp : 0 < ε + Y := by linarith
        have key : ∀ θ, σ θ * (x θ / (ε + X) - y θ / (ε + Y)) =
            ((ε + Y) * |x θ - y θ| - (X - Y) * (σ θ * y θ)) / ((ε + X) * (ε + Y)) := by
          intro θ
          rw [← hσ θ]
          field_simp
          ring
        rw [Finset.sum_congr rfl (fun θ _ => key θ), ← Finset.sum_div, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
        apply div_nonneg _ (by positivity)
        have h1 : |X - Y| ≤ ∑ θ, |x θ - y θ| := by
          rw [hX, hY, ← Finset.sum_sub_distrib]
          exact Finset.abs_sum_le_sum_abs _ _
        have h2 : |∑ θ, σ θ * y θ| ≤ Y := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          rw [hY]
          apply Finset.sum_le_sum
          intro θ _
          rw [abs_mul, abs_of_nonneg (hy θ)]
          nlinarith [hσ1 θ, hy θ]
        have h3 : (X - Y) * (∑ θ, σ θ * y θ) ≤ (∑ θ, |x θ - y θ|) * Y := by
          calc (X - Y) * (∑ θ, σ θ * y θ) ≤ |(X - Y) * (∑ θ, σ θ * y θ)| := le_abs_self _
            _ = |X - Y| * |∑ θ, σ θ * y θ| := abs_mul _ _
            _ ≤ (∑ θ, |x θ - y θ|) * Y := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        have h4 : 0 ≤ ∑ θ, |x θ - y θ| := by positivity
        nlinarith
      have hineq : ∀ u : Θ → ℝ, M.sys.InS u → ∀ σ : Θ → ℝ,
          (∀ θ, σ θ * (u θ - sstar θ) = |u θ - sstar θ|) → (∀ θ, |σ θ| ≤ 1) →
          ∑ θ, σ θ * drift M.sys lam tau u θ ≤ -∑ θ, tau * M.sys.ν θ * |u θ - sstar θ| := by
        intro u hu σ hσ hσ1
        have hγ : ∀ γ, 0 ≤ ∑ θ, σ θ * (M.sys.choice γ θ u - M.sys.choice γ θ sstar) := by
          intro γ
          have := alg (fun θ => M.sys.α γ θ * M.sys.v γ θ * u θ)
            (fun θ => M.sys.α γ θ * M.sys.v γ θ * sstar θ) σ (M.sys.eps γ) (hM.eps_pos γ)
            (fun θ => mul_nonneg (mul_pos (hM.alpha_pos γ θ) (hM.v_pos γ θ)).le (hu θ).1)
            (fun θ => mul_nonneg (mul_pos (hM.alpha_pos γ θ) (hM.v_pos γ θ)).le (hstar.1 θ).1)
            (by
              intro θ
              have hp := mul_pos (hM.alpha_pos γ θ) (hM.v_pos γ θ)
              rw [← mul_sub, abs_mul, abs_of_pos hp, ← hσ θ]
              ring) hσ1
          simpa [MFSystem.choice] using this
        have hterm : ∀ θ, σ θ * drift M.sys lam tau u θ = -(tau * M.sys.ν θ * |u θ - sstar θ|)
            - lam * ∑ γ, M.sys.φ γ * (σ θ * (M.sys.choice γ θ u - M.sys.choice γ θ sstar)) := by
          intro θ
          have h0 := hstar.2 θ
          have e1 : ∑ γ, M.sys.φ γ * (σ θ * (M.sys.choice γ θ u - M.sys.choice γ θ sstar))
              = σ θ * (∑ γ, M.sys.φ γ * M.sys.choice γ θ u
                  - ∑ γ, M.sys.φ γ * M.sys.choice γ θ sstar) := by
            rw [← Finset.sum_sub_distrib, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun γ _ => by ring)
          rw [e1, ← hσ θ]
          simp only [drift]
          linear_combination σ θ * h0
        rw [Finset.sum_congr rfl (fun θ _ => hterm θ), Finset.sum_sub_distrib, ← Finset.mul_sum,
          Finset.sum_comm, Finset.sum_neg_distrib]
        have hnn : 0 ≤ ∑ γ, ∑ θ, M.sys.φ γ *
            (σ θ * (M.sys.choice γ θ u - M.sys.choice γ θ sstar)) := by
          refine Finset.sum_nonneg (fun γ _ => ?_)
          rw [← Finset.mul_sum]
          exact mul_nonneg (hM.phi_pos γ).le (hγ γ)
        nlinarith [mul_nonneg hlam.le hnn]
      obtain ⟨c, hc0, hc⟩ : ∃ c > 0, ∀ θ, c ≤ tau * M.sys.ν θ := by
        rcases isEmpty_or_nonempty Θ with h | h
        · exact ⟨1, one_pos, fun θ => h.elim θ⟩
        · obtain ⟨θ0, hθ0⟩ := Finite.exists_min (fun θ => tau * M.sys.ν θ)
          exact ⟨_, mul_pos htau (hM.nu_pos θ0), hθ0⟩
      set ed : Θ → ℝ → ℝ := fun θ t => drift M.sys lam tau (s t) θ with hed
      set σf : Θ → ℝ → ℝ := fun θ t => if 0 < s t θ - sstar θ then 1 else
        if s t θ - sstar θ < 0 then -1 else if 0 ≤ ed θ t then 1 else -1 with hσf
      have hσe : ∀ θ t, σf θ t * (s t θ - sstar θ) = |s t θ - sstar θ| := by
        intro θ t
        simp only [hσf]
        split_ifs with h1 h2 h3
        · rw [abs_of_pos h1]; ring
        · rw [abs_of_neg h2]; ring
        · have : s t θ - sstar θ = 0 := by linarith [not_lt.1 h1, not_lt.1 h2]
          rw [this]; simp
        · have : s t θ - sstar θ = 0 := by linarith [not_lt.1 h1, not_lt.1 h2]
          rw [this]; simp
      have hσ1 : ∀ θ t, |σf θ t| ≤ 1 := by
        intro θ t
        simp only [hσf]
        split_ifs <;> simp
      have habsd : ∀ θ t, 0 ≤ t → HasDerivWithinAt (fun u => |s u θ - sstar θ|)
          (σf θ t * ed θ t) (Set.Ici t) t := by
        intro θ t ht
        have hd : HasDerivWithinAt (fun u => s u θ - sstar θ) (ed θ t) (Set.Ici t) t :=
          ((hs.2 θ t ht).mono (Set.Ici_subset_Ici.2 ht)).sub_const _
        by_cases h1 : 0 < s t θ - sstar θ
        · have e : σf θ t = 1 := by simp only [hσf]; rw [if_pos h1]
          rw [e, one_mul]
          refine hd.congr_of_eventuallyEq ?_ (abs_of_pos h1)
          filter_upwards [hd.continuousWithinAt.eventually (lt_mem_nhds h1)] with u hu
          exact abs_of_pos hu
        by_cases h2 : s t θ - sstar θ < 0
        · have e : σf θ t = -1 := by simp only [hσf]; rw [if_neg h1, if_pos h2]
          rw [e, neg_one_mul]
          refine hd.neg.congr_of_eventuallyEq ?_ (abs_of_neg h2)
          filter_upwards [hd.continuousWithinAt.eventually (gt_mem_nhds h2)] with u hu
          exact abs_of_neg hu
        have h0 : s t θ - sstar θ = 0 := by linarith [not_lt.1 h1, not_lt.1 h2]
        have e : σf θ t * ed θ t = |ed θ t| := by
          simp only [hσf]; rw [if_neg h1, if_neg h2]
          split_ifs with h3
          · rw [abs_of_nonneg h3]; ring
          · rw [abs_of_neg (not_le.1 h3)]; ring
        rw [e]
        rw [hasDerivWithinAt_iff_isLittleO] at hd ⊢
        refine Asymptotics.IsBigO.trans_isLittleO ?_ hd
        refine Asymptotics.IsBigO.of_bound 1 ?_
        filter_upwards [self_mem_nhdsWithin] with z hz
        have hz' : 0 ≤ z - t := sub_nonneg.2 hz
        rw [h0] at ⊢
        simp only [abs_zero, sub_zero, smul_eq_mul, Real.norm_eq_abs, one_mul]
        rw [show (z - t) * |ed θ t| = |(z - t) * ed θ t| by rw [abs_mul, abs_of_nonneg hz']]
        exact abs_abs_sub_abs_le_abs_sub _ _
      set V : ℝ → ℝ := fun t => ∑ θ, |s t θ - sstar θ| with hV
      have hVd : ∀ t, 0 ≤ t → HasDerivWithinAt V (∑ θ, σf θ t * ed θ t) (Set.Ici t) t := by
        intro t ht
        exact HasDerivWithinAt.fun_sum (fun θ _ => habsd θ t ht)
      have hVb : ∀ t, 0 ≤ t → ∑ θ, σf θ t * ed θ t ≤ -c * V t := by
        intro t ht
        have h := hineq (s t) (hs.1 t ht) (fun θ => σf θ t) (fun θ => hσe θ t) (fun θ => hσ1 θ t)
        have h2 : c * V t ≤ ∑ θ, tau * M.sys.ν θ * |s t θ - sstar θ| := by
          simp only [hV, Finset.mul_sum]
          exact Finset.sum_le_sum (fun θ _ => mul_le_mul_of_nonneg_right (hc θ) (abs_nonneg _))
        have h3 : ∑ θ, σf θ t * ed θ t = ∑ θ, σf θ t * drift M.sys lam tau (s t) θ := rfl
        linarith
      have hcont : ContinuousOn V (Set.Ici 0) := by
        have : ∀ θ, ContinuousOn (fun u => s u θ) (Set.Ici 0) :=
          fun θ t ht => (hs.2 θ t ht).continuousWithinAt
        exact continuousOn_finsetSum _ (fun θ _ => ((this θ).sub continuousOn_const).abs)
      set B : ℝ → ℝ := fun t => (V 0 + 1) * Real.exp (-(c / 2) * t) with hB
      have hV0 : 0 ≤ V 0 := Finset.sum_nonneg (fun θ _ => abs_nonneg _)
      have hVB : ∀ t, 0 ≤ t → V t ≤ B t := by
        intro b hb
        refine image_le_of_deriv_right_lt_deriv_boundary' (f := V) (a := 0) (b := b)
          (hcont.mono Set.Icc_subset_Ici_self) (fun x hx => hVd x hx.1)
          (B' := fun t => (V 0 + 1) * (Real.exp (-(c / 2) * t) * (-(c / 2))))
          (by simp [hB]) ?_ ?_ ?_ ⟨hb, le_rfl⟩
        · exact (continuous_const.mul (Real.continuous_exp.comp
            (continuous_const.mul continuous_id))).continuousOn
        · intro x hx
          have := ((hasDerivAt_id x).const_mul (-(c / 2))).exp.const_mul (V 0 + 1)
          have h' := this.hasDerivWithinAt (s := Set.Ici x)
          simp only [id, mul_one] at h'
          exact h'
        · intro x hx hfx
          have hb := hVb x hx.1
          have hBp : 0 < B x := by positivity
          have : (V 0 + 1) * (Real.exp (-(c / 2) * x) * (-(c / 2))) = -(c / 2) * B x := by
            simp only [hB]; ring
          rw [this]
          rw [hfx] at hb
          nlinarith
      have hBlim : Tendsto B atTop (𝓝 0) := by
        have : Tendsto (fun t => Real.exp (-(c / 2) * t)) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
        simp only [hB]
        simpa using this.const_mul (V 0 + 1)
      rw [tendsto_pi_nhds]
      intro θ
      have h1 : Tendsto (fun t => |s t θ - sstar θ|) atTop (𝓝 0) := by
        refine squeeze_zero' (Eventually.of_forall (fun t => abs_nonneg _)) ?_ hBlim
        filter_upwards [eventually_ge_atTop 0] with t ht
        refine le_trans ?_ (hVB t ht)
        exact Finset.single_le_sum (f := fun θ => |s t θ - sstar θ|)
          (fun θ _ => abs_nonneg _) (Finset.mem_univ θ)
      have h2 := (tendsto_zero_iff_abs_tendsto_zero _).2 h1
      have h3 := h2.add_const (sstar θ)
      simpa using h3
