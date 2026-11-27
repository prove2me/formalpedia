-- Prove2me | solution 1 for TwoSidedExp.DemandLimit.Supplement.theorem_1_step_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:28:45.999185+00:00
-- url     : https://prove2.me/submissions/f21b35b0-d774-4587-815d-018b0688baf6

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting
import Definitions.Def_TwoSidedExp_DemandLimit_Supplement_Lyapunov

open Filter Topology MeasureTheory

open TwoSidedExp
open TwoSidedExp.DemandLimit
open TwoSidedExp.DemandLimit.Supplement

/-- Step 5, p. A2: actual derivatives, strict dissipation, shifted positivity and log convergence. -/
theorem solution {Γ Θ : Type} [Fintype Γ] [Fintype Θ]
    (M : Model Γ Θ) (hM : M.Standing) (lam tau : ℝ)
    (hlam : 0 < lam) (htau : 0 < tau) (sstar : Θ → ℝ)
    (hstar : M.sys.IsSteady lam tau sstar) (s : ℝ → Θ → ℝ)
    (hs : Trajectory M.sys lam tau s) (hpos₀ : ∀ θ, 0 < s 0 θ) :
    (∀ t, 0 ≤ t → ∀ θ, 0 < s t θ) ∧
    (∀ y : Θ → ℝ, (∀ θ, y θ ≤ Real.log (M.sys.ρ θ)) →
      DifferentiableAt ℝ (V M.sys lam tau) y ∧
      ∀ θ, partialV M.sys lam tau y θ = -drift M.sys lam tau (fun θ => Real.exp (y θ)) θ) ∧
    (∀ t, 0 ≤ t →
      HasDerivWithinAt (fun u => M.sys.W lam tau (s u))
        (dissipation M.sys lam tau (s t)) (Set.Ici 0) t ∧
      (dissipation M.sys lam tau (s t) < 0 ↔ s t ≠ sstar) ∧
      (dissipation M.sys lam tau (s t) = 0 ↔ s t = sstar)) ∧
    (∀ z : Θ → ℝ, M.sys.InS z → (∀ θ, 0 < z θ) →
      0 ≤ M.sys.W lam tau z - M.sys.W lam tau sstar ∧
      (M.sys.W lam tau z - M.sys.W lam tau sstar = 0 ↔ z = sstar)) ∧
    Tendsto (fun t θ => Real.log (s t θ)) atTop (𝓝 (fun θ => Real.log (sstar θ))) := by
      classical
      have hρ := hM.rho_pos
      have hφ := hM.phi_pos
      have hε := hM.eps_pos
      have hν := hM.nu_pos
      have ha : ∀ γ θ, 0 < M.sys.α γ θ * M.sys.v γ θ := fun γ θ => mul_pos (hM.alpha_pos γ θ) (hM.v_pos γ θ)
      have hD : ∀ z : Θ → ℝ, (∀ θ, 0 ≤ z θ) → ∀ γ,
          0 < M.sys.eps γ + ∑ θ, M.sys.α γ θ * M.sys.v γ θ * z θ := by
        intro z hz γ
        have : 0 ≤ ∑ θ, M.sys.α γ θ * M.sys.v γ θ * z θ :=
          Finset.sum_nonneg (fun θ _ => mul_nonneg (ha γ θ).le (hz θ))
        linarith [hε γ]
      have mono : ∀ f f' : ℝ → ℝ, (∀ t, 0 ≤ t → HasDerivWithinAt f (f' t) (Set.Ici 0) t) →
          (∀ t, 0 ≤ t → 0 ≤ f' t) → MonotoneOn f (Set.Ici 0) := by
        intro f f' hf hf'
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
        · intro t ht; exact (hf t ht).continuousWithinAt
        · intro t ht
          rw [interior_Ici] at ht ⊢
          exact (hf t (le_of_lt ht)).mono Set.Ioi_subset_Ici_self
        · intro t ht; rw [interior_Ici] at ht; exact hf' t (le_of_lt ht)
      -- lower bound
      have L6 : ∀ θ, ∃ δ > 0, ∀ t, 0 ≤ t → δ ≤ s t θ := by
        intro θ
        set c := tau * M.sys.ν θ + lam * ∑ γ, M.sys.φ γ * (M.sys.α γ θ * M.sys.v γ θ / M.sys.eps γ) with hc
        have hc0 : 0 < c := by
          have : 0 ≤ ∑ γ, M.sys.φ γ * (M.sys.α γ θ * M.sys.v γ θ / M.sys.eps γ) :=
            Finset.sum_nonneg (fun γ _ => mul_nonneg (hφ γ).le (div_pos (ha γ θ) (hε γ)).le)
          have := mul_pos htau (hν θ)
          nlinarith
        set m := M.sys.ρ θ * (tau * M.sys.ν θ) / c with hm
        have hm0 : 0 < m := div_pos (mul_pos (hρ θ) (mul_pos htau (hν θ))) hc0
        have hdr : ∀ z : Θ → ℝ, M.sys.InS z →
            M.sys.ρ θ * (tau * M.sys.ν θ) - c * z θ ≤ drift M.sys lam tau z θ := by
          intro z hz
          have hz0 : ∀ θ, 0 ≤ z θ := fun θ => (hz θ).1
          have key : lam * ∑ γ, M.sys.φ γ * M.sys.choice γ θ z ≤
              lam * ∑ γ, M.sys.φ γ * (M.sys.α γ θ * M.sys.v γ θ / M.sys.eps γ) * z θ := by
            apply mul_le_mul_of_nonneg_left _ hlam.le
            apply Finset.sum_le_sum
            intro γ _
            rw [mul_assoc]
            apply mul_le_mul_of_nonneg_left _ (hφ γ).le
            unfold MFSystem.choice
            rw [div_mul_eq_mul_div]
            apply div_le_div_of_nonneg_left (mul_nonneg (ha γ θ).le (hz0 θ)) (hε γ)
            have : 0 ≤ ∑ θ, M.sys.α γ θ * M.sys.v γ θ * z θ :=
              Finset.sum_nonneg (fun θ _ => mul_nonneg (ha γ θ).le (hz0 θ))
            linarith
          have e2 : lam * ∑ γ, M.sys.φ γ * (M.sys.α γ θ * M.sys.v γ θ / M.sys.eps γ) * z θ =
              (lam * ∑ γ, M.sys.φ γ * (M.sys.α γ θ * M.sys.v γ θ / M.sys.eps γ)) * z θ := by
            rw [mul_assoc, Finset.sum_mul]
          unfold drift
          rw [hc]
          nlinarith
        refine ⟨min (s 0 θ) m, lt_min (hpos₀ θ) hm0, ?_⟩
        have hmon := mono (fun u => (s u θ - m) * Real.exp (c * u))
          (fun u => (drift M.sys lam tau (s u) θ + c * (s u θ - m)) * Real.exp (c * u)) ?_ ?_
        · intro t ht
          have h1 := hmon ((Set.mem_Ici.mpr le_rfl)) (Set.mem_Ici.mpr ht) ht
          simp only [mul_zero, Real.exp_zero, mul_one] at h1
          have he : 1 ≤ Real.exp (c * t) := Real.one_le_exp (mul_nonneg hc0.le ht)
          by_cases h0 : m ≤ s 0 θ
          · have : 0 ≤ s t θ - m := by
              by_contra hneg
              push Not at hneg
              nlinarith
            exact le_trans (min_le_right _ _) (by linarith)
          · push Not at h0
            by_cases h2 : m ≤ s t θ
            · exact le_trans (min_le_right _ _) h2
            · push Not at h2
              have : s t θ - m ≥ (s t θ - m) * Real.exp (c * t) := by nlinarith
              exact le_trans (min_le_left _ _) (by linarith)
        · intro t ht
          have h1 := (hs.2 θ t ht).sub_const m
          have h2 : HasDerivWithinAt (fun u => Real.exp (c * u)) (Real.exp (c * t) * c) (Set.Ici 0) t := by
            have := ((hasDerivAt_id t).const_mul c).exp
            simpa using this.hasDerivWithinAt
          exact (h1.mul h2).congr_deriv (by ring)
        · intro t ht
          apply mul_nonneg _ (Real.exp_pos _).le
          have := hdr (s t) (hs.1 t ht)
          have hcm : c * m = M.sys.ρ θ * (tau * M.sys.ν θ) := by rw [hm]; field_simp
          nlinarith
      choose δ hδpos hδ using L6
      have part1 : ∀ t, 0 ≤ t → ∀ θ, 0 < s t θ := fun t ht θ => lt_of_lt_of_le (hδpos θ) (hδ θ t ht)
      have hsp : ∀ θ, 0 < sstar θ := by
        intro θ
        rcases (hstar.1 θ).1.lt_or_eq with h | h
        · exact h
        · exfalso
          have e := hstar.2 θ
          have : ∑ γ, M.sys.φ γ * M.sys.choice γ θ sstar = 0 := by
            apply Finset.sum_eq_zero; intro γ _
            unfold MFSystem.choice; rw [← h]; simp
          rw [this, ← h] at e
          have := mul_pos (hρ θ) (mul_pos htau (hν θ))
          simp only [sub_zero, mul_zero] at e; linarith
      have L1 : ∀ γ (z w : Θ → ℝ), (∀ θ, 0 < z θ) → (∀ θ, 0 < w θ) →
          ∑ θ, M.sys.choice γ θ w * (Real.log (z θ) - Real.log (w θ))
            ≤ Real.log (M.sys.eps γ + ∑ θ, M.sys.α γ θ * M.sys.v γ θ * z θ)
              - Real.log (M.sys.eps γ + ∑ θ, M.sys.α γ θ * M.sys.v γ θ * w θ) := by
        intro γ z w hz hw
        have hDz := hD z (fun θ => (hz θ).le) γ
        have hDw := hD w (fun θ => (hw θ).le) γ
        set Az := ∑ θ, M.sys.α γ θ * M.sys.v γ θ * z θ with hAz
        set Aw := ∑ θ, M.sys.α γ θ * M.sys.v γ θ * w θ with hAw
        set r := Real.log (M.sys.eps γ + Az) - Real.log (M.sys.eps γ + Aw) with hr
        have term : ∀ θ, M.sys.choice γ θ w * (Real.log (z θ) - Real.log (w θ)) ≤
            M.sys.α γ θ * M.sys.v γ θ * z θ / (M.sys.eps γ + Az)
            - M.sys.α γ θ * M.sys.v γ θ * w θ / (M.sys.eps γ + Aw)
            + M.sys.α γ θ * M.sys.v γ θ * w θ / (M.sys.eps γ + Aw) * r := by
          intro θ
          have hx : 0 < z θ * (M.sys.eps γ + Aw) / (w θ * (M.sys.eps γ + Az)) :=
            div_pos (mul_pos (hz θ) hDw) (mul_pos (hw θ) hDz)
          have hl := Real.log_le_sub_one_of_pos hx
          rw [Real.log_div (mul_pos (hz θ) hDw).ne' (mul_pos (hw θ) hDz).ne',
            Real.log_mul (hz θ).ne' hDw.ne', Real.log_mul (hw θ).ne' hDz.ne'] at hl
          have hc : 0 ≤ M.sys.choice γ θ w := by
            unfold MFSystem.choice; exact div_nonneg (mul_nonneg (ha γ θ).le (hw θ).le) hDw.le
          have := mul_le_mul_of_nonneg_left
            (show Real.log (z θ) - Real.log (w θ) ≤
              (z θ * (M.sys.eps γ + Aw) / (w θ * (M.sys.eps γ + Az)) - 1) + r by rw [hr]; linarith) hc
          have e : M.sys.choice γ θ w * ((z θ * (M.sys.eps γ + Aw) / (w θ * (M.sys.eps γ + Az)) - 1) + r)
              = M.sys.α γ θ * M.sys.v γ θ * z θ / (M.sys.eps γ + Az)
                - M.sys.α γ θ * M.sys.v γ θ * w θ / (M.sys.eps γ + Aw)
                + M.sys.α γ θ * M.sys.v γ θ * w θ / (M.sys.eps γ + Aw) * r := by
            unfold MFSystem.choice
            rw [← hAw]
            have hwne := (hw θ).ne'
            field_simp
          linarith
        refine le_trans (Finset.sum_le_sum (fun θ _ => term θ)) ?_
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div,
          ← Finset.sum_div, ← hAz, ← hAw]
        have hk : 1 - r ≤ (M.sys.eps γ + Aw) / (M.sys.eps γ + Az) := by
          have := Real.log_le_sub_one_of_pos (div_pos hDw hDz)
          rw [Real.log_div hDw.ne' hDz.ne'] at this
          rw [hr]; linarith
        have e : Az / (M.sys.eps γ + Az) - Aw / (M.sys.eps γ + Aw) + Aw / (M.sys.eps γ + Aw) * r - r
            = M.sys.eps γ / (M.sys.eps γ + Aw) * (1 - r - (M.sys.eps γ + Aw) / (M.sys.eps γ + Az)) := by
          field_simp; ring
        have : M.sys.eps γ / (M.sys.eps γ + Aw) * (1 - r - (M.sys.eps γ + Aw) / (M.sys.eps γ + Az)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (div_pos (hε γ) hDw).le (by linarith)
        linarith
      have Wdiff : ∀ z : Θ → ℝ, M.sys.W lam tau z - M.sys.W lam tau sstar =
          ∑ γ, lam * M.sys.φ γ * (Real.log (M.sys.eps γ + ∑ θ, M.sys.α γ θ * M.sys.v γ θ * z θ)
              - Real.log (M.sys.eps γ + ∑ θ, M.sys.α γ θ * M.sys.v γ θ * sstar θ))
          + ∑ θ, (tau * M.sys.ν θ * (z θ - sstar θ)
              - tau * M.sys.ν θ * M.sys.ρ θ * (Real.log (z θ) - Real.log (sstar θ))) := by
        intro z
        unfold MFSystem.W
        simp only [mul_sub, Finset.sum_sub_distrib]
        ring
      have swap : ∀ (f : Γ → Θ → ℝ) (g : Θ → ℝ),
          ∑ γ, lam * M.sys.φ γ * ∑ θ, f γ θ * g θ = ∑ θ, (lam * ∑ γ, M.sys.φ γ * f γ θ) * g θ := by
        intro f g
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      have sqb : ∀ a b : ℝ, 0 < a → 0 < b →
          (Real.sqrt a - Real.sqrt b) ^ 2 ≤ a - b - b * (Real.log a - Real.log b) := by
        intro a b ha hb
        obtain ⟨p, hp, rfl⟩ : ∃ p, 0 < p ∧ p ^ 2 = a :=
          ⟨Real.sqrt a, Real.sqrt_pos.mpr ha, Real.sq_sqrt ha.le⟩
        obtain ⟨q, hq, rfl⟩ : ∃ q, 0 < q ∧ q ^ 2 = b :=
          ⟨Real.sqrt b, Real.sqrt_pos.mpr hb, Real.sq_sqrt hb.le⟩
        rw [Real.sqrt_sq hp.le, Real.sqrt_sq hq.le, Real.log_pow, Real.log_pow]
        have hl := Real.log_le_sub_one_of_pos (div_pos hp hq)
        rw [Real.log_div hp.ne' hq.ne'] at hl
        have h1 : q ^ 2 * (Real.log p - Real.log q) ≤ q ^ 2 * (p / q - 1) :=
          mul_le_mul_of_nonneg_left hl (sq_nonneg _)
        have e : q ^ 2 * (p / q - 1) = p * q - q ^ 2 := by field_simp
        push_cast
        nlinarith
      have expb : ∀ a b : ℝ, 0 < a → 0 < b → a - b ≤ a * (Real.log a - Real.log b) := by
        intro a b ha hb
        have hl := Real.log_le_sub_one_of_pos (div_pos hb ha)
        rw [Real.log_div hb.ne' ha.ne'] at hl
        have h1 := mul_le_mul_of_nonneg_left hl ha.le
        have e : a * (b / a - 1) = b - a := by field_simp
        nlinarith
      have L2 : ∀ z : Θ → ℝ, (∀ θ, 0 < z θ) →
          ∑ θ, tau * M.sys.ν θ * (Real.sqrt (z θ) - Real.sqrt (sstar θ)) ^ 2
            ≤ M.sys.W lam tau z - M.sys.W lam tau sstar := by
        intro z hz
        rw [Wdiff z]
        have h1 : ∑ γ, lam * M.sys.φ γ * ∑ θ, M.sys.choice γ θ sstar * (Real.log (z θ) - Real.log (sstar θ)) ≤
            ∑ γ, lam * M.sys.φ γ * (Real.log (M.sys.eps γ + ∑ θ, M.sys.α γ θ * M.sys.v γ θ * z θ)
              - Real.log (M.sys.eps γ + ∑ θ, M.sys.α γ θ * M.sys.v γ θ * sstar θ)) :=
          Finset.sum_le_sum (fun γ _ =>
            mul_le_mul_of_nonneg_left (L1 γ z sstar hz hsp) (mul_pos hlam (hφ γ)).le)
        rw [swap] at h1
        have h2 : ∀ θ, lam * ∑ γ, M.sys.φ γ * M.sys.choice γ θ sstar
            = (M.sys.ρ θ - sstar θ) * (tau * M.sys.ν θ) := fun θ => (hstar.2 θ).symm
        simp only [h2] at h1
        have h3 : ∑ θ, tau * M.sys.ν θ * (Real.sqrt (z θ) - Real.sqrt (sstar θ)) ^ 2 ≤
            ∑ θ, (M.sys.ρ θ - sstar θ) * (tau * M.sys.ν θ) * (Real.log (z θ) - Real.log (sstar θ))
            + ∑ θ, (tau * M.sys.ν θ * (z θ - sstar θ)
              - tau * M.sys.ν θ * M.sys.ρ θ * (Real.log (z θ) - Real.log (sstar θ))) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_le_sum; intro θ _
          have := mul_le_mul_of_nonneg_left (sqb (z θ) (sstar θ) (hz θ) (hsp θ)) (mul_pos htau (hν θ)).le
          nlinarith
        linarith
      have L3 : ∀ z : Θ → ℝ, (∀ θ, 0 < z θ) →
          M.sys.W lam tau z - M.sys.W lam tau sstar
            ≤ ∑ θ, (-drift M.sys lam tau z θ) * (Real.log (z θ) - Real.log (sstar θ)) := by
        intro z hz
        rw [Wdiff z]
        have h1 : ∑ γ, lam * M.sys.φ γ * (Real.log (M.sys.eps γ + ∑ θ, M.sys.α γ θ * M.sys.v γ θ * z θ)
              - Real.log (M.sys.eps γ + ∑ θ, M.sys.α γ θ * M.sys.v γ θ * sstar θ)) ≤
            ∑ γ, lam * M.sys.φ γ * ∑ θ, M.sys.choice γ θ z * (Real.log (z θ) - Real.log (sstar θ)) := by
          apply Finset.sum_le_sum; intro γ _
          apply mul_le_mul_of_nonneg_left _ (mul_pos hlam (hφ γ)).le
          have := L1 γ sstar z hsp hz
          have e : ∑ θ, M.sys.choice γ θ z * (Real.log (sstar θ) - Real.log (z θ)) =
              -∑ θ, M.sys.choice γ θ z * (Real.log (z θ) - Real.log (sstar θ)) := by
            rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun θ _ => by ring)
          linarith
        rw [swap] at h1
        have h3 : ∑ θ, (tau * M.sys.ν θ * (z θ - sstar θ)
              - tau * M.sys.ν θ * M.sys.ρ θ * (Real.log (z θ) - Real.log (sstar θ))) ≤
            ∑ θ, (tau * M.sys.ν θ * (z θ * (Real.log (z θ) - Real.log (sstar θ)))
              - tau * M.sys.ν θ * M.sys.ρ θ * (Real.log (z θ) - Real.log (sstar θ))) := by
          apply Finset.sum_le_sum; intro θ _
          have := mul_le_mul_of_nonneg_left (expb (z θ) (sstar θ) (hz θ) (hsp θ)) (mul_pos htau (hν θ)).le
          linarith
        have e : ∑ θ, (lam * ∑ γ, M.sys.φ γ * M.sys.choice γ θ z) * (Real.log (z θ) - Real.log (sstar θ))
            + ∑ θ, (tau * M.sys.ν θ * (z θ * (Real.log (z θ) - Real.log (sstar θ)))
              - tau * M.sys.ν θ * M.sys.ρ θ * (Real.log (z θ) - Real.log (sstar θ)))
            = ∑ θ, (-drift M.sys lam tau z θ) * (Real.log (z θ) - Real.log (sstar θ)) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun θ _ => by unfold drift; ring)
        linarith
      have part2 : ∀ y : Θ → ℝ, DifferentiableAt ℝ (V M.sys lam tau) y ∧
          ∀ θ, partialV M.sys lam tau y θ = -drift M.sys lam tau (fun θ => Real.exp (y θ)) θ := by
        intro y
        have hVeq : V M.sys lam tau = ((fun y : Θ → ℝ =>
            ∑ γ, lam * M.sys.φ γ * Real.log (M.sys.eps γ + ∑ θ, M.sys.α γ θ * M.sys.v γ θ * Real.exp (y θ)))
            - (fun y : Θ → ℝ => ∑ θ, tau * M.sys.ν θ * M.sys.ρ θ * y θ))
            + (fun y : Θ → ℝ => ∑ θ, tau * M.sys.ν θ * Real.exp (y θ)) := by
          funext y; unfold V MFSystem.W; simp only [Real.log_exp, Pi.add_apply, Pi.sub_apply]
        have hpos : ∀ γ, 0 < M.sys.eps γ + ∑ θ, M.sys.α γ θ * M.sys.v γ θ * Real.exp (y θ) :=
          hD _ (fun θ => (Real.exp_pos _).le)
        have hE : ∀ θ, HasFDerivAt (fun y : Θ → ℝ => Real.exp (y θ))
            (Real.exp (y θ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Θ => ℝ) θ) y :=
          fun θ => (hasFDerivAt_apply θ y).exp
        have hF := ((HasFDerivAt.fun_sum (u := Finset.univ) (fun γ _ =>
          (((HasFDerivAt.fun_sum (u := Finset.univ) (fun θ _ =>
            (hE θ).const_mul (M.sys.α γ θ * M.sys.v γ θ))).const_add (M.sys.eps γ)).log
              (hpos γ).ne').const_mul (lam * M.sys.φ γ))).sub
          (HasFDerivAt.fun_sum (u := Finset.univ) (fun θ _ =>
            (hasFDerivAt_apply (𝕜 := ℝ) θ y).const_mul (tau * M.sys.ν θ * M.sys.ρ θ)))).add
          (HasFDerivAt.fun_sum (u := Finset.univ) (fun θ _ => (hE θ).const_mul (tau * M.sys.ν θ)))
        refine ⟨?_, ?_⟩
        · rw [hVeq]; exact hF.differentiableAt
        · intro θ
          unfold partialV
          rw [hVeq, hF.fderiv]
          simp [Pi.single_apply, drift, MFSystem.choice]
          have : ∀ x, lam * M.sys.φ x * ((M.sys.eps x + ∑ i, M.sys.α x i * M.sys.v x i * Real.exp (y i))⁻¹
              * (M.sys.α x θ * M.sys.v x θ * Real.exp (y θ))) = lam * (M.sys.φ x *
              (M.sys.α x θ * M.sys.v x θ * Real.exp (y θ) /
                (M.sys.eps x + ∑ i, M.sys.α x i * M.sys.v x i * Real.exp (y i)))) := fun x => by ring
          simp only [this, ← Finset.mul_sum]; ring
      have L5 : ∀ t, 0 ≤ t → HasDerivWithinAt (fun u => M.sys.W lam tau (s u))
          (-∑ θ, (drift M.sys lam tau (s t) θ) ^ 2 / s t θ) (Set.Ici 0) t := by
        intro t ht
        have hst := part1 t ht
        have hd := fun θ => hs.2 θ t ht
        have hpos := hD (s t) (fun θ => (hst θ).le)
        have hF := ((HasDerivWithinAt.fun_sum (u := Finset.univ) (fun γ _ =>
          (((HasDerivWithinAt.fun_sum (u := Finset.univ) (fun θ _ =>
            (hd θ).const_mul (M.sys.α γ θ * M.sys.v γ θ))).const_add (M.sys.eps γ)).log
              (hpos γ).ne').const_mul (lam * M.sys.φ γ))).sub
          (HasDerivWithinAt.fun_sum (u := Finset.univ) (fun θ _ =>
            ((hd θ).log (hst θ).ne').const_mul (tau * M.sys.ν θ * M.sys.ρ θ)))).add
          (HasDerivWithinAt.fun_sum (u := Finset.univ) (fun θ _ => (hd θ).const_mul (tau * M.sys.ν θ)))
        unfold MFSystem.W
        refine hF.congr_deriv ?_
        have hC : ∀ θ, (lam * ∑ γ, M.sys.φ γ * (M.sys.α γ θ * M.sys.v γ θ /
            (M.sys.eps γ + ∑ θ', M.sys.α γ θ' * M.sys.v γ θ' * s t θ'))) * s t θ
            = lam * ∑ γ, M.sys.φ γ * M.sys.choice γ θ (s t) := by
          intro θ; rw [mul_assoc, Finset.sum_mul]; congr 1
          exact Finset.sum_congr rfl (fun γ _ => by unfold MFSystem.choice; ring)
        have e1 : ∑ γ, lam * M.sys.φ γ * ((∑ θ, M.sys.α γ θ * M.sys.v γ θ * drift M.sys lam tau (s t) θ)
            / (M.sys.eps γ + ∑ θ, M.sys.α γ θ * M.sys.v γ θ * s t θ))
            = ∑ θ, (lam * ∑ γ, M.sys.φ γ * (M.sys.α γ θ * M.sys.v γ θ /
              (M.sys.eps γ + ∑ θ', M.sys.α γ θ' * M.sys.v γ θ' * s t θ'))) * drift M.sys lam tau (s t) θ := by
          rw [← swap]
          exact Finset.sum_congr rfl (fun γ _ => by
            rw [Finset.sum_div]; congr 1; exact Finset.sum_congr rfl (fun θ _ => by ring))
        rw [e1, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl; intro θ _
        have h := hC θ
        have hsne := (hst θ).ne'
        set K := lam * ∑ γ, M.sys.φ γ * (M.sys.α γ θ * M.sys.v γ θ /
              (M.sys.eps γ + ∑ θ', M.sys.α γ θ' * M.sys.v γ θ' * s t θ')) with hKdef
        have hK : K = (lam * ∑ γ, M.sys.φ γ * M.sys.choice γ θ (s t)) / s t θ := by
          rw [← h]; field_simp
        rw [hK]; unfold drift; field_simp; ring
      have hdiss : ∀ t, 0 ≤ t → dissipation M.sys lam tau (s t)
          = -∑ θ, (drift M.sys lam tau (s t) θ) ^ 2 / s t θ := by
        intro t ht
        unfold dissipation
        have hst := part1 t ht
        have hexp : (fun θ => Real.exp (Real.log (s t θ))) = s t := funext (fun θ => Real.exp_log (hst θ))
        congr 1
        apply Finset.sum_congr rfl; intro θ _
        rw [(part2 _).2 θ, hexp, neg_sq]
      have hdrift0 : drift M.sys lam tau sstar = 0 := by
        funext θ; unfold drift; rw [hstar.2 θ]; simp
      have hsq0 : ∀ z : Θ → ℝ, (∀ θ, 0 < z θ) →
          M.sys.W lam tau z - M.sys.W lam tau sstar ≤ 0 → z = sstar := by
        intro z hz hW
        have h := L2 z hz
        have hnn : ∀ θ ∈ Finset.univ, 0 ≤ tau * M.sys.ν θ * (Real.sqrt (z θ) - Real.sqrt (sstar θ)) ^ 2 :=
          fun θ _ => mul_nonneg (mul_pos htau (hν θ)).le (sq_nonneg _)
        have hz0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp
          (le_antisymm (by linarith) (Finset.sum_nonneg hnn))
        funext θ
        have := hz0 θ (Finset.mem_univ _)
        rcases mul_eq_zero.mp this with h1 | h1
        · exact absurd h1 (mul_pos htau (hν θ)).ne'
        · have h2 := sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)
          exact (Real.sqrt_inj (hz θ).le (hsp θ).le).mp h2
      have part3 : ∀ t, 0 ≤ t →
          HasDerivWithinAt (fun u => M.sys.W lam tau (s u))
            (dissipation M.sys lam tau (s t)) (Set.Ici 0) t ∧
          (dissipation M.sys lam tau (s t) < 0 ↔ s t ≠ sstar) ∧
          (dissipation M.sys lam tau (s t) = 0 ↔ s t = sstar) := by
        intro t ht
        have hst := part1 t ht
        rw [hdiss t ht]
        have hnn : ∀ θ ∈ Finset.univ, 0 ≤ (drift M.sys lam tau (s t) θ) ^ 2 / s t θ :=
          fun θ _ => div_nonneg (sq_nonneg _) (hst θ).le
        have key : (-∑ θ, (drift M.sys lam tau (s t) θ) ^ 2 / s t θ = 0) ↔ s t = sstar := by
          constructor
          · intro h
            have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp (by linarith)
            have hd0 : ∀ θ, drift M.sys lam tau (s t) θ = 0 := by
              intro θ
              have := h0 θ (Finset.mem_univ _)
              rcases div_eq_zero_iff.mp this with h1 | h1
              · exact pow_eq_zero_iff two_ne_zero |>.mp h1
              · exact absurd h1 (hst θ).ne'
            apply hsq0 (s t) hst
            have := L3 (s t) hst
            simp only [hd0, neg_zero, zero_mul, Finset.sum_const_zero] at this
            exact this
          · intro h; rw [h, hdrift0]; simp
        refine ⟨L5 t ht, ?_, key⟩
        have hle : -∑ θ, (drift M.sys lam tau (s t) θ) ^ 2 / s t θ ≤ 0 :=
          neg_nonpos.mpr (Finset.sum_nonneg hnn)
        rw [ne_eq, ← key]; constructor
        · intro h; exact h.ne
        · intro h; exact lt_of_le_of_ne hle h
      have part4 : ∀ z : Θ → ℝ, M.sys.InS z → (∀ θ, 0 < z θ) →
          0 ≤ M.sys.W lam tau z - M.sys.W lam tau sstar ∧
          (M.sys.W lam tau z - M.sys.W lam tau sstar = 0 ↔ z = sstar) := by
        intro z _ hz
        have h := L2 z hz
        have hnn : 0 ≤ ∑ θ, tau * M.sys.ν θ * (Real.sqrt (z θ) - Real.sqrt (sstar θ)) ^ 2 :=
          Finset.sum_nonneg (fun θ _ => mul_nonneg (mul_pos htau (hν θ)).le (sq_nonneg _))
        exact ⟨le_trans hnn h, ⟨fun h0 => hsq0 z hz h0.le, fun h0 => by rw [h0]; ring⟩⟩
      set E : ℝ → ℝ := fun t => M.sys.W lam tau (s t) - M.sys.W lam tau sstar with hEdef
      have hEd : ∀ t, 0 ≤ t → HasDerivWithinAt E
          (-∑ θ, (drift M.sys lam tau (s t) θ) ^ 2 / s t θ) (Set.Ici 0) t :=
        fun t ht => (L5 t ht).sub_const _
      have hEnn : ∀ t, 0 ≤ t → 0 ≤ E t := fun t ht => (part4 (s t) (hs.1 t ht) (part1 t ht)).1
      have hP : ∀ t, 0 ≤ t → 0 ≤ ∑ θ, (drift M.sys lam tau (s t) θ) ^ 2 / s t θ :=
        fun t ht => Finset.sum_nonneg (fun θ _ => div_nonneg (sq_nonneg _) (part1 t ht θ).le)
      have hEanti : ∀ t₁ t₂, 0 ≤ t₁ → t₁ ≤ t₂ → E t₂ ≤ E t₁ := by
        intro t₁ t₂ h1 h12
        have := mono (fun t => -E t) (fun t => ∑ θ, (drift M.sys lam tau (s t) θ) ^ 2 / s t θ)
          (fun t ht => (hEd t ht).neg.congr_deriv (neg_neg _)) hP
          (Set.mem_Ici.mpr h1) (Set.mem_Ici.mpr (h1.trans h12)) h12
        simp only at this; linarith
      set B : ℝ := ∑ θ, M.sys.ρ θ * ((Real.log (δ θ) - Real.log (sstar θ)) ^ 2
          + (Real.log (M.sys.ρ θ) - Real.log (sstar θ)) ^ 2) + 1 with hB
      have hB0 : 0 < B := by
        have : 0 ≤ ∑ θ, M.sys.ρ θ * ((Real.log (δ θ) - Real.log (sstar θ)) ^ 2
          + (Real.log (M.sys.ρ θ) - Real.log (sstar θ)) ^ 2) :=
          Finset.sum_nonneg (fun θ _ => mul_nonneg (hρ θ).le (by positivity))
        linarith
      have hsl : ∀ t, 0 ≤ t → ∑ θ, s t θ * (Real.log (s t θ) - Real.log (sstar θ)) ^ 2 ≤ B := by
        intro t ht
        have : ∑ θ, s t θ * (Real.log (s t θ) - Real.log (sstar θ)) ^ 2 ≤
            ∑ θ, M.sys.ρ θ * ((Real.log (δ θ) - Real.log (sstar θ)) ^ 2
              + (Real.log (M.sys.ρ θ) - Real.log (sstar θ)) ^ 2) := by
          apply Finset.sum_le_sum; intro θ _
          have h1 : Real.log (δ θ) ≤ Real.log (s t θ) := Real.log_le_log (hδpos θ) (hδ θ t ht)
          have h2 : Real.log (s t θ) ≤ Real.log (M.sys.ρ θ) :=
            Real.log_le_log (part1 t ht θ) ((hs.1 t ht) θ).2
          have hsq : (Real.log (s t θ) - Real.log (sstar θ)) ^ 2 ≤
              (Real.log (δ θ) - Real.log (sstar θ)) ^ 2
                + (Real.log (M.sys.ρ θ) - Real.log (sstar θ)) ^ 2 := by
            rcases le_total 0 (Real.log (s t θ) - Real.log (sstar θ)) with h | h
            · nlinarith [sq_nonneg (Real.log (δ θ) - Real.log (sstar θ))]
            · nlinarith [sq_nonneg (Real.log (M.sys.ρ θ) - Real.log (sstar θ))]
          exact mul_le_mul ((hs.1 t ht) θ).2 hsq (sq_nonneg _) (hρ θ).le
        linarith
      have hkey : ∀ t, 0 ≤ t → ∀ k : ℝ, 0 < k →
          E t ≤ (∑ θ, (drift M.sys lam tau (s t) θ) ^ 2 / s t θ) / (4 * k) + k * B := by
        intro t ht k hk
        have h3 := L3 (s t) (part1 t ht)
        have h4 : ∑ θ, (-drift M.sys lam tau (s t) θ) * (Real.log (s t θ) - Real.log (sstar θ)) ≤
            ∑ θ, ((drift M.sys lam tau (s t) θ) ^ 2 / s t θ / (4 * k)
              + k * (s t θ * (Real.log (s t θ) - Real.log (sstar θ)) ^ 2)) := by
          apply Finset.sum_le_sum; intro θ _
          have hsθ := part1 t ht θ
          set d := drift M.sys lam tau (s t) θ
          set l := Real.log (s t θ) - Real.log (sstar θ)
          have e : d ^ 2 / s t θ / (4 * k) + k * (s t θ * l ^ 2) - (-d * l)
              = (d + 2 * k * s t θ * l) ^ 2 / (4 * k * s t θ) := by field_simp; ring
          have : 0 ≤ (d + 2 * k * s t θ * l) ^ 2 / (4 * k * s t θ) := by positivity
          linarith
        rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum] at h4
        have h5 := mul_le_mul_of_nonneg_left (hsl t ht) hk.le
        show M.sys.W lam tau (s t) - M.sys.W lam tau sstar ≤ _
        linarith
      have hElim : Tendsto E atTop (𝓝 0) := by
        rw [Metric.tendsto_atTop]
        intro η hη
        have hex : ∃ T, 0 ≤ T ∧ E T < η := by
          by_contra hcon
          push Not at hcon
          have hPl : ∀ t, 0 ≤ t → η ^ 2 / B ≤ ∑ θ, (drift M.sys lam tau (s t) θ) ^ 2 / s t θ := by
            intro t ht
            have h1 := hkey t ht (η / (2 * B)) (by positivity)
            have h2 := hcon t ht
            set P := ∑ θ, (drift M.sys lam tau (s t) θ) ^ 2 / s t θ
            have e : P / (4 * (η / (2 * B))) + η / (2 * B) * B = P * B / (2 * η) + η / 2 := by
              field_simp; ring
            rw [e] at h1
            rw [div_le_iff₀ hB0]
            have : η / 2 ≤ P * B / (2 * η) := by linarith
            rw [le_div_iff₀ (by positivity)] at this
            nlinarith
          have hmon := mono (fun t => -(E t + η ^ 2 / B * t))
            (fun t => ∑ θ, (drift M.sys lam tau (s t) θ) ^ 2 / s t θ - η ^ 2 / B)
            (fun t ht => ?_) (fun t ht => by linarith [hPl t ht])
          · set T := B * E 0 / η ^ 2 + 1 with hT
            have hT0 : 0 ≤ T := by have := hEnn 0 le_rfl; positivity
            have h1 := hmon (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hT0) hT0
            simp only [mul_zero, add_zero] at h1
            have h2 := hcon T hT0
            have e : η ^ 2 / B * T = E 0 + η ^ 2 / B := by rw [hT]; field_simp
            have : 0 < η ^ 2 / B := by positivity
            linarith
          · have := ((hEd t ht).add ((hasDerivAt_id t).const_mul (η ^ 2 / B)).hasDerivWithinAt).neg
            exact this.congr_deriv (by simp; ring)
        obtain ⟨T, hT0, hT⟩ := hex
        refine ⟨T, fun t ht => ?_⟩
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (hEnn t (hT0.trans ht))]
        exact lt_of_le_of_lt (hEanti T t hT0 ht) hT
      have part5 : Tendsto (fun t θ => Real.log (s t θ)) atTop (𝓝 (fun θ => Real.log (sstar θ))) := by
        rw [tendsto_pi_nhds]; intro θ
        have hτ := mul_pos htau (hν θ)
        have hg : Tendsto (fun t => (Real.sqrt (s t θ) - Real.sqrt (sstar θ)) ^ 2) atTop (𝓝 0) := by
          have hup : Tendsto (fun t => E t / (tau * M.sys.ν θ)) atTop (𝓝 0) := by
            simpa using hElim.div_const (tau * M.sys.ν θ)
          apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
          · exact Eventually.of_forall (fun t => sq_nonneg _)
          · filter_upwards [eventually_ge_atTop 0] with t ht
            rw [le_div_iff₀ hτ]
            have h1 := L2 (s t) (part1 t ht)
            have h2 : tau * M.sys.ν θ * (Real.sqrt (s t θ) - Real.sqrt (sstar θ)) ^ 2 ≤
                ∑ θ', tau * M.sys.ν θ' * (Real.sqrt (s t θ') - Real.sqrt (sstar θ')) ^ 2 :=
              Finset.single_le_sum
                (f := fun θ' => tau * M.sys.ν θ' * (Real.sqrt (s t θ') - Real.sqrt (sstar θ')) ^ 2)
                (fun θ' _ => mul_nonneg (mul_pos htau (hν θ')).le (sq_nonneg _)) (Finset.mem_univ θ)
            show _ ≤ M.sys.W lam tau (s t) - M.sys.W lam tau sstar
            linarith
        have habs : Tendsto (fun t => |Real.sqrt (s t θ) - Real.sqrt (sstar θ)|) atTop (𝓝 0) := by
          have := (Real.continuous_sqrt.tendsto 0).comp hg
          simp only [Real.sqrt_zero] at this
          refine this.congr (fun t => ?_)
          simp [Function.comp, Real.sqrt_sq_eq_abs]
        have hsq : Tendsto (fun t => Real.sqrt (s t θ)) atTop (𝓝 (Real.sqrt (sstar θ))) := by
          have := (tendsto_zero_iff_abs_tendsto_zero _).mpr habs
          simpa using this.add_const (Real.sqrt (sstar θ))
        have hs2 : Tendsto (fun t => s t θ) atTop (𝓝 (sstar θ)) := by
          have := hsq.pow 2
          rw [Real.sq_sqrt (hsp θ).le] at this
          refine this.congr' ?_
          filter_upwards [eventually_ge_atTop 0] with t ht
          exact Real.sq_sqrt (part1 t ht θ).le
        exact ((Real.continuousAt_log (hsp θ).ne').tendsto).comp hs2
      exact ⟨part1, fun y _ => part2 y, part3, part4, part5⟩
