-- Prove2me | solution 1 for StochSQP.Vanishing.Supplement.lemma_19
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:10:56.360684+00:00
-- url     : https://prove2.me/submissions/fbe890f7-9666-4a86-8a92-19f0cfdd36cd

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Supplement_Geometry
import Definitions.Def_StochSQP_Vanishing_Supplement_Deterministic
import Definitions.Def_StochSQP_Vanishing_Supplement_ShiftedMerit

open StochSQP
open StochSQP.Vanishing
open StochSQP.Vanishing.Supplement

open Filter
open scoped InnerProductSpace RealInnerProductSpace Topology

theorem solution
    {n m : ℕ} (P : Problem n m) (A : Params) (R : Run n m)
    (X : Set (E n)) (κH ζH : ℝ)
    (hA : A.Valid) (hP : Assumption1 P A.L A.Γ X)
    (hx : ∀ k, R.x k ∈ X) (hH : Assumption3 P R κH ζH)
    (hrun : IsRun P A R)
    (hdet : Deterministic P A R) (fInf : ℝ) (hf : ∀ k, fInf ≤ P.f (R.x k)) : ∀ k : ℕ,
    shiftedMerit P fInf (R.x k) (R.τ k) - shiftedMerit P fInf (R.x (k+1)) (R.τ (k+1)) ≥
      A.η * R.α k * deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) := by
        obtain ⟨hXo, hXc, -, hfC, hcC, -, -, hLf, -, -, hLJ, -⟩ := hP
        obtain ⟨hL, hΓ, hτ₀, hχ₀, hζ₀, hξ₀, hω, hεv, hεv1, hσ, hσ1, hετ, hετ1, hεχ, hεζ, hεζ1,
          hεξ, hεξ1, hη, hη1, hθ⟩ := hA
        obtain ⟨hg, β, ⟨hb0, hb1, -, hcond⟩, hβ⟩ := hdet
        have segX : ∀ x ∈ X, ∀ D, x + D ∈ X → ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • D ∈ X :=
          fun x hx D hxD t ht => hXc.add_smul_mem hx hxD ht
        have hfd : ∀ z ∈ X, HasFDerivAt P.f (InnerProductSpace.toDual ℝ (E n) (P.grad z)) z := by
          intro z hz
          have : DifferentiableAt ℝ P.f z :=
            ((hfC.differentiableOn (by norm_num)) z hz).differentiableAt (hXo.mem_nhds hz)
          exact this.hasGradientAt.hasFDerivAt
        have hcd : ∀ z ∈ X, HasFDerivAt P.c (P.J z) z := by
          intro z hz
          have : DifferentiableAt ℝ P.c z :=
            ((hcC.differentiableOn (by norm_num)) z hz).differentiableAt (hXo.mem_nhds hz)
          exact this.hasFDerivAt
        have hline : ∀ (x D : E n) (t : ℝ), HasDerivAt (fun s : ℝ => x + s • D) D t := by
          intro x D t
          simpa using ((hasDerivAt_id t).smul_const D).const_add x
        have hBd : ∀ (K : ℝ) (D : E n) (t : ℝ),
            HasDerivAt (fun s : ℝ => K / 2 * s ^ 2 * ‖D‖ ^ 2) (K * t * ‖D‖ ^ 2) t := by
          intro K D t
          have := ((hasDerivAt_pow 2 t).const_mul (K / 2)).mul_const (‖D‖ ^ 2)
          exact this.congr_deriv (by push_cast; ring)
        have taylor_f : ∀ x ∈ X, ∀ D, x + D ∈ X →
            P.f (x + D) ≤ P.f x + ⟪P.grad x, D⟫_ℝ + A.L / 2 * ‖D‖ ^ 2 := by
          intro x hx D hxD
          have hg' : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt
              (fun t : ℝ => P.f (x + t • D) - P.f x - t * ⟪P.grad x, D⟫_ℝ)
              (⟪P.grad (x + t • D), D⟫_ℝ - ⟪P.grad x, D⟫_ℝ) t := by
            intro t ht
            have h1 := (hfd _ (segX x hx D hxD t ht)).comp_hasDerivAt t (hline x D t)
            have h2 := (h1.sub_const (P.f x)).sub ((hasDerivAt_id t).mul_const ⟪P.grad x, D⟫_ℝ)
            exact h2.congr_deriv (by simp)
          have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
            (f := fun t : ℝ => P.f (x + t • D) - P.f x - t * ⟪P.grad x, D⟫_ℝ) (a := 0) (b := 1)
            (f' := fun t => ⟪P.grad (x + t • D), D⟫_ℝ - ⟪P.grad x, D⟫_ℝ)
            (B := fun s : ℝ => A.L / 2 * s ^ 2 * ‖D‖ ^ 2) (B' := fun t => A.L * t * ‖D‖ ^ 2)
            (fun t ht => (hg' t ht).continuousAt.continuousWithinAt)
            (fun t ht => (hg' t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
            (by simp) (fun t => hBd A.L D t)
            (by
              intro t ht
              have ht0 : 0 ≤ t := ht.1
              have hmem := segX x hx D hxD t (Set.Ico_subset_Icc_self ht)
              rw [← inner_sub_left, Real.norm_eq_abs]
              calc |⟪P.grad (x + t • D) - P.grad x, D⟫_ℝ|
                  ≤ ‖P.grad (x + t • D) - P.grad x‖ * ‖D‖ := abs_real_inner_le_norm _ _
                _ ≤ (A.L * ‖x + t • D - x‖) * ‖D‖ :=
                    mul_le_mul_of_nonneg_right (hLf _ hmem _ hx) (norm_nonneg _)
                _ = A.L * t * ‖D‖ ^ 2 := by
                    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]; ring)
            (x := 1) (by simp)
          simp only [one_smul, one_mul, one_pow, Real.norm_eq_abs] at key
          have := le_abs_self (P.f (x + D) - P.f x - ⟪P.grad x, D⟫_ℝ)
          linarith
        have taylor_c : ∀ x ∈ X, ∀ D, x + D ∈ X →
            ‖P.c (x + D) - P.c x - P.J x D‖ ≤ A.Γ / 2 * ‖D‖ ^ 2 := by
          intro x hx D hxD
          have hg' : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt
              (fun t : ℝ => P.c (x + t • D) - P.c x - t • P.J x D)
              (P.J (x + t • D) D - P.J x D) t := by
            intro t ht
            have h1 := (hcd _ (segX x hx D hxD t ht)).comp_hasDerivAt t (hline x D t)
            have h2 := (h1.sub_const (P.c x)).sub ((hasDerivAt_id t).smul_const (P.J x D))
            exact h2.congr_deriv (by simp)
          have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
            (f := fun t : ℝ => P.c (x + t • D) - P.c x - t • P.J x D) (a := 0) (b := 1)
            (f' := fun t => P.J (x + t • D) D - P.J x D)
            (B := fun s : ℝ => A.Γ / 2 * s ^ 2 * ‖D‖ ^ 2) (B' := fun t => A.Γ * t * ‖D‖ ^ 2)
            (fun t ht => (hg' t ht).continuousAt.continuousWithinAt)
            (fun t ht => (hg' t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
            (by simp) (fun t => hBd A.Γ D t)
            (by
              intro t ht
              have ht0 : 0 ≤ t := ht.1
              have hmem := segX x hx D hxD t (Set.Ico_subset_Icc_self ht)
              rw [← ContinuousLinearMap.sub_apply]
              calc ‖(P.J (x + t • D) - P.J x) D‖
                  ≤ ‖P.J (x + t • D) - P.J x‖ * ‖D‖ := ContinuousLinearMap.le_opNorm _ _
                _ ≤ (A.Γ * ‖x + t • D - x‖) * ‖D‖ :=
                    mul_le_mul_of_nonneg_right (hLJ _ hmem _ hx) (norm_nonneg _)
                _ = A.Γ * t * ‖D‖ ^ 2 := by
                    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]; ring)
            (x := 1) (by simp)
          simpa using key
        have h1η : 0 < 1 - A.η := by linarith
        -- numerator of the trial value is nonnegative
        have hnum : ∀ k, 0 ≤ ‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖ := by
          intro k
          obtain ⟨-, -, -, -, hcau, -, hJu, hd, -, -, -⟩ := hrun k
          have h0 := hcau 0 ⟨le_refl _, hω.le⟩
          simp only [zero_smul, add_zero, sub_self, mul_zero] at h0
          rw [hd, map_add, hJu, add_zero]
          exact h0
        have huHu : ∀ k, 0 ≤ ⟪R.u k, R.H k (R.u k)⟫_ℝ := by
          intro k
          obtain ⟨-, -, -, -, -, -, hJu, -, -, -, -⟩ := hrun k
          have := (hH.2.2 k).2.2 (R.u k) (by simpa [LinearMap.mem_ker] using hJu)
          have : 0 ≤ ζH * ‖R.u k‖ ^ 2 := mul_nonneg hH.2.1.le (sq_nonneg _)
          linarith
        have hτle : ∀ k, R.τ k ≤ prev R.τ A.τ₀ k := by
          intro k
          obtain ⟨-, -, -, -, -, -, -, -, hd0, hdne, -⟩ := hrun k
          by_cases hdk : R.d k = 0
          · exact (hd0 hdk).1.le
          · obtain ⟨⟨ht1, ht2⟩, -⟩ := hdne hdk
            rcases le_or_gt (⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ) 0 with hden | hden
            · exact (ht1 hden).le
            · obtain ⟨ha, hb⟩ := ht2 hden
              rcases le_or_gt (prev R.τ A.τ₀ k) ((1 - A.σ) * (‖P.c (R.x k)‖ -
                  ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖) /
                  (⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ)) with hc | hc
              · exact (ha hc).le
              · rw [hb hc]; exact (min_le_right _ _).trans hc.le
        have hτnn : ∀ k, 0 ≤ prev R.τ A.τ₀ k → 0 ≤ R.τ k := by
          intro k hp
          obtain ⟨-, -, -, -, -, -, -, -, hd0, hdne, -⟩ := hrun k
          by_cases hdk : R.d k = 0
          · rw [(hd0 hdk).1]; exact hp
          · obtain ⟨⟨ht1, ht2⟩, -⟩ := hdne hdk
            rcases le_or_gt (⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ) 0 with hden | hden
            · rw [ht1 hden]; exact hp
            · obtain ⟨ha, hb⟩ := ht2 hden
              rcases le_or_gt (prev R.τ A.τ₀ k) ((1 - A.σ) * (‖P.c (R.x k)‖ -
                  ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖) /
                  (⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ)) with hc | hc
              · rw [ha hc]; exact hp
              · rw [hb hc]
                exact le_min (mul_nonneg (by linarith) hp)
                  (div_nonneg (mul_nonneg (by linarith) (hnum k)) hden.le)
        have hΔ : ∀ k, 0 ≤ R.τ k → 0 ≤ deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) := by
          intro k hτ
          obtain ⟨-, -, -, -, -, -, -, -, -, hdne, -⟩ := hrun k
          have hn := hnum k
          have hu := huHu k
          unfold deltaL
          by_cases hdk : R.d k = 0
          · simp [hdk]
          · obtain ⟨⟨ht1, ht2⟩, -⟩ := hdne hdk
            rcases le_or_gt (⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ) 0 with hden | hden
            · have : R.τ k * ⟪R.g k, R.d k⟫_ℝ ≤ 0 :=
                mul_nonpos_of_nonneg_of_nonpos hτ (by linarith)
              linarith
            · obtain ⟨ha, hb⟩ := ht2 hden
              have hle : R.τ k ≤ (1 - A.σ) * (‖P.c (R.x k)‖ -
                  ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖) /
                  (⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ) := by
                rcases le_or_gt (prev R.τ A.τ₀ k) ((1 - A.σ) * (‖P.c (R.x k)‖ -
                    ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖) /
                    (⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ)) with hc | hc
                · rw [ha hc]; exact hc
                · rw [hb hc]; exact min_le_right _ _
              rw [le_div_iff₀ hden] at hle
              have : 0 ≤ R.τ k * ⟪R.u k, R.H k (R.u k)⟫_ℝ := mul_nonneg hτ hu
              have : 0 ≤ A.σ * (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖) :=
                mul_nonneg hσ.le hn
              nlinarith
        have hξle : ∀ k, R.ξ k ≤ prev R.ξ A.ξ₀ k := by
          intro k
          obtain ⟨-, -, -, -, -, -, -, -, hd0, hdne, -⟩ := hrun k
          by_cases hdk : R.d k = 0
          · exact (hd0 hdk).2.2.2.1.le
          · obtain ⟨-, -, ⟨hx1, hx2⟩, -⟩ := hdne hdk
            rcases le_or_gt (prev R.ξ A.ξ₀ k) (xiTrial P R k) with hc | hc
            · exact (hx1 hc).le
            · rw [hx2 hc]; exact (min_le_right _ _).trans hc.le
        have hξtr : ∀ k, R.d k ≠ 0 → R.ξ k ≤ xiTrial P R k := by
          intro k hdk
          obtain ⟨-, -, -, -, -, -, -, -, -, hdne, -⟩ := hrun k
          obtain ⟨-, -, ⟨hx1, hx2⟩, -⟩ := hdne hdk
          rcases le_or_gt (prev R.ξ A.ξ₀ k) (xiTrial P R k) with hc | hc
          · rw [hx1 hc]; exact hc
          · rw [hx2 hc]; exact min_le_right _ _
        have hξnn : ∀ k, 0 ≤ R.τ k → 0 ≤ prev R.ξ A.ξ₀ k → 0 ≤ R.ξ k := by
          intro k hτ hp
          obtain ⟨-, -, -, -, -, -, -, -, hd0, hdne, -⟩ := hrun k
          by_cases hdk : R.d k = 0
          · rw [(hd0 hdk).2.2.2.1]; exact hp
          · obtain ⟨-, -, ⟨hx1, hx2⟩, -⟩ := hdne hdk
            have htr : 0 ≤ xiTrial P R k := by
              unfold xiTrial
              split_ifs
              · exact div_nonneg (hΔ k hτ) (mul_nonneg hτ (sq_nonneg _))
              · exact div_nonneg (hΔ k hτ) (sq_nonneg _)
            rcases le_or_gt (prev R.ξ A.ξ₀ k) (xiTrial P R k) with hc | hc
            · rw [hx1 hc]; exact hp
            · rw [hx2 hc]; exact le_min (mul_nonneg (by linarith) hp) htr
        have hbnd : ∀ k, (0 ≤ R.τ k ∧ R.τ k ≤ A.τ₀) ∧ (0 ≤ R.ξ k ∧ R.ξ k ≤ A.ξ₀) := by
          have step : ∀ k, (0 ≤ prev R.τ A.τ₀ k ∧ prev R.τ A.τ₀ k ≤ A.τ₀) →
              (0 ≤ prev R.ξ A.ξ₀ k ∧ prev R.ξ A.ξ₀ k ≤ A.ξ₀) →
              (0 ≤ R.τ k ∧ R.τ k ≤ A.τ₀) ∧ (0 ≤ R.ξ k ∧ R.ξ k ≤ A.ξ₀) := by
            intro k h1 h2
            have a := hτnn k h1.1
            exact ⟨⟨a, (hτle k).trans h1.2⟩, ⟨hξnn k a h2.1, (hξle k).trans h2.2⟩⟩
          intro k
          induction k with
          | zero => exact step 0 ⟨hτ₀.le, le_refl _⟩ ⟨hξ₀.le, le_refl _⟩
          | succ k ih => exact step (k+1) ih.1 ih.2
        intro k
        obtain ⟨⟨hβ0, hβ1⟩, -, -, -, -, -, hJu, hd, hd0, hdne, hxs⟩ := hrun k
        obtain ⟨⟨hτ0, hτ1⟩, ⟨hξ0, hξ1⟩⟩ := hbnd k
        have hτ' : R.τ (k+1) ≤ R.τ k := hτle (k+1)
        have hfk1 := hf (k+1)
        have hΔk := hΔ k hτ0
        by_cases hdk : R.d k = 0
        · obtain ⟨-, -, -, -, hα⟩ := hd0 hdk
          rw [hxs, hdk, smul_zero, add_zero] at *
          unfold shiftedMerit
          have : 0 ≤ (R.τ k - R.τ (k+1)) * (P.f (R.x k) - fInf) :=
            mul_nonneg (by linarith) (by linarith [hf k])
          simp [deltaL]
          nlinarith
        · obtain ⟨-, -, -, hαr⟩ := hdne hdk
          unfold alphaRule at hαr
          have hdpos : 0 < ‖R.d k‖ := norm_pos_iff.mpr hdk
          have hd2 : 0 < ‖R.d k‖ ^ 2 := by positivity
          have hden : 0 < R.τ k * A.L + A.Γ := add_pos_of_nonneg_of_pos (mul_nonneg hτ0 hL.le) hΓ
          have hc0 : 0 ≤ 2 * (1 - A.η) * β := mul_nonneg (mul_nonneg (by norm_num) h1η.le) hb0.le
          have hc : 0 ≤ 2 * (1 - A.η) * β * (R.τ k * A.L + A.Γ) := mul_nonneg hc0 hden.le
          have hlo : projLo A R k ≤ 2 * (1 - A.η) * β * deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) /
              ((R.τ k * A.L + A.Γ) * ‖R.d k‖ ^ 2) := by
            have htr := hξtr k hdk
            unfold projLo; unfold xiTrial at htr; rw [hβ k]
            split_ifs at htr ⊢ with hTD
            · have key : R.ξ k * R.τ k * ‖R.d k‖ ^ 2 ≤ deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) := by
                rcases hτ0.eq_or_lt with h0 | h0
                · have : R.ξ k * R.τ k * ‖R.d k‖ ^ 2 = 0 := by rw [← h0]; ring
                  linarith
                · rw [le_div_iff₀ (by positivity)] at htr
                  linarith [show R.ξ k * R.τ k * ‖R.d k‖ ^ 2 = R.ξ k * (R.τ k * ‖R.d k‖ ^ 2) by ring]
              rw [div_le_div_iff₀ hden (mul_pos hden hd2)]
              nlinarith [mul_le_mul_of_nonneg_left key hc]
            · have key : R.ξ k * ‖R.d k‖ ^ 2 ≤ deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) := by
                rwa [le_div_iff₀ hd2] at htr
              rw [div_le_div_iff₀ hden (mul_pos hden hd2)]
              linear_combination mul_le_mul_of_nonneg_left key hc
          have hαS : R.α k ≤ 2 * (1 - A.η) * β * deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) /
              ((R.τ k * A.L + A.Γ) * ‖R.d k‖ ^ 2) := by
            have hsuff : alphaSuff P A R k ≤ 2 * (1 - A.η) * β *
                deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) / ((R.τ k * A.L + A.Γ) * ‖R.d k‖ ^ 2) := by
              unfold alphaSuff; rw [hβ k]; exact min_le_left _ _
            rw [hαr]
            exact max_le hlo ((min_le_left _ _).trans hsuff)
          have hlo0 : 0 ≤ projLo A R k := by
            unfold projLo; rw [hβ k]
            split_ifs
            · exact div_nonneg (mul_nonneg (mul_nonneg hc0 hξ0) hτ0) hden.le
            · exact div_nonneg (mul_nonneg hc0 hξ0) hden.le
          have hlo1 : projLo A R k ≤ 1 := by
            unfold projLo; rw [hβ k]
            have hM : 1 ≤ max A.τ₀ 1 := le_max_right _ _
            have hdenΓ : A.Γ ≤ R.τ k * A.L + A.Γ := le_add_of_nonneg_left (mul_nonneg hτ0 hL.le)
            have hnn : 0 ≤ 2 * (1 - A.η) * β * A.ξ₀ * max A.τ₀ 1 :=
              mul_nonneg (mul_nonneg hc0 hξ₀.le) (by linarith)
            split_ifs
            · have h1 : R.ξ k * R.τ k ≤ A.ξ₀ * max A.τ₀ 1 :=
                mul_le_mul hξ1 (hτ1.trans (le_max_left _ _)) hτ0 hξ₀.le
              calc 2 * (1 - A.η) * β * R.ξ k * R.τ k / (R.τ k * A.L + A.Γ)
                  ≤ 2 * (1 - A.η) * β * A.ξ₀ * max A.τ₀ 1 / A.Γ :=
                    div_le_div₀ hnn (by linear_combination mul_le_mul_of_nonneg_left h1 hc0) hΓ hdenΓ
                _ ≤ 1 := hcond
            · have h1 : R.ξ k ≤ A.ξ₀ * max A.τ₀ 1 := hξ1.trans (le_mul_of_one_le_right hξ₀.le hM)
              calc 2 * (1 - A.η) * β * R.ξ k / (R.τ k * A.L + A.Γ)
                  ≤ 2 * (1 - A.η) * β * A.ξ₀ * max A.τ₀ 1 / A.Γ :=
                    div_le_div₀ hnn (by linear_combination mul_le_mul_of_nonneg_left h1 hc0) hΓ hdenΓ
                _ ≤ 1 := hcond
          have hα0 : 0 ≤ R.α k := by rw [hαr]; exact hlo0.trans (le_max_left _ _)
          have hα1 : R.α k ≤ 1 := by
            have hs1 : alphaSuff P A R k ≤ 1 := by unfold alphaSuff; exact min_le_right _ _
            rw [hαr]
            exact max_le hlo1 ((min_le_left _ _).trans hs1)
          have hαM : R.α k * ((R.τ k * A.L + A.Γ) * ‖R.d k‖ ^ 2) ≤
              2 * (1 - A.η) * deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) := by
            have := (le_div_iff₀ (mul_pos hden hd2)).mp hαS
            linear_combination this + 2 * mul_le_mul_of_nonneg_left hb1 (mul_nonneg h1η.le hΔk)
          have hxD : R.x k + R.α k • R.d k ∈ X := hxs ▸ hx (k+1)
          have tf := taylor_f (R.x k) (hx k) _ hxD
          have tc := taylor_c (R.x k) (hx k) _ hxD
          rw [← hxs] at tf tc
          rw [map_smul] at tc
          simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα0, mul_pow] at tf tc
          have h3 : ‖P.c (R.x (k+1))‖ ≤ ‖P.c (R.x k) + R.α k • P.J (R.x k) (R.d k)‖ +
              A.Γ / 2 * (R.α k ^ 2 * ‖R.d k‖ ^ 2) := by
            have := norm_sub_norm_le (P.c (R.x (k+1))) (P.c (R.x k) + R.α k • P.J (R.x k) (R.d k))
            rw [← sub_sub] at this
            linarith
          have hconv : ‖P.c (R.x k) + R.α k • P.J (R.x k) (R.d k)‖ ≤
              (1 - R.α k) * ‖P.c (R.x k)‖ + R.α k * ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖ := by
            have he : P.c (R.x k) + R.α k • P.J (R.x k) (R.d k) =
                (1 - R.α k) • P.c (R.x k) + R.α k • (P.c (R.x k) + P.J (R.x k) (R.d k)) := by
              rw [smul_add, sub_smul, one_smul]; abel
            rw [he]
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hα0,
              abs_of_nonneg (by linarith)]
          have h1 : R.τ (k+1) * (P.f (R.x (k+1)) - fInf) ≤ R.τ k * (P.f (R.x (k+1)) - fInf) :=
            mul_le_mul_of_nonneg_right hτ' (sub_nonneg.mpr hfk1)
          have h2 := mul_le_mul_of_nonneg_left tf hτ0
          have h4 := mul_le_mul_of_nonneg_left hαM hα0
          rw [← hg k] at h2
          unfold shiftedMerit
          unfold deltaL at h4 ⊢
          linear_combination h1 + h2 + h3 + hconv + h4 / 2
