-- Prove2me | solution 1 for StochSQP.Vanishing.Supplement.lemma_18
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:10:32.561036+00:00
-- url     : https://prove2.me/submissions/050a10a8-2760-403d-acf4-90a4873c0aa1

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Supplement_Geometry
import Definitions.Def_StochSQP_Vanishing_Supplement_Deterministic

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
    (hdet : Deterministic P A R) : ∀ k : ℕ,
    merit P (R.x k) (R.τ k) - merit P (R.x k + R.α k • R.d k) (R.τ k) ≥
      A.η * R.α k * deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) := by
        have key : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (φ : E n → F)
            (D : E n → (E n →L[ℝ] F)) (x w : E n) (K : ℝ),
            (∀ t ∈ Set.Icc (0:ℝ) 1, HasFDerivAt φ (D (x + t • w)) (x + t • w)) →
            (∀ t ∈ Set.Icc (0:ℝ) 1, ‖D (x + t • w) w - D x w‖ ≤ K * t * ‖w‖ ^ 2) →
            ‖φ (x + w) - φ x - D x w‖ ≤ K / 2 * ‖w‖ ^ 2 := by
          intro F _ _ φ D x w K hD hb
          set ψ : ℝ → F := fun t => φ (x + t • w) - φ x - t • D x w with hψ
          have hderiv : ∀ t ∈ Set.Icc (0:ℝ) 1,
              HasDerivAt ψ (D (x + t • w) w - D x w) t := by
            intro t ht
            have h1 : HasDerivAt (fun s : ℝ => x + s • w) w t := by
              simpa using ((hasDerivAt_id t).smul_const w).const_add x
            have h2 := (hD t ht).comp_hasDerivAt t h1
            have h3 : HasDerivAt (fun s : ℝ => s • D x w) (D x w) t := by
              simpa using (hasDerivAt_id t).smul_const (D x w)
            exact (h2.sub_const (φ x)).sub h3
          have hcont : ContinuousOn ψ (Set.Icc 0 1) := fun t ht =>
            (hderiv t ht).continuousAt.continuousWithinAt
          have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := ψ) (a := 0) (b := 1)
            (f' := fun t => D (x + t • w) w - D x w) hcont
            (fun t ht => (hderiv t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
            (B := fun t => K / 2 * t ^ 2 * ‖w‖ ^ 2) (B' := fun t => K * t * ‖w‖ ^ 2)
            (by simp [hψ])
            (fun t => by
              have := ((hasDerivAt_pow 2 t).const_mul (K / 2)).mul_const (‖w‖ ^ 2)
              refine this.congr_deriv ?_
              simp only [Nat.cast_ofNat, pow_one, Nat.add_one_sub_one]; ring)
            (fun t ht => hb t (Set.Ico_subset_Icc_self ht))
            (show (1:ℝ) ∈ Set.Icc 0 1 by simp)
          simpa [hψ] using this
        obtain ⟨hL, hΓ, hτ₀, hχ₀, hζ₀, hξ₀, hω, hεv, hεv1, hσ, hσ1, hετ, hετ1, hεχ, hεζ, hεζ1,
          hεξ, hεξ1, hη, hη1, hθ⟩ := hA
        obtain ⟨hXo, hXc, -, hfC, hcC, -, -, hgL, -, -, hJL, -⟩ := hP
        obtain ⟨-, hζH, hHk⟩ := hH
        obtain ⟨hg, β, ⟨hβ0, hβ1, hc0, hc1⟩, hβ⟩ := hdet
        have hΔc : ∀ k, 0 ≤ ‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖ := by
          intro k
          obtain ⟨-, -, -, -, hcau, -, hJu, hd, -⟩ := hrun k
          have h0 := hcau 0 ⟨le_rfl, hω.le⟩
          rw [hd, map_add, hJu, add_zero]
          simp at h0
          linarith
        have huHu : ∀ k, 0 ≤ ⟪R.u k, R.H k (R.u k)⟫_ℝ := by
          intro k
          obtain ⟨-, -, -, -, -, -, hJu, -⟩ := hrun k
          obtain ⟨-, -, hker⟩ := hHk k
          have hmem : R.u k ∈ LinearMap.ker (P.J (R.x k) : E n →ₗ[ℝ] E m) := by
            rw [LinearMap.mem_ker]; exact hJu
          exact le_trans (mul_nonneg hζH.le (sq_nonneg _)) (hker _ hmem)
        have hτstep : ∀ k, 0 ≤ prev R.τ A.τ₀ k → 0 ≤ R.τ k ∧ R.τ k ≤ prev R.τ A.τ₀ k := by
          intro k hp
          obtain ⟨-, -, -, -, -, -, -, -, hd0, hdn, -⟩ := hrun k
          by_cases hdk : R.d k = 0
          · rw [(hd0 hdk).1]; exact ⟨hp, le_rfl⟩
          · obtain ⟨⟨hτa, hτb⟩, -⟩ := hdn hdk
            by_cases hs : ⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ ≤ 0
            · rw [hτa hs]; exact ⟨hp, le_rfl⟩
            · push_neg at hs
              obtain ⟨hτ1, hτ2⟩ := hτb hs
              have ht : 0 ≤ (1 - A.σ) * (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖) /
                  (⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ) :=
                div_nonneg (mul_nonneg (by linarith) (hΔc k)) hs.le
              by_cases hpt : prev R.τ A.τ₀ k ≤ (1 - A.σ) *
                  (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖) /
                  (⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ)
              · rw [hτ1 hpt]; exact ⟨hp, le_rfl⟩
              · push_neg at hpt
                rw [hτ2 hpt]
                exact ⟨le_min (mul_nonneg (by linarith) hp) ht, (min_le_right _ _).trans hpt.le⟩
        have hτb : ∀ k, 0 ≤ R.τ k ∧ R.τ k ≤ A.τ₀ := by
          intro k
          induction k with
          | zero => exact hτstep 0 hτ₀.le
          | succ k ih =>
            have := hτstep (k + 1) ih.1
            exact ⟨this.1, this.2.trans ih.2⟩
        have hΔl : ∀ k, 0 ≤ deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) := by
          intro k
          obtain ⟨-, -, -, -, -, -, -, -, hd0, hdn, -⟩ := hrun k
          have hc := hΔc k
          have hu := huHu k
          have ht0 := (hτb k).1
          unfold deltaL
          by_cases hdk : R.d k = 0
          · simp [hdk]
          obtain ⟨⟨-, hτb'⟩, -⟩ := hdn hdk
          by_cases hs : ⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ ≤ 0
          · nlinarith [mul_nonneg ht0 (by linarith : 0 ≤ -⟪R.g k, R.d k⟫_ℝ)]
          · push_neg at hs
            obtain ⟨hτ1, hτ2⟩ := hτb' hs
            have hle : R.τ k ≤ (1 - A.σ) *
                  (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖) /
                  (⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ) := by
              by_cases hpt : prev R.τ A.τ₀ k ≤ (1 - A.σ) *
                  (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖) /
                  (⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ)
              · rw [hτ1 hpt]; exact hpt
              · push_neg at hpt
                rw [hτ2 hpt]; exact min_le_right _ _
            have := (le_div_iff₀ hs).1 hle
            nlinarith [mul_nonneg ht0 hu, mul_nonneg hσ.le hc]
        have hξstep : ∀ k, 0 ≤ prev R.ξ A.ξ₀ k → 0 ≤ R.ξ k ∧ R.ξ k ≤ prev R.ξ A.ξ₀ k ∧
            (R.d k ≠ 0 → R.ξ k ≤ xiTrial P R k) := by
          intro k hp
          obtain ⟨-, -, -, -, -, -, -, -, hd0, hdn, -⟩ := hrun k
          have htr : 0 ≤ xiTrial P R k := by
            unfold xiTrial
            split_ifs
            · exact div_nonneg (hΔl k) (mul_nonneg (hτb k).1 (sq_nonneg _))
            · exact div_nonneg (hΔl k) (sq_nonneg _)
          by_cases hdk : R.d k = 0
          · rw [(hd0 hdk).2.2.2.1]; exact ⟨hp, le_rfl, fun h => absurd hdk h⟩
          · obtain ⟨-, -, ⟨hξ1, hξ2⟩, -⟩ := hdn hdk
            by_cases hpt : prev R.ξ A.ξ₀ k ≤ xiTrial P R k
            · rw [hξ1 hpt]; exact ⟨hp, le_rfl, fun _ => hpt⟩
            · push_neg at hpt
              rw [hξ2 hpt]
              exact ⟨le_min (mul_nonneg (by linarith) hp) htr, (min_le_right _ _).trans hpt.le,
                fun _ => min_le_right _ _⟩
        have hξb : ∀ k, 0 ≤ R.ξ k ∧ R.ξ k ≤ A.ξ₀ := by
          intro k
          induction k with
          | zero => exact ⟨(hξstep 0 hξ₀.le).1, (hξstep 0 hξ₀.le).2.1⟩
          | succ k ih =>
            have := hξstep (k + 1) ih.1
            exact ⟨this.1, this.2.1.trans ih.2⟩
        have hprevξ : ∀ k, 0 ≤ prev R.ξ A.ξ₀ k := by
          intro k
          cases k with
          | zero => exact hξ₀.le
          | succ k => exact (hξb k).1
        have hfd : ∀ y ∈ X, DifferentiableAt ℝ P.f y := fun y hy =>
          (hfC.differentiableOn one_ne_zero).differentiableAt (hXo.mem_nhds hy)
        have hcd : ∀ y ∈ X, DifferentiableAt ℝ P.c y := fun y hy =>
          (hcC.differentiableOn one_ne_zero).differentiableAt (hXo.mem_nhds hy)
        -- main
        intro k
        obtain ⟨-, -, -, -, -, -, -, -, hd0, hdn, hxk⟩ := hrun k
        by_cases hdk : R.d k = 0
        · simp [hdk, deltaL]
        obtain ⟨-, -, hξr, hαr⟩ := hdn hdk
        have hτ := hτb k
        have hξ := hξb k
        have hξt : R.ξ k ≤ xiTrial P R k := (hξstep k (hprevξ k)).2.2 hdk
        have hΔ := hΔl k
        have hd2 : 0 < ‖R.d k‖ ^ 2 := pow_pos (norm_pos_iff.2 hdk) 2
        have hden : 0 < R.τ k * A.L + A.Γ := add_pos_of_nonneg_of_pos (mul_nonneg hτ.1 hL.le) hΓ
        have hD : 0 < (R.τ k * A.L + A.Γ) * ‖R.d k‖ ^ 2 := mul_pos hden hd2
        have hc2 : 0 ≤ 2 * (1 - A.η) * β := mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hβ0.le
        have hβΔ : 2 * (1 - A.η) * β * deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) ≤
            2 * (1 - A.η) * deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) := by
          nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hη1.le) hΔ) (sub_nonneg.2 hβ1)]
        have hlo0 : 0 ≤ projLo A R k := by
          unfold projLo; rw [hβ k]
          split_ifs
          · exact div_nonneg (mul_nonneg (mul_nonneg hc2 hξ.1) hτ.1) hden.le
          · exact div_nonneg (mul_nonneg hc2 hξ.1) hden.le
        have hcnn : 0 ≤ 2 * (1 - A.η) * β * A.ξ₀ * max A.τ₀ 1 :=
          mul_nonneg (mul_nonneg hc2 hξ₀.le) (le_max_of_le_right zero_le_one)
        have hlo1 : projLo A R k ≤ 1 := by
          unfold projLo; rw [hβ k]
          have hΓle : A.Γ ≤ R.τ k * A.L + A.Γ := by nlinarith [mul_nonneg hτ.1 hL.le]
          split_ifs
          · refine le_trans (div_le_div₀ hcnn ?_ hΓ hΓle) hc1
            exact mul_le_mul (mul_le_mul_of_nonneg_left hξ.2 hc2) (hτ.2.trans (le_max_left _ _))
              hτ.1 (mul_nonneg hc2 hξ₀.le)
          · refine le_trans (div_le_div₀ hcnn ?_ hΓ hΓle) hc1
            have := mul_le_mul (mul_le_mul_of_nonneg_left hξ.2 hc2) (le_max_right A.τ₀ 1)
              zero_le_one (mul_nonneg hc2 hξ₀.le)
            linarith
        have hloD : projLo A R k * ((R.τ k * A.L + A.Γ) * ‖R.d k‖ ^ 2) ≤
            2 * (1 - A.η) * deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) := by
          unfold projLo xiTrial at *
          rw [hβ k]
          split_ifs at hξt ⊢ with hT
          · have e : 2 * (1 - A.η) * β * R.ξ k * R.τ k / (R.τ k * A.L + A.Γ) *
                ((R.τ k * A.L + A.Γ) * ‖R.d k‖ ^ 2) =
                2 * (1 - A.η) * β * (R.ξ k * (R.τ k * ‖R.d k‖ ^ 2)) := by
              field_simp
            have hX : R.ξ k * (R.τ k * ‖R.d k‖ ^ 2) ≤ deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) := by
              rcases hτ.1.eq_or_lt with h | h
              · have h0 : R.ξ k * (R.τ k * ‖R.d k‖ ^ 2) = 0 := by rw [← h]; ring
                linarith
              · exact (le_div_iff₀ (mul_pos h hd2)).1 hξt
            rw [e]
            exact le_trans (mul_le_mul_of_nonneg_left hX hc2) hβΔ
          · have e : 2 * (1 - A.η) * β * R.ξ k / (R.τ k * A.L + A.Γ) *
                ((R.τ k * A.L + A.Γ) * ‖R.d k‖ ^ 2) =
                2 * (1 - A.η) * β * (R.ξ k * ‖R.d k‖ ^ 2) := by
              field_simp
            have hX : R.ξ k * ‖R.d k‖ ^ 2 ≤ deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) :=
              (le_div_iff₀ hd2).1 hξt
            rw [e]
            exact le_trans (mul_le_mul_of_nonneg_left hX hc2) hβΔ
        have haS1 : alphaSuff P A R k ≤ 1 := min_le_right _ _
        have haSD : alphaSuff P A R k * ((R.τ k * A.L + A.Γ) * ‖R.d k‖ ^ 2) ≤
            2 * (1 - A.η) * deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) := by
          have h1 : alphaSuff P A R k ≤ 2 * (1 - A.η) * β * deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) /
              ((R.τ k * A.L + A.Γ) * ‖R.d k‖ ^ 2) := by
            unfold alphaSuff; rw [hβ k]; exact min_le_left _ _
          have h2 := mul_le_mul_of_nonneg_right h1 hD.le
          rw [div_mul_cancel₀ _ hD.ne'] at h2
          exact h2.trans hβΔ
        have hαeq : R.α k = max (projLo A R k) (min (alphaSuff P A R k) (projHi A R k)) := hαr
        have hα0 : 0 ≤ R.α k := by rw [hαeq]; exact le_trans hlo0 (le_max_left _ _)
        have hαle : R.α k ≤ max (projLo A R k) (alphaSuff P A R k) := by
          rw [hαeq]; exact max_le_max le_rfl (min_le_left _ _)
        have hα1 : R.α k ≤ 1 := hαle.trans (max_le hlo1 haS1)
        have hαD : R.α k * ((R.τ k * A.L + A.Γ) * ‖R.d k‖ ^ 2) ≤
            2 * (1 - A.η) * deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) := by
          refine le_trans (mul_le_mul_of_nonneg_right hαle hD.le) ?_
          rw [max_mul_of_nonneg _ _ hD.le]
          exact max_le hloD haSD
        -- analytic part
        set x := R.x k with hxdef
        set d := R.d k with hddef
        set α := R.α k with hαdef
        have hxX : x ∈ X := hx k
        have hx'X : x + α • d ∈ X := hxk ▸ hx (k + 1)
        have hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • (α • d) ∈ X := fun t ht =>
          hXc.add_smul_mem hxX hx'X ht
        have hw : ‖α • d‖ ^ 2 = α ^ 2 * ‖d‖ ^ 2 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hα0]; ring
        have hF := key ℝ P.f (fun y => InnerProductSpace.toDual ℝ (E n) (P.grad y)) x (α • d) A.L
          (fun t ht => hasGradientAt_iff_hasFDerivAt.1 ((hfd _ (hseg t ht)).hasGradientAt))
          (fun t ht => by
            simp only [InnerProductSpace.toDual_apply_apply]
            rw [← inner_sub_left, Real.norm_eq_abs]
            refine le_trans (abs_real_inner_le_norm _ _) ?_
            have := hgL _ (hseg t ht) _ hxX
            rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at this
            exact le_trans (mul_le_mul_of_nonneg_right this (norm_nonneg _)) (le_of_eq (by ring)))
        have hC := key (E m) P.c P.J x (α • d) A.Γ
          (fun t ht => (hcd _ (hseg t ht)).hasFDerivAt)
          (fun t ht => by
            rw [← ContinuousLinearMap.sub_apply]
            refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
            have := hJL _ (hseg t ht) _ hxX
            rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at this
            exact le_trans (mul_le_mul_of_nonneg_right this (norm_nonneg _)) (le_of_eq (by ring)))
        simp only [InnerProductSpace.toDual_apply_apply, real_inner_smul_right, hw] at hF
        rw [hw] at hC
        have hF' : P.f (x + α • d) ≤ P.f x + α * ⟪R.g k, d⟫_ℝ + A.L / 2 * (α ^ 2 * ‖d‖ ^ 2) := by
          rw [hg k]
          have := le_abs_self (P.f (x + α • d) - P.f x - α * ⟪P.grad x, d⟫_ℝ)
          rw [Real.norm_eq_abs] at hF
          linarith
        have hC' : ‖P.c (x + α • d)‖ ≤ ‖P.c x + P.J x (α • d)‖ + A.Γ / 2 * (α ^ 2 * ‖d‖ ^ 2) := by
          have := norm_add_le (P.c x + P.J x (α • d)) (P.c (x + α • d) - P.c x - P.J x (α • d))
          have e : P.c x + P.J x (α • d) + (P.c (x + α • d) - P.c x - P.J x (α • d)) =
            P.c (x + α • d) := by abel
          rw [e] at this
          linarith
        have hconv : ‖P.c x + P.J x (α • d)‖ ≤ (1 - α) * ‖P.c x‖ + α * ‖P.c x + P.J x d‖ := by
          have e : P.c x + P.J x (α • d) = (1 - α) • P.c x + α • (P.c x + P.J x d) := by
            rw [map_smul, smul_add, sub_smul, one_smul]; abel
          rw [e]
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hα0,
            abs_of_nonneg (by linarith)]
        have hτF := mul_le_mul_of_nonneg_left hF' hτ.1
        have hαA := mul_le_mul_of_nonneg_left hαD hα0
        unfold merit
        unfold deltaL at hαA ⊢
        linear_combination hτF + hC' + hconv + (1/2 : ℝ) * hαA
