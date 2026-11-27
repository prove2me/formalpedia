-- Prove2me | solution 1 for StochSQP.Vanishing.Supplement.lemma_21
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:11:26.768296+00:00
-- url     : https://prove2.me/submissions/584aad96-b418-4237-b1ac-84ba1672a4ea

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
    (hdet : Deterministic P A R) (B : NullBases P R) (hτ : ConstantMerit R) :
    Tendsto (fun k => ‖R.u k‖) atTop (nhds 0) ∧
    Tendsto (fun k => ‖R.d k‖) atTop (nhds 0) ∧
    Tendsto (lagrangianNorm P R) atTop (nhds 0) ∧
    Tendsto (reducedNorm P R B) atTop (nhds 0) := by
      obtain ⟨hL, hΓ, hτ₀, -, -, hξ₀, hω, hεv, -, hσ, hσ1, -, -, -, -, -, hεξ, hεξ1,
        hη, hη1, -⟩ := hA
      obtain ⟨hXo, hXc, -, hf, hc, -, hfb, hgL, -, hcB, hJL, hJB⟩ := hP
      obtain ⟨-, hζH, hH⟩ := hH
      obtain ⟨hg, β, ⟨hβ0, hβ1, -, hc23b⟩, hβ⟩ := hdet
      obtain ⟨K, t, ht, hτK⟩ := hτ
      have iEn : ContinuousSMul ℝ (E n) := inferInstance
      have iEm : ContinuousSMul ℝ (E m) := inferInstance
      have hline : ∀ (x d : E n) (s : ℝ), HasDerivAt (fun s : ℝ => x + s • d) d s := fun x d s => by
        have h := ((hasDerivAt_id s).smul_const d).const_add x
        rw [one_smul] at h; exact h
      have hsq2 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => s^2) (2*s) s := fun s => by
        simpa using hasDerivAt_pow 2 s
      have hfd : ∀ z ∈ X, DifferentiableAt ℝ P.f z := fun z hz =>
        (hf.differentiableOn one_ne_zero).differentiableAt (hXo.mem_nhds hz)
      have hcd : ∀ z ∈ X, DifferentiableAt ℝ P.c z := fun z hz =>
        (hc.differentiableOn one_ne_zero).differentiableAt (hXo.mem_nhds hz)
      have lineF : ∀ x d : E n, ∀ s : ℝ, x + s • d ∈ X →
          HasDerivAt (fun s : ℝ => P.f (x + s • d)) ⟪P.grad (x + s • d), d⟫ s := by
        intro x d s hs
        have hl := hline x d s
        have := ((hfd _ hs).hasFDerivAt).comp_hasDerivAt s hl
        have e : ⟪P.grad (x + s • d), d⟫ = fderiv ℝ P.f (x + s • d) d := by
          simp [Problem.grad, gradient, InnerProductSpace.toDual_symm_apply]
        rw [e]; exact this
      have lineC : ∀ x d : E n, ∀ s : ℝ, x + s • d ∈ X →
          HasDerivAt (fun s : ℝ => P.c (x + s • d)) (P.J (x + s • d) d) s := by
        intro x d s hs
        have hl := hline x d s
        exact ((hcd _ hs).hasFDerivAt).comp_hasDerivAt s hl
      have descF : ∀ x d : E n, ∀ α : ℝ, 0 ≤ α → (∀ s ∈ Set.Icc (0:ℝ) α, x + s • d ∈ X) →
          P.f (x + α • d) ≤ P.f x + α * ⟪P.grad x, d⟫ + A.L / 2 * α ^ 2 * ‖d‖ ^ 2 := by
        intro x d α hα hseg
        have hx0 : x ∈ X := by simpa using hseg 0 ⟨le_rfl, hα⟩
        have hder : ∀ s ∈ Set.Icc (0:ℝ) α, HasDerivAt (fun s : ℝ => P.f (x + s • d) - s * ⟪P.grad x, d⟫)
            (⟪P.grad (x + s • d), d⟫ - 1 * ⟪P.grad x, d⟫) s := fun s hs =>
          (lineF x d s (hseg s hs)).sub ((hasDerivAt_id s).mul_const _)
        have key := image_le_of_deriv_right_le_deriv_boundary
          (f := fun s : ℝ => P.f (x + s • d) - s * ⟪P.grad x, d⟫)
          (f' := fun s => ⟪P.grad (x + s • d), d⟫ - 1 * ⟪P.grad x, d⟫) (a := 0) (b := α)
          (fun s hs => (hder s hs).continuousAt.continuousWithinAt)
          (fun s hs => (hder s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt)
          (B := fun s => P.f x + A.L / 2 * s ^ 2 * ‖d‖ ^ 2) (B' := fun s => A.L * s * ‖d‖ ^ 2)
          (by show P.f (x + (0:ℝ) • d) - 0 * ⟪P.grad x, d⟫ ≤ P.f x + A.L / 2 * 0 ^ 2 * ‖d‖ ^ 2; simp) (by fun_prop)
          (fun s _ => by
            have hp := hsq2 s
            have := ((hp.const_mul (A.L/2)).mul_const (‖d‖^2)).const_add (P.f x)
            exact (this.congr_deriv (by ring)).hasDerivWithinAt)
          (fun s hs => by
            have hs' := Set.Ico_subset_Icc_self hs
            have h1 : ⟪P.grad (x + s • d), d⟫ - 1 * ⟪P.grad x, d⟫ = ⟪P.grad (x + s • d) - P.grad x, d⟫ := by
              rw [inner_sub_left]; ring
            have h2 := real_inner_le_norm (P.grad (x + s • d) - P.grad x) d
            have h3 := hgL _ (hseg s hs') x hx0
            have h4 : ‖x + s • d - x‖ = s * ‖d‖ := by
              simp [norm_smul, abs_of_nonneg hs.1]
            rw [h4] at h3
            show _ ≤ _
            rw [h1]
            calc _ ≤ _ := h2
              _ ≤ A.L * (s * ‖d‖) * ‖d‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
              _ = _ := by ring)
          ⟨hα, le_rfl⟩
        have key' : P.f (x + α • d) - α * ⟪P.grad x, d⟫ ≤ P.f x + A.L / 2 * α ^ 2 * ‖d‖ ^ 2 := key
        linarith
      have descC : ∀ x d : E n, ∀ α : ℝ, 0 ≤ α → (∀ s ∈ Set.Icc (0:ℝ) α, x + s • d ∈ X) →
          ‖P.c (x + α • d) - P.c x - α • P.J x d‖ ≤ A.Γ / 2 * α ^ 2 * ‖d‖ ^ 2 := by
        intro x d α hα hseg
        have hx0 : x ∈ X := by simpa using hseg 0 ⟨le_rfl, hα⟩
        have hder : ∀ s ∈ Set.Icc (0:ℝ) α, HasDerivAt (fun s : ℝ => P.c (x + s • d) - P.c x - s • P.J x d)
            (P.J (x + s • d) d - 0 - (1:ℝ) • P.J x d) s := fun s hs =>
          ((lineC x d s (hseg s hs)).sub (hasDerivAt_const s (P.c x))).sub ((hasDerivAt_id s).smul_const _)
        have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
          (f := fun s : ℝ => P.c (x + s • d) - P.c x - s • P.J x d)
          (f' := fun s => P.J (x + s • d) d - 0 - (1:ℝ) • P.J x d) (a := 0) (b := α)
          (fun s hs => (hder s hs).continuousAt.continuousWithinAt)
          (fun s hs => (hder s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt)
          (B := fun s => A.Γ / 2 * s ^ 2 * ‖d‖ ^ 2) (B' := fun s => A.Γ * s * ‖d‖ ^ 2)
          (by show ‖P.c (x + (0:ℝ) • d) - P.c x - (0:ℝ) • P.J x d‖ ≤ A.Γ / 2 * 0 ^ 2 * ‖d‖ ^ 2; simp)
          (fun s => by
            have hp := hsq2 s
            have := (hp.const_mul (A.Γ/2)).mul_const (‖d‖^2)
            exact this.congr_deriv (by ring))
          (fun s hs => by
            have hs' := Set.Ico_subset_Icc_self hs
            have h1 : P.J (x + s • d) d - 0 - (1:ℝ) • P.J x d = (P.J (x + s • d) - P.J x) d := by
              simp
            have h2 := (P.J (x + s • d) - P.J x).le_opNorm d
            have h3 := hJL _ (hseg s hs') x hx0
            have h4 : ‖x + s • d - x‖ = s * ‖d‖ := by
              simp [norm_smul, abs_of_nonneg hs.1]
            rw [h4] at h3
            show _ ≤ _
            rw [h1]
            calc _ ≤ _ := h2
              _ ≤ A.Γ * (s * ‖d‖) * ‖d‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
              _ = _ := by ring)
          ⟨hα, le_rfl⟩
        simpa using key
      clear hfd hcd lineF lineC hgL hJL hXo hf hc hsq2 hline
      -- constants
      obtain ⟨C0, hC0⟩ := isBounded_iff_forall_norm_le.mp hcB
      obtain ⟨M0, hM0⟩ := isBounded_iff_forall_norm_le.mp hJB
      obtain ⟨fl, hfl⟩ := hfb
      obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max C0 1 := ⟨_, rfl⟩
      obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = max M0 1 := ⟨_, rfl⟩
      have hC1 : 1 ≤ C := hCdef ▸ le_max_right _ _
      have hM1 : 1 ≤ M := hMdef ▸ le_max_right _ _
      have hCx : ∀ k, ‖P.c (R.x k)‖ ≤ C := fun k =>
        le_trans (hC0 _ ⟨R.x k, hx k, rfl⟩) (hCdef ▸ le_max_left _ _)
      have hMx : ∀ k, ‖P.J (R.x k)‖ ≤ M := fun k =>
        le_trans (hM0 _ ⟨R.x k, hx k, rfl⟩) (hMdef ▸ le_max_left _ _)
      have hflx : ∀ k, fl ≤ P.f (R.x k) := fun k => hfl ⟨R.x k, hx k, rfl⟩
      obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = min A.ω (1 / M ^ 2) := ⟨_, rfl⟩
      have ha0 : 0 < a := hadef ▸ lt_min hω (by positivity)
      have haω : a ≤ A.ω := hadef ▸ min_le_left _ _
      have haM : a * M ^ 2 ≤ 1 := by
        have : a ≤ 1 / M ^ 2 := hadef ▸ min_le_right _ _
        rw [le_div_iff₀ (by positivity)] at this; linarith
      obtain ⟨κv, hκvdef⟩ : ∃ κv : ℝ, κv = A.εv * a / (2 * C * A.ω ^ 2) := ⟨_, rfl⟩
      have hC0p : 0 < C := by linarith
      have hκv : 0 < κv := by rw [hκvdef]; positivity
      have sqkey : ∀ N N' W : ℝ, 0 ≤ N → 0 ≤ N' → N ≤ C → N' ^ 2 ≤ N ^ 2 - W → 0 ≤ W →
          W ≤ 2 * C * (N - N') := by
        intro N N' W h0 h0' hNC hsq hW
        have hle : N' ≤ N := (pow_le_pow_iff_left₀ h0' h0 two_ne_zero).mp (by linarith)
        have h1 : W ≤ (N - N') * (N + N') := by
          rw [show (N - N') * (N + N') = N ^ 2 - N' ^ 2 by ring]; linarith
        have h2 : (N - N') * (N + N') ≤ (N - N') * (2 * C) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        linarith
      -- orthogonality
      have horth : ∀ k, ‖R.d k‖ ^ 2 = ‖R.u k‖ ^ 2 + ‖R.v k‖ ^ 2 := by
        intro k
        obtain ⟨hβk, hnt, hvr, hvb, hcc, hlin, hJu, hd, hd0, hdn, hxn⟩ := hrun k
        obtain ⟨y', hy'⟩ := hvr
        have h0 : ⟪R.u k, R.v k⟫ = 0 := by
          rw [← hy']
          show ⟪R.u k, ContinuousLinearMap.adjoint (P.J (R.x k)) y'⟫ = 0
          rw [ContinuousLinearMap.adjoint_inner_right, hJu, inner_zero_left]
        rw [hd, add_comm, norm_add_sq_real, h0]; ring
      -- normal step decrease
      have hnorm : ∀ k, κv * ‖R.v k‖ ^ 2 ≤ ‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖ := by
        intro k
        obtain ⟨hβk, hnt, hvr, hvb, hcc, hlin, hJu, hd, hd0, hdn, hxn⟩ := hrun k
        set c := P.c (R.x k)
        set w := P.Jt (R.x k) c with hw
        have h1 := hcc a ⟨ha0.le, haω⟩
        have e1 : c + a • P.J (R.x k) (-(P.Jt (R.x k) c)) = c - a • P.J (R.x k) w := by
          rw [map_neg, smul_neg, ← sub_eq_add_neg]
        rw [e1] at h1
        have hinner : ⟪c, a • P.J (R.x k) w⟫ = a * ‖w‖ ^ 2 := by
          rw [real_inner_smul_right, ← ContinuousLinearMap.adjoint_inner_left, ← real_inner_self_eq_norm_sq]
          rfl
        have hJw : ‖P.J (R.x k) w‖ ≤ M * ‖w‖ :=
          le_trans ((P.J (R.x k)).le_opNorm w) (mul_le_mul_of_nonneg_right (hMx k) (norm_nonneg _))
        have hsq : ‖c - a • P.J (R.x k) w‖ ^ 2 ≤ ‖c‖ ^ 2 - a * ‖w‖ ^ 2 := by
          rw [norm_sub_sq_real, hinner, norm_smul, Real.norm_eq_abs, abs_of_pos ha0]
          have : (a * ‖P.J (R.x k) w‖) ^ 2 ≤ a * ‖w‖ ^ 2 := by
            have h2 : ‖P.J (R.x k) w‖ ^ 2 ≤ M ^ 2 * ‖w‖ ^ 2 := by
              rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hJw 2
            calc (a * ‖P.J (R.x k) w‖) ^ 2 = a * (a * ‖P.J (R.x k) w‖ ^ 2) := by ring
              _ ≤ a * (a * (M ^ 2 * ‖w‖ ^ 2)) := by gcongr
              _ = (a * M ^ 2) * (a * ‖w‖ ^ 2) := by ring
              _ ≤ 1 * (a * ‖w‖ ^ 2) := by gcongr
              _ = _ := one_mul _
          linarith
        have hmain : a * ‖w‖ ^ 2 ≤ 2 * C * (‖c‖ - ‖c - a • P.J (R.x k) w‖) :=
          sqkey _ _ _ (norm_nonneg _) (norm_nonneg _) (hCx k) hsq (by positivity)
        have hv2 : ‖R.v k‖ ^ 2 ≤ A.ω ^ 2 * ‖w‖ ^ 2 := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hvb 2
        have : κv * ‖R.v k‖ ^ 2 ≤ A.εv * (‖c‖ - ‖c - a • P.J (R.x k) w‖) := by
          rw [hκvdef]
          have hC0' : 0 < 2 * C * A.ω ^ 2 := by positivity
          rw [div_mul_eq_mul_div, div_le_iff₀ hC0']
          calc A.εv * a * ‖R.v k‖ ^ 2 ≤ A.εv * a * (A.ω ^ 2 * ‖w‖ ^ 2) := by gcongr
            _ = A.εv * A.ω ^ 2 * (a * ‖w‖ ^ 2) := by ring
            _ ≤ A.εv * A.ω ^ 2 * (2 * C * (‖c‖ - ‖c - a • P.J (R.x k) w‖)) := by gcongr
            _ = _ := by ring
        linarith
      -- τ is nonincreasing
      have hτprev : ∀ k, R.τ k ≤ prev R.τ A.τ₀ k := by
        intro k
        obtain ⟨hβk, hnt, hvr, hvb, hcc, hlin, hJu, hd, hd0, hdn, hxn⟩ := hrun k
        by_cases hdz : R.d k = 0
        · exact le_of_eq (hd0 hdz).1
        · obtain ⟨htr, -, -, -⟩ := hdn hdz
          by_cases hs : ⟪R.g k, R.d k⟫ + ⟪R.u k, R.H k (R.u k)⟫ ≤ 0
          · exact le_of_eq (htr.1 hs)
          · obtain ⟨h1, h2⟩ := htr.2 (lt_of_not_ge hs)
            by_cases hp : prev R.τ A.τ₀ k ≤ (1 - A.σ) * (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖) /
                (⟪R.g k, R.d k⟫ + ⟪R.u k, R.H k (R.u k)⟫)
            · exact le_of_eq (h1 hp)
            · rw [h2 (lt_of_not_ge hp)]
              exact le_trans (min_le_right _ _) (le_of_lt (lt_of_not_ge hp))
      have hτmono : ∀ j k, R.τ (k + j) ≤ R.τ k := by
        intro j; induction j with
        | zero => intro k; simp
        | succ j ih => intro k; exact le_trans (hτprev (k + j + 1)) (ih k)
      have hτt : ∀ k, t ≤ R.τ k := by
        intro k; rw [← hτK (k + K) (by omega)]; exact hτmono K k
      have hτ0 : ∀ k, R.τ k ≤ A.τ₀ := by
        intro k; induction k with
        | zero => exact hτprev 0
        | succ k ih => exact le_trans (hτprev (k + 1)) ih
      have htτ₀ : t ≤ A.τ₀ := le_trans (hτt 0) (hτ0 0)
      -- model reduction lower bound
      obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : ℝ, c₀ = min (t * ζH) (A.σ * κv) := ⟨_, rfl⟩
      have hc₀ : 0 < c₀ := by rw [hc₀def]; exact lt_min (by positivity) (by positivity)
      have hΔ : ∀ k, c₀ * ‖R.d k‖ ^ 2 ≤ deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) := by
        intro k
        obtain ⟨hβk, hnt, hvr, hvb, hcc, hlin, hJu, hd, hd0, hdn, hxn⟩ := hrun k
        by_cases hdz : R.d k = 0
        · rw [hdz]; simp [deltaL]
        obtain ⟨htr, -, -, -⟩ := hdn hdz
        have hJd : P.J (R.x k) (R.d k) = P.J (R.x k) (R.v k) := by rw [hd, map_add, hJu, add_zero]
        have hD := hnorm k
        rw [← hJd] at hD
        have huHu : ζH * ‖R.u k‖ ^ 2 ≤ ⟪R.u k, R.H k (R.u k)⟫ :=
          (hH k).2.2 (R.u k) (LinearMap.mem_ker.mpr (by simpa using hJu))
        have hτk := hτt k
        have hτs : R.τ k * (⟪R.g k, R.d k⟫ + ⟪R.u k, R.H k (R.u k)⟫) ≤
            (1 - A.σ) * (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖) := by
          by_cases hs : ⟪R.g k, R.d k⟫ + ⟪R.u k, R.H k (R.u k)⟫ ≤ 0
          · have : R.τ k * (⟪R.g k, R.d k⟫ + ⟪R.u k, R.H k (R.u k)⟫) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (by linarith) hs
            have : 0 ≤ (1 - A.σ) * (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖) :=
              mul_nonneg (by linarith) (le_trans (by positivity) hD)
            linarith
          · have hs' := lt_of_not_ge hs
            obtain ⟨h1, h2⟩ := htr.2 hs'
            have hle : R.τ k ≤ (1 - A.σ) * (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖) /
                (⟪R.g k, R.d k⟫ + ⟪R.u k, R.H k (R.u k)⟫) := by
              by_cases hp : prev R.τ A.τ₀ k ≤ (1 - A.σ) * (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖) /
                  (⟪R.g k, R.d k⟫ + ⟪R.u k, R.H k (R.u k)⟫)
              · rw [h1 hp]; exact hp
              · rw [h2 (lt_of_not_ge hp)]; exact min_le_right _ _
            rw [le_div_iff₀ hs'] at hle; linarith
        have hdd := horth k
        have hc1 : c₀ ≤ t * ζH := by rw [hc₀def]; exact min_le_left _ _
        have hc2 : c₀ ≤ A.σ * κv := by rw [hc₀def]; exact min_le_right _ _
        have e : deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) = -(R.τ k * (⟪R.g k, R.d k⟫ + ⟪R.u k, R.H k (R.u k)⟫))
            + R.τ k * ⟪R.u k, R.H k (R.u k)⟫ + (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖) := by
          simp only [deltaL]; ring
        rw [e, hdd]
        have i1 : t * ζH * ‖R.u k‖ ^ 2 ≤ R.τ k * ⟪R.u k, R.H k (R.u k)⟫ := by
          calc t * ζH * ‖R.u k‖ ^ 2 = t * (ζH * ‖R.u k‖ ^ 2) := by ring
            _ ≤ R.τ k * ⟪R.u k, R.H k (R.u k)⟫ :=
              mul_le_mul hτk huHu (by positivity) (by linarith)
        have i2 : c₀ * ‖R.u k‖ ^ 2 ≤ t * ζH * ‖R.u k‖ ^ 2 := by gcongr
        have i3 : c₀ * ‖R.v k‖ ^ 2 ≤ A.σ * (κv * ‖R.v k‖ ^ 2) := by
          rw [← mul_assoc]; gcongr
        have i4 : A.σ * (κv * ‖R.v k‖ ^ 2) ≤ A.σ * (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖) := by
          gcongr
        rw [mul_add]; linarith
      have hΔ0 : ∀ k, 0 ≤ deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) := fun k =>
        le_trans (by positivity) (hΔ k)
      -- ξ facts
      have hξfacts : ∀ k, R.ξ k ≤ prev R.ξ A.ξ₀ k ∧ (R.d k ≠ 0 → R.ξ k ≤ xiTrial P R k) := by
        intro k
        obtain ⟨hβk, hnt, hvr, hvb, hcc, hlin, hJu, hd, hd0, hdn, hxn⟩ := hrun k
        by_cases hdz : R.d k = 0
        · exact ⟨le_of_eq (hd0 hdz).2.2.2.1, fun h => absurd hdz h⟩
        · obtain ⟨-, -, hxi, -⟩ := hdn hdz
          by_cases hp : prev R.ξ A.ξ₀ k ≤ xiTrial P R k
          · rw [hxi.1 hp]; exact ⟨le_rfl, fun _ => hp⟩
          · have hlt := lt_of_not_ge hp
            rw [hxi.2 hlt]
            exact ⟨le_trans (min_le_right _ _) hlt.le, fun _ => min_le_right _ _⟩
      have hξ0 : ∀ k, R.ξ k ≤ A.ξ₀ := by
        intro k; induction k with
        | zero => exact (hξfacts 0).1
        | succ k ih => exact le_trans (hξfacts (k + 1)).1 ih
      obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = max A.τ₀ 1 := ⟨_, rfl⟩
      have hT1 : 1 ≤ T := by rw [hTdef]; exact le_max_right _ _
      have hTτ : A.τ₀ ≤ T := by rw [hTdef]; exact le_max_left _ _
      have hT0 : 0 < T := by linarith
      obtain ⟨ξs, hξsdef⟩ : ∃ ξs : ℝ, ξs = c₀ / T := ⟨_, rfl⟩
      have hξs : 0 < ξs := by rw [hξsdef]; positivity
      have hξsT : ξs * T = c₀ := by rw [hξsdef]; field_simp
      have hdpos : ∀ k, R.d k ≠ 0 → 0 < ‖R.d k‖ ^ 2 := fun k h => by
        have := norm_pos_iff.mpr h; positivity
      have htrial : ∀ k, R.d k ≠ 0 → ξs ≤ xiTrial P R k := by
        intro k hdz
        have hdp := hdpos k hdz
        have h1 := hΔ k
        have hτp : 0 < R.τ k := lt_of_lt_of_le ht (hτt k)
        have hb : ∀ z, 0 ≤ z → z ≤ T → ξs * (z * ‖R.d k‖ ^ 2) ≤ c₀ * ‖R.d k‖ ^ 2 := by
          intro z hz hzT
          rw [← hξsT]
          calc ξs * (z * ‖R.d k‖ ^ 2) ≤ ξs * (T * ‖R.d k‖ ^ 2) := by gcongr
            _ = _ := by ring
        unfold xiTrial
        split_ifs
        · rw [le_div_iff₀ (mul_pos hτp hdp)]
          exact le_trans (hb _ hτp.le (le_trans (hτ0 k) hTτ)) h1
        · rw [le_div_iff₀ hdp]
          have := hb 1 zero_le_one hT1
          rw [one_mul] at this
          exact le_trans this h1
      obtain ⟨ξm, hξmdef⟩ : ∃ ξm : ℝ, ξm = min A.ξ₀ ((1 - A.εξ) * ξs) := ⟨_, rfl⟩
      have h1εξ : 0 < 1 - A.εξ := by linarith
      have hξm : 0 < ξm := by rw [hξmdef]; exact lt_min hξ₀ (mul_pos h1εξ hξs)
      have hξm0 : ξm ≤ A.ξ₀ := by rw [hξmdef]; exact min_le_left _ _
      have hξm1 : ξm ≤ (1 - A.εξ) * ξs := by rw [hξmdef]; exact min_le_right _ _
      have hξms : ξm ≤ ξs := by
        have : 0 ≤ A.εξ * ξs := by positivity
        linarith
      have hξstep : ∀ k, ξm ≤ prev R.ξ A.ξ₀ k → ξm ≤ R.ξ k := by
        intro k hpk
        obtain ⟨hβk, hnt, hvr, hvb, hcc, hlin, hJu, hd, hd0, hdn, hxn⟩ := hrun k
        by_cases hdz : R.d k = 0
        · rw [(hd0 hdz).2.2.2.1]; exact hpk
        · obtain ⟨-, -, hxi, -⟩ := hdn hdz
          have htr := htrial k hdz
          by_cases hp : prev R.ξ A.ξ₀ k ≤ xiTrial P R k
          · rw [hxi.1 hp]; exact hpk
          · have hlt := lt_of_not_ge hp
            rw [hxi.2 hlt]
            refine le_min (le_trans hξm1 ?_) (le_trans hξms htr)
            exact mul_le_mul_of_nonneg_left (by linarith) h1εξ.le
      have hξlow : ∀ k, ξm ≤ R.ξ k := by
        intro k; induction k with
        | zero => exact hξstep 0 hξm0
        | succ k ih => exact hξstep (k + 1) ih
      -- step sizes for k ≥ K
      obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = 2 * (1 - A.η) * β := ⟨_, rfl⟩
      have hq : 0 < q := by rw [hqdef]; have : 0 < 1 - A.η := by linarith
                            positivity
      have hqΓ : q * A.ξ₀ * T ≤ A.Γ := by
        rw [hqdef, hTdef]; exact (div_le_one hΓ).mp hc23b
      obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = t * A.L + A.Γ := ⟨_, rfl⟩
      have hSΓ : A.Γ ≤ S := by rw [hSdef]; have := mul_pos ht hL; linarith
      have hS : 0 < S := by linarith
      obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ, μ = min t 1 := ⟨_, rfl⟩
      have hμ : 0 < μ := by rw [hμdef]; exact lt_min ht one_pos
      have hμt : μ ≤ t := by rw [hμdef]; exact min_le_left _ _
      have hμ1 : μ ≤ 1 := by rw [hμdef]; exact min_le_right _ _
      obtain ⟨αm, hαmdef⟩ : ∃ αm : ℝ, αm = q * ξm * μ / S := ⟨_, rfl⟩
      have hαm : 0 < αm := by rw [hαmdef]; positivity
      have hstep : ∀ k ≥ K, R.d k ≠ 0 → αm ≤ R.α k ∧ R.α k ≤ 1 ∧
          R.α k * (S * ‖R.d k‖ ^ 2) ≤ q * deltaL P (R.x k) t (R.g k) (R.d k) := by
        intro k hk hdz
        obtain ⟨hβk, hnt, hvr, hvb, hcc, hlin, hJu, hd, hd0, hdn, hxn⟩ := hrun k
        obtain ⟨-, -, -, hα⟩ := hdn hdz
        have hdp := hdpos k hdz
        have hτk := hτK k hk
        have hξtr := (hξfacts k).2 hdz
        have hξk0 : 0 < R.ξ k := lt_of_lt_of_le hξm (hξlow k)
        have key : ∀ z, μ ≤ z → z ≤ T → R.ξ k * (z * ‖R.d k‖ ^ 2) ≤ deltaL P (R.x k) t (R.g k) (R.d k) →
            αm ≤ q * R.ξ k * z / S ∧ q * R.ξ k * z / S ≤ 1 ∧
            q * R.ξ k * z / S ≤ q * deltaL P (R.x k) t (R.g k) (R.d k) / (S * ‖R.d k‖ ^ 2) := by
          intro z hz1 hz2 hz3
          have hz0 : 0 < z := lt_of_lt_of_le hμ hz1
          refine ⟨?_, ?_, ?_⟩
          · rw [hαmdef]
            have := hξlow k
            gcongr
          · rw [div_le_one hS]
            have : q * R.ξ k * z ≤ q * A.ξ₀ * T := by
              have := hξ0 k
              gcongr
            linarith
          · rw [div_le_div_iff₀ hS (mul_pos hS hdp)]
            calc q * R.ξ k * z * (S * ‖R.d k‖ ^ 2) = q * S * (R.ξ k * (z * ‖R.d k‖ ^ 2)) := by ring
              _ ≤ q * S * deltaL P (R.x k) t (R.g k) (R.d k) := by gcongr
              _ = _ := by ring
        have hlo : αm ≤ projLo A R k ∧ projLo A R k ≤ 1 ∧
            projLo A R k ≤ q * deltaL P (R.x k) t (R.g k) (R.d k) / (S * ‖R.d k‖ ^ 2) := by
          unfold xiTrial at hξtr
          unfold projLo
          rw [hτk] at hξtr
          rw [hτk, hβ k, ← hqdef, ← hSdef]
          split_ifs at hξtr ⊢
          · rw [le_div_iff₀ (mul_pos ht hdp)] at hξtr
            exact key t hμt (le_trans htτ₀ hTτ) hξtr
          · rw [le_div_iff₀ hdp] at hξtr
            have := key 1 hμ1 hT1 (by rw [one_mul]; exact hξtr)
            rwa [mul_one] at this
        have has : alphaSuff P A R k =
            min (q * deltaL P (R.x k) t (R.g k) (R.d k) / (S * ‖R.d k‖ ^ 2)) 1 := by
          unfold alphaSuff; rw [hτk, hβ k, ← hqdef, ← hSdef]
        have hα' : R.α k = max (projLo A R k) (min (alphaSuff P A R k) (projHi A R k)) := hα
        have hge : projLo A R k ≤ R.α k := by rw [hα']; exact le_max_left _ _
        have hle : R.α k ≤ alphaSuff P A R k := by
          rw [hα']
          exact max_le (by rw [has]; exact le_min hlo.2.2 hlo.2.1) (min_le_left _ _)
        rw [has] at hle
        refine ⟨le_trans hlo.1 hge, le_trans hle (min_le_right _ _), ?_⟩
        have := le_trans hle (min_le_left _ _)
        rwa [le_div_iff₀ (mul_pos hS hdp)] at this
      -- merit decrease
      obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = A.η * αm * c₀ := ⟨_, rfl⟩
      have hρ : 0 < ρ := by rw [hρdef]; positivity
      have hmerit : ∀ k ≥ K, merit P (R.x (k + 1)) t ≤ merit P (R.x k) t - ρ * ‖R.d k‖ ^ 2 := by
        intro k hk
        have hxn : R.x (k + 1) = R.x k + R.α k • R.d k := (hrun k).2.2.2.2.2.2.2.2.2.2
        by_cases hdz : R.d k = 0
        · rw [hxn, hdz]; simp
        obtain ⟨hα1, hα2, hα3⟩ := hstep k hk hdz
        have hα0 : 0 < R.α k := lt_of_lt_of_le hαm hα1
        have hseg : ∀ s ∈ Set.Icc (0:ℝ) (R.α k), R.x k + s • R.d k ∈ X := by
          intro s hs
          have h1 := hXc.add_smul_sub_mem (hx k) (hx (k + 1)) (t := s / R.α k)
            ⟨div_nonneg hs.1 hα0.le, (div_le_one hα0).mpr hs.2⟩
          rw [hxn, add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ hα0.ne'] at h1
          exact h1
        have hF := descF (R.x k) (R.d k) (R.α k) hα0.le hseg
        have hG := descC (R.x k) (R.d k) (R.α k) hα0.le hseg
        have hΔk := hΔ k
        have hΔk0 := hΔ0 k
        rw [hτK k hk] at hΔk hΔk0
        have hdl : deltaL P (R.x k) t (R.g k) (R.d k) = -t * ⟪P.grad (R.x k), R.d k⟫ + ‖P.c (R.x k)‖
            - ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖ := by rw [hg k]; rfl
        have hc1 : ‖P.c (R.x k + R.α k • R.d k)‖ ≤ ‖P.c (R.x k) + R.α k • P.J (R.x k) (R.d k)‖ +
            ‖P.c (R.x k + R.α k • R.d k) - P.c (R.x k) - R.α k • P.J (R.x k) (R.d k)‖ := by
          refine le_trans (le_of_eq ?_) (norm_add_le _ _)
          congr 1; abel
        have hc2 : ‖P.c (R.x k) + R.α k • P.J (R.x k) (R.d k)‖ ≤
            (1 - R.α k) * ‖P.c (R.x k)‖ + R.α k * ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖ := by
          have e : P.c (R.x k) + R.α k • P.J (R.x k) (R.d k) =
              (1 - R.α k) • P.c (R.x k) + R.α k • (P.c (R.x k) + P.J (R.x k) (R.d k)) := by module
          rw [e]
          refine le_trans (norm_add_le _ _) (le_of_eq ?_)
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hα0,
            abs_of_nonneg (by linarith)]
        have hF' := mul_le_mul_of_nonneg_left hF ht.le
        generalize hD : deltaL P (R.x k) t (R.g k) (R.d k) = D at *
        have hquad : S / 2 * R.α k ^ 2 * ‖R.d k‖ ^ 2 ≤ (1 - A.η) * (R.α k * D) := by
          have h1 : R.α k * (R.α k * (S * ‖R.d k‖ ^ 2)) ≤ R.α k * (q * D) := by gcongr
          have h2 : R.α k * (q * D) ≤ R.α k * (2 * (1 - A.η) * D) := by
            have : q ≤ 2 * (1 - A.η) := by
              rw [hqdef]; exact mul_le_of_le_one_right (by linarith) hβ1
            gcongr
          linarith
        have hlow : αm * (c₀ * ‖R.d k‖ ^ 2) ≤ R.α k * D :=
          mul_le_mul hα1 hΔk (by positivity) hα0.le
        have hlow' := mul_le_mul_of_nonneg_left hlow hη.le
        have hαD : R.α k * D = R.α k * (-t * ⟪P.grad (R.x k), R.d k⟫ + ‖P.c (R.x k)‖
            - ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖) := by rw [hdl]
        rw [hSdef] at hquad
        rw [hxn, hρdef]
        unfold merit
        linarith
      -- convergence
      have hψanti : Antitone (fun j => merit P (R.x (j + K)) t) := by
        refine antitone_nat_of_succ_le (fun j => ?_)
        have h1 := hmerit (j + K) (by omega)
        have h2 : 0 ≤ ρ * ‖R.d (j + K)‖ ^ 2 := by positivity
        rw [show j + 1 + K = j + K + 1 by omega]
        linarith
      have hψbdd : BddBelow (Set.range (fun j => merit P (R.x (j + K)) t)) := by
        refine ⟨t * fl, ?_⟩
        rintro _ ⟨j, rfl⟩
        have h1 := mul_le_mul_of_nonneg_left (hflx (j + K)) ht.le
        have h2 := norm_nonneg (P.c (R.x (j + K)))
        show t * fl ≤ t * P.f (R.x (j + K)) + ‖P.c (R.x (j + K))‖
        linarith
      have hψlim := tendsto_atTop_ciInf hψanti hψbdd
      have hψdiff : Tendsto (fun j => (merit P (R.x (j + K)) t - merit P (R.x (j + 1 + K)) t) / ρ)
          atTop (nhds 0) := by
        have := (hψlim.sub (hψlim.comp (tendsto_add_atTop_nat 1))).div_const ρ
        simpa using this
      have hdsq : Tendsto (fun j => ‖R.d (j + K)‖ ^ 2) atTop (nhds 0) := by
        refine squeeze_zero (fun j => by positivity) (fun j => ?_) hψdiff
        have h1 := hmerit (j + K) (by omega)
        rw [le_div_iff₀ hρ, show j + 1 + K = j + K + 1 by omega]
        linarith
      have hdlim : Tendsto (fun k => ‖R.d k‖) atTop (nhds 0) := by
        rw [← tendsto_add_atTop_iff_nat K]
        have := (Real.continuous_sqrt.tendsto 0).comp hdsq
        simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
      have hulim : Tendsto (fun k => ‖R.u k‖) atTop (nhds 0) := by
        refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hdlim
        refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
        have := horth k
        have := sq_nonneg ‖R.v k‖
        linarith
      have hκd : Tendsto (fun k => κH * ‖R.d k‖) atTop (nhds 0) := by
        simpa using hdlim.const_mul κH
      have hHd : ∀ k, ‖R.H k (R.d k)‖ ≤ κH * ‖R.d k‖ := fun k =>
        le_trans ((R.H k).le_opNorm _) (mul_le_mul_of_nonneg_right (hH k).2.1 (norm_nonneg _))
      have hres : ∀ k, P.grad (R.x k) + P.Jt (R.x k) (R.y k) = -(R.H k (R.d k)) := by
        intro k
        obtain ⟨hβk, hnt, hvr, hvb, hcc, hlin, hJu, hd, hd0, hdn, hxn⟩ := hrun k
        rw [hd, map_add, ← hg k]
        have e : P.Jt (R.x k) (R.y k) = -(R.g k + R.H k (R.v k)) - R.H k (R.u k) :=
          eq_sub_of_add_eq' hlin
        rw [e]; abel
      refine ⟨hulim, hdlim, ?_, ?_⟩
      · refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hκd
        unfold lagrangianNorm
        rw [hres k, norm_neg]
        exact hHd k
      · refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hκd
        unfold reducedNorm
        have hJt0 : ContinuousLinearMap.adjoint (B.Z k).toContinuousLinearMap (P.Jt (R.x k) (R.y k)) = 0 := by
          refine ext_inner_right ℝ (fun e => ?_)
          rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left]
          have hmem : (B.Z k) e ∈ LinearMap.ker (P.J (R.x k) : E n →ₗ[ℝ] E m) := by
            rw [← B.spans k]; exact ⟨e, rfl⟩
          have hz : P.J (R.x k) ((B.Z k) e) = 0 := by simpa using hmem
          show ⟪ContinuousLinearMap.adjoint (P.J (R.x k)) (R.y k), (B.Z k) e⟫ = 0
          rw [ContinuousLinearMap.adjoint_inner_left, hz, inner_zero_right]
        have hgr : P.grad (R.x k) = -(R.H k (R.d k)) - P.Jt (R.x k) (R.y k) :=
          eq_sub_of_add_eq (hres k)
        rw [hgr, map_sub, hJt0, sub_zero]
        refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
        rw [LinearIsometryEquiv.norm_map, norm_neg]
        calc ‖(B.Z k).toContinuousLinearMap‖ * ‖R.H k (R.d k)‖ ≤ 1 * ‖R.H k (R.d k)‖ :=
              mul_le_mul_of_nonneg_right (B.Z k).norm_toContinuousLinearMap_le (norm_nonneg _)
          _ ≤ _ := by rw [one_mul]; exact hHd k
