-- Prove2me | solution 1 for StochOptForest.ApxRisk.theorem_9_uniform
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T07:50:54.131984+00:00
-- url     : https://prove2.me/submissions/690ad26f-8498-4931-af89-9602cde08435

import Mathlib
import Definitions.Def_StochOptForest_ApxRisk_Model

open StochOptForest.ApxRisk

namespace SOFT9U

variable {d : ℕ}

lemma grad_C1 {f : Ed d → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (gradient f) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  exact (InnerProductSpace.toDual ℝ (Ed d)).symm.contDiff.comp h1

lemma diff_grad {f : Ed d → ℝ} (hf : ContDiff ℝ 2 f) : Differentiable ℝ (gradient f) :=
  (grad_C1 hf).differentiable (by norm_num)

lemma hess_cont {f : Ed d → ℝ} (hf : ContDiff ℝ 2 f) : Continuous (hess f) :=
  (grad_C1 hf).continuous_fderiv (by norm_num)

lemma fderiv_eq_inner {f : Ed d → ℝ} (z v : Ed d) :
    fderiv ℝ f z v = inner ℝ (gradient f z) v := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

lemma grad_add {f g : Ed d → ℝ} {z : Ed d} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    gradient (fun w => f w + g w) z = gradient f z + gradient g z := by
  unfold gradient
  rw [fderiv_fun_add hf hg, map_add]

lemma grad_sub {f g : Ed d → ℝ} {z : Ed d} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    gradient (fun w => f w - g w) z = gradient f z - gradient g z := by
  unfold gradient
  rw [fderiv_fun_sub hf hg, map_sub]

lemma hess_add {f g : Ed d → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (z : Ed d) :
    hess (fun w => f w + g w) z = hess f z + hess g z := by
  have e : gradient (fun w => f w + g w) = fun w => gradient f w + gradient g w := by
    funext w
    exact grad_add ((hf.differentiable (by norm_num)) w) ((hg.differentiable (by norm_num)) w)
  unfold hess
  rw [e, fderiv_fun_add ((diff_grad hf) z) ((diff_grad hg) z)]

lemma hess_sub {f g : Ed d → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (z : Ed d) :
    hess (fun w => f w - g w) z = hess f z - hess g z := by
  have e : gradient (fun w => f w - g w) = fun w => gradient f w - gradient g w := by
    funext w
    exact grad_sub ((hf.differentiable (by norm_num)) w) ((hg.differentiable (by norm_num)) w)
  unfold hess
  rw [e, fderiv_fun_sub ((diff_grad hf) z) ((diff_grad hg) z)]

/-- The Hessian is the second Fréchet derivative, read through the inner product. -/
lemma inner_hess {f : Ed d → ℝ} (hf : ContDiff ℝ 2 f) (z u v : Ed d) :
    inner ℝ (hess f z u) v = fderiv ℝ (fderiv ℝ f) z u v := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ f) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) z
  have h2 : HasFDerivAt (gradient f)
      (((InnerProductSpace.toDual ℝ (Ed d)).symm.toLinearIsometry.toContinuousLinearMap).comp
        (fderiv ℝ (fderiv ℝ f) z)) z := by
    have := ((InnerProductSpace.toDual ℝ (Ed d)).symm.toLinearIsometry.toContinuousLinearMap
      ).hasFDerivAt.comp z h1.hasFDerivAt
    exact this
  unfold hess
  rw [h2.fderiv]
  simp [InnerProductSpace.toDual_symm_apply]

lemma hess_symm {f : Ed d → ℝ} (hf : ContDiff ℝ 2 f) (z u v : Ed d) :
    inner ℝ (hess f z u) v = inner ℝ (hess f z v) u := by
  rw [inner_hess hf, inner_hess hf]
  have hs := (hf.contDiffAt (x := z)).isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  exact hs u v


/-- Second-order Taylor bound along a segment, with remainder controlled by the oscillation
of the Hessian on the segment. -/
lemma taylor2 {F : Ed d → ℝ} (hF : ContDiff ℝ 2 F) (z0 h : Ed d) (c : ℝ)
    (hc : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖hess F (z0 + s • h) - hess F z0‖ ≤ c) :
    |F (z0 + h) - F z0 - inner ℝ (gradient F z0) h - (1 / 2) * inner ℝ (hess F z0 h) h|
      ≤ c * ‖h‖ ^ 2 := by
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => z0 + s • h) h s := by
    intro s
    have := ((hasDerivAt_id s).smul_const h).const_add z0
    simpa using this
  have hφ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => F (z0 + s • h))
      (inner ℝ (gradient F (z0 + s • h)) h) s := by
    intro s
    have := ((hF.differentiable (by norm_num)) (z0 + s • h)).hasFDerivAt.comp_hasDerivAt s (hline s)
    rw [fderiv_eq_inner] at this
    exact this
  have hψ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => inner ℝ (gradient F (z0 + s • h)) h)
      (inner ℝ (hess F (z0 + s • h) h) h) s := by
    intro s
    have hG := ((diff_grad hF) (z0 + s • h)).hasFDerivAt.comp_hasDerivAt s (hline s)
    have := hG.inner ℝ (hasDerivAt_const s h)
    simpa [hess] using this
  set ψ0 := inner ℝ (gradient F z0) h
  set Q0 := inner ℝ (hess F z0 h) h
  have hQ : ∀ s ∈ Set.Icc (0 : ℝ) 1, |inner ℝ (hess F (z0 + s • h) h) h - Q0| ≤ c * ‖h‖ ^ 2 := by
    intro s hs
    have e : inner ℝ (hess F (z0 + s • h) h) h - Q0
        = inner ℝ ((hess F (z0 + s • h) - hess F z0) h) h := by
      simp [Q0, inner_sub_left]
    rw [e]
    calc |inner ℝ ((hess F (z0 + s • h) - hess F z0) h) h|
        ≤ ‖(hess F (z0 + s • h) - hess F z0) h‖ * ‖h‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖hess F (z0 + s • h) - hess F z0‖ * ‖h‖) * ‖h‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ (c * ‖h‖) * ‖h‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_right (hc s hs) (norm_nonneg _)
      _ = c * ‖h‖ ^ 2 := by ring
  -- first mean value step
  set b : ℝ → ℝ := fun s => inner ℝ (gradient F (z0 + s • h)) h - ψ0 - s * Q0 with hb
  have hb' : ∀ s, HasDerivAt b (inner ℝ (hess F (z0 + s • h) h) h - Q0) s := by
    intro s
    have := ((hψ s).sub_const ψ0).sub ((hasDerivAt_id s).mul_const Q0)
    refine this.congr_deriv ?_
    simp
  have hb0 : b 0 = 0 := by simp [b, ψ0]
  have hbB : ∀ s ∈ Set.Icc (0 : ℝ) 1, |b s| ≤ c * ‖h‖ ^ 2 * s := by
    intro s hs
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := b)
      (f' := fun s => inner ℝ (hess F (z0 + s • h) h) h - Q0) (C := c * ‖h‖ ^ 2)
      (fun x _ => (hb' x).hasDerivWithinAt)
      (fun x hx => by rw [Real.norm_eq_abs]; exact hQ x (Set.Ico_subset_Icc_self hx)) s hs
    rw [hb0, sub_zero, sub_zero, Real.norm_eq_abs] at this
    exact this
  -- second mean value step
  set a : ℝ → ℝ := fun s => F (z0 + s • h) - F z0 - s * ψ0 - s ^ 2 / 2 * Q0 with ha
  have ha' : ∀ s, HasDerivAt a (b s) s := by
    intro s
    have := ((((hφ s).sub_const (F z0)).sub ((hasDerivAt_id s).mul_const ψ0)).sub
      (((hasDerivAt_id s).pow 2).div_const 2 |>.mul_const Q0))
    refine this.congr_deriv ?_
    simp only [b, id]
    ring
  have ha0 : a 0 = 0 := by simp [a]
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := a) (f' := b) (C := c * ‖h‖ ^ 2)
    (fun x _ => (ha' x).hasDerivWithinAt)
    (fun x hx => by
      rw [Real.norm_eq_abs]
      have h1 := hbB x (Set.Ico_subset_Icc_self hx)
      have h2 : c * ‖h‖ ^ 2 * x ≤ c * ‖h‖ ^ 2 := by
        have hc0 : 0 ≤ c * ‖h‖ ^ 2 := (abs_nonneg _).trans (hQ 0 (by simp))
        nlinarith [hx.1, hx.2]
      linarith) 1 (by simp)
  rw [ha0, sub_zero, Real.norm_eq_abs] at this
  simp only [a, one_smul, one_mul, one_pow, sub_zero, mul_one] at this
  exact this

lemma quad_smul (H : Ed d →L[ℝ] Ed d) (t : ℝ) (v : Ed d) :
    inner ℝ (H (t • v)) (t • v) = t * t * inner ℝ (H v) v := by
  simp [map_smul, inner_smul_left, inner_smul_right]; ring

lemma coercive (H : Ed d →L[ℝ] Ed d) (hpd : ∀ v : Ed d, v ≠ 0 → 0 < inner ℝ (H v) v) :
    ∃ lam > 0, ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ (H v) v := by
  have hcont : Continuous fun v : Ed d => inner ℝ (H v) v := H.continuous.inner continuous_id
  have hsph : ∀ v : Ed d, v ≠ 0 → ‖v‖⁻¹ • v ∈ Metric.sphere (0 : Ed d) 1 := by
    intro v hv
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  by_cases hS : (Metric.sphere (0 : Ed d) 1).Nonempty
  · obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : Ed d) 1).exists_isMinOn hS hcont.continuousOn
    have hu0 : u ≠ 0 := by
      intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hu; exact zero_ne_one hu
    refine ⟨inner ℝ (H u) u, hpd u hu0, fun v => ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    have h1 : inner ℝ (H u) u ≤ inner ℝ (H (‖v‖⁻¹ • v)) (‖v‖⁻¹ • v) := hmin (hsph v hv)
    rw [quad_smul] at h1
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have h2 : inner ℝ (H u) u * ‖v‖ ^ 2 ≤ ‖v‖⁻¹ * ‖v‖⁻¹ * inner ℝ (H v) v * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : ‖v‖⁻¹ * ‖v‖⁻¹ * inner ℝ (H v) v * ‖v‖ ^ 2 = inner ℝ (H v) v := by
      field_simp
    rw [h3] at h2; linarith
  · refine ⟨1, one_pos, fun v => ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    exact absurd ⟨_, hsph v hv⟩ hS

lemma inv_spec (H : Ed d →L[ℝ] Ed d) (lam : ℝ) (hlam : 0 < lam)
    (hco : ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ (H v) v) (g : Ed d) : H (H.inverse g) = g := by
  have hinj : Function.Injective H := by
    intro a b hab
    have h0 : H (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have := hco (a - b)
    rw [h0, inner_zero_left] at this
    have : ‖a - b‖ ^ 2 ≤ 0 := by nlinarith
    have : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  have hsurj : Function.Surjective H :=
    (LinearMap.injective_iff_surjective (f := (H : Ed d →ₗ[ℝ] Ed d))).mp hinj
  let e := ContinuousLinearEquiv.ofBijective H (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj)
  have he : (e : Ed d →L[ℝ] Ed d) = H := rfl
  rw [← he, ContinuousLinearMap.inverse_equiv]
  simp

lemma gap (g : Ed d → ℝ) (hg : Continuous g) (zbar : Ed d) (hmin : IsUniqueMin g zbar)
    (hlev : ∃ α : ℝ, g zbar < α ∧ Bornology.IsBounded {z | g z ≤ α}) (r : ℝ) (hr : 0 < r) :
    ∃ γ > 0, ∀ z, r ≤ ‖z - zbar‖ → g zbar + γ ≤ g z := by
  obtain ⟨α, hα, hb⟩ := hlev
  set K := {z | g z ≤ α} ∩ {z : Ed d | r ≤ ‖z - zbar‖} with hKdef
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ (hb.subset Set.inter_subset_left)
    exact (isClosed_le hg continuous_const).inter
      (isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const)))
  by_cases hK : K.Nonempty
  · obtain ⟨w, hw, hwmin⟩ := hKc.exists_isMinOn hK hg.continuousOn
    have hlt : g zbar < g w := by
      refine lt_of_le_of_ne (hmin.1 w) fun heq => ?_
      have : w = zbar := hmin.2 w fun u => heq ▸ hmin.1 u
      have h2 := hw.2
      simp only [Set.mem_ofPred_eq, this, sub_self, norm_zero] at h2
      linarith
    refine ⟨min (α - g zbar) (g w - g zbar), lt_min (by linarith) (by linarith), fun z hz => ?_⟩
    by_cases hgz : g z ≤ α
    · have : g w ≤ g z := hwmin ⟨hgz, hz⟩
      linarith [min_le_right (α - g zbar) (g w - g zbar)]
    · linarith [min_le_left (α - g zbar) (g w - g zbar)]
  · refine ⟨α - g zbar, by linarith, fun z hz => ?_⟩
    by_cases hgz : g z ≤ α
    · exact absurd ⟨z, hgz, hz⟩ hK
    · linarith

end SOFT9U

open SOFT9U

set_option maxHeartbeats 1000000 in
theorem solution {d : ℕ} (fbar : Ed d → ℝ) (zbar : Ed d) (hfbar : ContDiff ℝ 2 fbar)
    (hmin : IsUniqueMin fbar zbar) (hpd : PosDefAt fbar zbar)
    (hlev : ∃ α : ℝ, fbar zbar < α ∧ Bornology.IsBounded {z | fbar z ≤ α}) :
    ∀ ε > 0, ∃ η > 0, ∀ (f0 : Ed d → ℝ) (z0 : Ed d), ContDiff ℝ 2 f0 →
      FNormLE (fun z => f0 z - fbar z) η → IsUniqueMin f0 z0 → PosDefAt f0 z0 →
      ∀ N : ℝ, N ≤ η → ∀ δf : Ed d → ℝ, ContDiff ℝ 2 δf → FNormLE δf N →
        |optVal (fun z => f0 z + δf z) - f0 z0 - δf z0
          + (1 / 2) * newtonQuad f0 δf z0| ≤ ε * N ^ 2 := by
  intro ε hε
  set Hb := hess fbar zbar with hHb
  obtain ⟨lam, hlam, hco⟩ := coercive Hb hpd
  set c := min (lam / 16) (ε * lam ^ 2 / 16) with hc
  have hcpos : 0 < c := lt_min (by positivity) (by positivity)
  have hc1 : c ≤ lam / 16 := min_le_left _ _
  have hc2 : c ≤ ε * lam ^ 2 / 16 := min_le_right _ _
  -- continuity of the Hessian of `fbar` at `zbar`
  obtain ⟨r, hr, hrH⟩ : ∃ r > 0, ∀ z, ‖z - zbar‖ < r → ‖hess fbar z - Hb‖ ≤ c / 4 := by
    obtain ⟨r, hr, h⟩ := Metric.continuousAt_iff.mp (hess_cont hfbar).continuousAt (c / 4)
      (by positivity)
    refine ⟨r, hr, fun z hz => ?_⟩
    have := h (x := z) (by rwa [dist_eq_norm])
    rw [dist_eq_norm] at this
    exact this.le
  obtain ⟨γ, hγ, hgap⟩ := gap fbar hfbar.continuous zbar hmin hlev (r / 2) (by positivity)
  have hηpos : 0 < min (c / 8) (min (γ / 5) (lam * r / 8)) :=
    lt_min (by positivity) (lt_min (by positivity) (by positivity))
  refine ⟨min (c / 8) (min (γ / 5) (lam * r / 8)), hηpos, ?_⟩
  intro f0 z0 hf0 hF0 hz0 _ N hN δf hδ hFN
  set η := min (c / 8) (min (γ / 5) (lam * r / 8)) with hη
  have hη1 : η ≤ c / 8 := min_le_left _ _
  have hη2 : η ≤ γ / 5 := (min_le_right _ _).trans (min_le_left _ _)
  have hη3 : η ≤ lam * r / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hN0 : 0 ≤ N := (abs_nonneg _).trans (hFN 0).1
  have hv0 : ∀ z, |f0 z - fbar z| ≤ η := fun z => (hF0 z).1
  have hH0 : ∀ z, ‖hess f0 z - hess fbar z‖ ≤ η := fun z => by
    have := (hF0 z).2.2; rwa [hess_sub hf0 hfbar] at this
  have hδv : ∀ z, |δf z| ≤ N := fun z => (hFN z).1
  have hδH : ∀ z, ‖hess δf z‖ ≤ N := fun z => (hFN z).2.2
  -- `z0` is close to `zbar`
  have hz0r : ‖z0 - zbar‖ < r / 2 := by
    by_contra hcon
    push Not at hcon
    have h1 := hgap z0 hcon
    have h2 := hz0.1 zbar
    have h3 := abs_le.mp (hv0 z0)
    have h4 := abs_le.mp (hv0 zbar)
    linarith
  -- Hessians on the ball
  have hball : ∀ z, ‖z - zbar‖ < r → ‖hess f0 z - Hb‖ ≤ η + c / 4 := by
    intro z hz
    calc ‖hess f0 z - Hb‖ = ‖(hess f0 z - hess fbar z) + (hess fbar z - Hb)‖ := by
          congr 1; abel
      _ ≤ ‖hess f0 z - hess fbar z‖ + ‖hess fbar z - Hb‖ := norm_add_le _ _
      _ ≤ η + c / 4 := add_le_add (hH0 z) (hrH z hz)
  set F : Ed d → ℝ := fun z => f0 z + δf z with hFdef
  have hFC : ContDiff ℝ 2 F := hf0.add hδ
  have hHF : ∀ z, hess F z = hess f0 z + hess δf z := hess_add hf0 hδ
  have hosc : ∀ z, ‖z - zbar‖ < r → ‖hess F z - hess F z0‖ ≤ c := by
    intro z hz
    rw [hHF, hHF]
    have e : hess f0 z + hess δf z - (hess f0 z0 + hess δf z0)
        = ((hess f0 z - Hb) - (hess f0 z0 - Hb) + hess δf z) - hess δf z0 := by abel
    rw [e]
    have h1 := hball z hz
    have h2 := hball z0 (by linarith)
    have h3 := hδH z
    have h4 := hδH z0
    calc _ ≤ ‖(hess f0 z - Hb) - (hess f0 z0 - Hb) + hess δf z‖ + ‖hess δf z0‖ :=
          norm_sub_le _ _
      _ ≤ ‖(hess f0 z - Hb) - (hess f0 z0 - Hb)‖ + ‖hess δf z‖ + ‖hess δf z0‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ ‖hess f0 z - Hb‖ + ‖hess f0 z0 - Hb‖ + ‖hess δf z‖ + ‖hess δf z0‖ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ c := by linarith
  -- coercivity of `H0 = ∇²f0(z0)`
  set H0 := hess f0 z0 with hH0def
  have hco0 : ∀ v, lam / 2 * ‖v‖ ^ 2 ≤ inner ℝ (H0 v) v := by
    intro v
    have h1 := hco v
    have hHH : ‖H0 - Hb‖ ≤ η + c / 4 := hball z0 (by linarith)
    have h2 : |inner ℝ ((H0 - Hb) v) v| ≤ (η + c / 4) * ‖v‖ ^ 2 := by
      calc |inner ℝ ((H0 - Hb) v) v| ≤ ‖(H0 - Hb) v‖ * ‖v‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖H0 - Hb‖ * ‖v‖) * ‖v‖ :=
            mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ ((η + c / 4) * ‖v‖) * ‖v‖ := by gcongr
        _ = (η + c / 4) * ‖v‖ ^ 2 := by ring
    have e : inner ℝ (H0 v) v = inner ℝ (Hb v) v + inner ℝ ((H0 - Hb) v) v := by
      simp [inner_sub_left]
    have h3 : (η + c / 4) * ‖v‖ ^ 2 ≤ lam / 2 * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    rw [e]
    linarith [(abs_le.mp h2).1]
  -- the Newton step `hs = -(∇²f0(z0))⁻¹ ∇δf(z0)`
  set g := gradient δf z0 with hgdef
  have hg : ‖g‖ ≤ N := (hFN z0).2.1
  set hs := -(H0.inverse g) with hsdef
  have hHs : H0 hs = -g := by
    rw [hsdef, map_neg, inv_spec H0 (lam / 2) (by positivity) hco0 g]
  have hnq : newtonQuad f0 δf z0 = inner ℝ (H0 hs) hs := by
    unfold newtonQuad
    rw [hHs, ← hH0def, ← hgdef, hsdef, inner_neg_left, inner_neg_right, neg_neg]
  have hgs : inner ℝ g hs = - newtonQuad f0 δf z0 := by
    rw [hnq, hHs, inner_neg_left, neg_neg]
  have hnq0 : 0 ≤ newtonQuad f0 δf z0 := by
    rw [hnq]; nlinarith [hco0 hs, sq_nonneg ‖hs‖]
  have hsN : ‖hs‖ ≤ 2 * N / lam := by
    have h1 := hco0 hs
    have h2 : inner ℝ (H0 hs) hs ≤ N * ‖hs‖ := by
      rw [hHs, inner_neg_left]
      have := abs_real_inner_le_norm g hs
      have := neg_le_abs (inner ℝ g hs)
      have : ‖g‖ * ‖hs‖ ≤ N * ‖hs‖ := mul_le_mul_of_nonneg_right hg (norm_nonneg _)
      linarith
    rw [le_div_iff₀ hlam]
    rcases eq_or_lt_of_le (norm_nonneg hs) with h0 | hpos
    · rw [← h0]; nlinarith
    · nlinarith
  -- the gradient of `F` at `z0`
  have hg0 : gradient f0 z0 = 0 := by
    have : IsLocalMin f0 z0 := Filter.Eventually.of_forall hz0.1
    simp [gradient, this.fderiv_eq_zero]
  have hgF : gradient F z0 = g := by
    rw [hFdef, grad_add ((hf0.differentiable (by norm_num)) z0) ((hδ.differentiable (by norm_num)) z0),
      hg0, zero_add]
  -- Taylor expansion of `F` around `z0` inside the ball
  have hT : ∀ h : Ed d, ‖z0 + h - zbar‖ < r →
      |F (z0 + h) - F z0 - inner ℝ g h - (1 / 2) * inner ℝ (H0 h) h| ≤ 2 * c * ‖h‖ ^ 2 := by
    intro h hh
    have hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖hess F (z0 + s • h) - hess F z0‖ ≤ c := by
      intro s hs'
      apply hosc
      have hmem := (convex_ball zbar r).add_smul_mem (x := z0) (y := h)
        (by rw [Metric.mem_ball, dist_eq_norm]; linarith)
        (by rwa [Metric.mem_ball, dist_eq_norm]) hs'
      rwa [Metric.mem_ball, dist_eq_norm] at hmem
    have h1 := taylor2 hFC z0 h c hseg
    rw [hgF, hHF z0] at h1
    have h2 : |inner ℝ (hess δf z0 h) h| ≤ N * ‖h‖ ^ 2 := by
      calc |inner ℝ (hess δf z0 h) h| ≤ ‖hess δf z0 h‖ * ‖h‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖hess δf z0‖ * ‖h‖) * ‖h‖ :=
            mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ (N * ‖h‖) * ‖h‖ := by gcongr; exact hδH z0
        _ = N * ‖h‖ ^ 2 := by ring
    have e : inner ℝ ((H0 + hess δf z0) h) h = inner ℝ (H0 h) h + inner ℝ (hess δf z0 h) h := by
      simp [inner_add_left]
    rw [e] at h1
    have h3 : N * ‖h‖ ^ 2 ≤ c * ‖h‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    have h4 := abs_le.mp h1
    have h5 := abs_le.mp h2
    rw [abs_le]
    constructor <;> linarith
  set base := f0 z0 + δf z0 with hbase
  have hFz0 : F z0 = base := rfl
  set E := 4 * c * ‖hs‖ ^ 2 with hE
  have hE0 : 0 ≤ E := by positivity
  -- lower bound for every `z`
  have hlow : ∀ z, base - (1 / 2) * newtonQuad f0 δf z0 - E ≤ F z := by
    intro z
    by_cases hz : ‖z - zbar‖ < r
    · set k := z - z0 - hs with hk
      have hzk : z = z0 + (hs + k) := by rw [hk]; abel
      have h1 := hT (hs + k) (by rwa [← hzk])
      rw [← hzk, hFz0] at h1
      have hsym : inner ℝ (H0 k) hs = inner ℝ (H0 hs) k := hess_symm hf0 z0 k hs
      have hgm : g = -(H0 hs) := by rw [hHs, neg_neg]
      have e1 : inner ℝ g (hs + k) + (1 / 2) * inner ℝ (H0 (hs + k)) (hs + k)
          = -(1 / 2) * inner ℝ (H0 hs) hs + (1 / 2) * inner ℝ (H0 k) k := by
        rw [hgm]
        simp only [map_add, inner_add_left, inner_add_right, inner_neg_left]
        rw [hsym]; ring
      have h2 := hco0 k
      have h3 : ‖hs + k‖ ^ 2 ≤ 2 * ‖hs‖ ^ 2 + 2 * ‖k‖ ^ 2 := by
        nlinarith [norm_add_le hs k, norm_nonneg hs, norm_nonneg k, norm_nonneg (hs + k),
          sq_nonneg (‖hs‖ - ‖k‖)]
      have h4 : 2 * c * ‖hs + k‖ ^ 2 ≤ 2 * c * (2 * ‖hs‖ ^ 2 + 2 * ‖k‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      have h5 : 0 ≤ (lam / 16 - c) * ‖k‖ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      have h6 := (abs_le.mp h1).1
      rw [hnq]
      linarith
    · push Not at hz
      have h1 := hgap z (by linarith)
      have h2 := abs_le.mp (hv0 z)
      have h3 := abs_le.mp (hδv z)
      have h4 := hz0.1 zbar
      have h5 := abs_le.mp (hv0 zbar)
      have h6 := abs_le.mp (hδv z0)
      have hFz : F z = f0 z + δf z := rfl
      have hb : base = f0 z0 + δf z0 := rfl
      rw [hFz]
      linarith
  -- upper bound at `z0 + hs`
  have hup : F (z0 + hs) ≤ base - (1 / 2) * newtonQuad f0 δf z0 + E := by
    have hsr : ‖hs‖ ≤ r / 4 := by
      have : 2 * N / lam ≤ r / 4 := by
        rw [div_le_iff₀ hlam]; nlinarith
      linarith
    have hin : ‖z0 + hs - zbar‖ < r := by
      calc ‖z0 + hs - zbar‖ = ‖(z0 - zbar) + hs‖ := by congr 1; abel
        _ ≤ ‖z0 - zbar‖ + ‖hs‖ := norm_add_le _ _
        _ < r := by linarith
    have h1 := (abs_le.mp (hT hs hin)).2
    rw [hFz0, hgs, ← hnq] at h1
    have : 2 * c * ‖hs‖ ^ 2 ≤ E := by rw [hE]; nlinarith [sq_nonneg ‖hs‖]
    linarith
  have hbdd : BddBelow (Set.range F) := ⟨_, by rintro _ ⟨z, rfl⟩; exact hlow z⟩
  have hopt_le : optVal F ≤ F (z0 + hs) := ciInf_le hbdd _
  have hopt_ge : base - (1 / 2) * newtonQuad f0 δf z0 - E ≤ optVal F := le_ciInf hlow
  have hEb : E ≤ ε * N ^ 2 := by
    have h1 : ‖hs‖ ^ 2 ≤ (2 * N / lam) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hsN 2
    have h2 : E ≤ 4 * c * (2 * N / lam) ^ 2 := by
      rw [hE]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 4 * c * (2 * N / lam) ^ 2 = 16 * c * N ^ 2 / lam ^ 2 := by field_simp; ring
    have h4 : 16 * c * N ^ 2 / lam ^ 2 ≤ ε * N ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : 16 * c ≤ ε * lam ^ 2 := by linarith
      nlinarith [sq_nonneg N]
    linarith
  rw [abs_le]
  constructor <;> linarith
