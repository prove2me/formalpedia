-- Prove2me | solution 1 for Viterbo.isSymplecticCapacity_gromovWidth_and_cylindricalCapacity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T16:02:31.959665+00:00
-- url     : https://prove2.me/submissions/bf3d2536-9483-4015-9c3d-33f73642d3da

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo
import Theorems.Thm_OAI_CylinderNonsqueezing_radius_le_of_map

set_option autoImplicit false

open scoped ENNReal ContDiff Pointwise

namespace Viterbo.Capacities

open OAI.SymmetricPolar Set Topology

/-! ## Generic facts about symplectic embeddings -/

/-- For `n ≥ 1`, a symplectic embedding is differentiable at every point of its domain. -/
theorem differentiableAt_of_symp {n : ℕ} (hn : 1 ≤ n) {e : Phase n → Phase n} {z : Phase n}
    (h : ∀ v w : Phase n, omega0 (fderiv ℝ e z v) (fderiv ℝ e z w) = omega0 v w) :
    DifferentiableAt ℝ e z := by
  by_contra hd
  have h0 := fderiv_zero_of_not_differentiableAt hd
  let x : Position n := EuclideanSpace.single ⟨0, hn⟩ 1
  have := h (x, 0) (0, x)
  rw [h0] at this
  simp [omega0, x] at this

theorem hse_mono {n : ℕ} {U U' V V' : Set (Phase n)} (h : HasSymplecticEmbedding U V)
    (hU : U' ⊆ U) (hV : V ⊆ V') : HasSymplecticEmbedding U' V' := by
  obtain ⟨e, hcd, hemb, hmaps, hsymp⟩ := h
  refine ⟨e, hcd.mono hU, ?_, (hmaps.mono_left hU).mono_right hV, fun z hz => hsymp z (hU hz)⟩
  exact hemb.comp (IsEmbedding.inclusion hU)

theorem hse_refl {n : ℕ} (U : Set (Phase n)) : HasSymplecticEmbedding U U := by
  refine ⟨id, contDiffOn_id, IsEmbedding.subtypeVal, mapsTo_id _, ?_⟩
  intro z _ v w
  simp

theorem hse_of_subset {n : ℕ} {U V : Set (Phase n)} (h : U ⊆ V) : HasSymplecticEmbedding U V :=
  hse_mono (hse_refl U) subset_rfl h

theorem hse_trans {n : ℕ} (hn : 1 ≤ n) {U V W : Set (Phase n)} (h₁ : HasSymplecticEmbedding U V)
    (h₂ : HasSymplecticEmbedding V W) : HasSymplecticEmbedding U W := by
  obtain ⟨e₁, hcd₁, hemb₁, hmaps₁, hsymp₁⟩ := h₁
  obtain ⟨e₂, hcd₂, hemb₂, hmaps₂, hsymp₂⟩ := h₂
  refine ⟨e₂ ∘ e₁, hcd₂.comp hcd₁ hmaps₁, ?_, hmaps₂.comp hmaps₁, ?_⟩
  · exact hemb₂.comp (hemb₁.codRestrict V (fun z => hmaps₁ z.2))
  · intro z hz v w
    have hd₁ := differentiableAt_of_symp hn (hsymp₁ z hz)
    have hd₂ := differentiableAt_of_symp hn (hsymp₂ (e₁ z) (hmaps₁ hz))
    rw [fderiv_comp z hd₂ hd₁]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hsymp₂ _ (hmaps₁ hz), hsymp₁ z hz]

/-- Conjugating a symplectic embedding by a conformally symplectic linear isomorphism. -/
theorem hse_conj {n : ℕ} (L : Phase n ≃L[ℝ] Phase n) (κ : ℝ)
    (hL : ∀ v w, omega0 (L v) (L w) = κ * omega0 v w) {U V : Set (Phase n)}
    (h : HasSymplecticEmbedding U V) : HasSymplecticEmbedding (L '' U) (L '' V) := by
  obtain ⟨e, hcd, hemb, hmaps, hsymp⟩ := h
  have hmU : MapsTo L.symm (L '' U) U := by
    rintro _ ⟨u, hu, rfl⟩
    simpa using hu
  refine ⟨fun z => L (e (L.symm z)), ?_, ?_, ?_, ?_⟩
  · exact L.contDiff.comp_contDiffOn (hcd.comp L.symm.contDiff.contDiffOn hmU)
  · let g : (L '' U) ≃ₜ U :=
      { toFun := fun z => ⟨L.symm z, hmU z.2⟩
        invFun := fun u => ⟨L u, mem_image_of_mem _ u.2⟩
        left_inv := fun z => Subtype.ext (by simp)
        right_inv := fun u => Subtype.ext (by simp)
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    have := L.toHomeomorph.isEmbedding.comp (hemb.comp g.isEmbedding)
    exact this
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨e u, hmaps hu, by simp⟩
  · rintro _ ⟨u, hu, rfl⟩ v w
    have hf : (fun z => L (e (L.symm z))) = L ∘ (e ∘ L.symm) := rfl
    rw [hf, L.comp_fderiv, L.symm.comp_right_fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
    rw [hL, hsymp u hu]
    have := hL (L.symm v) (L.symm w)
    simp only [ContinuousLinearEquiv.apply_symm_apply] at this
    exact this.symm

/-- Scaling by `α`. -/
noncomputable def scaleL (n : ℕ) (α : ℝ) (hα : α ≠ 0) : Phase n ≃L[ℝ] Phase n :=
  (LinearEquiv.smulOfNeZero ℝ (Phase n) α hα).toContinuousLinearEquiv

theorem scaleL_apply (n : ℕ) (α : ℝ) (hα : α ≠ 0) (z : Phase n) : scaleL n α hα z = α • z := rfl

theorem hse_smul {n : ℕ} {α : ℝ} (hα : α ≠ 0) {U V : Set (Phase n)}
    (h : HasSymplecticEmbedding U V) : HasSymplecticEmbedding (α • U) (α • V) := by
  have key := hse_conj (scaleL n α hα) (α ^ 2) (fun v w => by
    simp only [scaleL_apply, omega0, Prod.smul_fst, Prod.smul_snd, inner_smul_left,
      inner_smul_right, RCLike.conj_to_real]
    ring) h
  have himg : ∀ S : Set (Phase n), (scaleL n α hα) '' S = α • S := fun S => by
    rw [← Set.image_smul]; rfl
  rwa [himg, himg] at key

theorem smul_capacityBall (n : ℕ) {α : ℝ} (hα : α ≠ 0) (c : ℝ) :
    α • capacityBall n c = capacityBall n (α ^ 2 * c) := by
  ext z
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hα]
  simp only [capacityBall, mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, inv_pow]
  have h2 : 0 < α ^ 2 := by positivity
  rw [← mul_add, ← mul_assoc, mul_comm Real.pi, mul_assoc, inv_mul_lt_iff₀ h2]

theorem smul_capacityCylinder (n : ℕ) {α : ℝ} (hα : α ≠ 0) (c : ℝ) :
    α • capacityCylinder n c = capacityCylinder n (α ^ 2 * c) := by
  ext z
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hα]
  simp only [capacityCylinder, mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply,
    smul_eq_mul, mul_pow, inv_pow]
  have h2 : 0 < α ^ 2 := by positivity
  refine forall_congr' fun i => imp_congr_right fun _ => ?_
  rw [← mul_add, ← mul_assoc, mul_comm Real.pi, mul_assoc, inv_mul_lt_iff₀ h2]

theorem capacityBall_subset_cylinder {n : ℕ} (c : ℝ) :
    capacityBall n c ⊆ capacityCylinder n c := by
  intro z hz i _
  simp only [capacityBall, mem_ofPred_eq] at hz
  have h1 : z.1 i ^ 2 ≤ ‖z.1‖ ^ 2 := by
    have := PiLp.norm_apply_le z.1 i
    rw [Real.norm_eq_abs] at this
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have h2 : z.2 i ^ 2 ≤ ‖z.2‖ ^ 2 := by
    have := PiLp.norm_apply_le z.2 i
    rw [Real.norm_eq_abs] at this
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have := Real.pi_pos
  nlinarith

/-! ## The bridge `ℝ²ⁿ ≅ ℂⁿ`, `(q, p) ↦ q + i p` -/

noncomputable def phiL (n : ℕ) : Phase n →ₗ[ℝ] (OAI.FourierPolynomial.Vector (Fin n)) where
  toFun z := WithLp.toLp 2 (fun j => ((z.1 j : ℂ) + Complex.I * (z.2 j : ℂ)))
  map_add' x y := by
    ext j; simp; ring
  map_smul' r x := by
    ext j; simp; ring

noncomputable def psiL (n : ℕ) : (OAI.FourierPolynomial.Vector (Fin n)) →ₗ[ℝ] Phase n where
  toFun w := (WithLp.toLp 2 (fun j => (w j).re), WithLp.toLp 2 (fun j => (w j).im))
  map_add' x y := by
    ext j <;> simp
  map_smul' r x := by
    ext j <;> simp

noncomputable def Φ (n : ℕ) : Phase n →L[ℝ] (OAI.FourierPolynomial.Vector (Fin n)) := LinearMap.toContinuousLinearMap (phiL n)
noncomputable def Ψ (n : ℕ) : (OAI.FourierPolynomial.Vector (Fin n)) →L[ℝ] Phase n := LinearMap.toContinuousLinearMap (psiL n)

theorem Φ_apply_apply {n : ℕ} (z : Phase n) (j : Fin n) :
    Φ n z j = (z.1 j : ℂ) + Complex.I * (z.2 j : ℂ) := rfl

theorem Ψ_apply_fst {n : ℕ} (w : OAI.FourierPolynomial.Vector (Fin n)) (j : Fin n) : (Ψ n w).1 j = (w j).re := rfl
theorem Ψ_apply_snd {n : ℕ} (w : OAI.FourierPolynomial.Vector (Fin n)) (j : Fin n) : (Ψ n w).2 j = (w j).im := rfl

theorem Φ_Ψ {n : ℕ} (w : OAI.FourierPolynomial.Vector (Fin n)) : Φ n (Ψ n w) = w := by
  ext j
  apply Complex.ext <;> simp [Φ_apply_apply, Ψ_apply_fst, Ψ_apply_snd]

theorem Ψ_Φ {n : ℕ} (z : Phase n) : Ψ n (Φ n z) = z := by
  ext j
  · simp [Φ_apply_apply, Ψ_apply_fst]
  · simp [Φ_apply_apply, Ψ_apply_snd]

theorem norm_sq_Φ_apply {n : ℕ} (z : Phase n) (j : Fin n) :
    ‖Φ n z j‖ ^ 2 = z.1 j ^ 2 + z.2 j ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Φ_apply_apply]
  simp
  ring

theorem norm_sq_Φ {n : ℕ} (z : Phase n) : ‖Φ n z‖ ^ 2 = ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [norm_sq_Φ_apply, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]

theorem form_Φ {n : ℕ} (x y : Phase n) :
    OAI.ComplexSymplectic.form (Φ n x) (Φ n y) = omega0 x y := by
  simp only [OAI.ComplexSymplectic.form, omega0, real_inner_eq_re_inner, PiLp.inner_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Φ_apply_apply, inner]
  ring

theorem norm_sq_Ψ {n : ℕ} (w : OAI.FourierPolynomial.Vector (Fin n)) : ‖(Ψ n w).1‖ ^ 2 + ‖(Ψ n w).2‖ ^ 2 = ‖w‖ ^ 2 := by
  rw [← norm_sq_Φ, Φ_Ψ]

theorem isOpen_capacityBall (n : ℕ) (c : ℝ) : IsOpen (capacityBall n c) :=
  isOpen_lt (by fun_prop) continuous_const

/-! ## Non-squeezing in phase-space form -/

theorem le_of_embedding_aux {n : ℕ} (hn : 1 ≤ n) {a b a' : ℝ} (hb : 0 < b) (ha' : 0 < a')
    (haa : a' < a) (h : HasSymplecticEmbedding (capacityBall n a) (capacityCylinder n b)) :
    a' ≤ b := by
  obtain ⟨e, hcd, hemb, hmaps, hsymp⟩ := h
  have hpi := Real.pi_pos
  have hopen := isOpen_capacityBall n a
  have hinj : InjOn e (capacityBall n a) := by
    intro x hx y hy hxy
    have := hemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy
    simpa using congrArg Subtype.val this
  set L := a' / Real.pi with hLdef
  have hL : 0 < L := by positivity
  have hΨ : MapsTo (Ψ n) (OAI.PushedBall.domain L) (capacityBall n a) := by
    intro w hw
    simp only [OAI.PushedBall.domain, mem_ofPred_eq] at hw
    simp only [capacityBall, mem_ofPred_eq, norm_sq_Ψ]
    rw [lt_div_iff₀ hpi] at hw
    linarith
  -- compact set and bound
  set K := Ψ n '' Metric.closedBall 0 (Real.sqrt L) with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).image (Ψ n).continuous
  have hKsub : K ⊆ capacityBall n a := by
    rintro _ ⟨w, hw, rfl⟩
    rw [mem_closedBall_zero_iff] at hw
    have h1 : ‖w‖ ^ 2 ≤ L := by
      have := pow_le_pow_left₀ (norm_nonneg w) hw 2
      rwa [Real.sq_sqrt hL.le] at this
    simp only [capacityBall, mem_ofPred_eq, norm_sq_Ψ]
    rw [hLdef, le_div_iff₀ hpi] at h1
    linarith
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (f := fun x => Φ n (e x))
    ((Φ n).continuous.comp_continuousOn (hcd.continuousOn.mono hKsub))
  have key := OAI.CylinderNonsqueezing.radius_le_of_map (κ := Fin n) ⟨0, hn⟩ hL
    (div_pos hb hpi).le (sq_nonneg C) (fun w => Φ n (e (Ψ n w)))
    ((Φ n).contDiff.comp_contDiffOn (hcd.comp (Ψ n).contDiff.contDiffOn hΨ)) ?_ ?_ ?_ ?_
  · rwa [hLdef, div_le_div_iff_of_pos_right hpi] at key
  · intro x hx y hy hxy
    have h1 := congrArg (Ψ n) hxy
    simp only [Ψ_Φ] at h1
    have h2 := hinj (hΨ hx) (hΨ hy) h1
    simpa [Φ_Ψ] using congrArg (Φ n) h2
  · intro z hz v w
    have hd : DifferentiableAt ℝ e (Ψ n z) :=
      ((hcd.differentiableOn (by simp)) _ (hΨ hz)).differentiableAt (hopen.mem_nhds (hΨ hz))
    have hfd : HasFDerivAt (fun w => Φ n (e (Ψ n w)))
        ((Φ n).comp ((fderiv ℝ e (Ψ n z)).comp (Ψ n))) z :=
      (Φ n).hasFDerivAt.comp z (hd.hasFDerivAt.comp z (Ψ n).hasFDerivAt)
    rw [hfd.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    rw [form_Φ, hsymp _ (hΨ hz), ← form_Φ, Φ_Ψ, Φ_Ψ]
  · intro z hz
    have hzK : Ψ n z ∈ K := by
      refine mem_image_of_mem _ ?_
      rw [mem_closedBall_zero_iff]
      simp only [OAI.PushedBall.domain, mem_ofPred_eq] at hz
      have := Real.abs_le_sqrt hz.le
      rwa [abs_of_nonneg (norm_nonneg _)] at this
    exact pow_le_pow_left₀ (norm_nonneg _) (hC _ hzK) 2
  · intro z hz
    have hc := hmaps (hΨ hz) ⟨0, hn⟩ rfl
    rw [norm_sq_Φ_apply, le_div_iff₀ hpi]
    linarith

theorem le_of_embedding {n : ℕ} (hn : 1 ≤ n) {a b : ℝ} (hb : 0 < b)
    (h : HasSymplecticEmbedding (capacityBall n a) (capacityCylinder n b)) : a ≤ b := by
  by_contra hab
  rw [not_le] at hab
  have := le_of_embedding_aux hn hb (by linarith : 0 < (a + b) / 2) (by linarith) h
  linarith

/-! ## The two capacities -/

/-- Conformality from the one-sided inequality. -/
theorem conformal_of_le {n : ℕ} (c : Set (Phase n) → ℝ≥0∞)
    (h : ∀ α : ℝ, 0 < α → ∀ U : Set (Phase n), c (α • U) ≤ ENNReal.ofReal (α ^ 2) * c U) :
    ∀ α : ℝ, 0 < α → ∀ U : Set (Phase n), c (α • U) = ENNReal.ofReal (α ^ 2) * c U := by
  intro α hα U
  refine le_antisymm (h α hα U) ?_
  have h2 := h α⁻¹ (inv_pos.mpr hα) (α • U)
  rw [inv_smul_smul₀ hα.ne'] at h2
  calc ENNReal.ofReal (α ^ 2) * c U
      ≤ ENNReal.ofReal (α ^ 2) * (ENNReal.ofReal (α⁻¹ ^ 2) * c (α • U)) := by gcongr
    _ = ENNReal.ofReal (α ^ 2 * α⁻¹ ^ 2) * c (α • U) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    _ = c (α • U) := by
        rw [← mul_pow, mul_inv_cancel₀ hα.ne', one_pow, ENNReal.ofReal_one, one_mul]

theorem ball_smul_iff {n : ℕ} {α : ℝ} (hα : 0 < α) {c : ℝ} {U : Set (Phase n)}
    (h : HasSymplecticEmbedding (capacityBall n c) (α • U)) :
    HasSymplecticEmbedding (capacityBall n (α⁻¹ ^ 2 * c)) U := by
  have := hse_smul (inv_ne_zero hα.ne') h
  rwa [smul_capacityBall n (inv_ne_zero hα.ne'), inv_smul_smul₀ hα.ne'] at this

theorem gromovWidth_mono {n : ℕ} (hn : 1 ≤ n) (U V : Set (Phase n))
    (h : HasSymplecticEmbedding U V) : gromovWidth U ≤ gromovWidth V := by
  unfold gromovWidth
  refine sSup_le_sSup (image_mono fun c hc => ⟨hc.1, hse_trans hn hc.2 h⟩)

theorem gromovWidth_smul_le {n : ℕ} (α : ℝ) (hα : 0 < α) (U : Set (Phase n)) :
    gromovWidth (α • U) ≤ ENNReal.ofReal (α ^ 2) * gromovWidth U := by
  unfold gromovWidth
  refine sSup_le ?_
  rintro _ ⟨c, ⟨hc, hcU⟩, rfl⟩
  have hmem : α⁻¹ ^ 2 * c ∈ {c : ℝ | 0 < c ∧ HasSymplecticEmbedding (capacityBall n c) U} :=
    ⟨by positivity, ball_smul_iff hα hcU⟩
  calc ENNReal.ofReal c = ENNReal.ofReal (α ^ 2) * ENNReal.ofReal (α⁻¹ ^ 2 * c) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← mul_assoc, ← mul_pow,
          mul_inv_cancel₀ hα.ne', one_pow, one_mul]
    _ ≤ _ := by gcongr; exact le_sSup (mem_image_of_mem _ hmem)

theorem cyl_smul_iff {n : ℕ} {α : ℝ} (hα : 0 < α) {c : ℝ} {U : Set (Phase n)}
    (h : HasSymplecticEmbedding U (capacityCylinder n c)) :
    HasSymplecticEmbedding (α • U) (capacityCylinder n (α ^ 2 * c)) := by
  have := hse_smul hα.ne' h
  rwa [smul_capacityCylinder n hα.ne'] at this

theorem cyl_mono {n : ℕ} (hn : 1 ≤ n) (U V : Set (Phase n))
    (h : HasSymplecticEmbedding U V) : cylindricalCapacity U ≤ cylindricalCapacity V := by
  unfold cylindricalCapacity
  refine sInf_le_sInf (image_mono fun c hc => ⟨hc.1, hse_trans hn h hc.2⟩)

theorem cyl_smul_le {n : ℕ} (α : ℝ) (hα : 0 < α) (U : Set (Phase n)) :
    cylindricalCapacity (α • U) ≤ ENNReal.ofReal (α ^ 2) * cylindricalCapacity U := by
  unfold cylindricalCapacity
  rw [sInf_image, sInf_image, ENNReal.mul_iInf_of_ne (by simp; positivity) ENNReal.ofReal_ne_top]
  refine le_iInf fun c => ?_
  rw [ENNReal.mul_iInf_of_ne (by simp; positivity) ENNReal.ofReal_ne_top]
  refine le_iInf fun hc => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact iInf₂_le (α ^ 2 * c) ⟨by have := hc.1; positivity, cyl_smul_iff hα hc.2⟩

theorem isSymplecticCapacity_gromovWidth (n : ℕ) (hn : 1 ≤ n) :
    Viterbo.IsSymplecticCapacity n gromovWidth := by
  have hpi := Real.pi_pos
  refine ⟨gromovWidth_mono hn, conformal_of_le _ gromovWidth_smul_le, ?_, ?_⟩
  · refine le_antisymm ?_ ?_
    · refine sSup_le ?_
      rintro _ ⟨c, ⟨_, hcU⟩, rfl⟩
      exact ENNReal.ofReal_le_ofReal
        (le_of_embedding hn hpi (hse_mono hcU subset_rfl (capacityBall_subset_cylinder _)))
    · exact le_sSup (mem_image_of_mem _ ⟨hpi, hse_refl _⟩)
  · refine le_antisymm ?_ ?_
    · refine sSup_le ?_
      rintro _ ⟨c, ⟨_, hcU⟩, rfl⟩
      exact ENNReal.ofReal_le_ofReal (le_of_embedding hn hpi hcU)
    · exact le_sSup (mem_image_of_mem _ ⟨hpi, hse_of_subset (capacityBall_subset_cylinder _)⟩)

theorem isSymplecticCapacity_cylindricalCapacity (n : ℕ) (hn : 1 ≤ n) :
    Viterbo.IsSymplecticCapacity n Viterbo.cylindricalCapacity := by
  have hpi := Real.pi_pos
  refine ⟨cyl_mono hn, conformal_of_le _ cyl_smul_le, ?_, ?_⟩
  · refine le_antisymm ?_ ?_
    · exact sInf_le (mem_image_of_mem _ ⟨hpi, hse_of_subset (capacityBall_subset_cylinder _)⟩)
    · refine le_sInf ?_
      rintro _ ⟨c, ⟨hc, hcU⟩, rfl⟩
      exact ENNReal.ofReal_le_ofReal (le_of_embedding hn hc hcU)
  · refine le_antisymm ?_ ?_
    · exact sInf_le (mem_image_of_mem _ ⟨hpi, hse_refl _⟩)
    · refine le_sInf ?_
      rintro _ ⟨c, ⟨hc, hcU⟩, rfl⟩
      exact ENNReal.ofReal_le_ofReal
        (le_of_embedding hn hc (hse_mono hcU (capacityBall_subset_cylinder _) subset_rfl))

end Viterbo.Capacities

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    Viterbo.IsSymplecticCapacity n OAI.SymmetricPolar.gromovWidth ∧
      Viterbo.IsSymplecticCapacity n Viterbo.cylindricalCapacity :=
  ⟨Viterbo.Capacities.isSymplecticCapacity_gromovWidth n hn,
    Viterbo.Capacities.isSymplecticCapacity_cylindricalCapacity n hn⟩
