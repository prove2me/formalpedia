-- Prove2me | solution 1 for RegevLWE.Hyperplane.expectation_chain
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:27:00.713928+00:00
-- url     : https://prove2.me/submissions/cdb178c5-5e0b-4322-82fc-710791d5b074

import Mathlib
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian
import Theorems.Thm_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq
import Theorems.Thm_ZLattice_tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral
import Theorems.Thm_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule
import Theorems.Thm_RegevLWE_GaussConv_fourier_rhoShift
import Theorems.Thm_RegevLWE_Hyperplane_smoothing_remark

open MeasureTheory Filter Topology FourierTransform RegevLWE.GaussConv RegevLWE.Hyperplane
open scoped FourierTransform SchwartzMap

set_option backward.isDefEq.respectTransparency.types false

private lemma inner_nondegenerate (n : ℕ) :
    (innerₗ (EuclideanSpace ℝ (Fin n))).Nondegenerate :=
  ⟨fun x hx => inner_self_eq_zero.mp (hx x), fun x hx => inner_self_eq_zero.mp (hx x)⟩

private lemma inner_flip_eq (n : ℕ) :
    LinearMap.BilinForm.flip (innerₗ (EuclideanSpace ℝ (Fin n))) =
      innerₗ (EuclideanSpace ℝ (Fin n)) := by
  ext x y
  exact real_inner_comm x y

private lemma exists_schwartz_rho (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), ∀ x : EuclideanSpace ℝ (Fin n),
      f x = (rho r x : ℂ) := by
  obtain ⟨g, hg⟩ := SchwartzMap.exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq (Fin n)
  let u : ℝˣ := Units.mk0 r⁻¹ (inv_ne_zero hr.ne')
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.smulLeft u
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e g, fun x => ?_⟩
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hg, rho]
  congr 2
  have he : e x = r⁻¹ • x := rfl
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  ring

private lemma fourier_schwartz_rho {n : ℕ} {r : ℝ} (hr : 0 < r)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (hf : ∀ x, f x = (rho r x : ℂ))
    (w : EuclideanSpace ℝ (Fin n)) :
    VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
      (innerₗ (EuclideanSpace ℝ (Fin n))) (⇑f) w =
      (r : ℂ) ^ n * (rho (1 / r) w : ℂ) := by
  have hfn : (⇑f : EuclideanSpace ℝ (Fin n) → ℂ) = fun x => (rhoShift r 0 x : ℂ) := by
    funext x
    rw [hf x]
    simp [rhoShift]
  have h_four := RegevLWE.GaussConv.fourier_rhoShift hr (0 : EuclideanSpace ℝ (Fin n)) w
  change VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
    (innerₗ (EuclideanSpace ℝ (Fin n))) (fun x => (rhoShift r 0 x : ℂ)) w = _ at h_four
  rw [hfn, h_four]
  simp [inner_zero_left]

private lemma exists_orthonormalBasis_eq {n : ℕ} (i₀ : Fin n)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) :
    ∃ b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)), b i₀ = w := by
  let s : Set (Fin n) := {i₀}
  let v : Fin n → EuclideanSpace ℝ (Fin n) := fun _ => w
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [s, Set.mem_singleton_iff] at hi hj
    subst hi hj
    simp [Set.domRestrict, v, hw]
  have h_card : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by
    rw [finrank_euclideanSpace_fin, Fintype.card_fin]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq h_card hv
  exact ⟨b, hb i₀ (Set.mem_singleton i₀)⟩

private noncomputable def diagLin {n : ℕ} (d : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap ∘ₗ
    Matrix.toLin' (Matrix.diagonal d) ∘ₗ
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap

private lemma diagLin_ofLp {n : ℕ} (d : Fin n → ℝ) (z : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (diagLin d z).ofLp i = d i * z.ofLp i := by
  change ((Matrix.diagonal d).mulVec z.ofLp) i = d i * z.ofLp i
  rw [Matrix.mulVec_diagonal]

private lemma det_diagLin {n : ℕ} (d : Fin n → ℝ) :
    LinearMap.det (diagLin d) = ∏ i : Fin n, d i := by
  dsimp [diagLin]
  have h_conj := LinearMap.det_conj (Matrix.toLin' (Matrix.diagonal d))
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
  simp only [LinearEquiv.symm_symm] at h_conj
  rw [h_conj, LinearMap.det_toLin', Matrix.det_diagonal]

private noncomputable def diagLinearEquiv {n : ℕ} (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) :
    EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearEquiv.ofLinear (diagLin d) (diagLin (fun i => (d i)⁻¹))
    (by
      ext z i
      simp only [LinearMap.comp_apply, LinearMap.id_apply, diagLin_ofLp]
      rw [← mul_assoc, mul_inv_cancel₀ (hd i), one_mul])
    (by
      ext z i
      simp only [LinearMap.comp_apply, LinearMap.id_apply, diagLin_ofLp]
      rw [← mul_assoc, inv_mul_cancel₀ (hd i), one_mul])

private noncomputable def diagCLE {n : ℕ} (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (diagLinearEquiv d hd).toContinuousLinearEquiv

private lemma norm_sq_diagLin {n : ℕ} (i₀ : Fin n) (r : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) :
    let d : Fin n → ℝ := fun i => r⁻¹ * (if i = i₀ then Real.sqrt 2 else 1)
    ‖diagLin d z‖ ^ 2 = (‖z‖ ^ 2 + (z.ofLp i₀) ^ 2) / r ^ 2 := by
  intro d
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  have h_term : ∀ i : Fin n,
      ‖(diagLin d z).ofLp i‖ ^ 2 =
        (‖z.ofLp i‖ ^ 2 + (if i = i₀ then (z.ofLp i₀) ^ 2 else 0)) / r ^ 2 := by
    intro i
    rw [diagLin_ofLp, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    dsimp [d]
    split_ifs with h
    · subst h
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      calc (r⁻¹ * Real.sqrt 2 * z.ofLp i) ^ 2
        _ = r⁻¹ ^ 2 * Real.sqrt 2 ^ 2 * (z.ofLp i) ^ 2 := by ring
        _ = r⁻¹ ^ 2 * 2 * (z.ofLp i) ^ 2 := by rw [h2]
        _ = ((z.ofLp i) ^ 2 + (z.ofLp i) ^ 2) / r ^ 2 := by ring
    · ring
  simp_rw [h_term, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private lemma norm_sq_diagLin_inv {n : ℕ} (i₀ : Fin n) {r : ℝ} (hr : 0 < r)
    (z : EuclideanSpace ℝ (Fin n)) :
    let d : Fin n → ℝ := fun i => r⁻¹ * (if i = i₀ then Real.sqrt 2 else 1)
    ‖diagLin (fun i => (d i)⁻¹) z‖ ^ 2 = r ^ 2 * (‖z‖ ^ 2 - (z.ofLp i₀) ^ 2 / 2) := by
  intro d
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  have h_term : ∀ i : Fin n,
      ‖(diagLin (fun i => (d i)⁻¹) z).ofLp i‖ ^ 2 =
        r ^ 2 * (‖z.ofLp i‖ ^ 2 - (if i = i₀ then (z.ofLp i₀) ^ 2 / 2 else 0)) := by
    intro i
    rw [diagLin_ofLp, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    dsimp [d]
    split_ifs with h
    · subst h
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have _hr_ne : r ≠ 0 := hr.ne'
      calc ((r⁻¹ * Real.sqrt 2)⁻¹ * z.ofLp i) ^ 2
        _ = (r⁻¹)⁻¹ ^ 2 * (Real.sqrt 2 ^ 2)⁻¹ * (z.ofLp i) ^ 2 := by ring
        _ = r ^ 2 * 2⁻¹ * (z.ofLp i) ^ 2 := by rw [inv_inv, h2]
        _ = r ^ 2 * ((z.ofLp i) ^ 2 - (z.ofLp i) ^ 2 / 2) := by ring
    · simp
      ring
  simp_rw [h_term, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private lemma inner_diagLin_cancel {n : ℕ} (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0)
    (z₁ z₂ : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (diagLin d z₁) (diagLin (fun i => (d i)⁻¹) z₂) = inner ℝ z₁ z₂ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diagLin_ofLp, diagLin_ofLp]
  simp only [RCLike.inner_apply, conj_trivial]
  calc (d i)⁻¹ * z₂.ofLp i * (d i * z₁.ofLp i)
    _ = ((d i)⁻¹ * d i) * (z₂.ofLp i * z₁.ofLp i) := by ring
    _ = z₂.ofLp i * z₁.ofLp i := by rw [inv_mul_cancel₀ (hd i), one_mul]

private lemma fourier_unit_gaussian {n : ℕ}
    (g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (hg : ∀ z, g z = (rho 1 z : ℂ))
    (w : EuclideanSpace ℝ (Fin n)) :
    VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
      (innerₗ (EuclideanSpace ℝ (Fin n))) (⇑g) w = (rho 1 w : ℂ) := by
  have h := fourier_schwartz_rho (by norm_num : (0 : ℝ) < 1) g hg w
  simpa using h

theorem solution {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (h : Real.sqrt 2 * RegevLWE.GaussConv.smoothingParam L ε ≤ r)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) :
    (∑' x : L, RegevLWE.Hyperplane.discreteGaussian L r x *
        Real.exp (-Real.pi * (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2 / r ^ 2)) =
      1 / rhoLattice r L * ∑' x : L,
        Real.exp (-Real.pi * (‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 +
          (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2) / r ^ 2) ∧
    (∑' x : L, RegevLWE.Hyperplane.discreteGaussian L r x *
        Real.exp (-Real.pi * (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2 / r ^ 2)) =
      (ZLattice.covolume L)⁻¹ * r ^ n / (Real.sqrt 2 * rhoLattice r L) * ∑' y : RegevLWE.GaussConv.dual L,
        Real.exp (-Real.pi * r ^ 2 * (‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 -
          (inner ℝ w (y : EuclideanSpace ℝ (Fin n))) ^ 2 / 2)) ∧
    (∑' x : L, RegevLWE.Hyperplane.discreteGaussian L r x *
        Real.exp (-Real.pi * (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2 / r ^ 2)) ≤
      (ZLattice.covolume L)⁻¹ * r ^ n / (Real.sqrt 2 * rhoLattice r L) *
        rhoDual (Real.sqrt 2 / r) L ∧
    (∑' x : L, RegevLWE.Hyperplane.discreteGaussian L r x *
        Real.exp (-Real.pi * (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2 / r ^ 2)) ≤
      (ZLattice.covolume L)⁻¹ * r ^ n / (Real.sqrt 2 * rhoLattice r L) * (1 + ε) := by
  have hn : 0 < n := by
    by_contra h0
    have h_zero : n = 0 := by omega
    subst h_zero
    have hw0 : w = 0 := Subsingleton.elim w 0
    rw [hw0, norm_zero] at hw
    norm_num at hw
  let i₀ : Fin n := ⟨0, hn⟩
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_eq i₀ w hw
  let U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) := b.repr
  have hU_i₀ : ∀ v : EuclideanSpace ℝ (Fin n), (U v).ofLp i₀ = inner ℝ w v := by
    intro v
    rw [OrthonormalBasis.repr_apply_apply, hb]
  let d : Fin n → ℝ := fun i => r⁻¹ * (if i = i₀ then Real.sqrt 2 else 1)
  have hd : ∀ i : Fin n, d i ≠ 0 := by
    intro i
    dsimp [d]
    apply mul_ne_zero (inv_ne_zero hr.ne')
    split_ifs <;> positivity
  let D : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) := diagCLE d hd
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    U.toContinuousLinearEquiv.trans D
  have he_apply : ∀ x : EuclideanSpace ℝ (Fin n), e x = diagLin d (U x) := fun _ => rfl
  have he_norm_sq : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖e x‖ ^ 2 = (‖x‖ ^ 2 + (inner ℝ w x) ^ 2) / r ^ 2 := by
    intro x
    rw [he_apply, norm_sq_diagLin i₀ r (U x), U.norm_map, hU_i₀]
  obtain ⟨g₀, hg₀⟩ := SchwartzMap.exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq (Fin n)
  have hg : ∀ z : EuclideanSpace ℝ (Fin n), g₀ z = (rho 1 z : ℂ) := by
    intro z
    rw [hg₀ z]
    simp [rho]
  let f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e g₀
  have hf : ∀ x : EuclideanSpace ℝ (Fin n),
      f x = (Real.exp (-Real.pi * (‖x‖ ^ 2 + (inner ℝ w x) ^ 2) / r ^ 2) : ℂ) := by
    intro x
    simp only [f, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hg₀]
    congr 2
    rw [he_norm_sq]
    ring
  have h_part1 :
      (∑' x : L, RegevLWE.Hyperplane.discreteGaussian L r x *
          Real.exp (-Real.pi * (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2 / r ^ 2)) =
        1 / rhoLattice r L * ∑' x : L,
          Real.exp (-Real.pi * (‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 +
            (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2) / r ^ 2) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun x => ?_
    unfold RegevLWE.Hyperplane.discreteGaussian rho
    rw [div_mul_eq_mul_div, one_div_mul_eq_div]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  have h_det_d : LinearMap.det (diagLin d) = r⁻¹ ^ n * Real.sqrt 2 := by
    rw [det_diagLin]
    dsimp [d]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_ite_eq', if_pos (Finset.mem_univ i₀)]
  have h_det_pos : 0 < LinearMap.det (diagLin d) := by
    rw [h_det_d]
    positivity
  have h_det_inv_abs : |(LinearMap.det (diagLin d))⁻¹| = r ^ n / Real.sqrt 2 := by
    rw [abs_of_pos (inv_pos.mpr h_det_pos), h_det_d, mul_inv, inv_pow, inv_inv, div_eq_mul_inv]
  have h_map_e :
      Measure.map (⇑e) (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))) =
        ENNReal.ofReal (r ^ n / Real.sqrt 2) • MeasureTheory.volume := by
    have h_comp : (⇑e : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =
        (⇑(diagCLE d hd)) ∘ (⇑U) := rfl
    rw [h_comp, ← Measure.map_map (diagCLE d hd).continuous.measurable U.continuous.measurable,
      U.measurePreserving.map_eq]
    change Measure.map (⇑(diagLin d)) MeasureTheory.volume = _
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar MeasureTheory.volume (ne_of_gt h_det_pos),
      h_det_inv_abs]
  have h_fourier_f : ∀ y : EuclideanSpace ℝ (Fin n),
      VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
        (innerₗ (EuclideanSpace ℝ (Fin n))) (⇑f) y =
      ((r ^ n / Real.sqrt 2 *
        Real.exp (-Real.pi * r ^ 2 * (‖y‖ ^ 2 - (inner ℝ w y) ^ 2 / 2)) : ℝ) : ℂ) := by
    intro y
    let y' : EuclideanSpace ℝ (Fin n) := diagLin (fun i => (d i)⁻¹) (U y)
    have h_inner_eq : ∀ x : EuclideanSpace ℝ (Fin n),
        innerₗ (EuclideanSpace ℝ (Fin n)) x y =
          innerₗ (EuclideanSpace ℝ (Fin n)) (e x) y' := by
      intro x
      change inner ℝ x y = inner ℝ (diagLin d (U x)) (diagLin (fun i => (d i)⁻¹) (U y))
      rw [inner_diagLin_cancel d hd (U x) (U y), U.inner_map_map]
    unfold VectorFourier.fourierIntegral
    have h_integrand :
        (fun v : EuclideanSpace ℝ (Fin n) =>
          𝐞 (-innerₗ (EuclideanSpace ℝ (Fin n)) v y) • f v) =
        fun v : EuclideanSpace ℝ (Fin n) =>
          (fun z : EuclideanSpace ℝ (Fin n) =>
            𝐞 (-innerₗ (EuclideanSpace ℝ (Fin n)) z y') • g₀ z) (e v) := by
      funext v
      simp only [f, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, h_inner_eq v]
    rw [h_integrand]
    let e_meas : EuclideanSpace ℝ (Fin n) ≃ᵐ EuclideanSpace ℝ (Fin n) :=
      e.toHomeomorph.toMeasurableEquiv
    have h_int_map := MeasureTheory.integral_map_equiv (μ := MeasureTheory.volume) e_meas
      (fun z : EuclideanSpace ℝ (Fin n) =>
        𝐞 (-innerₗ (EuclideanSpace ℝ (Fin n)) z y') • g₀ z)
    have he_meas_coe : (⇑e_meas : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) = ⇑e := rfl
    rw [he_meas_coe, h_map_e, MeasureTheory.integral_smul_measure] at h_int_map
    rw [← h_int_map]
    have h_four_g := fourier_unit_gaussian g₀ hg y'
    unfold VectorFourier.fourierIntegral at h_four_g
    rw [h_four_g]
    have h_toReal : (ENNReal.ofReal (r ^ n / Real.sqrt 2)).toReal = r ^ n / Real.sqrt 2 :=
      ENNReal.toReal_ofReal (by positivity)
    rw [h_toReal]
    have hy'_norm : ‖y'‖ ^ 2 = r ^ 2 * (‖y‖ ^ 2 - (inner ℝ w y) ^ 2 / 2) := by
      dsimp [y']
      rw [norm_sq_diagLin_inv i₀ hr (U y), U.norm_map, hU_i₀]
    simp only [rho, Complex.real_smul, ← Complex.ofReal_mul]
    congr 1
    congr 1
    rw [hy'_norm]
    ring
  have h_poisson := ZLattice.tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral
    MeasureTheory.volume (innerₗ (EuclideanSpace ℝ (Fin n))) (inner_nondegenerate n)
    L f (0 : EuclideanSpace ℝ (Fin n))
  have h_sum := ZLattice.summable_fourierIntegral_mul_fourierChar_dualSubmodule
    MeasureTheory.volume (innerₗ (EuclideanSpace ℝ (Fin n))) (inner_nondegenerate n)
    L f (0 : EuclideanSpace ℝ (Fin n))
  rw [inner_flip_eq n] at h_poisson h_sum
  have h_lhs : (∑' x : L, f (0 + (x : EuclideanSpace ℝ (Fin n)))) =
      ((∑' x : L, Real.exp (-Real.pi * (‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 +
        (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2) / r ^ 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun x => ?_
    rw [zero_add, hf]
  have h_term : ∀ y : dual L,
      VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
        (innerₗ (EuclideanSpace ℝ (Fin n))) (⇑f) (y : EuclideanSpace ℝ (Fin n)) *
        (𝐞 (innerₗ (EuclideanSpace ℝ (Fin n)) 0 (y : EuclideanSpace ℝ (Fin n))) : ℂ) =
      ((r ^ n / Real.sqrt 2 *
        Real.exp (-Real.pi * r ^ 2 * (‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 -
          (inner ℝ w (y : EuclideanSpace ℝ (Fin n))) ^ 2 / 2)) : ℝ) : ℂ) := by
    intro y
    rw [h_fourier_f]
    simp
  have h_rhs : (∑' y : dual L,
      VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
        (innerₗ (EuclideanSpace ℝ (Fin n))) (⇑f) (y : EuclideanSpace ℝ (Fin n)) *
        (𝐞 (innerₗ (EuclideanSpace ℝ (Fin n)) 0 (y : EuclideanSpace ℝ (Fin n))) : ℂ)) =
      ((r ^ n / Real.sqrt 2 * ∑' y : dual L,
        Real.exp (-Real.pi * r ^ 2 * (‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 -
          (inner ℝ w (y : EuclideanSpace ℝ (Fin n))) ^ 2 / 2)) : ℝ) : ℂ) := by
    simp_rw [h_term]
    rw [← Complex.ofReal_tsum, tsum_mul_left]
  rw [h_lhs, h_rhs] at h_poisson
  have h_tsum_eq :
      (∑' x : L, Real.exp (-Real.pi * (‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 +
          (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2) / r ^ 2)) =
        (ZLattice.covolume L)⁻¹ * (r ^ n / Real.sqrt 2 * ∑' y : dual L,
          Real.exp (-Real.pi * r ^ 2 * (‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 -
            (inner ℝ w (y : EuclideanSpace ℝ (Fin n))) ^ 2 / 2))) := by
    apply Complex.ofReal_injective
    rw [h_poisson]
    push_cast
    ring
  have h_part2 :
      (∑' x : L, RegevLWE.Hyperplane.discreteGaussian L r x *
          Real.exp (-Real.pi * (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2 / r ^ 2)) =
        (ZLattice.covolume L)⁻¹ * r ^ n / (Real.sqrt 2 * rhoLattice r L) * ∑' y : RegevLWE.GaussConv.dual L,
          Real.exp (-Real.pi * r ^ 2 * (‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 -
            (inner ℝ w (y : EuclideanSpace ℝ (Fin n))) ^ 2 / 2)) := by
    rw [h_part1, h_tsum_eq]
    ring
  have h_sum_real : Summable (fun y : dual L =>
      r ^ n / Real.sqrt 2 * Real.exp (-Real.pi * r ^ 2 * (‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 -
        (inner ℝ w (y : EuclideanSpace ℝ (Fin n))) ^ 2 / 2))) := by
    have h_norm := h_sum.norm
    refine h_norm.congr fun y => ?_
    rw [h_term y, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h_sum_aniso : Summable (fun y : dual L =>
      Real.exp (-Real.pi * r ^ 2 * (‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 -
        (inner ℝ w (y : EuclideanSpace ℝ (Fin n))) ^ 2 / 2))) := by
    have h_c_ne : r ^ n / Real.sqrt 2 ≠ 0 := by positivity
    have h_mul := h_sum_real.mul_left (r ^ n / Real.sqrt 2)⁻¹
    refine h_mul.congr fun y => ?_
    exact inv_mul_cancel_left₀ h_c_ne _
  have hs : 0 < r / Real.sqrt 2 := by positivity
  have h_sum_rho_dual : Summable (fun y : dual L =>
      rho (Real.sqrt 2 / r) (y : EuclideanSpace ℝ (Fin n))) := by
    obtain ⟨f_iso, hf_iso⟩ := exists_schwartz_rho n hs
    have h_sum_iso := ZLattice.summable_fourierIntegral_mul_fourierChar_dualSubmodule
      MeasureTheory.volume (innerₗ (EuclideanSpace ℝ (Fin n))) (inner_nondegenerate n)
      L f_iso (0 : EuclideanSpace ℝ (Fin n))
    rw [inner_flip_eq n] at h_sum_iso
    have h_term_iso : ∀ y : dual L,
        VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
          (innerₗ (EuclideanSpace ℝ (Fin n))) (⇑f_iso) (y : EuclideanSpace ℝ (Fin n)) *
          (𝐞 (innerₗ (EuclideanSpace ℝ (Fin n)) 0 (y : EuclideanSpace ℝ (Fin n))) : ℂ) =
        (((r / Real.sqrt 2) ^ n * rho (1 / (r / Real.sqrt 2)) (y : EuclideanSpace ℝ (Fin n)) : ℝ) : ℂ) := by
      intro y
      rw [fourier_schwartz_rho hs f_iso hf_iso]
      simp
    have h_real : Summable (fun y : dual L =>
        (r / Real.sqrt 2) ^ n * rho (1 / (r / Real.sqrt 2)) (y : EuclideanSpace ℝ (Fin n))) := by
      refine h_sum_iso.norm.congr fun y => ?_
      rw [h_term_iso y, Complex.norm_real, Real.norm_of_nonneg (by unfold rho; positivity)]
    have h_mul := h_real.mul_left ((r / Real.sqrt 2) ^ n)⁻¹
    refine h_mul.congr fun y => ?_
    rw [inv_mul_cancel_left₀ (pow_ne_zero n hs.ne'), one_div_div]
  have h_tsum_le_rhoDual :
      (∑' y : RegevLWE.GaussConv.dual L,
        Real.exp (-Real.pi * r ^ 2 * (‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 -
          (inner ℝ w (y : EuclideanSpace ℝ (Fin n))) ^ 2 / 2))) ≤
      rhoDual (Real.sqrt 2 / r) L := by
    unfold rhoDual
    refine h_sum_aniso.tsum_le_tsum (fun y => ?_) h_sum_rho_dual
    unfold rho
    apply Real.exp_le_exp.mpr
    have h_cs := abs_real_inner_le_norm w (y : EuclideanSpace ℝ (Fin n))
    rw [hw, one_mul] at h_cs
    have h_sq : (inner ℝ w (y : EuclideanSpace ℝ (Fin n))) ^ 2 ≤
        ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
      rw [← sq_abs (inner ℝ w _)]
      exact sq_le_sq.mpr (by rwa [abs_abs, abs_of_nonneg (norm_nonneg _)])
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h_rhs_eq : -Real.pi * ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 / (Real.sqrt 2 / r) ^ 2 =
        -Real.pi * r ^ 2 * (‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 / 2) := by
      rw [div_pow, h2, div_div_eq_mul_div]
      ring
    rw [h_rhs_eq]
    have h_pi_r : 0 ≤ Real.pi * r ^ 2 := by positivity
    nlinarith
  have h_cov_pos : 0 < ZLattice.covolume L := ZLattice.covolume_pos L MeasureTheory.volume
  have h_rhoL_nonneg : 0 ≤ rhoLattice r L :=
    tsum_nonneg fun x => by unfold rho; positivity
  have h_pref_nonneg : 0 ≤ (ZLattice.covolume L)⁻¹ * r ^ n / (Real.sqrt 2 * rhoLattice r L) := by
    positivity
  have h_part3 :
      (∑' x : L, RegevLWE.Hyperplane.discreteGaussian L r x *
          Real.exp (-Real.pi * (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2 / r ^ 2)) ≤
        (ZLattice.covolume L)⁻¹ * r ^ n / (Real.sqrt 2 * rhoLattice r L) *
          rhoDual (Real.sqrt 2 / r) L := by
    rw [h_part2]
    exact mul_le_mul_of_nonneg_left h_tsum_le_rhoDual h_pref_nonneg
  have h_part4 :
      (∑' x : L, RegevLWE.Hyperplane.discreteGaussian L r x *
          Real.exp (-Real.pi * (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2 / r ^ 2)) ≤
        (ZLattice.covolume L)⁻¹ * r ^ n / (Real.sqrt 2 * rhoLattice r L) * (1 + ε) := by
    have hs_ge : smoothingParam L ε ≤ r / Real.sqrt 2 := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    obtain ⟨_, hanti, _, _, hsp⟩ := RegevLWE.Hyperplane.smoothing_remark hn L
    obtain ⟨hsp_pos, hsp_eq⟩ := hsp ε hε
    have h_nz_le : rhoDualNonzero (Real.sqrt 2 / r) L ≤ ε := by
      rw [← one_div_div r (Real.sqrt 2), ← hsp_eq]
      exact hanti.antitoneOn hsp_pos hs hs_ge
    have h_compl : ({0} : Set (dual L))ᶜ = {y : dual L | y ≠ 0} := by
      ext y
      simp
    have h_split := (h_sum_rho_dual.tsum_subtype_add_tsum_subtype_compl ({0} : Set (dual L))).symm
    rw [tsum_singleton 0 (fun y : dual L => rho (Real.sqrt 2 / r) (y : EuclideanSpace ℝ (Fin n))),
      h_compl] at h_split
    have h_rhoDual_eq : rhoDual (Real.sqrt 2 / r) L = 1 + rhoDualNonzero (Real.sqrt 2 / r) L := by
      unfold rhoDual rhoDualNonzero
      change ∑' y : dual L, rho (Real.sqrt 2 / r) (y : EuclideanSpace ℝ (Fin n)) =
        rho (Real.sqrt 2 / r) ((0 : dual L) : EuclideanSpace ℝ (Fin n)) +
          ∑' y : {y : dual L // y ≠ 0}, rho (Real.sqrt 2 / r) (y.1 : EuclideanSpace ℝ (Fin n)) at h_split
      rw [h_split]
      simp [rho]
    have h_rhoDual_le : rhoDual (Real.sqrt 2 / r) L ≤ 1 + ε := by linarith
    exact le_trans h_part3 (mul_le_mul_of_nonneg_left h_rhoDual_le h_pref_nonneg)
  exact ⟨h_part1, h_part2, h_part3, h_part4⟩
