-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SpherePhase_proof_fccb6cb4ea20
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:17:23.513354+00:00
-- url     : https://prove2.me/submissions/bf98ba19-5a6e-4567-b3f1-57bb5a9ff2f3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSpherePhase
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_phaseLaw_map_arg_exp_mul_b05b5462359a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_continuous_coordAlong_729188be789e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_isProbabilityMeasure_phaseLaw_a2795f84d538
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_orthoDir_50f4f53cb25a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory ProbabilityTheory Real
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace SpherePhase
theorem _root_.solution (h1 : SphereLawBasic.Statement) (h2 : SphereLawUnitary.Statement) :
    SpherePhase.Statement := by
  intro N p hp hN
  have hμ : IsProbabilityMeasure (sphereLaw N) := (h1 N (by omega)).1
  have hph : IsProbabilityMeasure phaseLaw := PointwiseLelong.isProbabilityMeasure_phaseLaw
  have hA : Continuous (coordAlong p) := PointwiseLelong.continuous_coordAlong p
  have hG : Measurable fun z ↦ (‖coordAlong p z‖, orthoDir p z) :=
    (continuous_norm.comp hA).measurable.prodMk (PointwiseLelong.measurable_orthoDir p)

  let L : (Fin N → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := coordAlong p
      map_add' := fun x y ↦ by simp [coordAlong, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x ↦ by simp [coordAlong, Finset.mul_sum, mul_assoc] }
  have hL : ∀ z, L z = coordAlong p z := fun _ ↦ rfl
  have hpp : coordAlong p p = 1 := by
    have : ∀ j, p j * star (p j) = ((‖p j‖ ^ 2 : ℝ) : ℂ) := fun j ↦ by
      rw [Complex.star_def, Complex.mul_conj']; push_cast; ring
    simp only [coordAlong, this]
    rw [← Complex.ofReal_sum, hp]; simp

  have key : ∀ (x : ℂ) (w : Fin N → ℂ), coordAlong p w = 0 →
      ∑ j, ‖x * p j + w j‖ ^ 2 = ‖x‖ ^ 2 + ∑ j, ‖w j‖ ^ 2 := by
    intro x w hw
    have hp' : ∑ j, Complex.normSq (p j) = 1 := by simpa [Complex.sq_norm] using hp
    have hcross : ∑ j, (x * p j * (starRingEnd ℂ) (w j)).re = 0 := by
      rw [← Complex.re_sum]
      have : ∑ j, x * p j * (starRingEnd ℂ) (w j) = x * (starRingEnd ℂ) (coordAlong p w) := by
        simp [coordAlong, map_sum, Finset.mul_sum, mul_comm, mul_assoc]
      rw [this, hw]; simp
    simp only [Complex.sq_norm, Complex.normSq_add, Complex.normSq_mul, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, hp', ← Finset.mul_sum, hcross]
    ring

  let R : ℝ → (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) := fun θ ↦
    LinearMap.id + ((Complex.exp (θ * Complex.I) - 1) • L).smulRight p
  have hR : ∀ θ z, R θ z = z + ((Complex.exp (θ * Complex.I) - 1) * coordAlong p z) • p :=
    fun θ z ↦ rfl
  have hRa : ∀ θ z, coordAlong p (R θ z) = Complex.exp (θ * Complex.I) * coordAlong p z := by
    intro θ z
    rw [← hL, hR, map_add, map_smul, smul_eq_mul, hL, hL, hpp]
    ring
  have hRw : ∀ θ z, R θ z - coordAlong p (R θ z) • p = z - coordAlong p z • p := by
    intro θ z
    rw [hRa, hR]
    ext j
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hRo : ∀ θ z, orthoDir p (R θ z) = orthoDir p z := by
    intro θ z
    rw [orthoDir, orthoDir, hRw]
  have hRn : ∀ θ v, ∑ j, ‖R θ v j‖ ^ 2 = ∑ j, ‖v j‖ ^ 2 := by
    intro θ v
    have hw0 : coordAlong p (v - coordAlong p v • p) = 0 := by
      rw [← hL, map_sub, map_smul, smul_eq_mul, hL, hL, hpp]
      ring
    have s1 : ∑ j, ‖R θ v j‖ ^ 2 = ∑ j,
        ‖(Complex.exp (θ * Complex.I) * coordAlong p v) * p j + (v - coordAlong p v • p) j‖ ^ 2 :=
      Finset.sum_congr rfl fun j _ ↦ by
        rw [hR]
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring_nf
    have s2 : ∑ j, ‖v j‖ ^ 2 = ∑ j, ‖coordAlong p v * p j + (v - coordAlong p v • p) j‖ ^ 2 :=
      Finset.sum_congr rfl fun j _ ↦ by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring_nf
    rw [s1, s2, key _ _ hw0, key _ _ hw0, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hinv : ∀ θ : ℝ, (sphereLaw N).map (R θ) = sphereLaw N := fun θ ↦ h2 N (R θ) (hRn θ)

  have hne : ∀ᵐ z ∂sphereLaw N, coordAlong p z ≠ 0 := by
    have hker : LinearMap.ker L ≠ ⊤ := by
      intro h
      have hp0 : p ∈ LinearMap.ker L := h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, hL, hpp] at hp0
      exact one_ne_zero hp0
    have h0 := (h1 N (by omega)).2.2 _ hker
    rw [ae_iff]
    have hset : {z | ¬coordAlong p z ≠ 0} = (LinearMap.ker L : Set (Fin N → ℂ)) := by
      ext z
      simp only [ne_eq, not_not, Set.mem_ofPred_eq, SetLike.mem_coe, LinearMap.mem_ker, hL]
    rw [hset, h0]

  have hF : Measurable fun z ↦ (Complex.arg (coordAlong p z), (‖coordAlong p z‖, orthoDir p z)) :=
    (Complex.measurable_arg.comp hA.measurable).prodMk hG
  let Φ : ℝ × (Fin N → ℂ) → ℝ × (ℝ × (Fin N → ℂ)) := fun q ↦
    (Complex.arg (Complex.exp (q.1 * Complex.I) * coordAlong p q.2),
      (‖coordAlong p q.2‖, orthoDir p q.2))
  have hΦ : Measurable Φ := by
    refine (Complex.measurable_arg.comp ?_).prodMk (hG.comp measurable_snd)
    exact ((Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_fst).mul
      continuous_const)).mul (hA.comp continuous_snd)).measurable
  ext S hS
  have hstep : ∀ θ : ℝ, (sphereLaw N)
      ((fun z ↦ (Complex.arg (coordAlong p z), (‖coordAlong p z‖, orthoDir p z))) ⁻¹' S) =
      ∫⁻ z, S.indicator 1 (Φ (θ, z)) ∂sphereLaw N := by
    intro θ
    conv_lhs => rw [← hinv θ]
    rw [Measure.map_apply (LinearMap.continuous_of_finiteDimensional (R θ)).measurable (hF hS)]
    have hpre : (R θ) ⁻¹' ((fun z ↦ (Complex.arg (coordAlong p z),
        (‖coordAlong p z‖, orthoDir p z))) ⁻¹' S) = (fun z ↦ Φ (θ, z)) ⁻¹' S := by
      ext z
      simp only [Set.mem_preimage, Φ, hRa, hRo, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    rw [hpre, ← lintegral_indicator_one (hS.preimage (hΦ.comp measurable_prodMk_left) :
      MeasurableSet ((fun z ↦ Φ (θ, z)) ⁻¹' S))]
    rfl
  rw [Measure.map_apply hF hS, Measure.prod_apply_symm hS]
  calc _ = ∫⁻ θ, (sphereLaw N)
          ((fun z ↦ (Complex.arg (coordAlong p z), (‖coordAlong p z‖, orthoDir p z))) ⁻¹' S)
          ∂phaseLaw := by rw [lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ θ, ∫⁻ z, S.indicator 1 (Φ (θ, z)) ∂sphereLaw N ∂phaseLaw :=
        lintegral_congr fun θ ↦ hstep θ
    _ = ∫⁻ z, ∫⁻ θ, S.indicator 1 (Φ (θ, z)) ∂phaseLaw ∂sphereLaw N :=
        lintegral_lintegral_swap ((measurable_one.indicator hS).comp hΦ).aemeasurable
    _ = ∫⁻ z, phaseLaw ((fun x ↦ (x, (‖coordAlong p z‖, orthoDir p z))) ⁻¹' S) ∂sphereLaw N := by
        refine lintegral_congr_ae (hne.mono fun z hz ↦ ?_)
        have hg : Measurable fun θ : ℝ ↦
            Complex.arg (Complex.exp (θ * Complex.I) * coordAlong p z) :=
          Complex.measurable_arg.comp ((Complex.continuous_exp.comp
            (Complex.continuous_ofReal.mul continuous_const)).mul continuous_const).measurable
        show ∫⁻ θ, S.indicator 1 (Φ (θ, z)) ∂phaseLaw =
          phaseLaw ((fun x ↦ (x, (‖coordAlong p z‖, orthoDir p z))) ⁻¹' S)
        rw [← lintegral_indicator_one (hS.preimage measurable_prodMk_right :
          MeasurableSet ((fun x ↦ (x, (‖coordAlong p z‖, orthoDir p z))) ⁻¹' S))]
        conv_rhs => rw [← phaseLaw_map_arg_exp_mul hz]
        rw [lintegral_map ((measurable_one.indicator (hS.preimage measurable_prodMk_right))) hg]
        rfl
    _ = ∫⁻ y, phaseLaw ((fun x ↦ (x, y)) ⁻¹' S)
          ∂(sphereLaw N).map fun z ↦ (‖coordAlong p z‖, orthoDir p z) :=
        (lintegral_map (measurable_measure_prodMk_right hS) hG).symm
end SpherePhase
end GroundTheory.Heights₂.Heights
