-- Prove2me | solution 1 for RobustOdds.SVM.z_law
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:17:06.199568+00:00
-- url     : https://prove2.me/submissions/5dab6f69-6aa6-4b0e-83ed-c943734fd003

import Mathlib
import Definitions.Def_RobustOdds_SVM_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

theorem solution (d : ℕ) (hd : 1 ≤ d) (η : ℝ) :
    ∀ y : ℝ, (RobustOdds.Tradeoff.weakLaw d η y).map (fun z => (1 / Real.sqrt d) * ∑ i, z i) =
      gaussianReal (y * η * Real.sqrt d) 1 := by
  intro y
  unfold RobustOdds.Tradeoff.weakLaw
  set μ0 : Fin d → Measure ℝ := fun _ => gaussianReal (y * η) 1 with hμ0
  set P : Measure (Fin d → ℝ) := Measure.pi μ0 with hP
  haveI : IsProbabilityMeasure P := by rw [hP]; infer_instance
  have hindep : iIndepFun (fun (i : Fin d) (z : Fin d → ℝ) => z i) P :=
    iIndepFun_pi (X := fun _ => (id : ℝ → ℝ)) (fun _ => aemeasurable_id)
  have hmapi : ∀ i : Fin d, P.map (fun z : Fin d → ℝ => z i) = gaussianReal (y * η) 1 :=
    fun i => (measurePreserving_eval μ0 i).map_eq
  have hlaw : ∀ i : Fin d, HasGaussianLaw (fun z : Fin d → ℝ => z i) P := by
    intro i
    haveI : IsGaussian (P.map (fun z : Fin d → ℝ => z i)) := by rw [hmapi i]; infer_instance
    exact IsGaussian.hasGaussianLaw
  have hsum := iIndepFun.hasGaussianLaw_fun_sum hlaw hindep
  have hZ := hsum.fun_smul (1 / Real.sqrt d)
  have hmap := hZ.map_eq_gaussianReal
  have hfun : (fun z : Fin d → ℝ => (1 / Real.sqrt d) * ∑ i, z i) =
      fun ω => (1 / Real.sqrt d) • ∑ i, (fun z : Fin d → ℝ => z i) ω := by
    funext z; simp [smul_eq_mul]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hsq : Real.sqrt d ^ 2 = d := Real.sq_sqrt hdpos.le
  have hsqpos : 0 < Real.sqrt d := Real.sqrt_pos.2 hdpos
  rw [hfun, hmap]
  congr 1
  · -- mean
    have hint : ∀ i : Fin d, ∫ z, z i ∂P = y * η := by
      intro i
      have hl : HasLaw (fun z : Fin d → ℝ => z i) (gaussianReal (y * η) 1) P :=
        ⟨(measurable_pi_apply i).aemeasurable, hmapi i⟩
      rw [hl.integral_eq, integral_id_gaussianReal]
    have hii : ∀ i : Fin d, Integrable (fun z : Fin d → ℝ => z i) P := fun i => (hlaw i).integrable
    simp only [smul_eq_mul]
    rw [integral_const_mul, integral_finset_sum _ (fun i _ => hii i)]
    simp only [hint, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    rw [hsq]
  · -- variance
    have hv : Var[fun ω => (1 / Real.sqrt d) • ∑ i, (fun z : Fin d → ℝ => z i) ω; P] = 1 := by
      simp only [smul_eq_mul]
      rw [variance_const_mul]
      have hs := variance_sum_pi (μ := μ0) (X := fun _ => (id : ℝ → ℝ))
        (fun i => memLp_id_gaussianReal 2)
      have hfun2 : (fun ω : Fin d → ℝ => ∑ i, ω i) = ∑ i : Fin d, fun ω : Fin d → ℝ => (id : ℝ → ℝ) (ω i) := by
        funext ω; simp
      rw [hfun2, hs]
      have hvar : ∀ i : Fin d, Var[(id : ℝ → ℝ); μ0 i] = 1 := fun i => by
        simp [hμ0, variance_id_gaussianReal]
      simp only [hvar, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      field_simp
      exact hsq.symm
    rw [hv]
    simp
