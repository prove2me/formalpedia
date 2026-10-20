-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P56.translation_invariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T05:53:18.643604+00:00
-- url     : https://prove2.me/submissions/e38e9562-d92b-44e2-b4da-74523c71413a

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

lemma h54b_cfc_conj {B : Type*} [Fintype B] [DecidableEq B] (u : Matrix.unitaryGroup B ℂ)
    (f : ℝ → ℝ) (A : Matrix B B ℂ) :
    cfc f ((u : Matrix B B ℂ) * A * (u : Matrix B B ℂ)ᴴ) =
      (u : Matrix B B ℂ) * cfc f A * (u : Matrix B B ℂ)ᴴ := by
  by_cases hA : IsSelfAdjoint A
  · let φ := Unitary.conjStarAlgAut ℂ (Matrix B B ℂ) u
    have hφ : Continuous φ :=
      (φ.toAlgEquiv.toLinearEquiv.toLinearMap).continuous_of_finiteDimensional
    have hφa : IsSelfAdjoint (φ A) := by
      simp only [φ, Unitary.conjStarAlgAut_apply]
      exact hA.conjugate _
    have := StarAlgHomClass.map_cfc φ f A ((Matrix.finite_real_spectrum).continuousOn _) hφ hA hφa
    simpa [φ, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using this.symm
  · have h2 : ¬ IsSelfAdjoint ((u : Matrix B B ℂ) * A * (u : Matrix B B ℂ)ᴴ) := by
      intro h
      apply hA
      have h3 := h.conjugate ((u : Matrix B B ℂ)ᴴ)
      have hu : (u : Matrix B B ℂ)ᴴ * (u : Matrix B B ℂ) = 1 := Unitary.star_mul_self_of_mem u.2
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] at h3
      have : (u : Matrix B B ℂ)ᴴ * ((u : Matrix B B ℂ) * A * (u : Matrix B B ℂ)ᴴ) *
          (u : Matrix B B ℂ) = A := by
        rw [show (u : Matrix B B ℂ)ᴴ * ((u : Matrix B B ℂ) * A * (u : Matrix B B ℂ)ᴴ) *
          (u : Matrix B B ℂ) = ((u : Matrix B B ℂ)ᴴ * (u : Matrix B B ℂ)) * A *
            ((u : Matrix B B ℂ)ᴴ * (u : Matrix B B ℂ)) by simp only [Matrix.mul_assoc]]
        rw [hu, Matrix.one_mul, Matrix.mul_one]
      rwa [this] at h3
    rw [cfc_apply_of_not_predicate _ h2, cfc_apply_of_not_predicate _ hA]
    simp

lemma h54b_entropy_conj {B : Type*} [Fintype B] [DecidableEq B] (u : Matrix.unitaryGroup B ℂ)
    (A : Matrix B B ℂ) :
    entropy ((u : Matrix B B ℂ) * A * (u : Matrix B B ℂ)ᴴ) = entropy A := by
  unfold entropy
  rw [h54b_cfc_conj, Matrix.trace_mul_cycle]
  have hu : (u : Matrix B B ℂ)ᴴ * (u : Matrix B B ℂ) = 1 := Unitary.star_mul_self_of_mem u.2
  rw [hu, Matrix.one_mul]

lemma h54b_orbit_mul {G B : Type*} [Group G] [Fintype B] [DecidableEq B]
    (U : ProjectiveRep G B) (ρ : Matrix B B ℂ) (v y : G) :
    orbit U ρ (v * y) = (U.unitary v : Matrix B B ℂ) * orbit U ρ y * (U.unitary v : Matrix B B ℂ)ᴴ := by
  unfold orbit
  rw [U.mul_phase]
  have hp : U.phase v y * star (U.phase v y) = 1 := by
    have := U.phase_norm v y
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, this]
    simp
  rw [Matrix.conjTranspose_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm, hp, one_smul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

lemma h54b_avg_translate {G B : Type*} [Group G] [Fintype G] [Fintype B] [DecidableEq B]
    (U : ProjectiveRep G B) (ρ : Matrix B B ℂ) (P : G → ℝ) (v : G) :
    average (orbit U ρ) (translate v P) =
      (U.unitary v : Matrix B B ℂ) * average (orbit U ρ) P * (U.unitary v : Matrix B B ℂ)ᴴ := by
  unfold average QAlgorithms.Papers.Independent.Information100.P56.translate
  rw [← Equiv.sum_comp (Equiv.mulLeft v)]
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, h54b_orbit_mul]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem solution
    {G B E : Type*} [Group G] [Fintype G] [Fintype B] [DecidableEq B]
    [Fintype E] [DecidableEq E] [Nonempty B] [Nonempty E]
    (UB : ProjectiveRep G B) (UE : ProjectiveRep G E)
    (rhoB : Matrix B B ℂ) (rhoE : Matrix E E ℂ)
    (hB : QAlgorithms.IsDensityMatrix rhoB) (hE : QAlgorithms.IsDensityMatrix rhoE)
    (P : G → ℝ) (hP : IsLaw P) (v : G) :
    average (orbit UB rhoB) (translate v P) =
      (UB.unitary v : Matrix B B ℂ) * average (orbit UB rhoB) P *
        (UB.unitary v : Matrix B B ℂ)ᴴ ∧
    average (orbit UE rhoE) (translate v P) =
      (UE.unitary v : Matrix E E ℂ) * average (orbit UE rhoE) P *
        (UE.unitary v : Matrix E E ℂ)ᴴ ∧
    delta (orbit UB rhoB) (orbit UE rhoE) (translate v P) =
      delta (orbit UB rhoB) (orbit UE rhoE) P := by
  refine ⟨h54b_avg_translate UB rhoB P v, h54b_avg_translate UE rhoE P v, ?_⟩
  unfold delta
  rw [h54b_avg_translate, h54b_avg_translate, h54b_entropy_conj, h54b_entropy_conj]

end
