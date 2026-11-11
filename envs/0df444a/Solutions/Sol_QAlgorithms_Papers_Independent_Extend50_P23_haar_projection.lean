-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P23.haar_projection
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T09:45:18.779724+00:00
-- url     : https://prove2.me/submissions/d51fb859-cbf4-4de6-b7d3-d1952f757e12

import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ComplexConjugate BigOperators Matrix.Norms.Elementwise
namespace S05P047

local instance matrixContinuousENorm {n : ℕ} :
    ContinuousENorm (Matrix (Fin n) (Fin n) ℂ) :=
  SeminormedAddGroup.toContinuousENorm

variable {G : Type*} [MeasurableSpace G] {mu : Measure G} {n : ℕ}
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ


-- Fixed matrix multiplication commutes with the Bochner integral in the exact elementwise norm.
def mulLeft (A : Mat n) : Mat n →L[ℂ] Mat n :=
  LinearMap.toContinuousLinearMap (mulLeftLinearMap (Fin n) ℂ A)

def mulRight (A : Mat n) : Mat n →L[ℂ] Mat n :=
  LinearMap.toContinuousLinearMap (mulRightLinearMap (Fin n) ℂ A)

lemma integral_mulLeft (F : G → Mat n) (hF : Integrable F mu) (A : Mat n) :
    (∫ g, A * F g ∂mu) = A * ∫ g, F g ∂mu :=
  (mulLeft A).integral_comp_comm hF

lemma integral_mulRight (F : G → Mat n) (hF : Integrable F mu) (A : Mat n) :
    (∫ g, F g * A ∂mu) = (∫ g, F g ∂mu) * A :=
  (mulRight A).integral_comp_comm hF

lemma integral_conjugate (F : G → Mat n) (hF : Integrable F mu) (A : Mat n) :
    (∫ g, A * F g * A.conjTranspose ∂mu) = A * (∫ g, F g ∂mu) * A.conjTranspose :=
  ((mulRight A.conjTranspose).comp (mulLeft A)).integral_comp_comm hF

section Compact
variable [TopologicalSpace G] [CompactSpace G] [T2Space G] [BorelSpace G]

lemma continuous_conjugate (rho : G → Mat n) (hc : Continuous rho) (X : Mat n) :
    Continuous (fun g => rho g * X * (rho g).conjTranspose) :=
  (hc.matrix_mul continuous_const).matrix_mul hc.matrix_conjTranspose

lemma integrable_continuous (F : G → Mat n) (hc : Continuous F)
    [IsFiniteMeasure mu] : Integrable F mu := by
  convert hc.integrable_of_hasCompactSupport (μ := mu)
    (HasCompactSupport.of_compactSpace F) using 1 <;> rfl

lemma integrable_conjugate (rho : G → Mat n) (hc : Continuous rho) (X : Mat n)
    [IsFiniteMeasure mu] : Integrable (fun g => rho g * X * (rho g).conjTranspose) mu :=
  integrable_continuous _ (continuous_conjugate rho hc X)

end Compact

section Invariance
variable [Group G] [MeasurableMul G] [Measure.IsMulLeftInvariant mu]

lemma haar_conjugate_invariant (rho : G → Mat n)
    (hmul : ∀ g h, rho (g * h) = rho g * rho h) (X : Mat n)
    (hF : Integrable (fun g => rho g * X * (rho g).conjTranspose) mu) (g : G) :
    rho g * (∫ h, rho h * X * (rho h).conjTranspose ∂mu) * (rho g).conjTranspose =
      (∫ h, rho h * X * (rho h).conjTranspose ∂mu) := by
  calc
    _ = ∫ h, rho g * (rho h * X * (rho h).conjTranspose) * (rho g).conjTranspose ∂mu :=
      (integral_conjugate _ hF _).symm
    _ = ∫ h, rho (g * h) * X * (rho (g * h)).conjTranspose ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with h
      rw [hmul, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = _ := integral_mul_left_eq_self (μ := mu)
      (fun h : G => rho h * X * (rho h).conjTranspose) g

lemma haar_commutes (rho : G → Mat n)
    (hmul : ∀ g h, rho (g * h) = rho g * rho h)
    (hunit : ∀ g, rho g ∈ Matrix.unitaryGroup (Fin n) ℂ) (X : Mat n)
    (hF : Integrable (fun g => rho g * X * (rho g).conjTranspose) mu) (g : G) :
    rho g * (∫ h, rho h * X * (rho h).conjTranspose ∂mu) =
      (∫ h, rho h * X * (rho h).conjTranspose ∂mu) * rho g := by
  have hstar : (rho g).conjTranspose * rho g = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (hunit g)
  have hi := haar_conjugate_invariant rho hmul X hF g
  calc
    _ = (rho g * (∫ h, rho h * X * (rho h).conjTranspose ∂mu) *
          (rho g).conjTranspose) * rho g := by
      simp only [Matrix.mul_assoc, hstar, Matrix.mul_one]
    _ = _ := congrArg (fun A => A * rho g) hi

end Invariance

lemma haar_fixed (rho : G → Mat n)
    (hunit : ∀ g, rho g ∈ Matrix.unitaryGroup (Fin n) ℂ) (X : Mat n)
    (hcomm : ∀ g, rho g * X = X * rho g) [IsProbabilityMeasure mu] :
    (∫ g, rho g * X * (rho g).conjTranspose ∂mu) = X := by
  have hconst : (fun g => rho g * X * (rho g).conjTranspose) = fun _ => X := by
    funext g
    rw [hcomm g, Matrix.mul_assoc]
    have hstar : rho g * (rho g).conjTranspose = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (hunit g)
    rw [hstar, Matrix.mul_one]
  rw [hconst]
  simp

end S05P047

open MeasureTheory
open scoped BigOperators

namespace S05P047

/-- On a finite group, every left-invariant probability measure averages a
function by the uniform finite sum. The exhaustiveness witness avoids imposing
a chosen finite enumeration on the ambient group. -/
theorem finite_haar_integral
    {G E : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (mu : Measure G) [Measure.IsMulLeftInvariant mu] [IsProbabilityMeasure mu]
    (F : G → E) (hF : Integrable F mu)
    (s : Finset G) (hs : ∀ g, g ∈ s) :
    (∫ g, F g ∂mu) = (s.card : ℂ)⁻¹ • ∑ g ∈ s, F g := by
  classical
  have hperm (h : G) : (∑ g ∈ s, F (g * h)) = ∑ g ∈ s, F g := by
    refine Finset.sum_bij (fun g _ => g * h) (fun g _ => hs (g * h)) ?_ ?_ ?_
    · intro g₁ _ g₂ _ heq
      exact mul_right_cancel heq
    · intro g _
      exact ⟨g * h⁻¹, hs _, by simp⟩
    · intro g _
      rfl
  have hsum : (s.card : ℂ) • (∫ g, F g ∂mu) = ∑ g ∈ s, F g := by
    calc
      (s.card : ℂ) • (∫ g, F g ∂mu)
          = ∑ g ∈ s, ∫ h, F (g * h) ∂mu := by
            simp only [integral_mul_left_eq_self, Finset.sum_const, Nat.cast_smul_eq_nsmul]
      _ = ∫ h, ∑ g ∈ s, F (g * h) ∂mu :=
        (integral_finsetSum s (fun g _ => hF.comp_mul_left g)).symm
      _ = ∫ _ : G, ∑ g ∈ s, F g ∂mu := by simp_rw [hperm]
      _ = ∑ g ∈ s, F g := by simp
  have hcard : (s.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr ⟨1, hs 1⟩)
  rw [← hsum, smul_smul, inv_mul_cancel₀ hcard, one_smul]

end S05P047

open scoped ComplexConjugate BigOperators Matrix.Norms.Elementwise
open MeasureTheory

namespace S05P047

local instance hsMatrixContinuousENorm {n : ℕ} :
    ContinuousENorm (Matrix (Fin n) (Fin n) ℂ) :=
  SeminormedAddGroup.toContinuousENorm

/-- The coordinate Hilbert--Schmidt pairing is the trace pairing. -/
theorem hs_eq_trace {n : ℕ} (Y X : Matrix (Fin n) (Fin n) ℂ) :
    (∑ a, ∑ b, conj (Y a b) * X a b) = Matrix.trace (Y.conjTranspose * X) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.star_def]
  exact Finset.sum_comm

/-- Unitary conjugation preserves pairing with every commuting matrix. -/
theorem hs_conjugate_eq {n : ℕ} (U X Y : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hcomm : U * Y = Y * U) :
    (∑ a, ∑ b, conj (Y a b) * (U * X * U.conjTranspose) a b) =
      ∑ a, ∑ b, conj (Y a b) * X a b := by
  have hinv : U.conjTranspose * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hstar : Y.conjTranspose * U.conjTranspose =
      U.conjTranspose * Y.conjTranspose := by
    simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hcomm
  have hy : U.conjTranspose * Y.conjTranspose * U = Y.conjTranspose := by
    rw [← hstar, Matrix.mul_assoc, hinv, Matrix.mul_one]
  rw [hs_eq_trace, hs_eq_trace]
  calc
    Matrix.trace (Y.conjTranspose * (U * X * U.conjTranspose)) =
        Matrix.trace ((Y.conjTranspose * U) * X * U.conjTranspose) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = Matrix.trace ((U.conjTranspose * (Y.conjTranspose * U)) * X) :=
      Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (Y.conjTranspose * X) := by
      rw [← Matrix.mul_assoc U.conjTranspose Y.conjTranspose U, hy]

/-- The pairing with a fixed matrix is continuous for the exact elementwise norm. -/
def hsCLM {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ where
  toFun X := ∑ a, ∑ b, conj (Y a b) * X a b
  map_add' X Z := by
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c X := by
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    exact mul_left_comm _ _ _
  cont := continuous_finsetSum _ (fun a _ => continuous_finsetSum _
    (fun b _ => continuous_const.mul ((continuous_apply b).comp (continuous_apply a))))

@[simp]
theorem hsCLM_apply {n : ℕ} (Y X : Matrix (Fin n) (Fin n) ℂ) :
    hsCLM Y X = ∑ a, ∑ b, conj (Y a b) * X a b := rfl

/-- The Hilbert--Schmidt functional commutes with the Bochner integral. -/
theorem hs_integral {G : Type*} [MeasurableSpace G] (mu : Measure G) {n : ℕ}
    (Y : Matrix (Fin n) (Fin n) ℂ) (F : G → Matrix (Fin n) (Fin n) ℂ)
    (hF : Integrable F mu) :
    (∑ a, ∑ b, conj (Y a b) * (∫ g, F g ∂mu) a b) =
      ∫ g, (∑ a, ∑ b, conj (Y a b) * F g a b) ∂mu := by
  change hsCLM Y (∫ g, F g ∂mu) = ∫ g, hsCLM Y (F g) ∂mu
  exact ((hsCLM Y).integral_comp_comm hF).symm

/-- A probability average of unitary conjugations is orthogonal to its error
against every matrix commuting with all the conjugating unitaries. -/
theorem hs_average_orthogonal {G : Type*} [MeasurableSpace G]
    (mu : Measure G) [IsProbabilityMeasure mu] {n : ℕ}
    (rho : G → Matrix (Fin n) (Fin n) ℂ) (X Y : Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ g, rho g ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hcomm : ∀ g, rho g * Y = Y * rho g)
    (hF : Integrable (fun g => rho g * X * (rho g).conjTranspose) mu) :
    (∑ a, ∑ b, conj (Y a b) *
      (X - ∫ g, rho g * X * (rho g).conjTranspose ∂mu) a b) = 0 := by
  have hconst : (fun g => hsCLM Y (rho g * X * (rho g).conjTranspose)) =
      fun _ : G => hsCLM Y X := by
    funext g
    simp only [hsCLM_apply]
    exact hs_conjugate_eq (rho g) X Y (hU g) (hcomm g)
  have havg : hsCLM Y (∫ g, rho g * X * (rho g).conjTranspose ∂mu) =
      hsCLM Y X := by
    calc
      _ = ∫ g, hsCLM Y (rho g * X * (rho g).conjTranspose) ∂mu :=
        ((hsCLM Y).integral_comp_comm hF).symm
      _ = ∫ _g : G, hsCLM Y X ∂mu :=
        congrArg (fun F : G → ℂ => ∫ g, F g ∂mu) hconst
      _ = hsCLM Y X := by simp
  calc
    _ = hsCLM Y (X - ∫ g, rho g * X * (rho g).conjTranspose ∂mu) :=
      (hsCLM_apply _ _).symm
    _ = hsCLM Y X - hsCLM Y (∫ g, rho g * X * (rho g).conjTranspose ∂mu) :=
      map_sub _ _ _
    _ = 0 := by rw [havg, sub_self]

end S05P047

open MeasureTheory
open scoped ComplexConjugate BigOperators Matrix.Norms.Elementwise

local instance rootMatrixContinuousENorm {n : ℕ} :
    ContinuousENorm (Matrix (Fin n) (Fin n) ℂ) :=
  SeminormedAddGroup.toContinuousENorm

-- The following type unfolds the three transparent public definitions verbatim.
-- Its equality to the published root is separately checked in P047InterfaceCertificate.
/-- PDF p.4, Eq.(8): the normalized Haar average is the Hilbert–Schmidt
projection onto the full commutant, including its finite-group formula.
No Hermitian, positivity, or trace-one restriction is placed on X. -/
theorem solution {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (mu : Measure G) [Measure.IsHaarMeasure mu] [Measure.Regular mu]
    [IsProbabilityMeasure mu] {n : ℕ}
    (rho : G → Matrix (Fin n) (Fin n) ℂ) (hrho : rho 1 = 1 ∧ (∀ g h, rho (g * h) = rho g * rho h) ∧
      (∀ g, rho g ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧ Continuous rho)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    (∀ a b : Fin n, Integrable (fun g => (rho g * X * (rho g).conjTranspose) a b) mu) ∧
    (∀ g, rho g * (∫ g, rho g * X * (rho g).conjTranspose ∂mu) = (∫ g, rho g * X * (rho g).conjTranspose ∂mu) * rho g) ∧
    ((∀ g, rho g * X = X * rho g) → (∫ g, rho g * X * (rho g).conjTranspose ∂mu) = X) ∧
    (∀ Y : Matrix (Fin n) (Fin n) ℂ, (∀ g, rho g * Y = Y * rho g) →
      (∑ a, ∑ b, conj (Y a b) * (X - (∫ g, rho g * X * (rho g).conjTranspose ∂mu)) a b) = 0) ∧
    (∀ s : Finset G, (∀ g, g ∈ s) →
      (∫ g, rho g * X * (rho g).conjTranspose ∂mu) = (s.card : ℂ)⁻¹ •
        ∑ g ∈ s, rho g * X * (rho g).conjTranspose)  := by
  rcases hrho with ⟨_, hmul, hunit, hcont⟩
  have hF : Integrable (fun g => rho g * X * (rho g).conjTranspose) mu :=
    S05P047.integrable_conjugate rho hcont X
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    exact ContinuousLinearMap.integrable_comp
      ((ContinuousLinearMap.proj b : (Fin n → ℂ) →L[ℂ] ℂ).comp
        (ContinuousLinearMap.proj a : Matrix (Fin n) (Fin n) ℂ →L[ℂ] (Fin n → ℂ))) hF
  · intro g
    exact S05P047.haar_commutes rho hmul hunit X hF g
  · intro hcomm
    exact S05P047.haar_fixed rho hunit X hcomm
  · intro Y hY
    exact S05P047.hs_average_orthogonal mu rho X Y hunit hY hF
  · intro s hs
    exact S05P047.finite_haar_integral mu
      (fun g => rho g * X * (rho g).conjTranspose) hF s hs



end

#print axioms solution
