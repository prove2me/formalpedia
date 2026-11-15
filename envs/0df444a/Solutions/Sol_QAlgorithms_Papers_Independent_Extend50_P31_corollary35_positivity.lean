-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.corollary35_positivity
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T06:53:58.373616+00:00
-- url     : https://prove2.me/submissions/fc875b66-7e53-405b-9c24-b38be497ef67

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
import Theorems.Thm_QuantumFiniteSpectral_orthonormal_spectrum_calculus
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_lemma29_choiBasis
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_proposition30_simultaneous
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31
open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)
open QAlgorithms.Papers.Independent.Information100.P34 (choi)
open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)
open scoped Matrix ComplexConjugate ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}
private lemma nonnegative_iff (z : ℂ) : NonnegativeScalar z ↔ 0 ≤ z := by
  simp only [NonnegativeScalar,Complex.nonneg_iff]
  tauto
private lemma choi_spectral (D : Data G A n) (l : OccurringIrrep D → ℂ) :
    choi (spectralMap D l) = ∑ a : OccurringIrrep D, l a • choi (centralMap D.U D.F a.val) := by
  ext p q
  simp [choi,spectralMap,LinearMap.sum_apply,Matrix.sum_apply]
private lemma spectral_choi_eigen (D : Data G A n) (P : Pivots D) (l : OccurringIrrep D → ℂ) (r : Row D) :
    (choi (spectralMap D l)).mulVec (choiVector D P r) = choiEigenvalueVector D P l r • choiVector D P r := by
  rw [choi_spectral,Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec,(proposition30_simultaneous D P).1,smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  change (∑ a : OccurringIrrep D, l a * spectralMatrix D P r a) = _
  simp only [choiEigenvalueVector,Matrix.mulVec,dotProduct]
  apply Finset.sum_congr rfl
  intro a ha
  ring
private lemma spectral_choi_calculus (D : Data G A n) (P : Pivots D) (l : OccurringIrrep D → ℂ) :
    (choi (spectralMap D l))ᴴ * choi (spectralMap D l) =
      choi (spectralMap D l) * (choi (spectralMap D l))ᴴ ∧
    ((choi (spectralMap D l)).PosSemidef ↔ ∀ r, 0 ≤ choiEigenvalueVector D P l r) ∧
    Matrix.trace (choi (spectralMap D l)) = ∑ r, choiEigenvalueVector D P l r := by
  exact QuantumFiniteSpectral.orthonormal_spectrum_calculus _ _ _ (lemma29_choiBasis D P).1 (lemma29_choiBasis D P).2 (spectral_choi_eigen D P l)


set_option autoImplicit false

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Extend50.P31
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq



open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

/-- PDF p.16, Corollary 35 Eq.(80), including the spectral equation and full complex reality. -/
theorem solution (D : Data G A n) (P : Pivots D) (l : OccurringIrrep D → ℂ)
    (hl : trivialCoefficient D l = 1) :
    (∀ r, (choi (spectralMap D l)).mulVec (choiVector D P r) =
      choiEigenvalueVector D P l r • choiVector D P r) ∧
    ((choi (spectralMap D l)).PosSemidef ↔ ∀ r, NonnegativeScalar (choiEigenvalueVector D P l r)) ∧
    (∀ r, choiEigenvalueVector D P l r = (Fintype.card G : ℂ)⁻¹ * ∑ g : G,
      (∑ a : OccurringIrrep D, l a * (D.F.dim a.val : ℂ) * character (D.F.irrep a.val) g⁻¹) *
        (Complex.normSq (Matrix.trace (eigenmatrix D P r * (D.U.rho g)ᴴ)) : ℂ)) := by
  refine ⟨spectral_choi_eigen D P l,?_,?_⟩
  · simpa only [nonnegative_iff] using (spectral_choi_calculus D P l).2.1
  · intro r
    simp only [choiEigenvalueVector,Matrix.mulVec,dotProduct,spectralMatrix,muAt,eigenmatrix,
      div_eq_mul_inv,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro g hg
    apply Finset.sum_congr rfl
    intro a ha
    ring
