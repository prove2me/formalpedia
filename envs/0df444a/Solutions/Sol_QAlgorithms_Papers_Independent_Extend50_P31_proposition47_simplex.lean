-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.proposition47_simplex
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T06:56:27.030895+00:00
-- url     : https://prove2.me/submissions/3166b2e2-56af-4e78-9776-e2fc3ba8934c

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
import Theorems.Thm_QuantumFiniteSpectral_orthonormal_spectrum_calculus
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_lemma29_choiBasis
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_proposition30_simultaneous
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_corollary35_positivity
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_proposition25_trace
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

private lemma cp_choi_positive (Phi : EndMat n) (hPhi : QAlgorithms.Entanglement.IsCompletelyPositive Phi) :
    (choi Phi).PosSemidef := by
  let v : Fin n × Fin n → ℂ := fun p => if p.1 = p.2 then 1 else 0
  have hp := Matrix.posSemidef_vecMulVec_self_star v
  have h := hPhi n (Matrix.vecMulVec v (star v)) hp
  have he : QAlgorithms.idTensorSuperop Phi (Matrix.vecMulVec v (star v)) = choi Phi := by
    ext p q
    change Phi (Matrix.of fun i j => v (p.1,i) * star v (q.1,j)) p.2 q.2 = Phi (matrixUnit p.1 q.1) p.2 q.2
    have hb : (Matrix.of fun i j => v (p.1,i) * star v (q.1,j)) = matrixUnit p.1 q.1 := by
      ext i j
      simp [v,matrixUnit,Matrix.single_apply,ite_and,Complex.star_def,eq_comm] <;> split_ifs <;> simp_all
    rw [hb]
  rw [he] at h
  exact h
private lemma trace_choi (Phi : EndMat n) : Matrix.trace (choi Phi) = ∑ i : Fin n, Matrix.trace (Phi (matrixUnit i i)) := by
  simp [choi,Matrix.trace,Matrix.diag_apply,Fintype.sum_prod_type,matrixUnit]
private lemma trace_choi_tp (Phi : EndMat n) (hPhi : TracePreserving Phi) : Matrix.trace (choi Phi) = (n : ℂ) := by
  rw [trace_choi]
  calc
    _ = ∑ i : Fin n, Matrix.trace (matrixUnit i i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hPhi (matrixUnit i i)
    _ = _ := by simp [matrixUnit]


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

/-- PDF p.20, Proposition 47 Eq.(105): inclusion in a simplex scaled by dim U. -/
theorem solution (D : Data G A n) (P : Pivots D) (l : OccurringIrrep D → ℂ)
    (hch : IsPaperChannel (spectralMap D l)) :
    choiEigenvalueVector D P l ∈ scaledSimplex D ∧
    choiEigenvalueVector D P l ∈ LinearMap.range (spectralMatrix D P).mulVecLin := by
  refine ⟨⟨?_,?_⟩,⟨l,rfl⟩⟩
  · have h := cp_choi_positive (spectralMap D l) hch.1
    have hl : trivialCoefficient D l = 1 := (proposition25_trace D l).mp hch.2
    exact ((corollary35_positivity D P l hl).2.1).mp h
  · rw [← (spectral_choi_calculus D P l).2.2]
    exact trace_choi_tp (spectralMap D l) hch.2

