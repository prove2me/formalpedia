-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.lemma39_hermiticity
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T05:11:20.384188+00:00
-- url     : https://prove2.me/submissions/48d89c0a-a8ae-4643-bea9-cf04be11007e

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
set_option backward.isDefEq.respectTransparency false

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

/-- PDF p.16 Lemma 39 Eq.(84), Appendix B p.39: all-operators adjoint preservation. -/
theorem solution (D : Data G A n) (Phi : EndMat n) (hPhi : IsIrrepCovariant D.U Phi) :
    (choi Phi).IsHermitian ↔ ∀ X : Mat n, (Phi X)ᴴ = Phi Xᴴ := by
  classical
  constructor
  · intro h X
    have hb (a b : Fin n) : (Phi (matrixUnit a b))ᴴ = Phi (matrixUnit b a) := by
      ext i j
      exact congrArg (fun C : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ => C (b,i) (a,j)) h
    have hx : X = ∑ a, ∑ b, X a b • matrixUnit a b := by
      ext i j
      simp only [Matrix.sum_apply]
      change X i j = ∑ a, ∑ b, X a b * matrixUnit a b i j
      simp [matrixUnit, Matrix.single_apply, ite_and]
    have hf := congrArg Phi hx
    simp only [map_sum, map_smul] at hf
    have hstar : (∑ a, ∑ b, conj (X a b) • matrixUnit b a) = Xᴴ := by
      ext i j
      simp only [Matrix.sum_apply]
      change (∑ a, ∑ b, conj (X a b) * matrixUnit b a i j) = conj (X j i)
      simp [matrixUnit, Matrix.single_apply, ite_and]
    calc
      _ = (∑ a, ∑ b, X a b • Phi (matrixUnit a b))ᴴ := congrArg Matrix.conjTranspose hf
      _ = ∑ a, ∑ b, conj (X a b) • Phi (matrixUnit b a) := by
        simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, hb, Complex.star_def]
      _ = Phi (∑ a, ∑ b, conj (X a b) • matrixUnit b a) := by simp only [map_sum, map_smul]
      _ = _ := congrArg Phi hstar
  · intro h
    apply Matrix.ext
    rintro ⟨a,i⟩ ⟨b,j⟩
    have hh := congrArg (fun X : Mat n => X i j) (h (matrixUnit b a))
    have he : (matrixUnit b a)ᴴ = matrixUnit a b := by simp [matrixUnit]
    rw [he] at hh
    simpa only [choi, matrixUnit, Matrix.conjTranspose_apply] using hh
