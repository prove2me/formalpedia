-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.lemma2_leftRight
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T04:57:20.737888+00:00
-- url     : https://prove2.me/submissions/9ebf7830-225c-4cb1-883b-f302ed759f52

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

/-- PDF p.6, Lemma 2 Eq.(12). Families are chosen before the arbitrary operator X. -/
theorem solution (n : ℕ) (hn : 0 < n) (Phi : EndMat n) :
    ∃ m : ℕ, m ≤ n^2 ∧ ∃ A B : Fin m → Mat n,
      ∀ X : Mat n, Phi X = ∑ v, A v * X * (B v)ᴴ := by
  classical
  let A : (Fin n × Fin n) → Mat n := fun p => matrixUnit p.1 p.2
  let B : (Fin n × Fin n) → Mat n := fun p i j => conj (Phi (matrixUnit p.2 j) p.1 i)
  let e : Fin (n*n) ≃ (Fin n × Fin n) := finProdFinEquiv.symm
  refine ⟨n*n, by simp [pow_two], (fun v => A (e v)), (fun v => B (e v)), ?_⟩
  intro X
  have hx : X = ∑ a, ∑ b, X a b • matrixUnit a b := by
    ext i j
    simp only [Matrix.sum_apply]
    change X i j = ∑ a, ∑ b, X a b * (matrixUnit a b i j)
    simp [matrixUnit, Matrix.single_apply, ite_and]
  have hf := congrArg Phi hx
  simp only [map_sum, map_smul, RingHom.id_apply] at hf
  have hsum : (∑ v : Fin (n*n), A (e v) * X * (B (e v))ᴴ) =
      ∑ p : Fin n × Fin n, A p * X * (B p)ᴴ := by
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [hsum, hf]
  ext i j
  simp only [Matrix.sum_apply]
  change (∑ a, ∑ b, X a b * Phi (matrixUnit a b) i j) = _
  simp only [Fintype.sum_prod_type]
  change (∑ a, ∑ b, X a b * Phi (matrixUnit a b) i j) =
    ∑ a, ∑ b, ∑ c, (∑ d, matrixUnit a b i d * X d c) *
      conj (conj (Phi (matrixUnit b c) a j))
  simp [matrixUnit, Matrix.single_apply, ite_and, Complex.conj_conj]
