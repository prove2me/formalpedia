-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P88.basic_construction_trace_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-21T21:21:22.419299+00:00
-- url     : https://prove2.me/submissions/8d05f4fc-ed84-4704-a4a7-ece2103d08fe

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P88

attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

open QAlgorithms.Papers.Independent.Information100.P65 (hookLength)

open QAlgorithms.Papers.Independent.Renew46.P30 (TensorIndex)

universe u v w x y

theorem basic_construction_trace_coefficients (F A B I J : Type*)
    [Field F] [IsAlgClosed F] [Ring A] [Algebra F A] [FiniteDimensional F A]
    [Ring B] [Algebra F B] [FiniteDimensional F B]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (da : I → ℕ) (db : J → ℕ) (ha : ∀ i, 0 < da i) (_hb : ∀ j, 0 < db j)
    (ea : A ≃ₐ[F] ((i : I) → Matrix (Fin (da i)) (Fin (da i)) F))
    (eb : B ≃ₐ[F] ((j : J) → Matrix (Fin (db j)) (Fin (db j)) F))
    (inc : A →ₐ[F] B) (_hinj : Function.Injective inc) (eps : B →ₗ[F] A)
    (_hleft : ∀ a b, eps (inc a * b) = a * eps b)
    (_hright : ∀ a b, eps (b * inc a) = eps b * a)
    (ca : I → F) (cb : J → F)
    (_htrace : ∀ b, splitTrace da ea ca (eps b) = splitTrace db eb cb b)
    (mu : I) (lam : J) (j : Fin (da mu) ↪ Fin (db lam))
    (_hcolumn : ∀ a, eb (inc a) lam * edgeMatrix (F := F) j = edgeMatrix j * ea a mu)
    (_hrow : ∀ a, (edgeMatrix (F := F) j).transpose * eb (inc a) lam =
      ea a mu * (edgeMatrix j).transpose) :
    let p : Fin (da mu) := ⟨0, ha mu⟩
    let scalar : F := ea (eps (splitMatrixUnit db eb lam (j p) (j p))) mu p p
    (∀ q : Fin (da mu), eps (splitMatrixUnit db eb lam (j q) (j q)) =
      scalar • splitMatrixUnit da ea mu q q) ∧ cb lam = scalar * ca mu := by
  intro p scalar
  set uA : Fin (da mu) → Fin (da mu) → A := fun q q' => splitMatrixUnit da ea mu q q' with huA
  set fB : Fin (db lam) → Fin (db lam) → B := fun r s => splitMatrixUnit db eb lam r s with hfB'
  have hfB : ∀ r s, eb (fB r s) = Pi.single lam (Matrix.single r s 1) := by
    intro r s; simp [fB, splitMatrixUnit]
  have hfA : ∀ r s, ea (uA r s) = Pi.single mu (Matrix.single r s 1) := by
    intro r s; simp [uA, splitMatrixUnit]
  have col : ∀ q q' x, eb (inc (uA q q')) lam x (j q') = if x = j q then 1 else 0 := by
    intro q q' x
    have := congrFun (congrFun (_hcolumn (uA q q')) x) q'
    have key : (eb (inc (uA q q')) lam * edgeMatrix (F := F) j) x q' = eb (inc (uA q q')) lam x (j q') := by
      simp [Matrix.mul_apply, edgeMatrix]
    rw [← key, this, hfA, Pi.single_eq_same]
    show (∑ r, edgeMatrix (F := F) j x r * Matrix.single q q' (1:F) r q') = _
    simp only [edgeMatrix, Matrix.single_apply, Matrix.transpose_apply]
    simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  have row : ∀ q q' y, eb (inc (uA q' q)) lam (j q') y = if y = j q then 1 else 0 := by
    intro q q' y
    have := congrFun (congrFun (_hrow (uA q' q)) q') y
    have key : ((edgeMatrix (F := F) j)ᵀ * eb (inc (uA q' q)) lam) q' y = eb (inc (uA q' q)) lam (j q') y := by
      simp [Matrix.mul_apply, edgeMatrix]
    rw [← key, this, hfA, Pi.single_eq_same]
    show (∑ r, Matrix.single q' q (1:F) q' r * (edgeMatrix (F := F) j)ᵀ r y) = _
    simp only [edgeMatrix, Matrix.single_apply, Matrix.transpose_apply]
    simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
    rw [Finset.sum_eq_single q]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  have L1 : ∀ q q', inc (uA q q') * fB (j q') (j q') = fB (j q) (j q') := by
    intro q q'
    apply eb.injective
    rw [map_mul, hfB, hfB]
    ext i x y
    by_cases hi : i = lam
    · subst hi
      simp only [Pi.mul_apply, Pi.single_eq_same, Matrix.mul_apply, Matrix.single_apply, ite_and]
      simp [Finset.sum_ite_eq, Finset.sum_ite_eq', col]
      split_ifs <;> (try rfl) <;> (exfalso; aesop)
    · simp [hi]
  have L2 : ∀ q q', fB (j q) (j q') * inc (uA q' q) = fB (j q) (j q) := by
    intro q q'
    apply eb.injective
    rw [map_mul, hfB, hfB]
    ext i x y
    by_cases hi : i = lam
    · subst hi
      simp only [Pi.mul_apply, Pi.single_eq_same, Matrix.mul_apply, Matrix.single_apply, ite_and]
      simp [Finset.sum_ite_eq, Finset.sum_ite_eq', row]
      split_ifs <;> (try rfl) <;> (exfalso; aesop)
    · simp [hi]
  have conj : ∀ q q', eps (fB (j q) (j q)) = uA q q' * eps (fB (j q') (j q')) * uA q' q := by
    intro q q'
    rw [← L2 q q', ← L1 q q', _hright, _hleft]
  -- the matrix entries
  have diag : ∀ q, eps (fB (j q) (j q)) = ea (eps (fB (j q) (j q))) mu q q • uA q q := by
    intro q
    apply ea.injective
    conv_lhs => rw [conj q q]
    rw [map_mul, map_mul, hfA, map_smul, hfA]
    ext i x y
    by_cases hi : i = mu
    · subst hi
      simp only [Pi.mul_apply, Pi.smul_apply, Pi.single_eq_same, Matrix.mul_apply, Matrix.single_apply,
        Matrix.smul_apply, ite_and]
      simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
      split_ifs <;> simp_all
    · simp [hi]
  have same : ∀ q, ea (eps (fB (j q) (j q))) mu q q = scalar := by
    intro q
    have h := conj q p
    rw [diag p] at h
    have := congrArg (fun b => ea b mu q q) h
    simp only [map_mul, map_smul, hfA, Pi.mul_apply, Pi.smul_apply, Pi.single_eq_same,
      Matrix.mul_apply, Matrix.single_apply, Matrix.smul_apply, ite_and] at this
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq'] at this
    rw [this]
  have hdiag : ∀ q, eps (fB (j q) (j q)) = scalar • uA q q := by
    intro q; have := diag q; rw [same q] at this; exact this
  refine ⟨hdiag, ?_⟩
  · have h := _htrace (fB (j p) (j p))
    rw [hdiag p] at h
    simp only [splitTrace, map_smul, hfA, hfB] at h
    rw [Finset.sum_eq_single mu, Finset.sum_eq_single lam] at h
    · simp [Matrix.trace, Matrix.single_apply, Finset.sum_ite_eq'] at h
      first | linear_combination h | linear_combination -h
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · intro hh; exact absurd (Finset.mem_univ _) hh
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · intro hh; exact absurd (Finset.mem_univ _) hh

theorem _root_.solution (F A B I J : Type*)
    [Field F] [IsAlgClosed F] [Ring A] [Algebra F A] [FiniteDimensional F A]
    [Ring B] [Algebra F B] [FiniteDimensional F B]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (da : I → ℕ) (db : J → ℕ) (ha : ∀ i, 0 < da i) (_hb : ∀ j, 0 < db j)
    (ea : A ≃ₐ[F] ((i : I) → Matrix (Fin (da i)) (Fin (da i)) F))
    (eb : B ≃ₐ[F] ((j : J) → Matrix (Fin (db j)) (Fin (db j)) F))
    (inc : A →ₐ[F] B) (_hinj : Function.Injective inc) (eps : B →ₗ[F] A)
    (_hleft : ∀ a b, eps (inc a * b) = a * eps b)
    (_hright : ∀ a b, eps (b * inc a) = eps b * a)
    (ca : I → F) (cb : J → F)
    (_htrace : ∀ b, splitTrace da ea ca (eps b) = splitTrace db eb cb b)
    (mu : I) (lam : J) (j : Fin (da mu) ↪ Fin (db lam))
    (_hcolumn : ∀ a, eb (inc a) lam * edgeMatrix (F := F) j = edgeMatrix j * ea a mu)
    (_hrow : ∀ a, (edgeMatrix (F := F) j).transpose * eb (inc a) lam =
      ea a mu * (edgeMatrix j).transpose) :
    let p : Fin (da mu) := ⟨0, ha mu⟩
    let scalar : F := ea (eps (splitMatrixUnit db eb lam (j p) (j p))) mu p p
    (∀ q : Fin (da mu), eps (splitMatrixUnit db eb lam (j q) (j q)) =
      scalar • splitMatrixUnit da ea mu q q) ∧ cb lam = scalar * ca mu :=
  basic_construction_trace_coefficients F A B I J da db ha _hb ea eb inc _hinj eps _hleft _hright
    ca cb _htrace mu lam j _hcolumn _hrow

end QAlgorithms.Papers.Independent.Intake100.P88
