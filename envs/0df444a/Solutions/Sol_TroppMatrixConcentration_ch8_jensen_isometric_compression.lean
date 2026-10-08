-- Prove2me | solution 1 for TroppMatrixConcentration.ch8_jensen_isometric_compression
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:51:40.060448+00:00
-- url     : https://prove2.me/submissions/223d162c-c850-48b3-a1f2-be1565f686e5

import Theorems.Thm_TroppMatrixConcentration_ch8_jensen_block_calculus
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic.NoncommRing
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Reindex

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open TroppMatrixConcentration
set_option autoImplicit false

private noncomputable def reindexStar {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) :
    Matrix ι ι ℂ ≃⋆ₐ[ℝ] Matrix κ κ ℂ :=
  { Matrix.reindexAlgEquiv ℝ ℂ e with
    map_star' := by intro A; rfl
    map_smul' := by intro r A; rfl }

private lemma reindex_cfc {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Nonempty ι] [Nonempty κ]
    (e : ι ≃ κ) (f : ℝ → ℝ) (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    reindexStar e (cfc f A) = cfc f (reindexStar e A) := by
  have hs : spectrum ℝ (reindexStar e A) = spectrum ℝ A :=
    AlgEquiv.spectrum_eq (reindexStar e).toAlgEquiv A
  by_cases hf : ContinuousOn f (spectrum ℝ A)
  · exact StarAlgHomClass.map_cfc (reindexStar e) f A hf
      (reindexStar e).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional hA
      (hA.submatrix _)
  · rw [cfc_apply_of_not_continuousOn A hf, map_zero,
      cfc_apply_of_not_continuousOn _ (by rwa [hs])]

lemma ch8_operatorConvexOn_finite {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (I : Set ℝ) (f : ℝ → ℝ) (hf : ch8_operatorConvexOn I f)
    (A H : Matrix ι ι ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian)
    (hAsp : spectrum ℝ A ⊆ I) (hHsp : spectrum ℝ H ⊆ I)
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    loewnerLE (ch8_matrixFunction f (t • A + (1-t) • H))
      (t • ch8_matrixFunction f A + (1-t) • ch8_matrixFunction f H) := by
  let e := Fintype.equivFin ι
  let E := reindexStar e
  have hs (B : Matrix ι ι ℂ) : spectrum ℝ (E B) = spectrum ℝ B :=
    AlgEquiv.spectrum_eq E.toAlgEquiv B
  have h := hf.2 (Fintype.card ι) inferInstance (E A) (E H)
    (hA.submatrix _) (hH.submatrix _) (by rwa [hs]) (by rwa [hs]) t ht₀ ht₁
  have hmix : (t • A + (1-t) • H).IsHermitian := (hA.smul (IsSelfAdjoint.all t)).add (hH.smul (IsSelfAdjoint.all (1-t)))
  change (t • cfc f (E A) + (1-t) • cfc f (E H) - cfc f (t • E A + (1-t) • E H)).PosSemidef at h
  have hm : t • E A + (1-t) • E H = E (t • A + (1-t) • H) := by simp
  rw [hm, ← reindex_cfc e f A hA, ← reindex_cfc e f H hH,
    ← reindex_cfc e f _ hmix, ← map_smul E, ← map_smul E, ← map_add E,
    ← map_sub E] at h
  have hh := h.submatrix e
  simpa [E, reindexStar, Matrix.reindexAlgEquiv, Matrix.reindex_apply,
    ch8_matrixFunction, loewnerLE, Matrix.submatrix_submatrix] using hh

private lemma unitary_calculus {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (U A : Matrix ι ι ℂ) (hU : U.conjTranspose = U) (hU2 : U * U = 1)
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (U * A * U).IsHermitian ∧ spectrum ℝ (U * A * U) = spectrum ℝ A ∧
    cfc f (U * A * U) = U * cfc f A * U := by
  have hunit : U ∈ unitary (Matrix ι ι ℂ) := by
    constructor <;> simpa only [Matrix.star_eq_conjTranspose, hU] using hU2
  let u : unitary (Matrix ι ι ℂ) := ⟨U, hunit⟩
  let E := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℂ) u
  have he (M : Matrix ι ι ℂ) : E M = U * M * U := by
    change U * M * U.conjTranspose = _
    rw [hU]
  have hh : (U * A * U).IsHermitian := by
    simpa only [hU] using Matrix.isHermitian_mul_mul_conjTranspose U hA
  refine ⟨hh, ?_, ?_⟩
  · rw [← he]; exact AlgEquiv.spectrum_eq E.toAlgEquiv A
  · rw [← he, ← he]
    symm
    exact StarAlgHomClass.map_cfc E f A (A.finite_real_spectrum.continuousOn f)
      E.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional hA
      (by rwa [he])

private lemma pinching {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Nonempty ι] [Nonempty κ]
    (I : Set ℝ) (f : ℝ → ℝ) (hf : ch8_operatorConvexOn I f)
    (X : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) (hX : X.IsHermitian)
    (hXI : spectrum ℝ X ⊆ I) :
    loewnerLE (cfc f (X.submatrix Sum.inr Sum.inr))
      ((cfc f X).submatrix Sum.inr Sum.inr) := by
  let V : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ := Matrix.fromBlocks 1 0 0 (-1)
  have hV : V.conjTranspose = V := by simp [V, Matrix.fromBlocks_conjTranspose]
  have hV2 : V * V = 1 := by
    simp [V, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  have hcalc := unitary_calculus V X hV hV2 hX f
  have hh := ch8_operatorConvexOn_finite I f hf X (V * X * V) hX hcalc.1 hXI
    (by rwa [hcalc.2.1]) (1/2) (by norm_num) (by norm_num)
  have hmid : (1/2 : ℝ) • X + (1 - (1/2 : ℝ)) • (V * X * V) =
      Matrix.fromBlocks (X.submatrix Sum.inl Sum.inl) 0 0 (X.submatrix Sum.inr Sum.inr) := by
    rw [← Matrix.fromBlocks_toBlocks X]
    simp only [V, Matrix.fromBlocks_multiply, one_mul, mul_one, neg_mul, mul_neg]
    ext i j <;> cases i <;> cases j <;> simp <;> ring
  unfold loewnerLE at hh
  rw [hmid, (ch8_jensen_block_calculus _ _ (hX.submatrix _) (hX.submatrix _) f).2.2] at hh
  have hr := hh.submatrix Sum.inr
  unfold loewnerLE
  convert hr using 1
  simp only [ch8_matrixFunction]
  rw [hcalc.2.2]
  ext i j
  simp [V, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  ring

private theorem ch8_jensen_reflection_algebra
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (K : Matrix ι κ ℂ) (hK : K.conjTranspose * K = 1)
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    let U := Matrix.fromBlocks (1 - K * K.conjTranspose) K K.conjTranspose 0
    U.IsHermitian ∧ U * U = 1 ∧
      (U * Matrix.fromBlocks A 0 0 B * U).toBlocks₂₂ = K.conjTranspose * A * K := by
  let P := 1 - K * K.conjTranspose
  have hP : P.IsHermitian := by
    simp only [P, Matrix.IsHermitian, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hPK : P * K = 0 := by
    simp only [P, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hK, Matrix.mul_one, sub_self]
  have hKP : K.conjTranspose * P = 0 := by
    simp only [P, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hK, Matrix.one_mul, sub_self]
  have hPP : P * P + K * K.conjTranspose = 1 := by
    calc
      P * P + K * K.conjTranspose = P - (P * K) * K.conjTranspose + K * K.conjTranspose := by
        rw [show P * P = P * (1 - K * K.conjTranspose) from rfl,
          Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc]
      _ = 1 := by rw [hPK]; simp [P]
  dsimp only
  refine ⟨hP.fromBlocks rfl (Matrix.isHermitian_zero), ?_, ?_⟩
  · rw [Matrix.fromBlocks_multiply]
    change Matrix.fromBlocks (P * P + K * K.conjTranspose) (P * K + K * 0)
      (K.conjTranspose * P + 0 * K.conjTranspose) (K.conjTranspose * K + 0 * 0) = 1
    simp only [hPP, hPK, hKP, hK, Matrix.mul_zero, Matrix.zero_mul, add_zero]
    exact Matrix.fromBlocks_one
  · simp only [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂,
      Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]



theorem solution
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (I : Set ℝ) (f : ℝ → ℝ) (hf : ch8_operatorConvexOn I f)
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (hAI : spectrum ℝ A ⊆ I)
    (K : Matrix ι κ ℂ) (hK : K.conjTranspose * K = 1) :
    loewnerLE (ch8_matrixFunction f (K.conjTranspose * A * K))
      (K.conjTranspose * ch8_matrixFunction f A * K) := by
  obtain ⟨c, hc⟩ := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) A hA
  let B : Matrix κ κ ℂ := algebraMap ℝ _ c
  have hB : B.IsHermitian := by
    change (algebraMap ℝ (Matrix κ κ ℂ) c).IsHermitian
    rw [Algebra.algebraMap_eq_smul_one]
    exact Matrix.isHermitian_one.smul (IsSelfAdjoint.all c)
  let D := Matrix.fromBlocks A 0 0 B
  have hD := ch8_jensen_block_calculus A B hA hB f
  have hDI : spectrum ℝ D ⊆ I := by
    rw [hD.2.1]
    apply Set.union_subset hAI
    change spectrum ℝ (algebraMap ℝ (Matrix κ κ ℂ) c) ⊆ I
    rw [spectrum.scalar_eq]
    exact Set.singleton_subset_iff.mpr (hAI hc)
  let U := Matrix.fromBlocks (1 - K * K.conjTranspose) K K.conjTranspose 0
  have hr := ch8_jensen_reflection_algebra K hK A B
  have hu : U.conjTranspose = U := hr.1
  have hu2 : U * U = 1 := hr.2.1
  have hcalc := unitary_calculus U D hu hu2 hD.1 f
  have hp := pinching I f hf (U * D * U) hcalc.1 (by rwa [hcalc.2.1])
  have hcorner : (U * D * U).submatrix Sum.inr Sum.inr = K.conjTranspose * A * K := hr.2.2
  rw [hcorner, hcalc.2.2] at hp
  have hcfc : (U * cfc f D * U).submatrix Sum.inr Sum.inr =
      K.conjTranspose * cfc f A * K := by
    rw [show cfc f D = Matrix.fromBlocks (cfc f A) 0 0 (cfc f B) from hD.2.2]
    exact (ch8_jensen_reflection_algebra K hK (cfc f A) (cfc f B)).2.2
  rw [hcfc] at hp
  exact hp
