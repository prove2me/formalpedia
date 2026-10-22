-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P08.split_algebra_has_jm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:20:04.141997+00:00
-- url     : https://prove2.me/submissions/3f24b232-ecfa-4bf0-9aa3-db2085aa1ca5

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Support21.P08
open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)
open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

lemma g67e_single_mul {K : Type*} [Field K] {m : ℕ} (s t : Fin m) (X : Matrix (Fin m) (Fin m) K) :
    Matrix.single s t (1 : K) * X = ∑ v : Fin m, X t v • Matrix.single s v (1 : K) := by
  ext a b
  rw [Matrix.sum_apply]
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  by_cases ha : s = a
  · simp [ha]
  · simp [ha]

lemma g67e_single_mul_diag {K : Type*} [Field K] {m : ℕ} (s t : Fin m) (f : Fin m → K) :
    Matrix.single s t (1 : K) * Matrix.diagonal f = f t • Matrix.single s t (1 : K) := by
  ext a b
  rw [Matrix.mul_diagonal]
  simp only [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  split_ifs with h1 h2 h2 <;> simp_all

theorem g67e_split {K A : Type*} [Field K] [Ring A] [Algebra K A]
    (r : ℕ) (d : Fin r → ℕ)
    (e : A ≃ₐ[K] ∀ i : Fin r, Matrix (Fin (d i)) (Fin (d i)) K) :
    ∃ D : CellDatum (R := K) (A := A) (T := fun i : Fin r => Fin (d i)),
      ∃ J : JMFamily D (∑ i, d i), separatesAll J := by
  let P := ∀ i : Fin r, Matrix (Fin (d i)) (Fin (d i)) K
  let ε : CellIndex (Fin r) (fun i : Fin r => Fin (d i)) → P :=
    fun z => Pi.single z.1 (Matrix.single z.2.1 z.2.2 (1 : K))
  let B0 : Module.Basis (CellIndex (Fin r) (fun i : Fin r => Fin (d i))) K P :=
    Pi.basis (fun i => Matrix.stdBasis K (Fin (d i)) (Fin (d i)))
  have hB0 : ∀ z, B0 z = ε z := by
    intro z; simp only [B0, ε]; rw [Pi.basis_apply, Matrix.stdBasis_eq_single]
  let B := B0.map e.symm.toLinearEquiv
  have hB : ∀ z, e (B z) = ε z := by
    intro z; simp [B, hB0]
  let tr : P →ₗ[K] P :=
    { toFun := fun y i => (y i).transpose
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let st : A →ₗ[K] A := e.symm.toLinearMap ∘ₗ tr ∘ₗ e.toLinearMap
  have hst : ∀ x, e (st x) = fun i => (e x i).transpose := by
    intro x
    show e (e.symm (tr (e x))) = _
    rw [AlgEquiv.apply_symm_apply]; rfl
  have hsingle_tr : ∀ (l : Fin r) (X : Matrix (Fin (d l)) (Fin (d l)) K),
      (fun i => (Pi.single (M := fun i => Matrix (Fin (d i)) (Fin (d i)) K) l X i).transpose) =
        Pi.single l X.transpose := by
    intro l X; funext i
    by_cases h : i = l
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  let D : CellDatum (R := K) (A := A) (T := fun i : Fin r => Fin (d i)) :=
    { basis := B
      star := st
      star_involutive := by
        intro x; apply e.injective; rw [hst, hst]; simp
      star_mul := by
        intro x y; apply e.injective
        rw [hst, map_mul, map_mul, hst, hst]
        funext i; simp [Matrix.transpose_mul]
      star_basis := by
        intro l s t; apply e.injective
        rw [hst, hB, hB]
        simp only [ε]
        rw [hsingle_tr, Matrix.transpose_single]
      multiplication := by
        intro l t x
        refine ⟨fun v => e x l t v, fun s => ?_⟩
        have : B ⟨l, (s, t)⟩ * x - ∑ v : Fin (d l), e x l t v • B ⟨l, (s, v)⟩ = 0 := by
          apply e.injective
          rw [map_sub, map_mul, map_sum, hB, map_zero, sub_eq_zero]
          simp only [map_smul, hB, ε]
          funext i
          by_cases h : i = l
          · subst h
            simp only [Pi.mul_apply, Pi.single_eq_same, Finset.sum_apply, Pi.smul_apply]
            exact g67e_single_mul s t (e x i)
          · simp [Pi.single_eq_of_ne h]
        rw [this]; exact Submodule.zero_mem _ }
  let σ := (finSigmaFinEquiv (n := d)).symm
  let Dg : Fin (∑ i, d i) → P := fun k i =>
    Matrix.diagonal (fun q => if (⟨i, q⟩ : (i : Fin r) × Fin (d i)) = σ k then (1 : K) else 0)
  let J : JMFamily D (∑ i, d i) :=
    { L := fun k => e.symm (Dg k)
      content := fun t k => if t = σ k then 1 else 0
      commuting := by
        intro i j; apply e.injective
        simp only [map_mul, AlgEquiv.apply_symm_apply]
        funext a
        simp only [Pi.mul_apply, Dg, Matrix.diagonal_mul_diagonal]
        congr 1; funext q; ring
      fixed := by
        intro k; apply e.injective
        show e (st _) = _
        rw [hst]; funext i
        simp [Dg, Matrix.diagonal_transpose]
      triangular := by
        intro l t k
        refine ⟨0, fun s => ?_⟩
        have : B ⟨l, (s, t)⟩ * e.symm (Dg k) -
            (if (⟨l, t⟩ : (i : Fin r) × Fin (d i)) = σ k then (1 : K) else 0) • B ⟨l, (s, t)⟩ = 0 := by
          apply e.injective
          rw [map_sub, map_mul, map_smul, hB, AlgEquiv.apply_symm_apply, map_zero, sub_eq_zero]
          simp only [ε]
          funext i
          by_cases h : i = l
          · subst h
            simp only [Pi.mul_apply, Pi.single_eq_same, Pi.smul_apply, Dg]
            rw [g67e_single_mul_diag]
          · simp [Pi.single_eq_of_ne h]
        simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, sub_zero]
        rw [this]; exact Submodule.zero_mem _ }
  refine ⟨D, J, ?_⟩
  intro t t' h
  have h1 := congrFun h (σ.symm t)
  simp only [J, Equiv.apply_symm_apply, if_true] at h1
  by_contra hne
  have : t' ≠ t := fun e => hne e.symm
  rw [if_neg this] at h1
  exact one_ne_zero h1

section WedderburnExample

theorem solution {K A : Type*} [Field K] [Ring A] [Algebra K A]
    (r : ℕ) (d : Fin r → ℕ) (hd : ∀ i, 0 < d i)
    (e : A ≃ₐ[K] ∀ i : Fin r, Matrix (Fin (d i)) (Fin (d i)) K) :
    ∃ D : CellDatum (R := K) (A := A) (T := fun i : Fin r => Fin (d i)),
      ∃ J : JMFamily D (∑ i, d i), separatesAll J := g67e_split r d e

end WedderburnExample
