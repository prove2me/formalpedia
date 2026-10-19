-- Prove2me | solution 1 for QAlgorithms.GottesmanThesis.standardForm_exists
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T01:56:05.627293+00:00
-- url     : https://prove2.me/submissions/3a098066-b4b2-460b-a1df-41dff6115fb1

import Definitions.Def_QAlgorithms_Defs_BinaryStabilizer
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Logic.Equiv.Fintype

open Matrix Module
set_option autoImplicit false

private lemma sf_adapt_basis {K : Type*} [Field K] {r m : ℕ}
    (v : Fin r → (Fin m → K)) (hv : LinearIndependent K v) :
    ∃ b : Basis (Fin m) K (Fin m → K),
      ∀ i : Fin r, b ⟨i, lt_of_lt_of_le i.isLt (by simpa using hv.fintype_card_le_finrank)⟩ = v i := by
  classical
  have hr : r ≤ m := by simpa using hv.fintype_card_le_finrank
  let S := hv.linearIndepOn_id.extend (Set.subset_univ (Set.range v))
  let b : Basis S K (Fin m → K) := Basis.extend hv.linearIndepOn_id
  let q : Fin r → S := fun i => ⟨v i, hv.linearIndepOn_id.subset_extend _ ⟨i, rfl⟩⟩
  have hq : Function.Injective q := by
    intro i j h
    exact hv.injective (congrArg Subtype.val h)
  letI := Module.Finite.finite_basis b
  letI := Fintype.ofFinite S
  have hc : Fintype.card S = m := by
    simpa using (Module.finrank_eq_card_basis b).symm
  let e := Fintype.equivFinOfCardEq hc
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_extending_pair
    (fun i : Fin r => (⟨i, lt_of_lt_of_le i.isLt hr⟩ : Fin m))
    (fun i : Fin r => e (q i))
    (by intro i j h; exact Fin.ext (congrArg (fun x : Fin m => x.val) h))
    (e.injective.comp hq)
  refine ⟨b.reindex (e.trans τ.symm), ?_⟩
  intro i
  have hi : (e.trans τ.symm).symm ⟨i, lt_of_lt_of_le i.isLt hr⟩ = q i := by
    apply (e.trans τ.symm).injective
    simpa using (τ.symm_apply_eq.mpr (hτ i).symm).symm
  rw [Basis.reindex_apply, hi]
  exact Basis.extend_apply_self hv.linearIndepOn_id (q i)

private lemma sf_coord_mul {K : Type*} [Field K] {m n : ℕ}
    (b : Basis (Fin m) K (Fin m → K)) (A : Matrix (Fin m) (Fin n) K) :
    b.toMatrix (Pi.basisFun K (Fin m)) * A = b.toMatrix A.col := by
  have h : (Pi.basisFun K (Fin m)).toMatrix A.col = A := by
    ext i j
    simp [Basis.toMatrix_apply]
  simpa only [h] using b.toMatrix_mul_toMatrix (Pi.basisFun K (Fin m)) A.col

private lemma sf_columns {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) :
    ∃ G : Matrix.GeneralLinearGroup (Fin m) K, ∃ σ : Equiv.Perm (Fin n),
      (∀ (i : Fin m) (j : Fin n), (j : ℕ) < A.rank →
        ((G : Matrix (Fin m) (Fin m) K) * A.submatrix id σ) i j =
          if (i : ℕ) = (j : ℕ) then 1 else 0) ∧
      (∀ (i : Fin m) (j : Fin n), A.rank ≤ (i : ℕ) →
        ((G : Matrix (Fin m) (Fin m) K) * A.submatrix id σ) i j = 0) := by
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K A.col
  letI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hc : Fintype.card κ = A.rank := by
    rw [A.rank_eq_finrank_span_cols, ← hsp, finrank_span_eq_card hli]
  let e : Fin A.rank ≃ κ := (Fintype.equivFinOfCardEq hc).symm
  let p : Fin A.rank → Fin n := a ∘ e
  have hp : Function.Injective p := ha.comp e.injective
  have hv : LinearIndependent K (A.col ∘ p) := hli.comp e e.injective
  obtain ⟨b, hb⟩ := sf_adapt_basis (A.col ∘ p) hv
  have hrn : A.rank ≤ n := A.rank_le_width
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun j : Fin A.rank => (⟨j, lt_of_lt_of_le j.isLt hrn⟩ : Fin n)) p
    (by intro i j h; exact Fin.ext (congrArg (fun x : Fin n => x.val) h)) hp
  let G : Matrix.GeneralLinearGroup (Fin m) K :=
    ⟨b.toMatrix (Pi.basisFun K (Fin m)), (Pi.basisFun K (Fin m)).toMatrix b,
      b.toMatrix_mul_toMatrix_flip _, (Pi.basisFun K (Fin m)).toMatrix_mul_toMatrix_flip _⟩
  have heq : (G : Matrix (Fin m) (Fin m) K) * A.submatrix id σ =
      b.toMatrix (A.submatrix id σ).col := sf_coord_mul b _
  refine ⟨G, σ, ?_, ?_⟩
  · intro i j hj
    rw [heq, Basis.toMatrix_apply]
    have hcol : (A.submatrix id σ).col j = b ⟨j, lt_of_lt_of_le hj A.rank_le_height⟩ := by
      rw [hb ⟨j, hj⟩]
      change A.col (σ j) = A.col (p ⟨j, hj⟩)
      rw [hσ ⟨j, hj⟩]
    rw [hcol, b.repr_self]
    simp [Finsupp.single_apply, Fin.ext_iff, eq_comm]
  · intro i j hi
    rw [heq, Basis.toMatrix_apply]
    have hsp' : Submodule.span K (Set.range (A.col ∘ p)) =
        Submodule.span K (Set.range A.col) := by
      rw [show A.col ∘ p = (A.col ∘ a) ∘ e from rfl, e.surjective.range_comp, hsp]
    have hmem : (A.submatrix id σ).col j ∈ Submodule.span K (Set.range (A.col ∘ p)) := by
      rw [hsp']
      exact Submodule.subset_span ⟨σ j, rfl⟩
    have hzero : ∀ x ∈ Submodule.span K (Set.range (A.col ∘ p)), b.repr x i = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨q, rfl⟩ := hx
          rw [← hb q, b.repr_self]
          simp [Finsupp.single_apply, Fin.ext_iff, show (q : ℕ) ≠ i by omega]
      | zero => simp
      | add x y hx hy h1 h2 => simp [map_add, h1, h2]
      | smul c x hx h => simp [map_smul, h]
    exact hzero _ hmem

private lemma sf_change {m n : ℕ}
    (X Z : Matrix (Fin m) (Fin n) (ZMod 2))
    (h : QAlgorithms.IsBinaryStabilizerMatrix X Z)
    (G : Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) (σ : Equiv.Perm (Fin n)) :
    QAlgorithms.IsBinaryStabilizerMatrix
      ((G : Matrix (Fin m) (Fin m) (ZMod 2)) * X.submatrix id σ)
      ((G : Matrix (Fin m) (Fin m) (ZMod 2)) * Z.submatrix id σ) := by
  classical
  let g := (G : Matrix (Fin m) (Fin m) (ZMod 2))
  constructor
  · unfold QAlgorithms.SymplecticCommuting
    have hc : X.submatrix id σ * (Z.submatrix id σ)ᵀ +
        Z.submatrix id σ * (X.submatrix id σ)ᵀ = 0 := by
      simpa only [transpose_submatrix, submatrix_mul_equiv, submatrix_id_id, QAlgorithms.SymplecticCommuting] using h.1
    calc
      _ = g * (X.submatrix id σ * (Z.submatrix id σ)ᵀ +
          Z.submatrix id σ * (X.submatrix id σ)ᵀ) * gᵀ := by
            simp only [transpose_mul]
            simp only [g, mul_add, add_mul]
            simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hc]; simp
  · have h1 : LinearIndependent (ZMod 2) (g * fromCols X Z).row := by
      apply Matrix.vecMul_injective_iff.mp
      intro u v huv
      apply Matrix.vecMul_injective_of_isUnit G.isUnit
      have ih : Function.Injective (fun w : Fin m → ZMod 2 => w ᵥ* fromCols X Z) :=
        Matrix.vecMul_injective_iff.mpr h.2
      apply ih
      simpa only [vecMul_vecMul, g] using huv
    let τ := Equiv.sumCongr σ σ
    have h2 : LinearIndependent (ZMod 2) ((g * fromCols X Z).submatrix id τ).row := by
      apply Matrix.vecMul_injective_iff.mp
      intro u v huv
      apply Matrix.vecMul_injective_iff.mpr h1
      ext q
      have hh := congrFun huv (τ.symm q)
      simpa [vecMul, dotProduct] using hh
    have hh : fromCols ((G : Matrix (Fin m) (Fin m) (ZMod 2)) * X.submatrix id σ)
        ((G : Matrix (Fin m) (Fin m) (ZMod 2)) * Z.submatrix id σ) =
        (g * fromCols X Z).submatrix id τ := by
      ext i q
      cases q <;> simp [g, τ, Matrix.mul_apply]
    rw [hh]
    exact h2

private lemma sf_lower_independent {r s t : ℕ}
    (X Z : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin t) (ZMod 2))
    (hX1 : ∀ i j : Fin r, X (Sum.inl i) (Sum.inl j) = if i = j then 1 else 0)
    (hX0 : ∀ (i : Fin s) j, X (Sum.inr i) j = 0)
    (hc : X * Zᵀ + Z * Xᵀ = 0)
    (hli : LinearIndependent (ZMod 2) (fromCols X Z)) :
    LinearIndependent (ZMod 2) (Z.submatrix Sum.inr Sum.inr).row := by
  classical
  let D := Z.submatrix Sum.inr Sum.inl
  let E := Z.submatrix Sum.inr Sum.inr
  let A := X.submatrix Sum.inl Sum.inr
  have hDE : D + E * Aᵀ = 0 := by
    ext i j
    have hh := congrArg (fun B => B (Sum.inr i) (Sum.inl j)) hc
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hX0, hX1, mul_ite, D, E, A] using hh
  have hd : D = -(E * Aᵀ) := eq_neg_of_add_eq_zero_left hDE
  apply Matrix.vecMul_injective_iff.mp
  intro u v huv
  change u ᵥ* E = v ᵥ* E at huv
  have huvD : u ᵥ* D = v ᵥ* D := by
    rw [hd, vecMul_neg, vecMul_neg, ← vecMul_vecMul, ← vecMul_vecMul, huv]
  let u' : Fin r ⊕ Fin s → ZMod 2 := Sum.elim (fun _ => 0) u
  let v' : Fin r ⊕ Fin s → ZMod 2 := Sum.elim (fun _ => 0) v
  have heq : u' ᵥ* fromCols X Z = v' ᵥ* fromCols X Z := by
    ext q
    rcases q with (j | j)
    · simp [vecMul, dotProduct, Fintype.sum_sum_type, u', v', hX0]
    · rcases j with (j | j)
      · simpa [vecMul, dotProduct, Fintype.sum_sum_type, u', v', D] using congrFun huvD j
      · simpa [vecMul, dotProduct, Fintype.sum_sum_type, u', v', E] using congrFun huv j
  have hu := (Matrix.vecMul_injective_iff.mpr hli) heq
  funext i
  exact congrFun hu (Sum.inr i)

private lemma sf_reindex_li {K : Type*} [Field K] {m n m' n' : Type*}
    (A : Matrix m n K) (h : LinearIndependent K A.row) (e : m' ≃ m) (f : n' ≃ n) :
    LinearIndependent K (A.submatrix e f).row := by
  have hf : Function.Injective (LinearMap.funLeft K K f) := by
    intro u v huv
    ext j
    simpa using congrFun huv (f.symm j)
  exact (h.map' (LinearMap.funLeft K K f) (LinearMap.ker_eq_bot.mpr hf)).comp e e.injective

open QAlgorithms

theorem solution {m k : ℕ} (Hx Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2))
    (hS : IsBinaryStabilizerMatrix Hx Hz) :
    ∃ G : Matrix.GeneralLinearGroup (Fin m) (ZMod 2), ∃ σ : Equiv.Perm (Fin (m + k)),
      IsStandardForm Hx.rank ((G : Matrix (Fin m) (Fin m) (ZMod 2)) * Hx.submatrix id σ)
        ((G : Matrix (Fin m) (Fin m) (ZMod 2)) * Hz.submatrix id σ) := by
  classical
  let r := Hx.rank
  have hr : r ≤ m := Hx.rank_le_height
  have hrn : r ≤ m + k := hr.trans (Nat.le_add_right _ _)
  obtain ⟨G0, σ0, h0, hz0⟩ := sf_columns Hx
  let X := (G0 : Matrix (Fin m) (Fin m) (ZMod 2)) * Hx.submatrix id σ0
  let Z := (G0 : Matrix (Fin m) (Fin m) (ZMod 2)) * Hz.submatrix id σ0
  have hS0 := sf_change Hx Hz hS G0 σ0
  let em : Fin r ⊕ Fin (m - r) ≃ Fin m :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hr))
  let en : Fin r ⊕ Fin (m + k - r) ≃ Fin (m + k) :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hrn))
  let Xs := X.submatrix em en
  let Zs := Z.submatrix em en
  have hX1 : ∀ i j : Fin r, Xs (Sum.inl i) (Sum.inl j) = if i = j then 1 else 0 := by
    intro i j
    simpa [Xs, X, em, en, Fin.ext_iff] using
      h0 (em (Sum.inl i)) (en (Sum.inl j)) (by change (j : ℕ) < r; exact j.isLt)
  have hX0 : ∀ (i : Fin (m - r)) j, Xs (Sum.inr i) j = 0 := by
    intro i j
    exact hz0 _ _ (by change r ≤ r + (i : ℕ); omega)
  have hcs : Xs * Zsᵀ + Zs * Xsᵀ = 0 := by
    have hh := congrArg (fun A => A.submatrix em em) hS0.1
    change (X * Zᵀ + Z * Xᵀ).submatrix em em = 0 at hh
    simpa only [Xs, Zs, transpose_submatrix,
      submatrix_mul_equiv, submatrix_add, submatrix_zero, Pi.add_apply] using hh
  have hlis : LinearIndependent (ZMod 2) (fromCols Xs Zs) := by
    have hh := sf_reindex_li (fromCols X Z) hS0.2 em (Equiv.sumCongr en en)
    have he : fromCols Xs Zs = (fromCols X Z).submatrix em (Equiv.sumCongr en en) := by
      ext i j
      cases j <;> rfl
    rw [he]
    exact hh
  let E := Zs.submatrix Sum.inr Sum.inr
  have hErank : E.rank = m - r := by
    simpa [E] using (sf_lower_independent Xs Zs hX1 hX0 hcs hlis).rank_matrix
  obtain ⟨G2, σ2, h2, _⟩ := sf_columns E
  let B : Matrix (Fin r ⊕ Fin (m - r)) (Fin r ⊕ Fin (m - r)) (ZMod 2) :=
    fromBlocks 1 0 0 (G2 : Matrix (Fin (m-r)) (Fin (m-r)) (ZMod 2))
  let Bi : Matrix (Fin r ⊕ Fin (m - r)) (Fin r ⊕ Fin (m - r)) (ZMod 2) :=
    fromBlocks 1 0 0 (↑(G2⁻¹) : Matrix (Fin (m-r)) (Fin (m-r)) (ZMod 2))
  have hBB : B * Bi = 1 := by
    simp [B, Bi, fromBlocks_multiply, ← Units.val_mul]
  have hBiB : Bi * B = 1 := by
    simp [B, Bi, fromBlocks_multiply, ← Units.val_mul]
  let P : Matrix.GeneralLinearGroup (Fin m) (ZMod 2) :=
    ⟨B.submatrix em.symm em.symm, Bi.submatrix em.symm em.symm,
      by rw [submatrix_mul_equiv, hBB]; simp,
      by rw [submatrix_mul_equiv, hBiB]; simp⟩
  let τ : Equiv.Perm (Fin r ⊕ Fin (m + k - r)) := Equiv.sumCongr (Equiv.refl _) σ2
  let σ' : Equiv.Perm (Fin (m+k)) := (en.symm.trans τ).trans en
  let σ : Equiv.Perm (Fin (m+k)) := σ'.trans σ0
  have hP : (P : Matrix (Fin m) (Fin m) (ZMod 2)).submatrix em em = B := by
    ext i j
    simp [P]
  have hcalc (W : Matrix (Fin m) (Fin (m+k)) (ZMod 2)) :
      ((↑(P * G0) : Matrix (Fin m) (Fin m) (ZMod 2)) * W.submatrix id σ).submatrix em en =
        B * ((G0 : Matrix (Fin m) (Fin m) (ZMod 2)) * W.submatrix id σ0).submatrix em
          (fun j => en (τ j)) := by
    have hw : ((G0 : Matrix (Fin m) (Fin m) (ZMod 2)) * W.submatrix id σ).submatrix em en =
        ((G0 : Matrix (Fin m) (Fin m) (ZMod 2)) * W.submatrix id σ0).submatrix em
          (fun j => en (τ j)) := by
      rw [← submatrix_mul_equiv _ _ em (Equiv.refl _) en,
        ← submatrix_mul_equiv _ _ em (Equiv.refl _) (fun j => en (τ j))]
      congr 1
      ext i j
      simp [σ, σ', Matrix.submatrix_apply]
    rw [Units.val_mul, Matrix.mul_assoc]
    change ((P : Matrix (Fin m) (Fin m) (ZMod 2)) *
      ((G0 : Matrix (Fin m) (Fin m) (ZMod 2)) * W.submatrix id σ)).submatrix em en = _
    rw [← submatrix_mul_equiv _ _ em em en, hP, hw]
  have hcalcX : ((↑(P * G0) : Matrix (Fin m) (Fin m) (ZMod 2)) *
      Hx.submatrix id σ).submatrix em en = B * Xs.submatrix id τ := by
    simpa [Xs, X, submatrix_submatrix, Function.comp_def] using hcalc Hx
  have hcalcZ : ((↑(P * G0) : Matrix (Fin m) (Fin m) (ZMod 2)) *
      Hz.submatrix id σ).submatrix em en = B * Zs.submatrix id τ := by
    simpa [Zs, Z, submatrix_submatrix, Function.comp_def] using hcalc Hz
  have htop (i : Fin r) (j : Fin r ⊕ Fin (m+k-r)) :
      (B * Xs.submatrix id τ) (Sum.inl i) j = Xs (Sum.inl i) (τ j) := by
    simp [B, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, ite_mul]
  have hbottom (i : Fin (m-r)) (j : Fin r ⊕ Fin (m+k-r)) :
      (B * Xs.submatrix id τ) (Sum.inr i) j = 0 := by
    simp [B, Matrix.mul_apply, Fintype.sum_sum_type, hX0]
  have hmiddle (i : Fin (m-r)) (j : Fin (m+k-r)) :
      (B * Zs.submatrix id τ) (Sum.inr i) (Sum.inr j) =
        ((G2 : Matrix (Fin (m-r)) (Fin (m-r)) (ZMod 2)) * E.submatrix id σ2) i j := by
    simp [B, E, τ, Matrix.mul_apply, Fintype.sum_sum_type]
  refine ⟨P * G0, σ, hr, ?_, ?_, ?_⟩
  · intro i j hi hj
    obtain ⟨i, rfl⟩ := em.surjective i
    obtain ⟨j, rfl⟩ := en.surjective j
    cases i with
    | inr i => change r + (i : ℕ) < r at hi; omega
    | inl i =>
      cases j with
      | inr j => change r + (j : ℕ) < r at hj; omega
      | inl j =>
        have hh := congrArg (fun A => A (Sum.inl i) (Sum.inl j)) hcalcX
        simpa [htop, τ, hX1, em, en, Fin.ext_iff] using hh
  · intro i j hi
    obtain ⟨i, rfl⟩ := em.surjective i
    obtain ⟨j, rfl⟩ := en.surjective j
    cases i with
    | inl i => change r ≤ (i : ℕ) at hi; omega
    | inr i =>
      have hh := congrArg (fun A => A (Sum.inr i) j) hcalcX
      simpa [hbottom] using hh
  · intro i j hi hj hjm
    obtain ⟨i, rfl⟩ := em.surjective i
    obtain ⟨j, rfl⟩ := en.surjective j
    cases i with
    | inl i => change r ≤ (i : ℕ) at hi; omega
    | inr i =>
      cases j with
      | inl j => change r ≤ (j : ℕ) at hj; omega
      | inr j =>
        have hj' : (j : ℕ) < E.rank := by
          rw [hErank]
          change r + (j : ℕ) < m at hjm
          omega
        have hh := congrArg (fun A => A (Sum.inr i) (Sum.inr j)) hcalcZ
        rw [hmiddle, h2 _ _ hj'] at hh
        simpa [em, en] using hh
