-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.assisted_message_dimension_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:47:58.300288+00:00
-- url     : https://prove2.me/submissions/2e1cfdc8-377c-413e-8f54-194866ae44fe

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder Kronecker
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P62
open Finset

private lemma left_span_bound {I A : Type} [Fintype I] [Fintype A]
    [DecidableEq I] (C : Submodule ℂ (Matrix I A ℂ)) :
    ∃ D : Submodule ℂ (Matrix I A ℂ),
      Module.finrank ℂ D ≤ Fintype.card I ^ 2 * Module.finrank ℂ C ∧
      ∀ (X : Matrix I I ℂ) (Y : Matrix I A ℂ), Y ∈ C → X * Y ∈ D := by
  classical
  let b := Module.finBasis ℂ C
  let v : (I × I) × Fin (Module.finrank ℂ C) → Matrix I A ℂ :=
    fun p => Matrix.single p.1.1 p.1.2 (1 : ℂ) * (b p.2 : Matrix I A ℂ)
  let D := Submodule.span ℂ (Set.range v)
  refine ⟨D, ?_, ?_⟩
  · have h := finrank_range_le_card (R := ℂ) v
    simpa [D, Set.finrank, Fintype.card_prod, pow_two, Nat.mul_assoc] using h
  · intro X Y hY
    have hb (i j : I) : Matrix.single i j (1 : ℂ) * Y ∈ D := by
      have hy := congrArg (fun z : C => (z : Matrix I A ℂ)) (b.sum_repr ⟨Y,hY⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at hy
      rw [← hy, Matrix.mul_sum]
      apply Submodule.sum_mem
      intro l _
      rw [Matrix.mul_smul]
      exact D.smul_mem _ (Submodule.subset_span ⟨((i,j),l),rfl⟩)
    induction X using Matrix.induction_on' with
    | h_zero => simp
    | h_add X Z hX hZ => simpa [Matrix.add_mul] using D.add_mem hX hZ
    | h_std_basis i j z =>
      have hs : Matrix.single i j z = z • (Matrix.single i j (1 : ℂ) : Matrix I I ℂ) := by
        ext u w
        simp [Matrix.single_apply]
      rw [hs, Matrix.smul_mul]
      exact D.smul_mem z (hb i j)

private lemma orthogonal_sum_injective {I A M : Type} [Fintype I] [Fintype A]
    [Fintype M] (C : M → Submodule ℂ (Matrix I A ℂ))
    (ho : ∀ j k, j ≠ k → ∀ X ∈ C j, ∀ Y ∈ C k, Matrix.trace (Xᴴ * Y) = 0) :
    Function.Injective (fun x : ∀ j, C j => ∑ j, (x j : Matrix I A ℂ)) := by
  classical
  let f : (∀ j, C j) →ₗ[ℂ] Matrix I A ℂ :=
    { toFun := fun x => ∑ j, (x j : Matrix I A ℂ)
      map_add' := by intros; simp [Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.smul_sum] }
  change Function.Injective f
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro x hx
  have hz : ∑ j, (x j : Matrix I A ℂ) = 0 := hx
  apply funext
  intro k
  apply Subtype.ext
  apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
  have ht := congrArg (fun Y : Matrix I A ℂ => Matrix.trace ((x k : Matrix I A ℂ)ᴴ * Y)) hz
  rw [Matrix.mul_zero, Matrix.trace_zero, Matrix.mul_sum, Matrix.trace_sum] at ht
  have he : (∑ j, Matrix.trace ((x k : Matrix I A ℂ)ᴴ * (x j : Matrix I A ℂ))) =
      Matrix.trace ((x k : Matrix I A ℂ)ᴴ * (x k : Matrix I A ℂ)) := by
    apply Finset.sum_eq_single k
    · intro j _ hj
      exact ho k j (Ne.symm hj) _ (x k).property _ (x j).property
    · simp
  exact he.symm.trans ht

private lemma span_trace_orthogonal {I A R : Type} [Fintype I] [Fintype A]
    (B D : R → Matrix I A ℂ)
    (ho : ∀ s t, Matrix.trace ((B s)ᴴ * D t) = 0)
    {X Y : Matrix I A ℂ}
    (hX : X ∈ Submodule.span ℂ (Set.range B))
    (hY : Y ∈ Submodule.span ℂ (Set.range D)) : Matrix.trace (Xᴴ * Y) = 0 := by
  induction hX using Submodule.span_induction with
  | mem X h =>
    obtain ⟨s,rfl⟩ := h
    induction hY using Submodule.span_induction with
    | mem Y h => obtain ⟨t,rfl⟩ := h; exact ho s t
    | zero => simp
    | add Y Z _ _ hY hZ => simp [Matrix.mul_add, Matrix.trace_add, hY, hZ]
    | smul z Y _ hY => simp [Matrix.mul_smul, Matrix.trace_smul, hY]
  | zero => simp
  | add X Z _ _ hX hZ =>
    simp [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.trace_add, hX, hZ]
  | smul z X _ hX =>
    simp [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.trace_smul, hX]

private lemma kraus_message_bound {I A R M : Type}
    [Fintype I] [Fintype A] [Fintype R] [Fintype M] [Nonempty M]
    [DecidableEq I] [DecidableEq A]
    (E : M → R → Matrix I A ℂ) (T : Matrix A A ℂ) (hT : T ≠ 0)
    (hE : ∀ j, ∑ s, (E j s)ᴴ * E j s = 1)
    (ho : ∀ j k, j ≠ k → ∀ s t, Matrix.trace ((E j s * T)ᴴ * (E k t * T)) = 0) :
    Fintype.card M ≤ Fintype.card I ^ 2 := by
  classical
  let B (j : M) (s : R) := E j s * T
  let C (j : M) := Submodule.span ℂ (Set.range (B j))
  have recov (j : M) : ∑ s, (E j s)ᴴ * B j s = T := by
    simp only [B, ← Matrix.mul_assoc, ← Matrix.sum_mul, hE, Matrix.one_mul]
  have hCpos (j : M) : 0 < Module.finrank ℂ (C j) := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hc : C j = ⊥ := Submodule.finrank_eq_zero.mp hz
    have hb (s : R) : B j s = 0 := by
      have hmem : B j s ∈ C j := Submodule.subset_span ⟨s,rfl⟩
      simpa [hc] using hmem
    apply hT
    rw [← recov j]
    simp [hb]
  obtain ⟨k,_,hk⟩ := Finset.exists_min_image Finset.univ
    (fun j => Module.finrank ℂ (C j)) Finset.univ_nonempty
  obtain ⟨D,hDb,hD⟩ := left_span_bound (C k)
  have hCD (j : M) : C j ≤ D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s,rfl⟩
    have heq : B j s = ∑ t, (E j s * (E k t)ᴴ) * B k t := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_sum, recov]
      rfl
    rw [heq]
    exact D.sum_mem fun t _ => hD _ _ (Submodule.subset_span ⟨t,rfl⟩)
  let f : (∀ j, C j) →ₗ[ℂ] D :=
    { toFun := fun x => ⟨∑ j, (x j : Matrix I A ℂ), D.sum_mem fun j _ => hCD j (x j).property⟩
      map_add' := by intros; apply Subtype.ext; simp [Finset.sum_add_distrib]
      map_smul' := by intros; apply Subtype.ext; simp [Finset.smul_sum] }
  have hf : Function.Injective f := by
    intro x y hxy
    apply orthogonal_sum_injective C (fun j k hjk X hX Y hY =>
      span_trace_orthogonal (B j) (B k) (ho j k hjk) hX hY)
    exact congrArg (fun z : D => (z : Matrix I A ℂ)) hxy
  have hdim := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_pi_fintype] at hdim
  have hmin : Fintype.card M * Module.finrank ℂ (C k) ≤ ∑ j, Module.finrank ℂ (C j) := by
    calc
      _ = ∑ _j : M, Module.finrank ℂ (C k) := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => hk j (Finset.mem_univ j)
  exact Nat.le_of_mul_le_mul_right (hmin.trans (hdim.trans hDb)) (hCpos k)

private abbrev rowBlock {I A R : Type} (U : Matrix (I × R) A ℂ) (s : R) : Matrix I A ℂ :=
  U.submatrix (fun i => (i,s)) id

private lemma rowBlock_compress {I A R : Type} [Fintype I] [Fintype R]
    [DecidableEq I] [DecidableEq R]
    (U V : Matrix (I × R) A ℂ) (s t : R) :
    (rowBlock U s)ᴴ * rowBlock V t =
      Uᴴ * ((1 : Matrix I I ℂ) ⊗ₖ Matrix.single s t (1 : ℂ)) * V := by
  ext a b
  simp [rowBlock, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.single_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    ite_and]

private lemma rowBlock_complete {I A R : Type} [Fintype I] [Fintype R]
    (U : Matrix (I × R) A ℂ) :
    ∑ s, (rowBlock U s)ᴴ * rowBlock U s = Uᴴ * U := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    rowBlock, Matrix.submatrix_apply, id_eq, Fintype.sum_prod_type]
  exact Finset.sum_comm

private lemma trace_rowBlock {I A R : Type} [Fintype I] [Fintype A] [Fintype R]
    [DecidableEq I] [DecidableEq R]
    (U V : Matrix (I × R) A ℂ) (T : Matrix A A ℂ) (s t : R) :
    Matrix.trace ((rowBlock U s * T)ᴴ * (rowBlock V t * T)) =
      Matrix.trace ((U * (T * Tᴴ) * Vᴴ)ᴴ *
        ((1 : Matrix I I ℂ) ⊗ₖ Matrix.single s t (1 : ℂ))) := by
  let K := (1 : Matrix I I ℂ) ⊗ₖ Matrix.single s t (1 : ℂ)
  calc
    _ = Matrix.trace (Tᴴ * (((rowBlock U s)ᴴ * rowBlock V t) * T)) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Matrix.trace ((((rowBlock U s)ᴴ * rowBlock V t) * T) * Tᴴ) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((T * Tᴴ) * ((rowBlock U s)ᴴ * rowBlock V t)) := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
    _ = Matrix.trace ((T * Tᴴ) * (Uᴴ * K * V)) := by rw [rowBlock_compress]
    _ = _ := by
      simpa only [K, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc] using Matrix.trace_mul_cycle' (T * Tᴴ) (Uᴴ * K) V



theorem solution {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (S : Submodule ℂ (Matrix I I ℂ)) (hS : IsSystem S)
    {m a r : ℕ} (_ha : 0 < a) (_hr : 0 < r)
    (rho : Matrix (Fin a) (Fin a) ℂ) (hpos : rho.PosSemidef)
    (htr : Matrix.trace rho = 1)
    (W : Fin m → Matrix (I × Fin r) (Fin a) ℂ)
    (hW : ∀ j, (W j)ᴴ * W j = 1)
    (ho : ∀ j k, j ≠ k → ∀ X ∈ S, ∀ Y : Matrix (Fin r) (Fin r) ℂ,
      Matrix.trace ((W j * rho * (W k)ᴴ)ᴴ * Matrix.kronecker X Y) = 0) :
    m ≤ Fintype.card I ^ 2 := by
  classical
  by_cases hm : m = 0
  · simp [hm]
  have : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hm)
  obtain ⟨R,hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpos.nonneg
  let T : Matrix (Fin a) (Fin a) ℂ := Rᴴ
  have hT : T * Tᴴ = rho := by simpa [T, Matrix.star_eq_conjTranspose] using hR.symm
  have hn : T ≠ 0 := by
    intro hzero
    have hz : rho = 0 := by rw [← hT, hzero, Matrix.zero_mul]
    simp [hz] at htr
  have hb := kraus_message_bound (fun j s => rowBlock (W j) s) T hn
    (fun j => (rowBlock_complete (W j)).trans (hW j))
    (fun j k hjk s t => by
      rw [trace_rowBlock, hT]
      exact ho j k hjk 1 hS.1 _)
  simpa using hb

#print axioms solution
