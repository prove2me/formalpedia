-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P16.triangularization_iffSolvable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T15:02:28.434765+00:00
-- url     : https://prove2.me/submissions/dcf258e2-1749-4d1a-84cb-c7dc5786325b

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

open scoped Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace X6P16T

/-- an invariant flag for a solvable Lie subalgebra of matrices -/
theorem flag {n : ℕ} (L : LieSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    [LieAlgebra.IsSolvable L] :
    ∀ k ≤ n, ∃ b : Fin k → (Fin n → ℂ), LinearIndependent ℂ b ∧
      ∀ X ∈ L, ∀ j : Fin k, X *ᵥ b j ∈ Submodule.span ℂ (b '' {i | i ≤ j}) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨Fin.elim0, linearIndependent_empty_type, fun _ _ j => j.elim0⟩
  | succ k ih =>
    intro hk
    obtain ⟨b, hli, hfl⟩ := ih (by omega)
    set W : Submodule ℂ (Fin n → ℂ) := Submodule.span ℂ (Set.range b)
    have hW : ∀ X ∈ L, ∀ v ∈ W, X *ᵥ v ∈ W := by
      intro X hX v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        exact Submodule.span_mono (Set.image_subset_range _ _) (hfl X hX j)
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact W.add_mem hx hy
      | smul c x _ hx => rw [Matrix.mulVec_smul]; exact W.smul_mem c hx
    let W' : LieSubmodule ℂ L (Fin n → ℂ) :=
      { W with lie_mem := fun {x v} hv => hW x.1 x.2 v hv }
    have hfin : Module.finrank ℂ W = k := by
      rw [finrank_span_eq_card hli]; simp
    have hnt : Nontrivial ((Fin n → ℂ) ⧸ W') := by
      obtain ⟨v, hv⟩ : ∃ v, v ∉ W := by
        by_contra h
        push Not at h
        have h1 : W = ⊤ := eq_top_iff.2 fun v _ => h v
        have : Module.finrank ℂ W = n := by rw [h1, finrank_top]; simp
        omega
      exact ⟨⟨LieSubmodule.Quotient.mk' W' v, 0, fun h =>
        hv ((LieSubmodule.Quotient.mk_eq_zero' (N := W')).1 h)⟩⟩
    obtain ⟨χ, hχ⟩ := LieModule.exists_nontrivial_weightSpace_of_isSolvable ℂ L
      ((Fin n → ℂ) ⧸ W')
    obtain ⟨⟨wq, hwq⟩, hwq0⟩ := exists_ne (0 : LieModule.weightSpace ((Fin n → ℂ) ⧸ W') χ)
    rw [LieModule.mem_weightSpace] at hwq
    obtain ⟨w, rfl⟩ := LieSubmodule.Quotient.surjective_mk' W' wq
    have hw0 : w ∉ W := by
      intro h
      apply hwq0
      ext
      simpa using (LieSubmodule.Quotient.mk_eq_zero' (N := W')).2 h
    have hwX : ∀ x : L, (x : Matrix (Fin n) (Fin n) ℂ) *ᵥ w - χ x • w ∈ W := by
      intro x
      have h := hwq x
      have : LieSubmodule.Quotient.mk' W' ((x : Matrix (Fin n) (Fin n) ℂ) *ᵥ w - χ x • w) = 0 := by
        rw [map_sub, map_smul]
        rw [← h]
        rw [sub_eq_zero]
        rfl
      exact (LieSubmodule.Quotient.mk_eq_zero' (N := W')).1 this
    refine ⟨Fin.snoc b w, ?_, ?_⟩
    · rw [linearIndependent_finSnoc]; exact ⟨hli, hw0⟩
    · intro X hX j
      have hWsub : W ≤ Submodule.span ℂ ((Fin.snoc b w : Fin (k + 1) → _) '' {i | i ≤ Fin.last k}) := by
        apply Submodule.span_mono
        rintro _ ⟨i, rfl⟩
        exact ⟨Fin.castSucc i, Fin.le_last _, by simp⟩
      refine Fin.lastCases ?_ (fun j' => ?_) j
      · simp only [Fin.snoc_last]
        have hwmem : w ∈ Submodule.span ℂ ((Fin.snoc b w : Fin (k + 1) → _) '' {i | i ≤ Fin.last k}) :=
          Submodule.subset_span ⟨Fin.last k, show Fin.last k ≤ Fin.last k from le_rfl, by simp⟩
        have := hWsub (hwX ⟨X, hX⟩)
        have h2 := Submodule.add_mem _ this (Submodule.smul_mem _ (χ ⟨X, hX⟩) hwmem)
        simpa using h2
      · simp only [Fin.snoc_castSucc]
        refine Submodule.span_mono ?_ (hfl X hX j')
        rintro _ ⟨i, hi, rfl⟩
        exact ⟨Fin.castSucc i, Fin.castSucc_le_castSucc_iff.2 hi, by simp⟩


open QAlgorithms.Papers.Independent.Dependency50.P16

theorem tri_of_solvable {n : ℕ} (A : Set (Matrix (Fin n) (Fin n) ℂ))
    (h : LieAlgebra.IsSolvable (LieSubalgebra.lieSpan ℂ (Matrix (Fin n) (Fin n) ℂ) A)) :
    ∃ B C : Matrix (Fin n) (Fin n) ℂ, B * C = 1 ∧ C * B = 1 ∧
      ∀ X ∈ A, (C * X * B).IsUpperTriangular := by
  obtain ⟨b, hli, hfl⟩ := flag (LieSubalgebra.lieSpan ℂ (Matrix (Fin n) (Fin n) ℂ) A) n le_rfl
  set B : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => b j i
  have hBT : (fun i => Bᵀ i) = b := by funext i; ext j; rfl
  have hB : IsUnit B := Matrix.linearIndependent_cols_iff_isUnit.1 (by
    have : B.col = b := by funext j i; rfl
    rw [this]; exact hli)
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).1 hB
  refine ⟨B, B⁻¹, Matrix.mul_nonsing_inv B hdet, Matrix.nonsing_inv_mul B hdet, fun X hX => ?_⟩
  intro i j hji
  have hmem := hfl X (LieSubalgebra.subset_lieSpan hX) j
  rw [Finsupp.mem_span_image_iff_linearCombination] at hmem
  obtain ⟨l, hl, hlc⟩ := hmem
  have hXb : X *ᵥ b j = B *ᵥ (fun r => l r) := by
    rw [← hlc, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
    ext r
    simp [Matrix.mulVec, dotProduct, B, Finset.sum_apply, mul_comm]
  have hBe : B *ᵥ Pi.single j 1 = b j := by
    ext r; simp [B, Matrix.mulVec_single_one]
  have hcol : (B⁻¹ * X * B) *ᵥ Pi.single j 1 = fun r => l r := by
    rw [← Matrix.mulVec_mulVec, hBe, ← Matrix.mulVec_mulVec, hXb, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul B hdet, Matrix.one_mulVec]
  have hentry : (B⁻¹ * X * B) i j = l i := by
    have := congrFun hcol i
    simpa [Matrix.mulVec_single_one] using this
  rw [hentry]
  exact (Finsupp.mem_supported' ℂ l).1 hl i (by simpa using hji)

/-- entries vanish below the m-th superdiagonal after conjugation -/
def P {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ i j : Fin n, j.val < i.val + m → (C * M * B) i j = 0

theorem P_add {n : ℕ} {B C : Matrix (Fin n) (Fin n) ℂ} {m : ℕ} {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : P B C m X) (hY : P B C m Y) : P B C m (X + Y) := by
  intro i j h; simp [Matrix.mul_add, Matrix.add_mul, hX i j h, hY i j h]

theorem P_smul {n : ℕ} {B C : Matrix (Fin n) (Fin n) ℂ} {m : ℕ} {X : Matrix (Fin n) (Fin n) ℂ}
    (c : ℂ) (hX : P B C m X) : P B C m (c • X) := by
  intro i j h; simp [hX i j h]

theorem P_zero {n : ℕ} {B C : Matrix (Fin n) (Fin n) ℂ} {m : ℕ} : P B C m 0 := by
  intro i j _; simp

theorem P_mono {n : ℕ} {B C : Matrix (Fin n) (Fin n) ℂ} {m : ℕ} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : P B C (m + 1) X) : P B C m X := fun i j h => hX i j (by omega)

theorem P_bracket {n : ℕ} {B C : Matrix (Fin n) (Fin n) ℂ} (hBC : B * C = 1) {m : ℕ}
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : P B C m X) (hY : P B C m Y) :
    P B C (m + 1) (X * Y - Y * X) := by
  intro i j h
  have hconj : ∀ U V : Matrix (Fin n) (Fin n) ℂ, C * (U * V) * B = (C * U * B) * (C * V * B) := by
    intro U V
    calc C * (U * V) * B = C * U * (B * C) * V * B := by rw [hBC]; simp [Matrix.mul_assoc]
      _ = (C * U * B) * (C * V * B) := by simp [Matrix.mul_assoc]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply, hconj, hconj]
  set X' := C * X * B
  set Y' := C * Y * B
  have hterm : ∀ (U V : Matrix (Fin n) (Fin n) ℂ), P B C m U → P B C m V → ∀ l : Fin n,
      (C * U * B) i l * (C * V * B) l j =
        if l = i ∧ j = i then (C * U * B) i i * (C * V * B) i i else 0 := by
    intro U V hU hV l
    by_cases h1 : l.val < i.val + m
    · rw [hU i l h1, zero_mul]
      split_ifs with h3
      · rw [h3.1] at h1; rw [hU i i h1, zero_mul]
      · rfl
    by_cases h2 : j.val < l.val + m
    · rw [hV l j h2, mul_zero]
      split_ifs with h3
      · rw [h3.1, h3.2] at h2; rw [hV i i h2, mul_zero]
      · rfl
    have hli : l = i := Fin.ext (by omega)
    have hji : j = i := Fin.ext (by omega)
    subst hli; subst hji
    simp
  simp only [Matrix.mul_apply]
  rw [Finset.sum_congr rfl fun l _ => hterm X Y hX hY l,
    Finset.sum_congr rfl fun l _ => hterm Y X hY hX l]
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  by_cases hji : j = i
  · subst hji; simp [mul_comm]
  · simp [hji]

theorem solvable_of_tri {n : ℕ} (A : Set (Matrix (Fin n) (Fin n) ℂ))
    (h : ∃ B C : Matrix (Fin n) (Fin n) ℂ, B * C = 1 ∧ C * B = 1 ∧
      ∀ X ∈ A, (C * X * B).IsUpperTriangular) :
    LieAlgebra.IsSolvable (LieSubalgebra.lieSpan ℂ (Matrix (Fin n) (Fin n) ℂ) A) := by
  obtain ⟨B, C, hBC, hCB, hT⟩ := h
  let T : LieSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ) :=
    { carrier := {X | P B C 0 X}
      add_mem' := fun hX hY => P_add hX hY
      zero_mem' := P_zero
      smul_mem' := fun c _ hX => P_smul c hX
      lie_mem' := fun {X Y} hX hY => by
        show P B C 0 ⁅X, Y⁆
        rw [Ring.lie_def]
        exact P_mono (P_bracket hBC hX hY) }
  have hAT : LieSubalgebra.lieSpan ℂ (Matrix (Fin n) (Fin n) ℂ) A ≤ T := by
    rw [LieSubalgebra.lieSpan_le]
    intro X hX i j hij
    exact hT X hX (by simpa using hij)
  set L := LieSubalgebra.lieSpan ℂ (Matrix (Fin n) (Fin n) ℂ) A
  have key : ∀ m, ∀ x ∈ LieAlgebra.derivedSeries ℂ L m, P B C m (x : Matrix (Fin n) (Fin n) ℂ) := by
    intro m
    induction m with
    | zero => intro x _; exact hAT x.2
    | succ m ih =>
      intro x hx
      rw [LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_succ,
        ← LieAlgebra.derivedSeries_def] at hx
      have hx' : x ∈ (⁅LieAlgebra.derivedSeries ℂ L m, LieAlgebra.derivedSeries ℂ L m⁆ :
          LieIdeal ℂ L).toSubmodule := hx
      rw [LieSubmodule.lieIdeal_oper_eq_linear_span] at hx'
      clear hx
      induction hx' using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, c, rfl⟩ := hy
        show P B C (m + 1) (((⁅(a : L), (c : L)⁆ : L)) : Matrix (Fin n) (Fin n) ℂ)
        rw [LieSubalgebra.coe_bracket, Ring.lie_def]
        exact P_bracket hBC (ih _ a.2) (ih _ c.2)
      | zero => exact P_zero
      | add y z _ _ hy hz => exact P_add hy hz
      | smul c y _ hy => exact P_smul c hy
  apply LieAlgebra.IsSolvable.mk (R := ℂ) (L := L) (k := n)
  rw [eq_bot_iff]
  intro x hx
  have hP := key n x hx
  have hzero : C * (x : Matrix (Fin n) (Fin n) ℂ) * B = 0 := by
    ext i j; exact hP i j (by omega)
  have : (x : Matrix (Fin n) (Fin n) ℂ) = 0 := by
    calc (x : Matrix (Fin n) (Fin n) ℂ) = B * (C * (x : Matrix (Fin n) (Fin n) ℂ) * B) * C := by
          simp only [← Matrix.mul_assoc, hBC, Matrix.one_mul]
          rw [Matrix.mul_assoc, hBC, Matrix.mul_one]
      _ = 0 := by rw [hzero]; simp
  rw [LieSubmodule.mem_bot]
  exact Subtype.ext this

end X6P16T

theorem solution {n : ℕ} (hn : 2 ≤ n)
    (A : Set (Matrix (Fin n) (Fin n) ℂ)) :
    QAlgorithms.Papers.Independent.Dependency50.P16.triangularizable A ↔
      QAlgorithms.Papers.Independent.Dependency50.P16.solvableGenerated A :=
  ⟨X6P16T.solvable_of_tri A, X6P16T.tri_of_solvable A⟩
