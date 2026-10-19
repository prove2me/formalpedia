-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.processing_systems
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:09:40.302104+00:00
-- url     : https://prove2.me/submissions/3615e026-7b72-486e-878d-1012ebd98881

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P62
noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.15, 16, Lemma 2.11: processing of operator systems. -/
theorem h62_prodKraus {I O J : Type} [Fintype I] [Fintype O] [Fintype J] [DecidableEq I] [DecidableEq O]
    {m r : ℕ} (K : Fin m → Matrix J O ℂ) (E : Fin r → Matrix O I ℂ)
    (hK : IsKrausFamily K) (hE : IsKrausFamily E) :
    IsKrausFamily (fun t : Fin (m * r) => K (finProdFinEquiv.symm t).1 * E (finProdFinEquiv.symm t).2) := by
  unfold IsKrausFamily at *
  rw [← finProdFinEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Matrix.conjTranspose_mul]
  rw [Finset.sum_comm]
  have : ∀ y : Fin r, ∑ x : Fin m, (E y)ᴴ * (K x)ᴴ * (K x * E y) = (E y)ᴴ * E y := by
    intro y
    rw [show (E y)ᴴ * E y = (E y)ᴴ * (∑ x, (K x)ᴴ * K x) * E y by rw [hK, Matrix.mul_one],
      Matrix.mul_sum, Matrix.sum_mul]
    simp only [Matrix.mul_assoc]
  simp_rw [this, hE]

theorem h62_prodApply {I O J : Type} [Fintype I] [Fintype O] [Fintype J]
    {m r : ℕ} (K : Fin m → Matrix J O ℂ) (E : Fin r → Matrix O I ℂ) (R : Matrix I I ℂ) :
    krausApply K (krausApply E R) =
      krausApply (fun t : Fin (m * r) => K (finProdFinEquiv.symm t).1 * E (finProdFinEquiv.symm t).2) R := by
  unfold krausApply
  rw [← finProdFinEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Matrix.conjTranspose_mul,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]

theorem h62_gen {I O J : Type} [Fintype I] [Fintype O] [Fintype J] [DecidableEq I] [DecidableEq O]
    (F : Superop I O) (G : Superop O J)
    {m r : ℕ} (K : Fin m → Matrix J O ℂ) (E : Fin r → Matrix O I ℂ)
    (hK : IsKrausFamily K) (hE : IsKrausFamily E) (hGK : ∀ R, G R = krausApply K R)
    (hFE : ∀ R, F R = krausApply E R) (a b : Fin m) (i j : Fin r) :
    (K a * E i)ᴴ * (K b * E j) ∈ graph (G ∘ F) := by
  apply Submodule.subset_span
  refine ⟨m * r, _, h62_prodKraus K E hK hE, ?_, finProdFinEquiv (a, i), finProdFinEquiv (b, j), ?_⟩
  · intro R; simp only [Function.comp_apply, hFE, hGK, h62_prodApply]
  · simp

theorem solution [Nonempty I] [Nonempty O] [Nonempty J]
    (F : Superop I O) (G : Superop O J) (hF : IsChannel F) (hG : IsChannel G) :
    graph F ≤ graph (G ∘ F) ∧ GraphHom (graph (G ∘ F)) (graph G) := by
  obtain ⟨m, K, hK, hGK⟩ := hG
  obtain ⟨r, E, hE, hFE⟩ := hF
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h
      exfalso
      unfold IsKrausFamily at hE
      simp at hE
    · exact h
  refine ⟨?_, ?_⟩
  · rw [graph, Submodule.span_le]
    rintro X ⟨r', E', hE', hFE', i, j, rfl⟩
    have : (E' i)ᴴ * E' j = ∑ a, (K a * E' i)ᴴ * (K a * E' j) := by
      unfold IsKrausFamily at hK
      rw [show (E' i)ᴴ * E' j = (E' i)ᴴ * (∑ a, (K a)ᴴ * K a) * E' j by rw [hK, Matrix.mul_one],
        Matrix.mul_sum, Matrix.sum_mul]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this]
    exact Submodule.sum_mem _ (fun a _ => h62_gen F G K E' hK hE' hGK hFE' a a i j)
  · refine ⟨r, hr, Matrix.of fun p x => E p.2 p.1 x, ?_, ?_⟩
    · unfold IsKrausFamily at hE
      rw [← hE]
      ext x y
      simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]
      rw [Finset.sum_comm]
    · have hmap : ∀ i j, ∀ X ∈ graph G, (E i)ᴴ * X * E j ∈ graph (G ∘ F) := by
        intro i j X hX
        induction hX using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨m', K', hK', hGK', a, b, rfl⟩ := hx
          have := h62_gen F G K' E hK' hE hGK' hFE a b i j
          simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using this
        | zero => simp
        | add x y _ _ hx hy => simpa [Matrix.mul_add, Matrix.add_mul] using add_mem hx hy
        | smul c x _ hx => simpa [Matrix.mul_smul, Matrix.smul_mul] using Submodule.smul_mem _ c hx
      intro X hX Y
      have : (Matrix.of fun (p : O × Fin r) (x : I) => E p.2 p.1 x)ᴴ * Matrix.kronecker X Y *
          (Matrix.of fun (p : O × Fin r) (x : I) => E p.2 p.1 x) =
          ∑ i, ∑ j, Y i j • ((E i)ᴴ * X * E j) := by
        ext x y
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fintype.sum_prod_type,
          Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
          Finset.sum_mul, Finset.mul_sum]
        refine (Finset.sum_congr rfl fun o' _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans ?_
        refine (Finset.sum_congr rfl fun o' _ => Finset.sum_comm).trans ?_
        refine Finset.sum_comm.trans ?_
        refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun o' _ => Finset.sum_congr rfl fun o _ => ?_
        ring
      rw [this]
      exact Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun j _ =>
        Submodule.smul_mem _ _ (hmap i j X hX)))


end

