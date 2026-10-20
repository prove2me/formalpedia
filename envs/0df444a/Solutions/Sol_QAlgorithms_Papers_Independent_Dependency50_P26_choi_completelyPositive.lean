-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P26.choi_completelyPositive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:48:53.215213+00:00
-- url     : https://prove2.me/submissions/cb0fd3ba-e423-46b3-8a28-708f902eac97

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P26

theorem g52b_choi_apply {I O : Type*} [Fintype I] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (o o' : O) (i i' : I) :
    outputFirstChoi M (o, i) (o', i') = M (Matrix.single i i' 1) o o' := rfl

theorem g52b_lin_expand {I O : Type*} [Fintype I] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (X : Matrix I I ℂ) : M X = ∑ i, ∑ j, X i j • M (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

theorem g52b_sum_psd {I ι : Type*} [Fintype I] (s : Finset ι) (A : ι → Matrix I I ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

theorem g52b_swap22 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ i, ∑ j, ∑ m, ∑ l, f i j m l = ∑ m, ∑ l, ∑ i, ∑ j, f i j m l := by
  calc ∑ i, ∑ j, ∑ m, ∑ l, f i j m l = ∑ i, ∑ m, ∑ j, ∑ l, f i j m l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ j, ∑ l, f i j m l := Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ l, ∑ j, f i j m l :=
        Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ l, ∑ i, ∑ j, f i j m l := Finset.sum_congr rfl fun m _ => Finset.sum_comm

theorem g52b_cp_of_choi {I O : Type*} [Fintype I] [Fintype O]
    (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hC : (outputFirstChoi M).PosSemidef) :
    Entanglement.IsCompletelyPositive M := by
  intro r X hX
  obtain ⟨m1, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hX
  obtain ⟨m2, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hC
  have hMij : ∀ i j o o', M (Matrix.single i j 1) o o' =
      ∑ l, g l (o, i) * star (g l (o', j)) := by
    intro i j o o'
    rw [← g52b_choi_apply, hg, Matrix.sum_apply]
    simp [Matrix.vecMulVec_apply]
  let F : Fin m1 → Fin m2 → (Fin r × O → ℂ) := fun a l q => ∑ i, v a (q.1, i) * g l (q.2, i)
  have hY : idTensorSuperop M X = ∑ a, ∑ l, Matrix.vecMulVec (F a l) (star (F a l)) := by
    ext ⟨x, o⟩ ⟨y, o'⟩
    show M (Matrix.of fun i j => X (x, i) (y, j)) o o' = _
    rw [g52b_lin_expand]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, hMij, hv,
      Matrix.vecMulVec_apply, Pi.star_apply, F, star_sum, star_mul']
    simp only [Finset.sum_mul_sum]
    rw [g52b_swap22]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hY]
  exact g52b_sum_psd _ _ fun a => g52b_sum_psd _ _ fun l =>
    Matrix.posSemidef_vecMulVec_self_star _

theorem g52b_choi_of_cp {I O : Type*} [Fintype I] [Fintype O]
    (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (h : Entanglement.IsCompletelyPositive M) :
    (outputFirstChoi M).PosSemidef := by
  let e := Fintype.equivFin I
  let Ω : Fin (Fintype.card I) × I → ℂ := fun q => if q.1 = e q.2 then 1 else 0
  have hY := h _ _ (Matrix.posSemidef_vecMulVec_self_star Ω)
  have hE : outputFirstChoi M = (idTensorSuperop M (Matrix.vecMulVec Ω (star Ω))).submatrix
      (fun q : O × I => (e q.2, q.1)) (fun q => (e q.2, q.1)) := by
    ext ⟨o, i⟩ ⟨o', i'⟩
    rw [g52b_choi_apply, Matrix.submatrix_apply]
    show M (Matrix.single i i' 1) o o' =
      M (Matrix.of fun j j' => Matrix.vecMulVec Ω (star Ω) (e i, j) (e i', j')) o o'
    have hX : (Matrix.of fun j j' => Matrix.vecMulVec Ω (star Ω) (e i, j) (e i', j')) =
        Matrix.single i i' 1 := by
      ext j j'
      by_cases h1 : i = j <;> by_cases h2 : i' = j' <;>
        simp [Matrix.single_apply, Matrix.vecMulVec_apply, Ω, h1, h2, Ne.symm, eq_comm]
    rw [hX]
  rw [hE]
  exact hY.submatrix _


/-- PDF p.3, Lemma 3; the Kraus characterization in the proof is attributed there to [1]. -/
theorem solution {I O : Type*} [Fintype I] [Fintype O]
    [Nonempty I] [Nonempty O] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    Entanglement.IsCompletelyPositive M ↔ (outputFirstChoi M).PosSemidef := ⟨g52b_choi_of_cp M, g52b_cp_of_choi M⟩


end

