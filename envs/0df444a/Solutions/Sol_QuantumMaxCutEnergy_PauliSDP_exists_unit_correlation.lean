-- Prove2me | solution 1 for QuantumMaxCutEnergy.PauliSDP.exists_unit_correlation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T04:30:51.459686+00:00
-- url     : https://prove2.me/submissions/ce01ac0b-3225-4b8d-bff1-e5960e51fed1

import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib
open scoped BigOperators
open QuantumMaxCutEnergy.PauliSDP

noncomputable section
namespace QuantumMaxCutEnergy.PauliSDP

/-! ## Part A: PSD ⟹ Gram factorisation -/

lemma hermitian_apply_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (i j : ι) :
    A i j = ∑ k, hA.eigenvalues k * ((hA.eigenvectorBasis k : EuclideanSpace ℝ ι) i) *
      ((hA.eigenvectorBasis k : EuclideanSpace ℝ ι) j) := by
  conv_lhs => rw [hA.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial,
    RCLike.ofReal_real_eq_id, Matrix.IsHermitian.eigenvectorUnitary_apply,
    Function.comp_apply, id_eq, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl (fun k _ => by ring)

/-- Unit-vector realisation of a positive semidefinite real matrix: `inner (psdVec i) (psdVec j) = A i j`. -/
noncomputable def psdVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (i : ι) : EuclideanSpace ℝ ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm
    (fun k => Real.sqrt (hA.1.eigenvalues k) * ((hA.1.eigenvectorBasis k : EuclideanSpace ℝ ι) i))

lemma inner_psdVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (i j : ι) :
    inner ℝ (psdVec hA i) (psdVec hA j) = A i j := by
  rw [hermitian_apply_eq_sum hA.1 i j, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [psdVec, WithLp.equiv_symm_apply, star_trivial]
  have hs : Real.sqrt (hA.1.eigenvalues k) * Real.sqrt (hA.1.eigenvalues k) = hA.1.eigenvalues k :=
    Real.mul_self_sqrt (hA.eigenvalues_nonneg k)
  linear_combination (((hA.1.eigenvectorBasis k : EuclideanSpace ℝ ι) i) *
    ((hA.1.eigenvectorBasis k : EuclideanSpace ℝ ι) j)) * hs

lemma norm_psdVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (i : ι) (hii : A i i = 1) :
    ‖psdVec hA i‖ = 1 := by
  rw [← Real.sqrt_sq (norm_nonneg _), ← real_inner_self_eq_norm_sq, inner_psdVec, hii,
    Real.sqrt_one]

/-! ## Part B: single-qubit Pauli words and their Gram vectors -/

def oneWord {n : ℕ} (a : Label) (i : Fin n) : Word n := fun t => if t = i then a else 0

lemma support_oneWord {n : ℕ} (a : Label) (i : Fin n) : support (oneWord a i) ⊆ {i} := by
  intro t ht
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  simp only [Finset.mem_singleton]
  by_contra h
  exact ht (by simp [oneWord, h])

lemma card_support_oneWord {n : ℕ} (a : Label) (i : Fin n) :
    (support (oneWord a i)).card ≤ 1 := by
  calc (support (oneWord a i)).card ≤ ({i} : Finset (Fin n)).card :=
        Finset.card_le_card (support_oneWord a i)
    _ = 1 := Finset.card_singleton i

lemma oneWord_zero {n : ℕ} (i : Fin n) : oneWord (0 : Label) i = identityWord n := by
  funext t; simp [oneWord, identityWord]

variable {n : ℕ} {L : Word n → ℝ} {k : ℕ}

/-- The Gram vector of the single-qubit Pauli `a` at vertex `i`, from the level-`k` moment matrix. -/
noncomputable def pauliVec (hk : 2 ≤ k) (hL : Feasible k L) (a : Label) (i : Fin n) :
    EuclideanSpace ℝ (Index n k) :=
  psdVec hL.2 ⟨oneWord a i, le_trans (card_support_oneWord a i) (by omega)⟩

lemma inner_pauliVec (hk : 2 ≤ k) (hL : Feasible k L) (a b : Label) (i j : Fin n) :
    inner ℝ (pauliVec hk hL a i) (pauliVec hk hL b j) =
      (wordPhase (oneWord a i) (oneWord b j)).re *
        L (wordProduct (oneWord a i) (oneWord b j)) := by
  rw [pauliVec, pauliVec, inner_psdVec]
  rfl

/-! ### Evaluation of the multiplication table on single-qubit words -/

lemma localPhase_zero_left (b : Label) : localPhase 0 b = 1 := by
  fin_cases b <;> simp [localPhase]

lemma localPhase_zero_right (a : Label) : localPhase a 0 = 1 := by
  fin_cases a <;> simp [localPhase]

lemma localPhase_pos_re (a b : Label) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    (localPhase a b).re = 0 := by
  fin_cases a <;> fin_cases b <;> simp_all [localPhase]

lemma localProduct_self (a : Label) (ha : a ≠ 0) : localProduct a a = 0 := by
  fin_cases a <;> simp_all [localProduct]

lemma localProduct_zero_left (b : Label) : localProduct 0 b = b := by
  fin_cases b <;> rfl

lemma localProduct_zero_right (a : Label) : localProduct a 0 = a := by
  fin_cases a <;> rfl

lemma localPhase_self_re (a : Label) (ha : a ≠ 0) : (localPhase a a).re = 1 := by
  fin_cases a <;> simp_all [localPhase]

lemma wordPhase_oneWord_ne {n : ℕ} {a b : Label} {i j : Fin n} (hij : i ≠ j) :
    wordPhase (oneWord a i) (oneWord b j) = 1 := by
  rw [wordPhase, Finset.prod_eq_one]
  intro t _
  by_cases h : t = i
  · subst h
    simp [oneWord, hij, localPhase_zero_right]
  · by_cases h2 : t = j
    · subst h2
      simp [oneWord, h, localPhase_zero_left]
    · simp [oneWord, h, h2, localPhase_zero_left]

lemma wordPhase_oneWord_same {n : ℕ} {a b : Label} {i : Fin n} :
    wordPhase (oneWord a i) (oneWord b i) = localPhase a b := by
  rw [wordPhase, Finset.prod_eq_single i]
  · simp [oneWord]
  · intro t _ ht
    simp [oneWord, ht, localPhase_zero_left]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma wordProduct_oneWord_same {n : ℕ} {a b : Label} {i : Fin n} :
    wordProduct (oneWord a i) (oneWord b i) = oneWord (localProduct a b) i := by
  funext t
  by_cases h : t = i <;> simp [wordProduct, oneWord, h, localProduct_zero_left]

lemma wordProduct_oneWord_ne {n : ℕ} {a b : Label} {i j : Fin n} (hij : i ≠ j) :
    wordProduct (oneWord a i) (oneWord b j) =
      fun t => if t = i then a else if t = j then b else 0 := by
  funext t
  by_cases h : t = i
  · subst h; simp [wordProduct, oneWord, hij, localProduct_zero_right]
  · by_cases h2 : t = j
    · subst h2; simp [wordProduct, oneWord, h, localProduct_zero_left]
    · simp [wordProduct, oneWord, h, h2, localProduct_zero_left]

/-- Orthonormality of the three Pauli Gram vectors at a single vertex. -/
lemma inner_pauliVec_same (hk : 2 ≤ k) (hL : Feasible k L) {a b : Label} (ha : a ≠ 0)
    (hb : b ≠ 0) (i : Fin n) :
    inner ℝ (pauliVec hk hL a i) (pauliVec hk hL b i) = if a = b then 1 else 0 := by
  rw [inner_pauliVec, wordPhase_oneWord_same, wordProduct_oneWord_same]
  by_cases hab : a = b
  · rw [if_pos hab, hab, localPhase_self_re b hb, localProduct_self b hb, oneWord_zero, hL.1,
      mul_one]
  · rw [if_neg hab, localPhase_pos_re a b ha hb hab, zero_mul]

/-- Cross-vertex inner products recover the two-body moments. -/
lemma inner_pauliVec_ne (hk : 2 ≤ k) (hL : Feasible k L) (a b : Label) {i j : Fin n}
    (hij : i ≠ j) :
    inner ℝ (pauliVec hk hL a i) (pauliVec hk hL b j) =
      L (fun t => if t = i then a else if t = j then b else 0) := by
  rw [inner_pauliVec, wordPhase_oneWord_ne hij, wordProduct_oneWord_ne hij]
  simp

/-! ## Part C: the block vector exhibiting the paper's edge parameter -/

/-- The concatenation of the three Pauli Gram vectors at a vertex. -/
noncomputable def blockVec (hk : 2 ≤ k) (hL : Feasible k L) (i : Fin n) :
    EuclideanSpace ℝ (Fin 3 × Index n k) :=
  (WithLp.equiv 2 ((Fin 3 × Index n k) → ℝ)).symm
    (fun p => pauliVec hk hL (Fin.succ p.1) i p.2)

lemma inner_blockVec (hk : 2 ≤ k) (hL : Feasible k L) (i j : Fin n) :
    inner ℝ (blockVec hk hL i) (blockVec hk hL j) =
      ∑ a : Fin 3, inner ℝ (pauliVec hk hL (Fin.succ a) i) (pauliVec hk hL (Fin.succ a) j) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  simp [blockVec]

lemma inner_blockVec_self (hk : 2 ≤ k) (hL : Feasible k L) (i : Fin n) :
    inner ℝ (blockVec hk hL i) (blockVec hk hL i) = 3 := by
  rw [inner_blockVec, show (3 : ℝ) = ∑ _a : Fin 3, (1 : ℝ) from by simp]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [inner_pauliVec_same hk hL (Fin.succ_ne_zero a) (Fin.succ_ne_zero a) i, if_pos rfl]

lemma inner_blockVec_ne (hk : 2 ≤ k) (hL : Feasible k L) {i j : Fin n} (hij : i ≠ j) :
    inner ℝ (blockVec hk hL i) (blockVec hk hL j) =
      ∑ a : Fin 3, L (fun t => if t = i then Fin.succ a else if t = j then Fin.succ a else 0) := by
  rw [inner_blockVec]
  exact Finset.sum_congr rfl (fun a _ => inner_pauliVec_ne hk hL _ _ hij)



/-! ## Part D: the unit vectors realising the level-2 edge correlation -/

lemma pairWord_eq_twoBody {n : ℕ} {a : Label} {i j : Fin n} (hij : i < j) :
    (fun t => if t = i then a else if t = j then a else 0) = twoBody a ⟨(i, j), hij⟩ := by
  funext t
  have hne : i ≠ j := ne_of_lt hij
  rcases eq_or_ne t i with h | h <;> rcases eq_or_ne t j with h2 | h2
  · exact absurd (h.symm.trans h2) hne
  · subst h; simp [twoBody, h2]
  · subst h2; simp [twoBody, h]
  · simp [twoBody, h, h2]

/-- **The level-`k` Pauli moment relaxation yields unit vectors whose inner products are the
edge correlations `(L(XX)+L(YY)+L(ZZ))/3`.** This is the interface needed by hyperplane
rounding: the paper's edge parameter `s_e = -<u_i,u_j>` and the objective coefficient
`c_e = (1 - 3 <u_i,u_j>)/2`. -/
theorem exists_unit_correlation {n k : ℕ} (hk : 2 ≤ k) (L : Word n → ℝ) (hL : Feasible k L) :
    ∃ u : Fin n → EuclideanSpace ℝ (Fin 3 × Index n k),
      (∀ i, ‖u i‖ = 1) ∧
      ∀ e : Edge n, inner ℝ (u e.val.1) (u e.val.2) =
        (L (twoBody 1 e) + L (twoBody 2 e) + L (twoBody 3 e)) / 3 := by
  have hsqrt3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  set c : ℝ := (Real.sqrt 3)⁻¹ with hc
  have hcc : c * c = 1/3 := by
    rw [hc, ← one_div]
    field_simp
    rw [sq, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have hnorm : ∀ i : Fin n, ‖blockVec hk hL i‖ = Real.sqrt 3 := by
    intro i
    rw [← Real.sqrt_sq (norm_nonneg _), ← real_inner_self_eq_norm_sq, inner_blockVec_self]
  refine ⟨fun i => c • blockVec hk hL i, ?_, ?_⟩
  · intro i
    rw [norm_smul, hnorm i, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqrt3)]
    exact inv_mul_cancel₀ (ne_of_gt hsqrt3)
  · intro e
    have hlt : e.val.1 < e.val.2 := e.2
    have hne : e.val.1 ≠ e.val.2 := ne_of_lt hlt
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, hcc, inner_blockVec,
      Fin.sum_univ_three]
    rw [inner_pauliVec_ne hk hL _ _ hne, inner_pauliVec_ne hk hL _ _ hne,
      inner_pauliVec_ne hk hL _ _ hne]
    have h1 : (Fin.succ (0 : Fin 3) : Label) = 1 := rfl
    have h2 : (Fin.succ (1 : Fin 3) : Label) = 2 := rfl
    have h3 : (Fin.succ (2 : Fin 3) : Label) = 3 := rfl
    rw [h1, h2, h3, pairWord_eq_twoBody hlt, pairWord_eq_twoBody hlt,
      pairWord_eq_twoBody hlt]
    ring

/-- The objective is exactly the average of the level-2 edge coefficients expressed through
those unit vectors: `objective w L = ∑ e, w e * (1 - 3 <u_{e.1}, u_{e.2}>)/2`. -/
theorem objective_eq_of_unit_correlation {n k : ℕ} (w : Weights n) (L : Word n → ℝ)
    (u : Fin n → EuclideanSpace ℝ (Fin 3 × Index n k))
    (hu : ∀ e : Edge n, inner ℝ (u e.val.1) (u e.val.2) =
      (L (twoBody 1 e) + L (twoBody 2 e) + L (twoBody 3 e)) / 3) :
    objective w L = ∑ e, (w e : ℝ) * (1 - 3 * inner ℝ (u e.val.1) (u e.val.2)) / 2 := by
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [hu e]
  ring




/-- **The objective in the shape used by the scalar certificate `lp24_strict_scalar`.**  With
`s e := -<u_{e.1}, u_{e.2}>` (the paper's edge parameter, in `[-1, 1]`) the edge coefficient is
`c e = (1 + 3 * s e) / 2`. -/
theorem objective_eq_of_s {n k : ℕ} (w : Weights n) (L : Word n → ℝ)
    (u : Fin n → EuclideanSpace ℝ (Fin 3 × Index n k))
    (hu : ∀ e : Edge n, inner ℝ (u e.val.1) (u e.val.2) =
      (L (twoBody 1 e) + L (twoBody 2 e) + L (twoBody 3 e)) / 3) :
    objective w L = ∑ e, (w e : ℝ) * ((1 + 3 * (- inner ℝ (u e.val.1) (u e.val.2))) / 2) := by
  rw [objective_eq_of_unit_correlation w L u hu]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  ring

end QuantumMaxCutEnergy.PauliSDP

/-! ## Axiom audit -/

theorem solution {n k : ℕ} (hk : 2 ≤ k) (L : QuantumMaxCutEnergy.PauliSDP.Word n → ℝ)
    (hL : QuantumMaxCutEnergy.PauliSDP.Feasible k L) :
    ∃ u : Fin n → EuclideanSpace ℝ (Fin 3 × QuantumMaxCutEnergy.PauliSDP.Index n k),
      (∀ i, ‖u i‖ = 1) ∧
      ∀ e : QuantumMaxCutEnergy.Edge n, inner ℝ (u e.val.1) (u e.val.2) =
        (L (QuantumMaxCutEnergy.PauliSDP.twoBody 1 e) + L (QuantumMaxCutEnergy.PauliSDP.twoBody 2 e) + L (QuantumMaxCutEnergy.PauliSDP.twoBody 3 e)) / 3 :=
  QuantumMaxCutEnergy.PauliSDP.exists_unit_correlation hk L hL
