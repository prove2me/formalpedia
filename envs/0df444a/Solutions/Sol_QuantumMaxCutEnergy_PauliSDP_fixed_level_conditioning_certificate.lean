-- Prove2me | solution 1 for QuantumMaxCutEnergy.PauliSDP.fixed_level_conditioning_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T15:49:49.434435+00:00
-- url     : https://prove2.me/submissions/3f7d9bc5-7d22-4387-ac42-70c49f8eaf6b

import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib

/-! Elementary exact conditioning of the fixed Pauli moment relaxation.
All results below are finite algebra, counting, and norm estimates.
No approximation-algorithm theorem, unpublished research result,
optimization oracle, or finite-bit SDP running time is assumed. -/

noncomputable section
open scoped BigOperators
namespace QuantumMaxCutEnergy.PauliSDP

lemma localProduct_self (a : Label) : localProduct a a = 0 := by
  fin_cases a <;> decide

lemma localProduct_identity_left (a : Label) : localProduct 0 a = a := by
  fin_cases a <;> decide

lemma localProduct_identity_right (a : Label) : localProduct a 0 = a := by
  fin_cases a <;> decide

lemma localProduct_eq_zero_iff (a b : Label) : localProduct a b = 0 ↔ a = b := by
  fin_cases a <;> fin_cases b <;> decide

lemma localPhase_self (a : Label) : localPhase a a = 1 := by
  fin_cases a <;> norm_num [localPhase]

lemma localPhase_identity_left (a : Label) : localPhase 0 a = 1 := by
  fin_cases a <;> norm_num [localPhase]

lemma localPhase_identity_right (a : Label) : localPhase a 0 = 1 := by
  fin_cases a <;> norm_num [localPhase]

lemma wordProduct_self {n : ℕ} (P : Word n) :
    wordProduct P P = identityWord n := by
  funext i
  exact localProduct_self (P i)

lemma wordProduct_identity_left {n : ℕ} (P : Word n) :
    wordProduct (identityWord n) P = P := by
  funext i
  exact localProduct_identity_left (P i)

lemma wordProduct_identity_right {n : ℕ} (P : Word n) :
    wordProduct P (identityWord n) = P := by
  funext i
  exact localProduct_identity_right (P i)

lemma wordProduct_eq_identity_iff {n : ℕ} (P Q : Word n) :
    wordProduct P Q = identityWord n ↔ P = Q := by
  constructor
  · intro h
    funext i
    exact (localProduct_eq_zero_iff (P i) (Q i)).mp (congrFun h i)
  · rintro rfl
    exact wordProduct_self P

lemma wordPhase_self {n : ℕ} (P : Word n) : wordPhase P P = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  exact localPhase_self (P i)

lemma wordPhase_identity_left {n : ℕ} (P : Word n) :
    wordPhase (identityWord n) P = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  exact localPhase_identity_left (P i)

lemma wordPhase_identity_right {n : ℕ} (P : Word n) :
    wordPhase P (identityWord n) = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  exact localPhase_identity_right (P i)

lemma support_identity (n : ℕ) : support (identityWord n) = ∅ := by
  simp [support, identityWord]

lemma support_product_subset {n : ℕ} (P Q : Word n) :
    support (wordProduct P Q) ⊆ support P ∪ support Q := by
  intro i hi
  have hn := (Finset.mem_filter.mp hi).2
  apply Finset.mem_union.mpr
  by_cases hp : P i = 0
  · right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ i, ?_⟩
    intro hq
    exact hn (by simp [wordProduct, hp, hq, localProduct])
  · left
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hp⟩

lemma support_product_card_le {n : ℕ} (P Q : Word n) :
    (support (wordProduct P Q)).card ≤ (support P).card + (support Q).card :=
  (Finset.card_le_card (support_product_subset P Q)).trans
    (Finset.card_union_le (support P) (support Q))

/-- The apparent full-word moment domain has no effect beyond degree2k.
This is a projection property, not a claim of a polynomial-time solver. -/
theorem realGram_congr_low_moments {n k : ℕ} (L L' : Word n → ℝ)
    (h : ∀ P : Word n, (support P).card ≤ 2 * k → L P = L' P) :
    realGram k L = realGram k L' := by
  ext P Q
  have hb := support_product_card_le P.val Q.val
  have hP := P.property
  have hQ := Q.property
  have hm : (support (wordProduct P.val Q.val)).card ≤ 2 * k := by omega
  simp only [realGram, h _ hm]

def identityIndex (n k : ℕ) : Index n k :=
  ⟨identityWord n, by simp [support_identity]⟩

/-- The maximally mixed state moments. -/
def mixedMoments (n : ℕ) (P : Word n) : ℝ :=
  if P = identityWord n then 1 else 0

lemma mixed_realGram (n k : ℕ) : realGram k (mixedMoments n) = 1 := by
  classical
  ext P Q
  by_cases h : P = Q
  · subst Q
    simp [realGram, mixedMoments, wordProduct_self, wordPhase_self]
  · have hval : P.val ≠ Q.val := by
      intro hh
      exact h (Subtype.ext hh)
    have hprod := (wordProduct_eq_identity_iff P.val Q.val).not.mpr hval
    simp [realGram, mixedMoments, hprod, h]

theorem mixed_feasible (n k : ℕ) : Feasible k (mixedMoments n) := by
  refine ⟨by simp [mixedMoments], ?_⟩
  rw [mixed_realGram]
  exact Matrix.PosSemidef.one

lemma realGram_diag {n k : ℕ} {L : Word n → ℝ} (hL : Feasible k L)
    (P : Index n k) : realGram k L P P = 1 := by
  simp [realGram, wordProduct_self, wordPhase_self, hL.1]

lemma realGram_identity_left {n k : ℕ} (L : Word n → ℝ) (P : Index n k) :
    realGram k L (identityIndex n k) P = L P.val := by
  simp [realGram, identityIndex, wordProduct_identity_left, wordPhase_identity_left]

lemma realGram_identity_right {n k : ℕ} (L : Word n → ℝ) (P : Index n k) :
    realGram k L P (identityIndex n k) = L P.val := by
  simp [realGram, identityIndex, wordProduct_identity_right, wordPhase_identity_right]

/-- A two-by-two principal Gram test bounds every represented moment. -/
theorem represented_moment_bounds {n k : ℕ} {L : Word n → ℝ}
    (hL : Feasible k L) (P : Word n) (hP : (support P).card ≤ k) :
    -1 ≤ L P ∧ L P ≤ 1 := by
  let p : Index n k := ⟨P, hP⟩
  let f : Fin 2 → Index n k := fun i => if i = 0 then identityIndex n k else p
  have hM := hL.2.submatrix f
  have hplus := hM.dotProduct_mulVec_nonneg ![(1 : ℝ), 1]
  have hminus := hM.dotProduct_mulVec_nonneg ![(1 : ℝ), -1]
  simp only [Matrix.submatrix, Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    f, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue, one_ne_zero, if_true, if_false,
    Pi.star_apply, star_trivial] at hplus hminus
  simp only [realGram_diag hL, realGram_identity_left,
    realGram_identity_right, p] at hplus hminus
  constructor <;> linarith

lemma support_twoBody_le {n : ℕ} (a : Label) (e : Edge n) :
    (support (twoBody a e)).card ≤ 2 := by
  have hsub : support (twoBody a e) ⊆ ({e.val.1, e.val.2} : Finset (Fin n)) := by
    intro i hi
    have hn := (Finset.mem_filter.mp hi).2
    by_cases h : i = e.val.1 ∨ i = e.val.2
    · simpa using h
    · simp [twoBody, h] at hn
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

lemma twoBody_ne_identity {n : ℕ} (a : Label) (ha : a ≠ 0) (e : Edge n) :
    twoBody a e ≠ identityWord n := by
  intro h
  have hi := congrFun h e.val.1
  simp [twoBody, identityWord] at hi
  exact ha hi

lemma mixed_objective {n : ℕ} (w : Weights n) :
    objective w (mixedMoments n) = (∑ e, (w e : ℝ)) / 2 := by
  simp [objective, mixedMoments, twoBody_ne_identity 1 (by decide),
    twoBody_ne_identity 2 (by decide), twoBody_ne_identity 3 (by decide),
    Finset.sum_div]

theorem objective_upper_bound {n k : ℕ} (hk : 2 ≤ k) (w : Weights n)
    {L : Word n → ℝ} (hL : Feasible k L) :
    objective w L ≤ 2 * ∑ e, (w e : ℝ) := by
  unfold objective
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  have h1 := (represented_moment_bounds hL (twoBody 1 e)
    ((support_twoBody_le 1 e).trans hk)).1
  have h2 := (represented_moment_bounds hL (twoBody 2 e)
    ((support_twoBody_le 2 e).trans hk)).1
  have h3 := (represented_moment_bounds hL (twoBody 3 e)
    ((support_twoBody_le 3 e).trans hk)).1
  have hw : (0 : ℝ) ≤ (w e : ℝ) := by positivity
  nlinarith

theorem objective_values_nonempty (k : ℕ) (G : Input) :
    {v : ℝ | ∃ L : Word G.n → ℝ, Feasible k L ∧ v = objective G.weights L}.Nonempty :=
  ⟨_, mixedMoments G.n, mixed_feasible G.n k, rfl⟩

theorem objective_values_bddAbove (k : ℕ) (hk : 2 ≤ k) (G : Input) :
    BddAbove {v : ℝ | ∃ L : Word G.n → ℝ, Feasible k L ∧ v = objective G.weights L} := by
  refine ⟨2 * ∑ e, (G.weights e : ℝ), ?_⟩
  rintro v ⟨L, hL, rfl⟩
  exact objective_upper_bound hk G.weights hL

theorem value_bounds (k : ℕ) (hk : 2 ≤ k) (G : Input) :
    (∑ e, (G.weights e : ℝ)) / 2 ≤ value k G ∧
      value k G ≤ 2 * ∑ e, (G.weights e : ℝ) := by
  constructor
  · have hmem : objective G.weights (mixedMoments G.n) ∈
        {v : ℝ | ∃ L : Word G.n → ℝ, Feasible k L ∧ v = objective G.weights L} :=
      ⟨mixedMoments G.n, mixed_feasible G.n k, rfl⟩
    have h := le_csSup (objective_values_bddAbove k hk G) hmem
    simpa [value, mixed_objective] using h
  · apply csSup_le (objective_values_nonempty k G)
    rintro v ⟨L, hL, rfl⟩
    exact objective_upper_bound hk G.weights hL

theorem value_zero_weights (k : ℕ) (G : Input)
    (hw : ∀ e, G.weights e = 0) : value k G = 0 := by
  have hz : ∀ L : Word G.n → ℝ, objective G.weights L = 0 := by
    intro L
    simp [objective, hw]
  have hset : {v : ℝ | ∃ L : Word G.n → ℝ,
      Feasible k L ∧ v = objective G.weights L} = {0} := by
    ext v
    constructor
    · rintro ⟨L, hL, rfl⟩
      simp [hz]
    · intro hv
      have hv0 : v = 0 := Set.mem_singleton_iff.mp hv
      refine ⟨mixedMoments G.n, mixed_feasible G.n k, ?_⟩
      rw [hz, hv0]
  unfold value
  rw [hset]
  simp


end QuantumMaxCutEnergy.PauliSDP


-- Source: SDPConditioning.lean


/-!
Quantitative conditioning for the concrete Pauli moment SDP. These results
prove a rational Slater neighborhood and a quadratic-form margin; they do not
assert an SDP algorithm, a finite-bit separation routine, or a time bound.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace QuantumMaxCutEnergy.PauliSDP

lemma localProduct_comm (a b : Label) : localProduct a b = localProduct b a := by
  fin_cases a <;> fin_cases b <;> decide

lemma localPhase_swap (a b : Label) : localPhase b a = star (localPhase a b) := by
  fin_cases a <;> fin_cases b <;> norm_num [localPhase, Complex.star_def]

lemma localPhase_norm (a b : Label) : ‖localPhase a b‖ = 1 := by
  fin_cases a <;> fin_cases b <;> norm_num [localPhase]

lemma wordProduct_comm {n : ℕ} (P Q : Word n) : wordProduct P Q = wordProduct Q P := by
  funext i
  exact localProduct_comm _ _

lemma wordPhase_swap {n : ℕ} (P Q : Word n) : wordPhase Q P = star (wordPhase P Q) := by
  unfold wordPhase
  calc
    _ = ∏ i, star (localPhase (P i) (Q i)) :=
      Finset.prod_congr rfl (fun i _ => localPhase_swap (P i) (Q i))
    _ = _ := (map_prod (starRingEnd ℂ) (fun i => localPhase (P i) (Q i)) Finset.univ).symm

lemma wordPhase_re_comm {n : ℕ} (P Q : Word n) :
    (wordPhase Q P).re = (wordPhase P Q).re := by
  rw [wordPhase_swap]
  rfl

lemma wordPhase_norm {n : ℕ} (P Q : Word n) : ‖wordPhase P Q‖ = 1 := by
  simp [wordPhase, norm_prod, localPhase_norm]

lemma wordPhase_re_abs_le_one {n : ℕ} (P Q : Word n) : |(wordPhase P Q).re| ≤ 1 := by
  exact (Complex.abs_re_le_norm _).trans_eq (wordPhase_norm P Q)

theorem realGram_isHermitian {n k : ℕ} (L : Word n → ℝ) : (realGram k L).IsHermitian := by
  change (realGram k L).conjTranspose = realGram k L
  ext P Q
  simp only [Matrix.conjTranspose_apply, realGram, star_trivial,
    wordPhase_re_comm P.val Q.val, wordProduct_comm Q.val P.val]

end QuantumMaxCutEnergy.PauliSDP

namespace QMCSDPConditioning

lemma matrix_quadratic_error_bound {ι : Type*} [Fintype ι]
    (E : Matrix ι ι ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hE : ∀ i j, |E i j| ≤ ε) (x : ι → ℝ) :
    -(ε * (Fintype.card ι : ℝ)) * (∑ i, (x i) ^ 2) ≤
      star x ⬝ᵥ (E *ᵥ x) := by
  have hpoint (i j : ι) : -(ε / 2) * ((x i) ^ 2 + (x j) ^ 2) ≤
      x i * E i j * x j := by
    have hxy : 2 * |x i| * |x j| ≤ (x i) ^ 2 + (x j) ^ 2 := by
      nlinarith [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]
    have hp : |x i * E i j * x j| ≤ ε * ((x i) ^ 2 + (x j) ^ 2) / 2 := by
      calc
        _ = |E i j| * (|x i| * |x j|) := by simp only [abs_mul]; ring
        _ ≤ ε * (|x i| * |x j|) :=
          mul_le_mul_of_nonneg_right (hE i j) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hxy hε]
    have hh := (abs_le.mp hp).1
    nlinarith only [hh]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hpoint i j))
  have heq : (∑ i : ι, ∑ j : ι, -(ε / 2) * ((x i) ^ 2 + (x j) ^ 2)) =
      -(ε * (Fintype.card ι : ℝ)) * (∑ i, (x i) ^ 2) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  rw [heq] at hs
  simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
    Finset.mul_sum, mul_assoc] using hs

lemma matrix_quadratic_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hM : ∀ i j, |(M - 1) i j| ≤ ε) (x : ι → ℝ) :
    (1 - ε * (Fintype.card ι : ℝ)) * (∑ i, (x i) ^ 2) ≤
      star x ⬝ᵥ (M *ᵥ x) := by
  have hh := matrix_quadratic_error_bound (M - 1) ε hε hM x
  have hself : star x ⬝ᵥ x = ∑ i, (x i) ^ 2 := by
    simp only [dotProduct, Pi.star_apply, star_trivial, pow_two]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hself] at hh
  nlinarith only [hh]

theorem matrix_posDef_of_small_entries {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hHerm : M.IsHermitian) (ε : ℝ) (hε : 0 ≤ ε)
    (hsize : ε * (Fintype.card ι : ℝ) ≤ 1 / 2)
    (hM : ∀ i j, |(M - 1) i j| ≤ ε) : M.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hHerm
  intro x hx
  have hi : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  obtain ⟨i, hi⟩ := hi
  have hS : 0 < ∑ j, (x j) ^ 2 :=
    (sq_pos_of_ne_zero hi).trans_le (Finset.single_le_sum
      (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i))
  have hh := matrix_quadratic_lower M ε hε hM x
  have hm := mul_le_mul_of_nonneg_right hsize hS.le
  nlinarith only [hh, hm, hS]

end QMCSDPConditioning

namespace QuantumMaxCutEnergy.PauliSDP

/-- A rational radius with natural denominator, in normalized low-moment coordinates. -/
def slaterRadius (n k : ℕ) : ℝ := 1 / (2 * ((Fintype.card (Index n k) : ℝ) + 1))

lemma slaterRadius_pos (n k : ℕ) : 0 < slaterRadius n k := by
  unfold slaterRadius
  positivity

lemma slaterRadius_card_le_half (n k : ℕ) :
    slaterRadius n k * (Fintype.card (Index n k) : ℝ) ≤ 1 / 2 := by
  let N : ℝ := Fintype.card (Index n k)
  have hN : 0 ≤ N := by positivity
  have hd : 0 < 2 * (N + 1) := by positivity
  have he : slaterRadius n k * N = N / (2 * (N + 1)) := by
    unfold slaterRadius N
    ring
  change slaterRadius n k * N ≤ 1 / 2
  rw [he, div_le_iff₀ hd]
  linarith

theorem gram_small_entries {n k : ℕ} (L : Word n → ℝ)
    (hidentity : L (identityWord n) = 1)
    (hsmall : ∀ P : Word n, (support P).card ≤ 2 * k → P ≠ identityWord n →
      |L P| ≤ slaterRadius n k) :
    ∀ P Q : Index n k, |(realGram k L - 1) P Q| ≤ slaterRadius n k := by
  classical
  intro P Q
  by_cases hPQ : P = Q
  · subst Q
    simp [realGram, wordProduct_self, wordPhase_self, hidentity,
      (slaterRadius_pos n k).le]
  · have hprod : wordProduct P.val Q.val ≠ identityWord n := by
      exact (wordProduct_eq_identity_iff P.val Q.val).not.mpr
        (fun hh => hPQ (Subtype.ext hh))
    have hs : (support (wordProduct P.val Q.val)).card ≤ 2 * k := by
      have hh := support_product_card_le P.val Q.val
      have hP := P.property
      have hQ := Q.property
      omega
    simp only [Matrix.sub_apply, Matrix.one_apply, if_neg hPQ, sub_zero, realGram, abs_mul]
    exact (mul_le_mul (wordPhase_re_abs_le_one P.val Q.val) (hsmall _ hs hprod)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

/-- The mixed moment vector has an explicit rational neighborhood of strictly
positive definite Gram matrices, in the normalized affine coordinate space. -/
theorem slater_posDef {n k : ℕ} (L : Word n → ℝ)
    (hidentity : L (identityWord n) = 1)
    (hsmall : ∀ P : Word n, (support P).card ≤ 2 * k → P ≠ identityWord n →
      |L P| ≤ slaterRadius n k) : (realGram k L).PosDef := by
  classical
  exact QMCSDPConditioning.matrix_posDef_of_small_entries (realGram k L)
    (realGram_isHermitian L) (slaterRadius n k) (slaterRadius_pos n k).le
    (slaterRadius_card_le_half n k) (gram_small_entries L hidentity hsmall)

theorem slater_feasible {n k : ℕ} (L : Word n → ℝ)
    (hidentity : L (identityWord n) = 1)
    (hsmall : ∀ P : Word n, (support P).card ≤ 2 * k → P ≠ identityWord n →
      |L P| ≤ slaterRadius n k) : Feasible k L :=
  ⟨hidentity, (slater_posDef L hidentity hsmall).posSemidef⟩

end QuantumMaxCutEnergy.PauliSDP



-- Source: SDPSize.lean


/-!
Polynomial size bounds for fixed-level Pauli moment coordinates. The proof
uses a finite sparse-word encoding and counts bounded subsets. It is a size
certificate, not a certificate for enumerating or optimizing the SDP.
-/

noncomputable section
open scoped BigOperators

namespace QMCSDPConditioning

def boundedSubsetIndex {α : Type*} [Fintype α] (k : ℕ)
    (s : {s : Finset α // s.card ≤ k}) :
    Σ j : Fin (k + 1), {s : Finset α // s.card = j.val} :=
  ⟨⟨s.val.card, Nat.lt_succ_of_le s.property⟩, ⟨s.val, rfl⟩⟩

lemma boundedSubsetIndex_injective {α : Type*} [Fintype α] (k : ℕ) :
    Function.Injective (boundedSubsetIndex (α := α) k) := by
  intro s t h
  apply Subtype.ext
  exact congrArg (fun a : Σ j : Fin (k + 1), {s : Finset α // s.card = j.val} => a.2.val) h

theorem bounded_subsets_card_le {α : Type*} [Fintype α] (k : ℕ) :
    Fintype.card {s : Finset α // s.card ≤ k} ≤
      (k + 1) * (Fintype.card α + 1) ^ k := by
  classical
  calc
    _ ≤ Fintype.card (Σ j : Fin (k + 1), {s : Finset α // s.card = j.val}) :=
      Fintype.card_le_of_injective _ (boundedSubsetIndex_injective k)
    _ = ∑ j : Fin (k + 1), (Fintype.card α).choose j.val := by
      simp only [Fintype.card_sigma, Fintype.card_finset_len]
    _ ≤ ∑ _j : Fin (k + 1), (Fintype.card α + 1) ^ k := by
      apply Finset.sum_le_sum
      intro j hj
      exact (Nat.choose_le_pow _ _).trans
        ((Nat.pow_le_pow_left (Nat.le_succ _) _).trans
          (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_of_lt_succ j.isLt)))
    _ = _ := by simp

end QMCSDPConditioning

namespace QuantumMaxCutEnergy.PauliSDP

/-- The finite graph of the nonidentity entries of a Pauli word. -/
def wordGraph {n : ℕ} (P : Word n) : Finset (Fin n × Label) :=
  (support P).image (fun i => (i, P i))

lemma wordGraph_mem {n : ℕ} (P : Word n) (i : Fin n) (a : Label) :
    (i, a) ∈ wordGraph P ↔ P i ≠ 0 ∧ P i = a := by
  classical
  simp only [wordGraph, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hji⟩
    have hfirst : j = i := congrArg Prod.fst hji
    subst j
    exact ⟨(Finset.mem_filter.mp hj).2, congrArg Prod.snd hji⟩
  · rintro ⟨h0, ha⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩, by rw [ha]⟩

lemma wordGraph_card {n : ℕ} (P : Word n) : (wordGraph P).card = (support P).card := by
  classical
  apply Finset.card_image_of_injective
  intro i j h
  exact congrArg Prod.fst h

lemma wordGraph_injective (n : ℕ) : Function.Injective (wordGraph (n := n)) := by
  classical
  intro P Q h
  funext i
  by_cases hP : P i = 0
  · by_cases hQ : Q i = 0
    · exact hP.trans hQ.symm
    · have hm : (i, Q i) ∈ wordGraph Q := (wordGraph_mem Q i _).2 ⟨hQ, rfl⟩
      rw [← h] at hm
      exact ((wordGraph_mem P i _).1 hm).2
  · have hm : (i, P i) ∈ wordGraph P := (wordGraph_mem P i _).2 ⟨hP, rfl⟩
    rw [h] at hm
    exact ((wordGraph_mem Q i _).1 hm).2.symm

def indexSparseCode (n k : ℕ) (P : Index n k) :
    {s : Finset (Fin n × Label) // s.card ≤ k} :=
  ⟨wordGraph P.val, by rw [wordGraph_card]; exact P.property⟩

lemma indexSparseCode_injective (n k : ℕ) : Function.Injective (indexSparseCode n k) := by
  intro P Q h
  apply Subtype.ext
  exact wordGraph_injective n (congrArg Subtype.val h)

/-- For every fixed level k, the Gram matrix has polynomially many rows in n. -/
theorem index_card_le (n k : ℕ) :
    Fintype.card (Index n k) ≤ (k + 1) * (4 * n + 1) ^ k := by
  calc
    _ ≤ Fintype.card {s : Finset (Fin n × Label) // s.card ≤ k} :=
      Fintype.card_le_of_injective _ (indexSparseCode_injective n k)
    _ ≤ (k + 1) * (Fintype.card (Fin n × Label) + 1) ^ k :=
      QMCSDPConditioning.bounded_subsets_card_le k
    _ = _ := by simp [Label, Nat.mul_comm]

def indexSizeBound (k : ℕ) : Polynomial ℕ :=
  Polynomial.C (k + 1) * (Polynomial.C 4 * Polynomial.X + 1) ^ k

theorem index_card_le_polynomial (n k : ℕ) :
    Fintype.card (Index n k) ≤ (indexSizeBound k).eval n := by
  simpa [indexSizeBound] using index_card_le n k

theorem moment_and_gram_size_bounds (n k : ℕ) :
    Fintype.card (Index n (2 * k)) ≤ (2 * k + 1) * (4 * n + 1) ^ (2 * k) ∧
      Fintype.card (Index n k) ^ 2 ≤ ((k + 1) * (4 * n + 1) ^ k) ^ 2 :=
  ⟨index_card_le n (2 * k), Nat.pow_le_pow_left (index_card_le n k) 2⟩

end QuantumMaxCutEnergy.PauliSDP



-- Source: SDPOuterBounds.lean


noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy.PauliSDP

def restrictWord {n : ℕ} (P : Word n) (S : Finset (Fin n)) : Word n :=
  fun i => if i ∈ S then P i else 0

def outsideWord {n : ℕ} (P : Word n) (S : Finset (Fin n)) : Word n :=
  fun i => if i ∈ S then 0 else P i

lemma support_restrictWord {n : ℕ} (P : Word n) (S : Finset (Fin n)) :
    support (restrictWord P S) = support P ∩ S := by
  ext i
  by_cases hi : i ∈ S <;> simp [support, restrictWord, hi]

lemma support_outsideWord {n : ℕ} (P : Word n) (S : Finset (Fin n)) :
    support (outsideWord P S) = support P \ S := by
  ext i
  by_cases hi : i ∈ S <;> simp [support, outsideWord, hi]

lemma wordProduct_split {n : ℕ} (P : Word n) (S : Finset (Fin n)) :
    wordProduct (restrictWord P S) (outsideWord P S) = P := by
  funext i
  by_cases hi : i ∈ S <;>
    simp [wordProduct, restrictWord, outsideWord, hi,
      localProduct_identity_left, localProduct_identity_right]

lemma wordPhase_split {n : ℕ} (P : Word n) (S : Finset (Fin n)) :
    wordPhase (restrictWord P S) (outsideWord P S) = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  by_cases hs : i ∈ S <;>
    simp [restrictWord, outsideWord, hs, localPhase_identity_left, localPhase_identity_right]

/-- Every represented free moment is an entry of the level-k Gram matrix. -/
theorem exists_word_split {n k : ℕ} (P : Word n) (hP : (support P).card ≤ 2 * k) :
    ∃ A B : Index n k, wordProduct A.val B.val = P ∧ wordPhase A.val B.val = 1 := by
  classical
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq
    (s := support P) (Nat.min_le_right k (support P).card)
  have hA : (support (restrictWord P S)).card ≤ k := by
    rw [support_restrictWord]
    exact (Finset.card_le_card Finset.inter_subset_right).trans (by rw [hcard]; omega)
  have hB : (support (outsideWord P S)).card ≤ k := by
    rw [support_outsideWord, Finset.card_sdiff_of_subset hS, hcard]
    omega
  exact ⟨⟨restrictWord P S, hA⟩, ⟨outsideWord P S, hB⟩,
    wordProduct_split P S, wordPhase_split P S⟩

lemma gram_entry_bounds {n k : ℕ} {L : Word n → ℝ} (hL : Feasible k L)
    (A B : Index n k) : -1 ≤ realGram k L A B ∧ realGram k L A B ≤ 1 := by
  let f : Fin 2 → Index n k := fun i => if i = 0 then A else B
  have hM := hL.2.submatrix f
  have hplus := hM.dotProduct_mulVec_nonneg ![(1 : ℝ), 1]
  have hminus := hM.dotProduct_mulVec_nonneg ![(1 : ℝ), -1]
  have hs : realGram k L B A = realGram k L A B := by
    simp only [realGram, wordPhase_re_comm A.val B.val, wordProduct_comm B.val A.val]
  simp only [Matrix.submatrix, Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    f, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, one_ne_zero,
    if_true, if_false, Pi.star_apply, star_trivial] at hplus hminus
  simp only [realGram_diag hL, hs] at hplus hminus
  constructor <;> linarith

/-- All support-at-most-2k coordinates are bounded, not merely those of order k. -/
theorem low_moment_bounds {n k : ℕ} {L : Word n → ℝ} (hL : Feasible k L)
    (P : Word n) (hP : (support P).card ≤ 2 * k) : -1 ≤ L P ∧ L P ≤ 1 := by
  obtain ⟨A, B, hp, hphase⟩ := exists_word_split P hP
  have hh := gram_entry_bounds hL A B
  simpa only [realGram, hp, hphase, Complex.one_re, one_mul] using hh

/-- An outer squared-radius bound on precisely the finite free moment coordinates.
No bound is claimed for irrelevant moments of support greater than 2k. -/
theorem low_moment_sum_sq_le_card {n k : ℕ} {L : Word n → ℝ} (hL : Feasible k L) :
    (∑ P : Index n (2 * k), (L P.val) ^ 2) ≤
      (Fintype.card (Index n (2 * k)) : ℝ) := by
  calc
    _ ≤ ∑ _P : Index n (2 * k), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro P hP
      exact (sq_le_one_iff_abs_le_one (L P.val)).2
        (abs_le.mpr (low_moment_bounds hL P.val P.property))
    _ = _ := by simp

end QuantumMaxCutEnergy.PauliSDP



-- Source: SDPRationalData.lean


noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy.PauliSDP

def IsPauliPhase (z : ℂ) : Prop := z = 1 ∨ z = -1 ∨ z = Complex.I ∨ z = -Complex.I

lemma localPhase_isPauliPhase (a b : Label) : IsPauliPhase (localPhase a b) := by
  fin_cases a <;> fin_cases b <;> norm_num [localPhase, IsPauliPhase]

lemma IsPauliPhase.mul {z w : ℂ} (hz : IsPauliPhase z) (hw : IsPauliPhase w) :
    IsPauliPhase (z * w) := by
  rcases hz with rfl | rfl | rfl | rfl <;>
    rcases hw with rfl | rfl | rfl | rfl <;>
      norm_num [IsPauliPhase, Complex.I_mul_I]

lemma wordPhase_isPauliPhase {n : ℕ} (P Q : Word n) : IsPauliPhase (wordPhase P Q) := by
  exact Finset.prod_induction (fun i => localPhase (P i) (Q i)) IsPauliPhase
    (fun _ _ ha hb => ha.mul hb) (Or.inl rfl)
    (fun i _ => localPhase_isPauliPhase (P i) (Q i))

/-- Every Gram coefficient is exactly an integer of magnitude at most one. -/
theorem wordPhase_re_integer {n : ℕ} (P Q : Word n) :
    ∃ z : ℤ, (-1 ≤ z ∧ z ≤ 1) ∧ (wordPhase P Q).re = (z : ℝ) := by
  rcases wordPhase_isPauliPhase P Q with h | h | h | h
  · exact ⟨1, by norm_num, by rw [h]; norm_num⟩
  · exact ⟨-1, by norm_num, by rw [h]; norm_num⟩
  · exact ⟨0, by norm_num, by rw [h]; norm_num⟩
  · exact ⟨0, by norm_num, by rw [h]; norm_num⟩

theorem rational_moments_gram_rational {n k : ℕ} (L : Word n → ℚ)
    (P Q : Index n k) :
    ∃ q : ℚ, realGram k (fun W => (L W : ℝ)) P Q = (q : ℝ) := by
  obtain ⟨z, _, hz⟩ := wordPhase_re_integer P.val Q.val
  refine ⟨(z : ℚ) * L (wordProduct P.val Q.val), ?_⟩
  simp [realGram, hz]

end QuantumMaxCutEnergy.PauliSDP



-- Source: SDPGeometry.lean


/-!
Explicit rational inner and outer radius data for the fixed-level Pauli SDP.
The finite coordinate space consists only of moments with support at most 2k.
No optimization or finite-bit running-time theorem is asserted here.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace QuantumMaxCutEnergy.PauliSDP

theorem slater_quadratic_lower {n k : ℕ} (L : Word n → ℝ)
    (hidentity : L (identityWord n) = 1)
    (hsmall : ∀ P : Word n, (support P).card ≤ 2 * k → P ≠ identityWord n →
      |L P| ≤ slaterRadius n k) (x : Index n k → ℝ) :
    (1 / 2 : ℝ) * (∑ P, (x P) ^ 2) ≤ star x ⬝ᵥ ((realGram k L) *ᵥ x) := by
  classical
  have hh := QMCSDPConditioning.matrix_quadratic_lower (realGram k L)
    (slaterRadius n k) (slaterRadius_pos n k).le
    (gram_small_entries L hidentity hsmall) x
  have hsize := slaterRadius_card_le_half n k
  have hc : (1 / 2 : ℝ) ≤ 1 - slaterRadius n k * (Fintype.card (Index n k) : ℝ) := by
    linarith
  exact (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun P _ => sq_nonneg (x P)))).trans hh

def conditioningSize (n k : ℕ) : ℕ := (k + 1) * (4 * n + 1) ^ k

/-- A rational lower bound for the intrinsic Slater radius with polynomial denominator. -/
def rationalInnerRadius (n k : ℕ) : ℚ := 1 / (2 * (conditioningSize n k + 1) : ℚ)

def rationalOuterRadius (n k : ℕ) : ℚ := conditioningSize n (2 * k) + 1

lemma rationalInnerRadius_cast (n k : ℕ) :
    (rationalInnerRadius n k : ℝ) = 1 / (2 * ((conditioningSize n k : ℝ) + 1)) := by
  simp [rationalInnerRadius]

lemma rationalInnerRadius_pos (n k : ℕ) : 0 < rationalInnerRadius n k := by
  unfold rationalInnerRadius
  positivity

lemma rationalInnerRadius_le_slater (n k : ℕ) :
    (rationalInnerRadius n k : ℝ) ≤ slaterRadius n k := by
  have hcard : (Fintype.card (Index n k) : ℝ) ≤ (conditioningSize n k : ℝ) := by
    exact_mod_cast index_card_le n k
  rw [rationalInnerRadius_cast, slaterRadius]
  apply one_div_le_one_div_of_le (by positivity)
  linarith

theorem feasible_of_polynomial_inner_radius {n k : ℕ} (L : Word n → ℝ)
    (hidentity : L (identityWord n) = 1)
    (hsmall : ∀ P : Word n, (support P).card ≤ 2 * k → P ≠ identityWord n →
      |L P| ≤ (rationalInnerRadius n k : ℝ)) : Feasible k L :=
  slater_feasible L hidentity (fun P hP hne =>
    (hsmall P hP hne).trans (rationalInnerRadius_le_slater n k))

theorem gram_lower_of_polynomial_inner_radius {n k : ℕ} (L : Word n → ℝ)
    (hidentity : L (identityWord n) = 1)
    (hsmall : ∀ P : Word n, (support P).card ≤ 2 * k → P ≠ identityWord n →
      |L P| ≤ (rationalInnerRadius n k : ℝ)) (x : Index n k → ℝ) :
    (1 / 2 : ℝ) * (∑ P, (x P) ^ 2) ≤ star x ⬝ᵥ ((realGram k L) *ᵥ x) :=
  slater_quadratic_lower L hidentity (fun P hP hne =>
    (hsmall P hP hne).trans (rationalInnerRadius_le_slater n k)) x

theorem low_moment_sum_sq_le_polynomial {n k : ℕ} {L : Word n → ℝ}
    (hL : Feasible k L) :
    (∑ P : Index n (2 * k), (L P.val) ^ 2) ≤ (conditioningSize n (2 * k) : ℝ) := by
  exact (low_moment_sum_sq_le_card hL).trans (by exact_mod_cast index_card_le n (2 * k))

theorem low_moment_sum_sq_le_outer_radius_sq {n k : ℕ} {L : Word n → ℝ}
    (hL : Feasible k L) :
    (∑ P : Index n (2 * k), (L P.val) ^ 2) ≤ (rationalOuterRadius n k : ℝ) ^ 2 := by
  have hh := low_moment_sum_sq_le_polynomial hL
  have hN : (0 : ℝ) ≤ (conditioningSize n (2 * k) : ℝ) := by positivity
  have hr : (rationalOuterRadius n k : ℝ) = (conditioningSize n (2 * k) : ℝ) + 1 := by
    simp [rationalOuterRadius]
  rw [hr]
  nlinarith only [hh, hN]

/-- The center itself has exact rational coordinates 0 and 1. -/
def rationalMixedMoments (n : ℕ) (P : Word n) : ℚ := if P = identityWord n then 1 else 0

lemma rationalMixedMoments_cast (n : ℕ) (P : Word n) :
    (rationalMixedMoments n P : ℝ) = mixedMoments n P := by
  unfold rationalMixedMoments mixedMoments
  split_ifs <;> norm_num

theorem rational_center_gram (n k : ℕ) :
    realGram k (fun P => (rationalMixedMoments n P : ℝ)) = 1 := by
  simp only [rationalMixedMoments_cast]
  exact mixed_realGram n k

/-- The actual Euclidean vector of the relevant finite moments. -/
def momentVector {n : ℕ} (k : ℕ) (L : Word n → ℝ) :
    EuclideanSpace ℝ (Index n (2 * k)) := WithLp.toLp 2 (fun P => L P.val)

/-- A Euclidean ball around the rational mixed center, relative to L(I)=1,
lies inside the feasible set. -/
theorem feasible_of_euclidean_inner_ball {n k : ℕ} (L : Word n → ℝ)
    (hidentity : L (identityWord n) = 1)
    (hball : ‖momentVector k L - momentVector k (mixedMoments n)‖ ≤
      (rationalInnerRadius n k : ℝ)) : Feasible k L := by
  apply feasible_of_polynomial_inner_radius L hidentity
  intro P hP hne
  have hh := (PiLp.norm_apply_le
    (momentVector k L - momentVector k (mixedMoments n)) (⟨P, hP⟩ : Index n (2 * k))).trans hball
  simpa [momentVector, mixedMoments, hne] using hh

theorem feasible_euclidean_outer_ball {n k : ℕ} {L : Word n → ℝ}
    (hL : Feasible k L) : ‖momentVector k L‖ ≤ (rationalOuterRadius n k : ℝ) := by
  have hsq : ‖momentVector k L‖ ^ 2 ≤ (rationalOuterRadius n k : ℝ) ^ 2 := by
    simpa only [EuclideanSpace.real_norm_sq_eq, momentVector, PiLp.toLp_apply] using
      low_moment_sum_sq_le_outer_radius_sq hL
  have hR : (0 : ℝ) ≤ (rationalOuterRadius n k : ℝ) := by
    simp [rationalOuterRadius]
    positivity
  exact (sq_le_sq₀ (norm_nonneg _) hR).1 hsq

end QuantumMaxCutEnergy.PauliSDP



-- Source: SDPObjectiveLipschitz.lean


noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy.PauliSDP

/-- A certified error budget for rationally approximating the objective moments. -/
theorem objective_lipschitz {n : ℕ} (w : Weights n) (L L' : Word n → ℝ)
    (δ : ℝ) (hclose : ∀ P : Word n, (support P).card ≤ 2 → |L P - L' P| ≤ δ) :
    |objective w L - objective w L'| ≤
      (3 * δ / 2) * (∑ e, (w e : ℝ)) := by
  have hs (e : Edge n) :
      |(L (twoBody 1 e) - L' (twoBody 1 e)) +
        (L (twoBody 2 e) - L' (twoBody 2 e)) +
        (L (twoBody 3 e) - L' (twoBody 3 e))| ≤ 3 * δ := by
    calc
      _ ≤ |(L (twoBody 1 e) - L' (twoBody 1 e)) +
          (L (twoBody 2 e) - L' (twoBody 2 e))| +
          |L (twoBody 3 e) - L' (twoBody 3 e)| := abs_add_le _ _
      _ ≤ (|L (twoBody 1 e) - L' (twoBody 1 e)| +
          |L (twoBody 2 e) - L' (twoBody 2 e)|) +
          |L (twoBody 3 e) - L' (twoBody 3 e)| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ _ := by
        have h1 := hclose (twoBody 1 e) (support_twoBody_le 1 e)
        have h2 := hclose (twoBody 2 e) (support_twoBody_le 2 e)
        have h3 := hclose (twoBody 3 e) (support_twoBody_le 3 e)
        linarith
  unfold objective
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ e : Edge n,
        |(w e : ℝ) * (1 - L (twoBody 1 e) - L (twoBody 2 e) - L (twoBody 3 e)) / 2 -
          (w e : ℝ) * (1 - L' (twoBody 1 e) - L' (twoBody 2 e) - L' (twoBody 3 e)) / 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e : Edge n, (3 * δ / 2) * (w e : ℝ) := by
      apply Finset.sum_le_sum
      intro e he
      have hid :
          (w e : ℝ) * (1 - L (twoBody 1 e) - L (twoBody 2 e) - L (twoBody 3 e)) / 2 -
          (w e : ℝ) * (1 - L' (twoBody 1 e) - L' (twoBody 2 e) - L' (twoBody 3 e)) / 2 =
          -((w e : ℝ) / 2) * ((L (twoBody 1 e) - L' (twoBody 1 e)) +
            (L (twoBody 2 e) - L' (twoBody 2 e)) + (L (twoBody 3 e) - L' (twoBody 3 e))) := by
        ring
      rw [hid, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (w e : ℝ) / 2)]
      exact (mul_le_mul_of_nonneg_left (hs e) (by positivity)).trans_eq (by ring)
    _ = _ := (Finset.mul_sum _ _ _).symm

end QuantumMaxCutEnergy.PauliSDP



-- Source: SDPRobustRounding.lean


/-!
A certified feasibility-preserving rounding step for moment coordinates:
mix with the rational identity center, then perturb the low-order moments.
The result is analytic conditioning for a finite-bit solver, not a solver
or a polynomial-time certificate by itself.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace QuantumMaxCutEnergy.PauliSDP

def mixMoments {n : ℕ} (τ : ℝ) (L : Word n → ℝ) (P : Word n) : ℝ :=
  (1 - τ) * L P + τ * mixedMoments n P

lemma realGram_mix {n k : ℕ} (τ : ℝ) (L : Word n → ℝ) :
    realGram k (mixMoments τ L) =
      (1 - τ) • realGram k L + τ • (1 : Matrix (Index n k) (Index n k) ℝ) := by
  have hh : realGram k (mixMoments τ L) =
      (1 - τ) • realGram k L + τ • realGram k (mixedMoments n) := by
    ext P Q
    simp only [realGram, mixMoments, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  simpa only [mixed_realGram] using hh

lemma realGram_quadratic_mix {n k : ℕ} (τ : ℝ) (L : Word n → ℝ)
    (x : Index n k → ℝ) :
    star x ⬝ᵥ ((realGram k (mixMoments τ L)) *ᵥ x) =
      (1 - τ) * (star x ⬝ᵥ ((realGram k L) *ᵥ x)) + τ * (∑ P, (x P) ^ 2) := by
  classical
  rw [realGram_mix]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul]
  congr 1
  congr 1
  simp only [dotProduct, Pi.star_apply, star_trivial, pow_two]

lemma realGram_difference_entries {n k : ℕ} (L L' : Word n → ℝ) (δ : ℝ)
    (hclose : ∀ P : Word n, (support P).card ≤ 2 * k → |L' P - L P| ≤ δ) :
    ∀ P Q : Index n k, |(realGram k L' - realGram k L) P Q| ≤ δ := by
  intro P Q
  have hs : (support (wordProduct P.val Q.val)).card ≤ 2 * k := by
    have hh := support_product_card_le P.val Q.val
    have hP := P.property
    have hQ := Q.property
    omega
  have hid : (realGram k L' - realGram k L) P Q =
      (wordPhase P.val Q.val).re * (L' (wordProduct P.val Q.val) - L (wordProduct P.val Q.val)) := by
    simp only [Matrix.sub_apply, realGram]
    ring
  rw [hid, abs_mul]
  exact (mul_le_mul (wordPhase_re_abs_le_one P.val Q.val) (hclose _ hs)
    (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

/-- After mixing toward the identity center, sufficiently fine coordinate
rounding leaves a positive-definite Gram matrix. -/
theorem mixed_rounding_posDef {n k : ℕ} {L : Word n → ℝ} (hL : Feasible k L)
    (τ δ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hδ : 0 ≤ δ)
    (hbudget : δ * (Fintype.card (Index n k) : ℝ) ≤ τ / 2)
    (L' : Word n → ℝ)
    (hclose : ∀ P : Word n, (support P).card ≤ 2 * k →
      |L' P - mixMoments τ L P| ≤ δ) : (realGram k L').PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (realGram_isHermitian L')
  intro x hx
  have hi : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  obtain ⟨i, hi⟩ := hi
  have hS : 0 < ∑ j, (x j) ^ 2 :=
    (sq_pos_of_ne_zero hi).trans_le (Finset.single_le_sum
      (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i))
  have hbase := hL.2.dotProduct_mulVec_nonneg x
  have hmix : τ * (∑ P, (x P) ^ 2) ≤
      star x ⬝ᵥ ((realGram k (mixMoments τ L)) *ᵥ x) := by
    rw [realGram_quadratic_mix]
    have hh := mul_nonneg (sub_nonneg.mpr hτ1) hbase
    linarith
  have herr := QMCSDPConditioning.matrix_quadratic_error_bound
    (realGram k L' - realGram k (mixMoments τ L)) δ hδ
    (realGram_difference_entries (mixMoments τ L) L' δ hclose) x
  rw [Matrix.sub_mulVec, dotProduct_sub] at herr
  have hbud := mul_le_mul_of_nonneg_right hbudget hS.le
  have hpos : 0 < (τ / 2) * (∑ P, (x P) ^ 2) := mul_pos (by linarith) hS
  nlinarith only [hmix, herr, hbud, hpos]

theorem mixed_rounding_feasible {n k : ℕ} {L : Word n → ℝ} (hL : Feasible k L)
    (τ δ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hδ : 0 ≤ δ)
    (hbudget : δ * (Fintype.card (Index n k) : ℝ) ≤ τ / 2)
    (L' : Word n → ℝ) (hidentity : L' (identityWord n) = 1)
    (hclose : ∀ P : Word n, (support P).card ≤ 2 * k →
      |L' P - mixMoments τ L P| ≤ δ) : Feasible k L' :=
  ⟨hidentity, (mixed_rounding_posDef hL τ δ hτ hτ1 hδ hbudget L' hclose).posSemidef⟩

end QuantumMaxCutEnergy.PauliSDP





open QuantumMaxCutEnergy.PauliSDP

theorem solution (n k : ℕ) :
    Fintype.card (QuantumMaxCutEnergy.PauliSDP.Index n k) ≤ (k + 1) * (4 * n + 1) ^ k ∧
    (∀ L : QuantumMaxCutEnergy.PauliSDP.Word n → ℝ,
      QuantumMaxCutEnergy.PauliSDP.Feasible k L →
      (∀ P : QuantumMaxCutEnergy.PauliSDP.Word n,
        (QuantumMaxCutEnergy.PauliSDP.support P).card ≤ 2 * k → -1 ≤ L P ∧ L P ≤ 1) ∧
      (∑ P : QuantumMaxCutEnergy.PauliSDP.Index n (2 * k), (L P.val) ^ 2) ≤
        (((2 * k + 1) * (4 * n + 1) ^ (2 * k) : ℕ) : ℝ)) ∧
    (∀ L : QuantumMaxCutEnergy.PauliSDP.Word n → ℝ,
      L (QuantumMaxCutEnergy.PauliSDP.identityWord n) = 1 →
      (∀ P : QuantumMaxCutEnergy.PauliSDP.Word n,
        (QuantumMaxCutEnergy.PauliSDP.support P).card ≤ 2 * k →
        P ≠ QuantumMaxCutEnergy.PauliSDP.identityWord n →
        |L P| ≤ 1 / (2 * ((((k + 1) * (4 * n + 1) ^ k : ℕ) : ℝ) + 1))) →
      QuantumMaxCutEnergy.PauliSDP.Feasible k L ∧
      (QuantumMaxCutEnergy.PauliSDP.realGram k L).PosDef ∧
      ∀ x : QuantumMaxCutEnergy.PauliSDP.Index n k → ℝ,
        (1 / 2 : ℝ) * (∑ P, (x P) ^ 2) ≤
          star x ⬝ᵥ ((QuantumMaxCutEnergy.PauliSDP.realGram k L) *ᵥ x))  := by
  refine ⟨index_card_le n k, ?_, ?_⟩
  · intro L hL
    exact ⟨fun P hP => low_moment_bounds hL P hP, low_moment_sum_sq_le_polynomial hL⟩
  · intro L hidentity hsmall
    have hs : ∀ P : Word n, (support P).card ≤ 2 * k → P ≠ identityWord n →
        |L P| ≤ (rationalInnerRadius n k : ℝ) := by
      intro P hP hne
      simpa only [rationalInnerRadius_cast, conditioningSize] using hsmall P hP hne
    have hs' := fun P hP hne => (hs P hP hne).trans (rationalInnerRadius_le_slater n k)
    exact ⟨feasible_of_polynomial_inner_radius L hidentity hs,
      slater_posDef L hidentity hs', gram_lower_of_polynomial_inner_radius L hidentity hs⟩

#print axioms solution
