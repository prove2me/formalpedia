-- Prove2me | solution 1 for QuantumMaxCutEnergy.PauliSDP.low_moment_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T15:13:00.701626+00:00
-- url     : https://prove2.me/submissions/7c1afec5-a037-4b4c-a169-119ad652e283

import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib

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

#print axioms mixed_feasible
#print axioms represented_moment_bounds
#print axioms objective_values_bddAbove
#print axioms value_bounds
#print axioms value_zero_weights

end QuantumMaxCutEnergy.PauliSDP


open scoped BigOperators

theorem publication_pauli_wellposed
    (k : ℕ) (hk : 2 ≤ k) (G : QuantumMaxCutEnergy.Input) :
    (∃ L : QuantumMaxCutEnergy.PauliSDP.Word G.n → ℝ,
      QuantumMaxCutEnergy.PauliSDP.Feasible k L) ∧
    (∑ e, (G.weights e : ℝ)) / 2 ≤ QuantumMaxCutEnergy.PauliSDP.value k G ∧
    QuantumMaxCutEnergy.PauliSDP.value k G ≤ 2 * ∑ e, (G.weights e : ℝ) ∧
    ((∀ e, G.weights e = 0) → QuantumMaxCutEnergy.PauliSDP.value k G = 0) := by
  refine ⟨⟨_, QuantumMaxCutEnergy.PauliSDP.mixed_feasible G.n k⟩,
    (QuantumMaxCutEnergy.PauliSDP.value_bounds k hk G).1,
    (QuantumMaxCutEnergy.PauliSDP.value_bounds k hk G).2, ?_⟩
  exact QuantumMaxCutEnergy.PauliSDP.value_zero_weights k G

theorem solution
    {n k : ℕ} (hk : 2 ≤ k)
    (L L' : QuantumMaxCutEnergy.PauliSDP.Word n → ℝ)
    (h : ∀ P : QuantumMaxCutEnergy.PauliSDP.Word n,
      (QuantumMaxCutEnergy.PauliSDP.support P).card ≤ 2 * k → L P = L' P) :
    (QuantumMaxCutEnergy.PauliSDP.Feasible k L ↔
      QuantumMaxCutEnergy.PauliSDP.Feasible k L') ∧
    ∀ w : QuantumMaxCutEnergy.Weights n,
      QuantumMaxCutEnergy.PauliSDP.objective w L =
        QuantumMaxCutEnergy.PauliSDP.objective w L' := by
  have hI := h (QuantumMaxCutEnergy.PauliSDP.identityWord n) (by
    simp [QuantumMaxCutEnergy.PauliSDP.support_identity])
  have hGram := QuantumMaxCutEnergy.PauliSDP.realGram_congr_low_moments L L' h
  constructor
  · simp only [QuantumMaxCutEnergy.PauliSDP.Feasible, hI, hGram]
  · intro w
    unfold QuantumMaxCutEnergy.PauliSDP.objective
    apply Finset.sum_congr rfl
    intro e he
    have hb (a : QuantumMaxCutEnergy.PauliSDP.Label) :
        (QuantumMaxCutEnergy.PauliSDP.support
          (QuantumMaxCutEnergy.PauliSDP.twoBody a e)).card ≤ 2 * k :=
      (QuantumMaxCutEnergy.PauliSDP.support_twoBody_le a e).trans (by omega)
    rw [h _ (hb 1), h _ (hb 2), h _ (hb 3)]

#print axioms publication_pauli_wellposed
#print axioms solution
