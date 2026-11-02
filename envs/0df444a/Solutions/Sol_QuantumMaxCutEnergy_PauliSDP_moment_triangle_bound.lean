-- Prove2me | solution 1 for QuantumMaxCutEnergy.PauliSDP.moment_triangle_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T16:03:37.902906+00:00
-- url     : https://prove2.me/submissions/2105638f-9bc3-41d8-87b4-a49c051472ba

import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Definitions.Def_QMaxCutSDP_Rounding_Model
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

def identityIndex (n k : ℕ) : Index n k :=
  ⟨identityWord n, by simp [support_identity]⟩

lemma realGram_diag {n k : ℕ} {L : Word n → ℝ} (hL : Feasible k L)
    (P : Index n k) : realGram k L P P = 1 := by
  simp [realGram, wordProduct_self, wordPhase_self, hL.1]

lemma realGram_identity_left {n k : ℕ} (L : Word n → ℝ) (P : Index n k) :
    realGram k L (identityIndex n k) P = L P.val := by
  simp [realGram, identityIndex, wordProduct_identity_left, wordPhase_identity_left]

lemma realGram_identity_right {n k : ℕ} (L : Word n → ℝ) (P : Index n k) :
    realGram k L P (identityIndex n k) = L P.val := by
  simp [realGram, identityIndex, wordProduct_identity_right, wordPhase_identity_right]

end QuantumMaxCutEnergy.PauliSDP

noncomputable section
open scoped BigOperators MatrixOrder
open Matrix

namespace QuantumMaxCutEnergy.PauliSDP.LeeBridge

def color (a : Fin 3) : Label := ⟨a.val + 1, by omega⟩

def singleWord {n : ℕ} (a : Fin 3) (i : Fin n) : Word n :=
  fun t => if t = i then color a else 0

def pairWord {n : ℕ} (a : Fin 3) (i j : Fin n) : Word n :=
  fun t => if t = i ∨ t = j then color a else 0

lemma single_support_le {n : ℕ} (a : Fin 3) (i : Fin n) :
    (support (singleWord a i)).card ≤ 1 := by
  have hs : support (singleWord a i) ⊆ ({i} : Finset (Fin n)) := by
    intro t ht
    have hn := (Finset.mem_filter.mp ht).2
    by_cases h : t = i
    · simpa using h
    · simp [singleWord, h] at hn
  simpa using Finset.card_le_card hs

lemma pair_support_le {n : ℕ} (a : Fin 3) (i j : Fin n) :
    (support (pairWord a i j)).card ≤ 2 := by
  have hs : support (pairWord a i j) ⊆ ({i, j} : Finset (Fin n)) := by
    intro t ht
    have hn := (Finset.mem_filter.mp ht).2
    by_cases h : t = i ∨ t = j
    · simpa using h
    · simp [pairWord, h] at hn
  exact (Finset.card_le_card hs).trans Finset.card_le_two

def singleIndex {n k : ℕ} (hk : 2 ≤ k) (a : Fin 3) (i : Fin n) : Index n k :=
  ⟨singleWord a i, (single_support_le a i).trans (by omega)⟩

def pairIndex {n k : ℕ} (hk : 2 ≤ k) (a : Fin 3) (i j : Fin n) : Index n k :=
  ⟨pairWord a i j, (pair_support_le a i j).trans hk⟩

lemma pairWord_symm {n : ℕ} (a : Fin 3) (i j : Fin n) :
    pairWord a i j = pairWord a j i := by
  funext t
  simp only [pairWord, or_comm]

lemma pairIndex_symm {n k : ℕ} (hk : 2 ≤ k) (a : Fin 3) (i j : Fin n) :
    pairIndex hk a i j = pairIndex hk a j i :=
  Subtype.ext (pairWord_symm a i j)

lemma phase_single_color_ne (a b : Fin 3) (hab : a ≠ b) :
    (localPhase (color a) (color b)).re = 0 := by
  fin_cases a <;> fin_cases b <;> norm_num [color, localPhase] at *

lemma product_color_third (a b c : Fin 3)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    localProduct (color a) (color b) = color c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [color, localProduct] at * <;> decide

lemma phase_color_ne_sq (a b : Fin 3) (hab : a ≠ b) :
    (localPhase (color a) (color b)) ^ 2 = -1 := by
  fin_cases a <;> fin_cases b <;> norm_num [color, localPhase] at *

lemma phase_reduce {n : ℕ} (P Q : Word n) (S : Finset (Fin n))
    (h : ∀ t, t ∉ S → localPhase (P t) (Q t) = 1) :
    wordPhase P Q = ∏ t ∈ S, localPhase (P t) (Q t) := by
  unfold wordPhase
  symm
  exact Finset.prod_subset (Finset.subset_univ S) (fun t ht hn => h t hn)

lemma phase_single_single {n : ℕ} (a b : Fin 3) (i : Fin n) :
    wordPhase (singleWord a i) (singleWord b i) = localPhase (color a) (color b) := by
  rw [phase_reduce _ _ {i} (by
    intro t ht
    have hti : t ≠ i := by simpa using ht
    simp [singleWord, hti, localPhase])]
  simp [singleWord]

lemma phase_single_disjoint {n : ℕ} (a : Fin 3) (i j : Fin n) (hij : i ≠ j) :
    wordPhase (singleWord a i) (singleWord a j) = 1 := by
  apply Finset.prod_eq_one
  intro t ht
  by_cases hti : t = i <;> by_cases htj : t = j <;>
    simp_all [singleWord, localPhase_self, localPhase_identity_left,
      localPhase_identity_right]

lemma product_single_disjoint {n : ℕ} (a : Fin 3) (i j : Fin n) (hij : i ≠ j) :
    wordProduct (singleWord a i) (singleWord a j) = pairWord a i j := by
  funext t
  by_cases hti : t = i <;> by_cases htj : t = j <;>
    simp_all [singleWord, pairWord, wordProduct, localProduct_self,
      localProduct_identity_left, localProduct_identity_right]

lemma phase_pair_chain_same {n : ℕ} (a : Fin 3) (i j l : Fin n) :
    wordPhase (pairWord a i j) (pairWord a j l) = 1 := by
  apply Finset.prod_eq_one
  intro t ht
  by_cases h1 : t = i ∨ t = j <;> by_cases h2 : t = j ∨ t = l <;>
    simp [pairWord, h1, h2, localPhase_self, localPhase_identity_left,
      localPhase_identity_right]

lemma product_pair_chain_same {n : ℕ} (a : Fin 3) (i j l : Fin n)
    (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    wordProduct (pairWord a i j) (pairWord a j l) = pairWord a i l := by
  funext t
  by_cases hti : t = i <;> by_cases htj : t = j <;> by_cases htl : t = l <;>
    simp_all [pairWord, wordProduct, localProduct_self,
      localProduct_identity_left, localProduct_identity_right]

lemma phase_pair_chain_ne {n : ℕ} (a b : Fin 3) (i j l : Fin n)
    (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    wordPhase (pairWord a i j) (pairWord b j l) = localPhase (color a) (color b) := by
  rw [phase_reduce _ _ {j} (by
    intro t ht
    have htj : t ≠ j := by simpa using ht
    by_cases hti : t = i <;> by_cases htl : t = l <;>
      simp_all [pairWord, localPhase_identity_left, localPhase_identity_right])]
  simp [pairWord]

lemma phase_pair_colors {n : ℕ} (a b : Fin 3) (i j : Fin n) (hij : i ≠ j) :
    wordPhase (pairWord a i j) (pairWord b i j) =
      (localPhase (color a) (color b)) ^ 2 := by
  rw [phase_reduce _ _ {i, j} (by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    simp [pairWord, ht.1, ht.2, localPhase])]
  simp [pairWord, hij, pow_two]

lemma product_pair_colors {n : ℕ} (a b c : Fin 3) (i j : Fin n)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    wordProduct (pairWord a i j) (pairWord b i j) = pairWord c i j := by
  funext t
  by_cases h : t = i ∨ t = j
  · simp [pairWord, wordProduct, h, product_color_third a b c hab hbc hac]
  · simp [pairWord, wordProduct, h, localProduct]

/-- A genuine finite-dimensional Gram representation of the specified
PSD moment matrix. This supplies Lee's vector variables, not an
assumed feasible SDP solution or a monogamy premise. -/
theorem gram_vectors {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.PosSemidef) :
    ∃ V : ι → (Fin (Fintype.card ι) → ℝ),
      ∀ P Q, V P ⬝ᵥ V Q = M P Q := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨fun P s => B (e.symm s) P, ?_⟩
  intro P Q
  rw [hB]
  simpa only [dotProduct, star_eq_conjTranspose, Matrix.mul_apply,
    Matrix.conjTranspose_apply, star_trivial] using
    e.symm.sum_comp (fun t => B t P * B t Q)

def asLeeVector {n k N : ℕ} (hk : 2 ≤ k) (V : Index n k → (Fin N → ℝ)) :
    QMaxCutSDP.Rounding.SDPVec n N where
  v0 := V (identityIndex n k)
  vi i a := V (singleIndex hk a i)
  vij i j a := V (pairIndex hk a i j)

/-- Every feasible concrete Pauli moment matrix gives a vector tuple
satisfying all of Lee's explicit constraints. No star bound is assumed. -/
theorem asLeeVector_feasible {n k N : ℕ} (hk : 2 ≤ k)
    (L : Word n → ℝ) (hL : Feasible k L) (V : Index n k → (Fin N → ℝ))
    (hV : ∀ P Q, V P ⬝ᵥ V Q = realGram k L P Q) :
    QMaxCutSDP.Rounding.IsSFeasible (asLeeVector hk V) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change V (identityIndex n k) ⬝ᵥ V (identityIndex n k) = 1
    rw [hV]
    exact realGram_diag hL _
  · intro i a
    change V (singleIndex hk a i) ⬝ᵥ V (singleIndex hk a i) = 1
    rw [hV]
    exact realGram_diag hL _
  · intro i a b hab
    change V (singleIndex hk a i) ⬝ᵥ V (singleIndex hk b i) = 0
    rw [hV]
    change (wordPhase (singleWord a i) (singleWord b i)).re *
      L (wordProduct (singleWord a i) (singleWord b i)) = 0
    rw [phase_single_single, phase_single_color_ne a b hab]
    ring
  · intro i j a hij
    change V (pairIndex hk a i j) ⬝ᵥ V (pairIndex hk a i j) = 1
    rw [hV]
    exact realGram_diag hL _
  · intro i j a hij
    change V (singleIndex hk a i) ⬝ᵥ V (singleIndex hk a j) =
      V (pairIndex hk a i j) ⬝ᵥ V (identityIndex n k)
    rw [hV, hV, realGram_identity_right]
    change (wordPhase (singleWord a i) (singleWord a j)).re *
      L (wordProduct (singleWord a i) (singleWord a j)) = L (pairWord a i j)
    rw [phase_single_disjoint a i j hij, product_single_disjoint a i j hij]
    simp
  · intro i j l a hij hjl hil
    change V (pairIndex hk a i j) ⬝ᵥ V (pairIndex hk a j l) =
      V (pairIndex hk a i l) ⬝ᵥ V (identityIndex n k)
    rw [hV, hV, realGram_identity_right]
    change (wordPhase (pairWord a i j) (pairWord a j l)).re *
      L (wordProduct (pairWord a i j) (pairWord a j l)) = L (pairWord a i l)
    rw [phase_pair_chain_same, product_pair_chain_same a i j l hij hjl hil]
    simp
  · intro i j l a b hij hjl hil hab
    change V (pairIndex hk a i j) ⬝ᵥ V (pairIndex hk b j l) = 0
    rw [hV]
    change (wordPhase (pairWord a i j) (pairWord b j l)).re *
      L (wordProduct (pairWord a i j) (pairWord b j l)) = 0
    rw [phase_pair_chain_ne a b i j l hij hjl hil, phase_single_color_ne a b hab]
    ring
  · intro i j a b c hij hab hbc hac
    change V (pairIndex hk a i j) ⬝ᵥ V (pairIndex hk b i j) =
      -(V (pairIndex hk c i j) ⬝ᵥ V (identityIndex n k))
    rw [hV, hV, realGram_identity_right]
    change (wordPhase (pairWord a i j) (pairWord b i j)).re *
      L (wordProduct (pairWord a i j) (pairWord b i j)) = -L (pairWord c i j)
    rw [phase_pair_colors a b i j hij, phase_color_ne_sq a b hab,
      product_pair_colors a b c i j hab hbc hac]
    norm_num
  · intro i j a hij
    change V (pairIndex hk a i j) = V (pairIndex hk a j i)
    rw [pairIndex_symm]

theorem asLeeVector_edge_moments {n k N : ℕ} (hk : 2 ≤ k)
    (L : Word n → ℝ) (V : Index n k → (Fin N → ℝ))
    (hV : ∀ P Q, V P ⬝ᵥ V Q = realGram k L P Q) (i j : Fin n) :
    QMaxCutSDP.Rounding.vEdge (asLeeVector hk V) i j ⬝ᵥ
      (asLeeVector hk V).v0 = ∑ a : Fin 3, L (pairWord a i j) := by
  unfold QMaxCutSDP.Rounding.vEdge
  rw [sum_dotProduct]
  apply Finset.sum_congr rfl
  intro a ha
  change V (pairIndex hk a i j) ⬝ᵥ V (identityIndex n k) = L (pairWord a i j)
  rw [hV, realGram_identity_right]
  rfl

theorem exists_lee_representation {n k : ℕ} (hk : 2 ≤ k)
    (L : Word n → ℝ) (hL : Feasible k L) :
    ∃ v : QMaxCutSDP.Rounding.SDPVec n (Fintype.card (Index n k)),
      QMaxCutSDP.Rounding.IsSFeasible v ∧
      ∀ i j : Fin n, QMaxCutSDP.Rounding.vEdge v i j ⬝ᵥ v.v0 =
        ∑ a : Fin 3, L (pairWord a i j) := by
  obtain ⟨V, hV⟩ := gram_vectors (realGram k L) hL.2
  exact ⟨asLeeVector hk V, asLeeVector_feasible hk L hL V hV,
    asLeeVector_edge_moments hk L V hV⟩


end QuantumMaxCutEnergy.PauliSDP.LeeBridge

theorem publication_pauli_lee_vector {n k : ℕ} (hk : 2 ≤ k)
    (L : QuantumMaxCutEnergy.PauliSDP.Word n → ℝ)
    (hL : QuantumMaxCutEnergy.PauliSDP.Feasible k L) :
    ∃ v : QMaxCutSDP.Rounding.SDPVec n
        (Fintype.card (QuantumMaxCutEnergy.PauliSDP.Index n k)),
      QMaxCutSDP.Rounding.IsSFeasible v ∧
      ∀ i j : Fin n, QMaxCutSDP.Rounding.vEdge v i j ⬝ᵥ v.v0 =
        L (fun t => if t = i ∨ t = j then 1 else 0) +
        L (fun t => if t = i ∨ t = j then 2 else 0) +
        L (fun t => if t = i ∨ t = j then 3 else 0) := by
  obtain ⟨v, hv, he⟩ :=
    QuantumMaxCutEnergy.PauliSDP.LeeBridge.exists_lee_representation hk L hL
  refine ⟨v, hv, ?_⟩
  intro i j
  rw [he]
  simp only [Fin.sum_univ_three]
  rfl


open QMaxCutSDP.Rounding QuantumMaxCutEnergy.PauliSDP

namespace PauliTriangleVectorAux

lemma nn {N : ℕ} (x : Fin N → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg _

lemma selfE {n N : ℕ} (v : SDPVec n N) (hv : IsSFeasible v) (p q : Fin n) (hpq : p ≠ q) :
    vEdge v p q ⬝ᵥ vEdge v p q = 3 - 2 * (vEdge v p q ⬝ᵥ v.v0) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hv
  simp only [vEdge, Fin.sum_univ_three, add_dotProduct, dotProduct_add]
  rw [h3 p q 0 hpq, h3 p q 1 hpq, h3 p q 2 hpq,
    h7 p q 0 1 2 hpq (by decide) (by decide) (by decide),
    h7 p q 0 2 1 hpq (by decide) (by decide) (by decide),
    h7 p q 1 0 2 hpq (by decide) (by decide) (by decide),
    h7 p q 1 2 0 hpq (by decide) (by decide) (by decide),
    h7 p q 2 0 1 hpq (by decide) (by decide) (by decide),
    h7 p q 2 1 0 hpq (by decide) (by decide) (by decide)]
  ring

lemma Sle1 {n N : ℕ} (v : SDPVec n N) (hv : IsSFeasible v) (p q : Fin n) (hpq : p ≠ q) :
    vEdge v p q ⬝ᵥ v.v0 ≤ 1 := by
  have h := nn (v.v0 - vEdge v p q)
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, selfE v hv p q hpq, hv.1,
    dotProduct_comm v.v0 (vEdge v p q)] at h
  linarith only [h]

lemma crossE {n N : ℕ} (v : SDPVec n N) (hv : IsSFeasible v) (i j k : Fin n) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) :
    vEdge v i j ⬝ᵥ vEdge v i k = vEdge v j k ⬝ᵥ v.v0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hv
  simp only [vEdge, Fin.sum_univ_three, add_dotProduct, dotProduct_add]
  rw [h8 i j 0 hij, h8 i j 1 hij, h8 i j 2 hij]
  rw [h5 j i k 0 hij.symm hik hjk, h5 j i k 1 hij.symm hik hjk, h5 j i k 2 hij.symm hik hjk,
    h6 j i k 0 1 hij.symm hik hjk (by decide), h6 j i k 0 2 hij.symm hik hjk (by decide),
    h6 j i k 1 0 hij.symm hik hjk (by decide), h6 j i k 1 2 hij.symm hik hjk (by decide),
    h6 j i k 2 0 hij.symm hik hjk (by decide), h6 j i k 2 1 hij.symm hik hjk (by decide)]
  ring

end PauliTriangleVectorAux

namespace PauliTriangleVectorAux

lemma edge_symm {n N : ℕ} (v : SDPVec n N) (hv : IsSFeasible v)
    (i j : Fin n) (hij : i ≠ j) : vEdge v i j = vEdge v j i := by
  unfold vEdge
  apply Finset.sum_congr rfl
  intro a ha
  exact hv.2.2.2.2.2.2.2.2 i j a hij

lemma triangle {n N : ℕ} (v : SDPVec n N) (hv : IsSFeasible v)
    (i j l : Fin n) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    -3 ≤ vEdge v i j ⬝ᵥ v.v0 + vEdge v i l ⬝ᵥ v.v0 +
      vEdge v j l ⬝ᵥ v.v0 := by
  let A := vEdge v i j
  let B := vEdge v i l
  let C := vEdge v j l
  have hA : A ⬝ᵥ A = 3 - 2 * (A ⬝ᵥ v.v0) := selfE v hv i j hij
  have hB : B ⬝ᵥ B = 3 - 2 * (B ⬝ᵥ v.v0) := selfE v hv i l hil
  have hC : C ⬝ᵥ C = 3 - 2 * (C ⬝ᵥ v.v0) := selfE v hv j l hjl
  have hAB : A ⬝ᵥ B = C ⬝ᵥ v.v0 := crossE v hv i j l hij hil hjl
  have hAC : A ⬝ᵥ C = B ⬝ᵥ v.v0 := by
    have h := crossE v hv j i l hij.symm hjl hil
    rw [edge_symm v hv j i hij.symm] at h
    exact h
  have hBC : B ⬝ᵥ C = A ⬝ᵥ v.v0 := by
    have h := crossE v hv l i j hil.symm hjl.symm hij
    rw [edge_symm v hv l i hil.symm, edge_symm v hv l j hjl.symm] at h
    exact h
  have h := nn (A + B + C + (3 : ℝ) • v.v0)
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul] at h
  rw [hA, hB, hC, hAB, hAC, hBC,
    dotProduct_comm B A, dotProduct_comm C A, dotProduct_comm C B,
    hAB, hAC, hBC, dotProduct_comm v.v0 A, dotProduct_comm v.v0 B,
    dotProduct_comm v.v0 C, hv.1] at h
  change -3 ≤ A ⬝ᵥ v.v0 + B ⬝ᵥ v.v0 + C ⬝ᵥ v.v0
  linarith only [h]

end PauliTriangleVectorAux


theorem solution {n k : ℕ} (hk : 2 ≤ k)
    (L : Word n → ℝ) (hL : Feasible k L)
    (i j l : Fin n) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    (1 - L (fun t => if t = i ∨ t = j then 1 else 0) -
      L (fun t => if t = i ∨ t = j then 2 else 0) -
      L (fun t => if t = i ∨ t = j then 3 else 0)) / 2 +
    (1 - L (fun t => if t = i ∨ t = l then 1 else 0) -
      L (fun t => if t = i ∨ t = l then 2 else 0) -
      L (fun t => if t = i ∨ t = l then 3 else 0)) / 2 +
    (1 - L (fun t => if t = j ∨ t = l then 1 else 0) -
      L (fun t => if t = j ∨ t = l then 2 else 0) -
      L (fun t => if t = j ∨ t = l then 3 else 0)) / 2 ≤ 3 := by
  obtain ⟨v, hv, he⟩ := LeeBridge.exists_lee_representation hk L hL
  have h := PauliTriangleVectorAux.triangle v hv i j l hij hil hjl
  rw [he, he, he] at h
  simp only [Fin.sum_univ_three] at h
  change -3 ≤
    L (fun t => if t = i ∨ t = j then 1 else 0) +
    L (fun t => if t = i ∨ t = j then 2 else 0) +
    L (fun t => if t = i ∨ t = j then 3 else 0) +
    (L (fun t => if t = i ∨ t = l then 1 else 0) +
    L (fun t => if t = i ∨ t = l then 2 else 0) +
    L (fun t => if t = i ∨ t = l then 3 else 0)) +
    (L (fun t => if t = j ∨ t = l then 1 else 0) +
    L (fun t => if t = j ∨ t = l then 2 else 0) +
    L (fun t => if t = j ∨ t = l then 3 else 0)) at h
  linarith


#print axioms solution
