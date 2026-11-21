-- Prove2me | solution 1 for StreamSubmod.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:17:59.689481+00:00
-- url     : https://prove2.me/submissions/ecf37316-7c23-480d-aa42-6790dba47762

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_IsApproxOffline
import Definitions.Def_StreamSubmod_Algorithm1

namespace Aux_StreamSubmod_lemma_5

open StreamSubmod NonmonotoneSubmod.Shared

variable {E : Type} [DecidableEq E]

lemma scan_none {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (e : E) (S : Fin p → Finset E) :
    ∀ l : List (Fin p), (scan f k θ e S l).1 = none →
      ∀ i ∈ l, (S i).card < k → marginal f e (S i) < θ := by
  intro l
  induction l with
  | nil => intro _ i hi; simp at hi
  | cons j l ih =>
    intro h i hi hc
    simp only [scan] at h
    by_cases h1 : (S j).card < k
    · rw [if_pos h1] at h
      by_cases h2 : θ ≤ marginal f e (S j)
      · rw [if_pos h2] at h
        simp at h
      · rw [if_neg h2] at h
        rcases List.mem_cons.mp hi with rfl | hi
        · exact not_le.mp h2
        · exact ih h i hi hc
    · rw [if_neg h1] at h
      rcases List.mem_cons.mp hi with rfl | hi
      · exact absurd hc h1
      · exact ih h i hi hc

lemma thresh_cases {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (e : E) (S : Fin p → Finset E) :
    (threshStep f k θ e S).1 = S ∨
      ∃ j, (threshStep f k θ e S).1 = Function.update S j (insert e (S j)) := by
  unfold threshStep
  rcases hs : scan f k θ e S (List.finRange p) with ⟨o, n⟩
  cases o with
  | none => left; rfl
  | some j => right; exact ⟨j, rfl⟩

lemma thresh_rej {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (e : E) (S : Fin p → Finset E)
    (h : ∀ i, e ∉ (threshStep f k θ e S).1 i) :
    ∀ i, (S i).card < k → marginal f e (S i) < θ := by
  unfold threshStep at h
  rcases hs : scan f k θ e S (List.finRange p) with ⟨o, n⟩
  rw [hs] at h
  cases o with
  | none =>
    intro i hc
    exact scan_none f k θ e S _ (by rw [hs]) i (List.mem_finRange i) hc
  | some j =>
    have := h j
    simp at this

lemma thresh_mono {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (e : E) (S : Fin p → Finset E)
    (i : Fin p) : S i ⊆ (threshStep f k θ e S).1 i := by
  rcases thresh_cases f k θ e S with h | ⟨j, h⟩
  · intro x hx
    rw [h]
    exact hx
  · rw [h]
    intro x hx
    by_cases hi : i = j
    · rw [hi, Function.update_self]
      rw [hi] at hx
      exact Finset.mem_insert_of_mem hx
    · rw [Function.update_of_ne hi]
      exact hx

lemma run_mono {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (L : List E) :
    ∀ S : Fin p → Finset E, ∀ i,
      S i ⊆ (L.foldl (fun S e => (threshStep f k θ e S).1) S) i := by
  induction L with
  | nil => intro S i; exact Finset.Subset.refl _
  | cons a L ih =>
    intro S i
    simp only [List.foldl_cons]
    exact (thresh_mono f k θ a S i).trans (ih _ i)

lemma run_disj {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (L : List E) (hnd : L.Nodup) :
    ∀ S : Fin p → Finset E, (∀ i j, i ≠ j → Disjoint (S i) (S j)) → (∀ i, ∀ e ∈ L, e ∉ S i) →
      ∀ i j, i ≠ j → Disjoint ((L.foldl (fun S e => (threshStep f k θ e S).1) S) i)
        ((L.foldl (fun S e => (threshStep f k θ e S).1) S) j) := by
  induction L with
  | nil => intro S hS _; exact hS
  | cons a L ih =>
    intro S hS hL
    rw [List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    have haS : ∀ i, a ∉ S i := fun i => hL i a (List.mem_cons.mpr (Or.inl rfl))
    apply ih hnd.2
    · rcases thresh_cases f k θ a S with h | ⟨j, h⟩
      · rw [h]
        exact hS
      · rw [h]
        intro i i' hii'
        by_cases hi : i = j
        · rw [hi] at hii' ⊢
          rw [Function.update_self, Function.update_of_ne (Ne.symm hii')]
          exact Finset.disjoint_insert_left.mpr ⟨haS i', hS j i' hii'⟩
        · by_cases hi' : i' = j
          · rw [hi'] at hii' ⊢
            rw [Function.update_self, Function.update_of_ne hi]
            exact Finset.disjoint_insert_right.mpr ⟨haS i, hS i j hii'⟩
          · rw [Function.update_of_ne hi, Function.update_of_ne hi']
            exact hS i i' hii'
    · intro i e he hm
      have hea : e ≠ a := fun h' => hnd.1 (h' ▸ he)
      have heS : e ∉ S i := hL i e (List.mem_cons_of_mem a he)
      rcases thresh_cases f k θ a S with h | ⟨j, h⟩
      · rw [h] at hm
        exact heS hm
      · rw [h] at hm
        by_cases hi : i = j
        · rw [hi, Function.update_self] at hm
          rw [hi] at heS
          rcases Finset.mem_insert.mp hm with h1 | h1
          · exact hea h1
          · exact heS h1
        · rw [Function.update_of_ne hi] at hm
          exact heS hm

lemma rejected {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (σ : List E) (o : E) (ho : o ∈ σ)
    (hnot : ∀ i : Fin p,
      o ∉ (σ.foldl (fun S e => (threshStep f k θ e S).1) (fun _ : Fin p => (∅ : Finset E))) i) :
    ∀ i : Fin p, ∃ Y : Finset E,
      Y ⊆ (σ.foldl (fun S e => (threshStep f k θ e S).1) (fun _ : Fin p => (∅ : Finset E))) i ∧
      (Y.card < k → marginal f o Y < θ) := by
  obtain ⟨L1, L2, hL⟩ := List.append_of_mem ho
  rw [hL, List.foldl_append, List.foldl_cons] at hnot ⊢
  obtain ⟨St, hSt⟩ : ∃ St : Fin p → Finset E,
      St = L1.foldl (fun S e => (threshStep f k θ e S).1) (fun _ : Fin p => (∅ : Finset E)) :=
    ⟨_, rfl⟩
  rw [← hSt] at hnot ⊢
  intro i
  have hrej := thresh_rej f k θ o St (fun j hj => hnot j (run_mono f k θ L2 _ j hj))
  exact ⟨St i, (thresh_mono f k θ o St i).trans (run_mono f k θ L2 _ i), hrej i⟩

variable [Fintype E]

lemma add_rej (f : Finset E → ℝ) (hf : Submodular f) (θ : ℝ) (hθ : 0 ≤ θ) (Z : Finset E) :
    ∀ Q : Finset E, (∀ q ∈ Q, ∃ Y ⊆ Z, marginal f q Y < θ) →
      f (Z ∪ Q) ≤ f Z + (Q.card : ℝ) * θ := by
  intro Q
  refine Finset.induction_on Q ?_ ?_
  · intro _
    simp
  · intro q Q hq ih hQ
    have ih' := ih (fun q' hq' => hQ q' (Finset.mem_insert_of_mem hq'))
    rw [Finset.union_insert, Finset.card_insert_of_notMem hq]
    push_cast
    by_cases hm : q ∈ Z ∪ Q
    · rw [Finset.insert_eq_of_mem hm]
      linarith
    · obtain ⟨Y, hYZ, hY⟩ := hQ q (Finset.mem_insert_self q Q)
      have hsub := hf (insert q Y) (Z ∪ Q)
      have hYZQ : Y ⊆ Z ∪ Q := hYZ.trans Finset.subset_union_left
      have e1 : insert q Y ∪ (Z ∪ Q) = insert q (Z ∪ Q) := by
        rw [Finset.insert_union, Finset.union_eq_right.mpr hYZQ]
      have e2 : insert q Y ∩ (Z ∪ Q) = Y := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · rw [h1] at h2
            exact absurd h2 hm
          · exact h1
        · intro h
          exact ⟨Or.inr h, hYZQ h⟩
      rw [e1, e2] at hsub
      unfold marginal at hY
      linarith

lemma disj_union (f : Finset E → ℝ) (hf : Submodular f) (X : Finset E) {p : ℕ}
    (S : Fin p → Finset E) (hd : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    ∀ I : Finset (Fin p), f (X ∪ I.biUnion S) + ((I.card : ℝ) - 1) * f X ≤
      ∑ i ∈ I, f (X ∪ S i) := by
  intro I
  refine Finset.induction_on I ?_ ?_
  · simp only [Finset.biUnion_empty, Finset.union_empty, Finset.card_empty, Finset.sum_empty,
      Nat.cast_zero]
    linarith
  · intro j I hj ih
    rw [Finset.sum_insert hj, Finset.card_insert_of_notMem hj, Finset.biUnion_insert]
    push_cast
    have hsub := hf (X ∪ S j) (X ∪ I.biUnion S)
    have e1 : X ∪ S j ∪ (X ∪ I.biUnion S) = X ∪ (S j ∪ I.biUnion S) := by
      ext x
      simp only [Finset.mem_union]
      tauto
    have e2 : (X ∪ S j) ∩ (X ∪ I.biUnion S) = X := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_biUnion]
      constructor
      · rintro ⟨h1 | h1, h2 | ⟨i, hi, h2⟩⟩
        · exact h1
        · exact h1
        · exact h2
        · exfalso
          have hij : j ≠ i := fun h => hj (by rw [h]; exact hi)
          exact Finset.disjoint_left.mp (hd j i hij) h1 h2
      · intro h
        exact ⟨Or.inl h, Or.inl h⟩
    rw [e1, e2] at hsub
    linarith

end Aux_StreamSubmod_lemma_5

open Aux_StreamSubmod_lemma_5 in
open NonmonotoneSubmod.Shared in
open StreamSubmod in
theorem solution {E : Type} [Fintype E] [DecidableEq E] (f : Finset E → ℝ) (hf0 : ∀ S, 0 ≤ f S)
    (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (p : ℕ)
    (hp : 1 ≤ p) (τ : ℝ) (hτ : 0 ≤ τ) (σ : List E) (hσ : IsStream σ) (OPT : Finset E)
    (hlt : ∀ i, (alg1Sets p f k α τ σ i).card < k) (A : Finset E) :
    let S := alg1Sets p f k α τ σ
    let O := OPT \ Finset.univ.biUnion S
    let b : ℝ := (O.card : ℝ) / (k : ℝ)
    (1 - (p : ℝ)⁻¹) * f (O ∪ A) - α * b * τ / (1 + α) ≤ (p : ℝ)⁻¹ * ∑ i, f (S i ∪ A) := by
  intro S O b
  have hb : b = (O.card : ℝ) / (k : ℝ) := rfl
  have hO : O = OPT \ Finset.univ.biUnion S := rfl
  have hSdef : S = σ.foldl (fun S e => (threshStep f k (threshold α k τ) e S).1)
      (fun _ => (∅ : Finset E)) := rfl
  have hθ0 : 0 ≤ threshold α k τ := by
    unfold threshold
    have : (0 : ℝ) ≤ α / (1 + α) := div_nonneg hα0.le (by linarith)
    exact div_nonneg (mul_nonneg this hτ) (Nat.cast_nonneg k)
  have hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j) := by
    rw [hSdef]
    exact run_disj f k _ σ hσ.1 _ (fun _ _ _ => by simp) (fun _ _ _ => by simp)
  have hrej : ∀ q ∈ O, ∀ i, ∃ Y ⊆ S i, marginal f q Y < threshold α k τ := by
    intro q hq i
    have hq' : ∀ j, q ∉ S j := by
      intro j hj
      rw [hO] at hq
      exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hj⟩)
    rw [hSdef] at hq' ⊢
    obtain ⟨Y, hY1, hY2⟩ := rejected f k (threshold α k τ) σ q (hσ.2 q) hq' i
    exact ⟨Y, hY1, hY2 (lt_of_le_of_lt (Finset.card_le_card hY1) (hlt i))⟩
  have hclaim1 : ∀ i, f ((O ∪ A) ∪ S i) ≤ f (S i ∪ A) + (O.card : ℝ) * threshold α k τ := by
    intro i
    have := add_rej f hf (threshold α k τ) hθ0 (S i ∪ A) O
      (fun q hq => by
        obtain ⟨Y, hY1, hY2⟩ := hrej q hq i
        exact ⟨Y, hY1.trans Finset.subset_union_left, hY2⟩)
    have e : (O ∪ A) ∪ S i = (S i ∪ A) ∪ O := by
      ext x
      simp only [Finset.mem_union]
      tauto
    rw [e]
    exact this
  have hclaim2 := disj_union f hf (O ∪ A) S hdisj Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at hclaim2
  have hnn : 0 ≤ f ((O ∪ A) ∪ Finset.univ.biUnion S) := hf0 _
  have hsum : ∑ i, f ((O ∪ A) ∪ S i) ≤ ∑ i, (f (S i ∪ A) + (O.card : ℝ) * threshold α k τ) :=
    Finset.sum_le_sum (fun i _ => hclaim1 i)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  have key : ((p : ℝ) - 1) * f (O ∪ A) - (p : ℝ) * ((O.card : ℝ) * threshold α k τ) ≤
      ∑ i, f (S i ∪ A) := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have m := mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hp0.le)
  have hP : (p : ℝ)⁻¹ * p = 1 := inv_mul_cancel₀ hp0.ne'
  have e : (p : ℝ)⁻¹ * (((p : ℝ) - 1) * f (O ∪ A) - (p : ℝ) * ((O.card : ℝ) * threshold α k τ))
      = (1 - (p : ℝ)⁻¹) * f (O ∪ A) - (O.card : ℝ) * threshold α k τ := by
    linear_combination (f (O ∪ A) - (O.card : ℝ) * threshold α k τ) * hP
  have hθb : (O.card : ℝ) * threshold α k τ = α * b * τ / (1 + α) := by
    rw [hb]
    unfold threshold
    ring
  rw [← hθb]
  linarith
