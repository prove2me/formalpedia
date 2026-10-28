-- Prove2me | solution 1 for ThresholdTheorem.isLocalStochastic_relabel
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T20:39:46.675973+00:00
-- url     : https://prove2.me/submissions/0e455506-04fc-43fc-913c-0deda726219f

import Mathlib
import Definitions.Def_threshold_theorem_local_stochastic

open ThresholdTheorem

namespace ThresholdTheorem.RelabelAux

open Matrix

/-- Precomposition with an equivalence, as an equivalence of bit strings. -/
def bitEquiv {A B : Type*} (τ : A ≃ B) : (B → Fin 2) ≃ (A → Fin 2) where
  toFun x := x ∘ τ
  invFun y := y ∘ τ.symm
  left_inv x := by funext b; simp
  right_inv y := by funext a; simp

/-- Relabel an operator along `τ`. -/
def rel {A B : Type*} (τ : A ≃ B) (ρ : Op A) : Op B :=
  ρ.submatrix (bitEquiv τ) (bitEquiv τ)

lemma rel_mul {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (τ : A ≃ B) (X Y : Op A) :
    rel τ (X * Y) = rel τ X * rel τ Y := by
  unfold rel
  rw [Matrix.submatrix_mul_equiv X Y _ (bitEquiv τ) _]

lemma rel_conjTranspose {A B : Type*} (τ : A ≃ B) (X : Op A) :
    rel τ Xᴴ = (rel τ X)ᴴ := by
  unfold rel; rw [Matrix.conjTranspose_submatrix]

lemma rel_add {A B : Type*} (τ : A ≃ B) (X Y : Op A) :
    rel τ (X + Y) = rel τ X + rel τ Y := by
  unfold rel; rfl

lemma rel_zero {A B : Type*} (τ : A ≃ B) : rel τ (0 : Op A) = 0 := by
  unfold rel; rfl

lemma rel_smul {A B : Type*} (τ : A ≃ B) (c : ℝ) (X : Op A) :
    rel τ (c • X) = c • rel τ X := by
  unfold rel; rfl

lemma rel_list_sum {A B : Type*} (τ : A ≃ B) (l : List (Op A)) :
    rel τ l.sum = (l.map (rel τ)).sum := by
  induction l with
  | nil => simp [rel_zero]
  | cons a l ih => simp [rel_add, ih]

lemma liftOp_rel {A B : Type*} {k : ℕ} (τ : A ≃ B) (s : Fin k ↪ A) (M : QMat k) :
    liftOp (s.trans τ.toEmbedding) M = rel τ (liftOp s M) := by
  funext x y
  simp only [liftOp, rel, Matrix.submatrix_apply, bitEquiv, Equiv.coe_fn_mk]
  have hc : (∀ q, q ∉ Set.range (s.trans τ.toEmbedding) → x q = y q) ↔
      (∀ q, q ∉ Set.range s → (x ∘ τ) q = (y ∘ τ) q) := by
    constructor
    · intro h q hq
      apply h (τ q)
      rintro ⟨i, hi⟩
      apply hq
      refine ⟨i, ?_⟩
      simpa using τ.injective (by simpa using hi)
    · intro h q hq
      have := h (τ.symm q) (by
        rintro ⟨i, hi⟩
        apply hq
        exact ⟨i, by simp [hi]⟩)
      simpa using this
  have he1 : x ∘ (s.trans τ.toEmbedding) = (x ∘ τ) ∘ s := by
    funext i; simp
  have he2 : y ∘ (s.trans τ.toEmbedding) = (y ∘ τ) ∘ s := by
    funext i; simp
  by_cases h : ∀ q, q ∉ Set.range s → (x ∘ τ) q = (y ∘ τ) q
  · rw [if_pos (hc.2 h), if_pos h, he1, he2]
  · rw [if_neg (fun h' => h (hc.1 h')), if_neg h]

lemma applyKraus_rel {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {k : ℕ} (τ : A ≃ B) (s : Fin k ↪ A) (K : List (QMat k)) (ρ : Op A) :
    applyKraus (s.trans τ.toEmbedding) K (rel τ ρ) = rel τ (applyKraus s K ρ) := by
  unfold applyKraus
  rw [rel_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro M _
  simp only [Function.comp_apply, liftOp_rel, rel_mul, rel_conjTranspose]

lemma initState_rel {A B : Type*} (τ : A ≃ B) : rel τ (initState A) = initState B := by
  funext x y
  simp only [rel, initState, Matrix.submatrix_apply, bitEquiv, Equiv.coe_fn_mk]
  have h : ∀ z : B → Fin 2, z ∘ τ = 0 ↔ z = 0 := by
    intro z
    constructor
    · intro hz; funext b
      have := congrFun hz (τ.symm b); simpa using this
    · intro hz; subst hz; rfl
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [h, hx, hy]

/-- The relabelling equivalence on data plus environment. -/
def tau {Q Q' : Type*} (σ : Q ≃ Q') (m : ℕ) : Q ⊕ Fin m ≃ Q' ⊕ Fin m :=
  Equiv.sumCongr σ (Equiv.refl _)

lemma envEmbed_rel {Q Q' : Type*} {k : ℕ} (σ : Q ≃ Q') (m : ℕ) (s : Fin k ↪ Q) :
    envEmbed m (s.trans σ.toEmbedding) = (envEmbed m s).trans (tau σ m).toEmbedding := by
  ext i
  induction i using Fin.addCases with
  | left i =>
    show Fin.addCases (fun i => Sum.inl (σ (s i))) (fun j => Sum.inr j) (Fin.castAdd m i) =
      tau σ m (Fin.addCases (fun i => Sum.inl (s i)) (fun j => Sum.inr j) (Fin.castAdd m i))
    simp [tau, Fin.addCases_left]
  | right j =>
    show Fin.addCases (fun i => Sum.inl (σ (s i))) (fun j => Sum.inr j) (Fin.natAdd k j) =
      tau σ m (Fin.addCases (fun i => Sum.inl (s i)) (fun j => Sum.inr j) (Fin.natAdd k j))
    simp [tau, Fin.addCases_right]

lemma inl_rel {Q Q' : Type*} {k : ℕ} (σ : Q ≃ Q') (m : ℕ) (s : Fin k ↪ Q) :
    ((s.trans σ.toEmbedding).trans (Function.Embedding.inl : Q' ↪ Q' ⊕ Fin m)) =
      (s.trans Function.Embedding.inl).trans (tau σ m).toEmbedding := by
  ext i; simp [tau]

lemma zipIdx_map {α β : Type*} (f : α → β) (l : List α) (n : ℕ) :
    (l.map f).zipIdx n = (l.zipIdx n).map (fun p => (f p.1, p.2)) := by
  induction l generalizing n with
  | nil => simp
  | cons a l ih => simp [List.zipIdx_cons, ih]

lemma faultyLayer_rel {Q Q' : Type*} [Fintype Q] [DecidableEq Q] [Fintype Q'] [DecidableEq Q']
    {m : ℕ} (σ : Q ≃ Q') (F : Finset (ℕ × ℕ)) (fault : ℕ → ℕ → (k : ℕ) → Channel (k + m))
    (t : ℕ) (L : Layer Q) (ρ : Op (Q ⊕ Fin m)) :
    faultyLayer F fault t (L.relabel σ) (rel (tau σ m) ρ) =
      rel (tau σ m) (faultyLayer F fault t L ρ) := by
  unfold faultyLayer
  simp only [Layer.relabel]
  rw [zipIdx_map, List.foldl_map]
  apply List.foldl_hom
  intro x ℓj
  by_cases h : (t, ℓj.2) ∈ F
  · simp only [if_pos h, Location.relabel]
    rw [envEmbed_rel, applyKraus_rel]
  · simp only [if_neg h, Location.relabel]
    rw [inl_rel, applyKraus_rel]

lemma faultyState_rel {Q Q' : Type*} [Fintype Q] [DecidableEq Q] [Fintype Q'] [DecidableEq Q']
    {m : ℕ} (σ : Q ≃ Q') (F : Finset (ℕ × ℕ)) (fault : ℕ → ℕ → (k : ℕ) → Channel (k + m))
    (C : Circuit Q) :
    faultyState F fault (C.relabel σ) = rel (tau σ m) (faultyState F fault C) := by
  unfold faultyState
  simp only [Circuit.relabel]
  rw [zipIdx_map, List.foldl_map, ← initState_rel (tau σ m)]
  apply List.foldl_hom
  intro x Lt
  exact faultyLayer_rel σ F fault Lt.2 Lt.1 x

lemma dataOutDist_rel {Q Q' : Type*} [Fintype Q] [DecidableEq Q] [Fintype Q'] [DecidableEq Q']
    {m : ℕ} (σ : Q ≃ Q') (ρ : Op (Q ⊕ Fin m)) (x : Q → Fin 2) :
    dataOutDist (rel (tau σ m) ρ) (x ∘ σ.symm) = dataOutDist ρ x := by
  unfold dataOutDist
  apply Finset.sum_congr rfl
  intro y _
  have : (Sum.elim (x ∘ σ.symm) y) ∘ (tau σ m) = Sum.elim x y := by
    funext z; cases z <;> simp [tau]
  simp only [rel, Matrix.submatrix_apply, bitEquiv, Equiv.coe_fn_mk, this]

lemma pushDist_comp {Q Q' : Type*} [Fintype Q] [Fintype Q'] [DecidableEq Q] [DecidableEq Q']
    (σ : Q ≃ Q') (P : (Q' → Fin 2) → ℝ) (x : Q → Fin 2) :
    pushDist (fun x' => x' ∘ σ) P x = P (x ∘ σ.symm) := by
  unfold pushDist
  have hmem : x ∘ σ.symm ∈ Finset.univ.filter (fun x' : Q' → Fin 2 => x' ∘ σ = x) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    funext q; simp
  rw [Finset.sum_eq_single_of_mem (x ∘ σ.symm) (by convert hmem)]
  intro b hb hne
  exfalso; apply hne
  have hb' : b ∘ σ = x := by simpa using hb
  subst hb'; funext q; simp

end ThresholdTheorem.RelabelAux

open ThresholdTheorem.RelabelAux in
theorem solution {Q Q' : Type*} [Fintype Q] [DecidableEq Q] [Fintype Q']
    [DecidableEq Q'] (σ : Q ≃ Q') (C : Circuit Q) (e : ℝ) (P : (Q' → Fin 2) → ℝ)
    (hP : IsLocalStochasticDist (C.relabel σ) e P) :
    IsLocalStochasticDist C e (pushDist (fun x => x ∘ σ) P) := by
  obtain ⟨r, m, w, F, fault, hw, hsum, hS, hPeq⟩ := hP
  refine ⟨r, m, w, F, fault, hw, hsum, hS, ?_⟩
  funext x
  rw [pushDist_comp, hPeq]
  simp only [faultyState_rel, dataOutDist_rel]

#print axioms solution
