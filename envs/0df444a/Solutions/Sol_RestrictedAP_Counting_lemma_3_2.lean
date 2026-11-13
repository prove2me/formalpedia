-- Prove2me | solution 1 for RestrictedAP.Counting.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:44:37.758807+00:00
-- url     : https://prove2.me/submissions/4fc91637-bc72-43ea-bd92-f960fda2c084

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_ProductFunctions

section
set_option autoImplicit false

/-!
# Basic facts about normalized product functions (shared by Lemmas 3.2–3.4)

* F1: `component` of a normalized product function is its factor; norm one, nonzero.
* F2: `proj σs K P` is a normalized product function with components
  `if i ∈ K then component σs P i else 1`.
* F3: powers: `P ^ N = 1 → (proj σs K P) ^ N = 1`; `orderOf (proj σs K P) ∣ orderOf P`.
* F4: rigidity of product decompositions over a nonempty alphabet, and the extraction of a
  small exceptional set from `symbolicDist F 1 < D`.
-/

namespace RestrictedAP.Counting.Dev.ProdBasics
open RestrictedAP.Counting

/-! ## F4: rigidity -/

/-- Evaluating a product decomposition at `s` updated in coordinate `i`. -/
theorem prod_update_eq {α : Type*} {n : ℕ} (w : Fin n → α → ℂ) (s : Fin n → α) (i : Fin n)
    (a : α) :
    ∏ j, w j (Function.update s i a j) = w i a * ∏ j ∈ ({i}ᶜ : Finset (Fin n)), w j (s j) := by
  rw [Fintype.prod_eq_mul_prod_compl i]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun j hj => ?_
    have : j ≠ i := by simpa using hj
    simp [Function.update_of_ne this]

/-! ## F1: components -/

variable {Sig : Type*} [DecidableEq Sig] {n : ℕ}

theorem component_eq_factor (σs : Sig) (P : (Fin n → Sig) → ℂ) (u : Fin n → Sig → ℂ)
    (hu1 : ∀ i, u i σs = 1) (hP : ∀ x, P x = ∏ i, u i (x i)) (i : Fin n) (a : Sig) :
    component σs P i a = u i a := by
  unfold component
  rw [hP, prod_update_eq]
  simp [hu1]

theorem component_norm (σs : Sig) (P : (Fin n → Sig) → ℂ) (hP : IsProductFunction σs P)
    (i : Fin n) (a : Sig) : ‖component σs P i a‖ = 1 := by
  obtain ⟨u, hu, hu1, hPu⟩ := hP
  rw [component_eq_factor σs P u hu1 hPu]; exact hu i a

theorem component_self (σs : Sig) (P : (Fin n → Sig) → ℂ) (hP : IsProductFunction σs P)
    (i : Fin n) : component σs P i σs = 1 := by
  obtain ⟨u, hu, hu1, hPu⟩ := hP
  rw [component_eq_factor σs P u hu1 hPu]; exact hu1 i

/-- F1: a normalized product function is the product of its components. -/
theorem eq_prod_component (σs : Sig) (P : (Fin n → Sig) → ℂ) (hP : IsProductFunction σs P)
    (x : Fin n → Sig) : P x = ∏ i, component σs P i (x i) := by
  obtain ⟨u, hu, hu1, hPu⟩ := hP
  rw [hPu]
  exact Finset.prod_congr rfl fun i _ => (component_eq_factor σs P u hu1 hPu i (x i)).symm

/-! ## F2: projections -/

theorem proj_apply (σs : Sig) (K : Finset (Fin n)) (P : (Fin n → Sig) → ℂ) (x : Fin n → Sig) :
    proj σs K P x = ∏ i, (if i ∈ K then component σs P i (x i) else 1) := by
  classical
  unfold proj
  rw [Finset.prod_ite_mem, Finset.univ_inter]

theorem proj_isProductFunction (σs : Sig) (K : Finset (Fin n)) (P : (Fin n → Sig) → ℂ)
    (hP : IsProductFunction σs P) : IsProductFunction σs (proj σs K P) := by
  classical
  refine ⟨fun i a => if i ∈ K then component σs P i a else 1, ?_, ?_, ?_⟩
  · intro i a; dsimp only; split_ifs
    · exact component_norm σs P hP i a
    · exact norm_one
  · intro i; dsimp only; split_ifs
    · exact component_self σs P hP i
    · rfl
  · intro x; rw [proj_apply]

theorem component_proj (σs : Sig) (K : Finset (Fin n)) (P : (Fin n → Sig) → ℂ)
    (hP : IsProductFunction σs P) (i : Fin n) (a : Sig) :
    component σs (proj σs K P) i a = if i ∈ K then component σs P i a else 1 := by
  classical
  have := component_eq_factor σs (proj σs K P) (fun i a => if i ∈ K then component σs P i a else 1)
    (fun i => by split_ifs; exacts [component_self σs P hP i, rfl])
    (fun x => by rw [proj_apply]) i a
  exact this

/-! ## F3: powers and orders -/

end RestrictedAP.Counting.Dev.ProdBasics
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Symbolic distance between normalized product functions (Fact 2.11 and friends)

* S1: normalized product functions are closed under `1`, `*`, powers, finite products; so is
  every element of `spanN C` when `C` consists of normalized product functions.
* S2: for normalized `P`, `Q`, `symbolicDist P Q` is exactly the number of coordinates where
  their normalized components differ (`symbolicDist_eq_card`).
* S3: Fact 2.11: `sd(P,P) = 0`, symmetry, triangle inequality, `sd(PQ, P'Q') ≤ sd(P,P') + sd(Q,Q')`,
  `sd(P^k, Q^k) ≤ sd(P,Q)`, and `sd(P,Q) ≤ |J|` when the components agree off `J`.
* S4: `spanN` is a submonoid (`one`, `mul`, `pow`, `prod`, members); `distToSpan` bounds.
* S5: `EqOff σs J P Q` (components agree off `J`), a congruence; covering spans.
* S6: `Close C C' b`: every element of `span C` is within `b` of an element of `span C'`;
  reflexivity, monotonicity, transitivity (sum of bounds).
-/

namespace RestrictedAP.Counting.Dev.SymDist
open RestrictedAP.Counting RestrictedAP.Counting.Dev.ProdBasics

open Classical

variable {Sig : Type*} [DecidableEq Sig] {n : ℕ}

/-! ## S1: closure of normalized product functions -/

theorem isProductFunction_one (σs : Sig) :
    IsProductFunction σs (1 : (Fin n → Sig) → ℂ) :=
  ⟨fun _ _ => 1, fun _ _ => norm_one, fun _ => rfl, fun _ => by simp⟩

theorem isProductFunction_mul (σs : Sig) (P Q : (Fin n → Sig) → ℂ)
    (hP : IsProductFunction σs P) (hQ : IsProductFunction σs Q) :
    IsProductFunction σs (P * Q) := by
  obtain ⟨u, hu, hu1, hPu⟩ := hP
  obtain ⟨v, hv, hv1, hQv⟩ := hQ
  refine ⟨fun i a => u i a * v i a, fun i a => by simp [hu, hv], fun i => by simp [hu1, hv1],
    fun x => ?_⟩
  simp only [Pi.mul_apply, hPu, hQv, Finset.prod_mul_distrib]

theorem isProductFunction_pow (σs : Sig) (P : (Fin n → Sig) → ℂ)
    (hP : IsProductFunction σs P) (k : ℕ) : IsProductFunction σs (P ^ k) := by
  induction k with
  | zero => simpa using isProductFunction_one σs
  | succ k ih => rw [pow_succ]; exact isProductFunction_mul σs _ _ ih hP

theorem isProductFunction_prod {ι : Type*} (σs : Sig) (s : Finset ι)
    (f : ι → (Fin n → Sig) → ℂ) (hf : ∀ i ∈ s, IsProductFunction σs (f i)) :
    IsProductFunction σs (∏ i ∈ s, f i) :=
  Finset.prod_induction f (IsProductFunction σs) (fun a b ha hb => isProductFunction_mul σs a b ha hb)
    (isProductFunction_one σs) hf

theorem isProductFunction_of_mem_spanN (σs : Sig) (C : Finset ((Fin n → Sig) → ℂ))
    (hC : ∀ P ∈ C, IsProductFunction σs P) (Q : (Fin n → Sig) → ℂ) (hQ : Q ∈ spanN C) :
    IsProductFunction σs Q := by
  obtain ⟨a, rfl⟩ := hQ
  exact isProductFunction_prod σs C _ fun P hP => isProductFunction_pow σs P (hC P hP) _

/-! ## Components of products and powers -/

theorem component_mul (σs : Sig) (P Q : (Fin n → Sig) → ℂ) (i : Fin n) :
    component σs (P * Q) i = component σs P i * component σs Q i := rfl

theorem component_npow_apply (σs : Sig) (P : (Fin n → Sig) → ℂ) (k : ℕ) (i : Fin n) (a : Sig) :
    component σs (P ^ k) i a = component σs P i a ^ k := rfl

theorem component_npow (σs : Sig) (P : (Fin n → Sig) → ℂ) (k : ℕ) (i : Fin n) :
    component σs (P ^ k) i = component σs P i ^ k := by
  funext a; rfl

theorem component_one (σs : Sig) (i : Fin n) :
    component σs (1 : (Fin n → Sig) → ℂ) i = 1 := by
  funext a; rfl

/-! ## S2: symbolic distance as a count of differing components -/

/-- Any norm-one decomposition `u` of a normalized `P` is a constant multiple of its
components: `component σs P i a * u i σs = u i a`. -/
theorem component_mul_factor (σs : Sig) (P : (Fin n → Sig) → ℂ) (hP : IsProductFunction σs P)
    (u : Fin n → Sig → ℂ) (hPu : ∀ x, P x = ∏ i, u i (x i)) (i : Fin n) (a : Sig) :
    component σs P i a * u i σs = u i a := by
  have h1 : component σs P i σs = 1 := component_self σs P hP i
  have ha : component σs P i a = u i a * ∏ j ∈ ({i}ᶜ : Finset (Fin n)), u j σs := by
    unfold component; rw [hPu, prod_update_eq]
  have hs : component σs P i σs = u i σs * ∏ j ∈ ({i}ᶜ : Finset (Fin n)), u j σs := by
    unfold component; rw [hPu, prod_update_eq]
  rw [ha, mul_assoc, mul_comm _ (u i σs), ← hs, h1, mul_one]

/-- The set of coordinates where the components of `P` and `Q` differ. -/
noncomputable def diffSet (σs : Sig) (P Q : (Fin n → Sig) → ℂ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => component σs P i ≠ component σs Q i)

theorem symbolicDist_le_card_diffSet (σs : Sig) (P Q : (Fin n → Sig) → ℂ)
    (hP : IsProductFunction σs P) (hQ : IsProductFunction σs Q) :
    symbolicDist P Q ≤ (diffSet σs P Q).card := by
  unfold symbolicDist
  apply Nat.sInf_le
  refine ⟨component σs P, component σs Q, component_norm σs P hP, component_norm σs Q hQ,
    eq_prod_component σs P hP, eq_prod_component σs Q hQ, ?_⟩
  unfold diffSet
  congr 1

/-- **S2.** For normalized product functions, the symbolic distance is the number of coordinates
where their normalized components differ. -/
theorem symbolicDist_eq_card (σs : Sig) (P Q : (Fin n → Sig) → ℂ)
    (hP : IsProductFunction σs P) (hQ : IsProductFunction σs Q) :
    symbolicDist P Q = (diffSet σs P Q).card := by
  refine le_antisymm (symbolicDist_le_card_diffSet σs P Q hP hQ) ?_
  have hne : {k | ∃ u v : Fin n → Sig → ℂ, (∀ i a, ‖u i a‖ = 1) ∧ (∀ i a, ‖v i a‖ = 1) ∧
      (∀ x, P x = ∏ i, u i (x i)) ∧ (∀ x, Q x = ∏ i, v i (x i)) ∧
      (Finset.univ.filter (fun i => u i ≠ v i)).card = k}.Nonempty :=
    ⟨_, component σs P, component σs Q, component_norm σs P hP, component_norm σs Q hQ,
      eq_prod_component σs P hP, eq_prod_component σs Q hQ, rfl⟩
  obtain ⟨u, v, hu, hv, hPu, hQv, hcard⟩ := Nat.sInf_mem hne
  unfold symbolicDist
  rw [← hcard]
  apply Finset.card_le_card
  intro i hi
  simp only [diffSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  intro huv
  apply hi
  funext a
  have h1 := component_mul_factor σs P hP u hPu i a
  have h2 := component_mul_factor σs Q hQ v hQv i a
  have hu0 : u i σs ≠ 0 := fun h => by simpa [h] using hu i σs
  rw [huv] at h1
  have h1' : component σs P i a * v i σs = component σs Q i a * v i σs := by
    rw [h1, h2]
  have hv0 : v i σs ≠ 0 := by rwa [← huv]
  exact mul_right_cancel₀ hv0 h1'

/-! ## S3: Fact 2.11 -/

theorem symbolicDist_le_of_eqOn (σs : Sig) (P Q : (Fin n → Sig) → ℂ)
    (hP : IsProductFunction σs P) (hQ : IsProductFunction σs Q) (J : Finset (Fin n))
    (h : ∀ i, i ∉ J → component σs P i = component σs Q i) :
    symbolicDist P Q ≤ J.card := by
  rw [symbolicDist_eq_card σs P Q hP hQ]
  apply Finset.card_le_card
  intro i hi
  simp only [diffSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  by_contra hJ
  exact hi (h i hJ)

theorem symbolicDist_self (σs : Sig) (P : (Fin n → Sig) → ℂ) (hP : IsProductFunction σs P) :
    symbolicDist P P = 0 := by
  have := symbolicDist_le_of_eqOn σs P P hP hP ∅ (fun _ _ => rfl)
  simpa using this

theorem symbolicDist_triangle (σs : Sig) (P Q R : (Fin n → Sig) → ℂ)
    (hP : IsProductFunction σs P) (hQ : IsProductFunction σs Q) (hR : IsProductFunction σs R) :
    symbolicDist P R ≤ symbolicDist P Q + symbolicDist Q R := by
  rw [symbolicDist_eq_card σs P Q hP hQ, symbolicDist_eq_card σs Q R hQ hR]
  refine (symbolicDist_le_of_eqOn σs P R hP hR (diffSet σs P Q ∪ diffSet σs Q R) ?_).trans
    (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_union, diffSet, Finset.mem_filter, Finset.mem_univ, true_and,
    not_or, not_not] at hi
  rw [hi.1, hi.2]

/-- `sd(R, 1)` counts the coordinates where the component of `R` is not identically `1`. -/
theorem symbolicDist_one_eq_card (σs : Sig) (R : (Fin n → Sig) → ℂ)
    (hR : IsProductFunction σs R) :
    symbolicDist R 1 = (Finset.univ.filter (fun i => component σs R i ≠ 1)).card := by
  rw [symbolicDist_eq_card σs R 1 hR (isProductFunction_one σs)]
  unfold diffSet
  simp only [component_one]

/-! ## S4: the span -/

variable {Ω : Type*}

theorem one_mem_spanN (C : Finset ((Fin n → Ω) → ℂ)) : (1 : (Fin n → Ω) → ℂ) ∈ spanN C :=
  ⟨fun _ => 0, by simp⟩

theorem mul_mem_spanN (C : Finset ((Fin n → Ω) → ℂ)) (Q₁ Q₂ : (Fin n → Ω) → ℂ)
    (h₁ : Q₁ ∈ spanN C) (h₂ : Q₂ ∈ spanN C) : Q₁ * Q₂ ∈ spanN C := by
  obtain ⟨a, rfl⟩ := h₁
  obtain ⟨b, rfl⟩ := h₂
  exact ⟨fun P => a P + b P, by rw [← Finset.prod_mul_distrib]; simp [pow_add]⟩

theorem pow_mem_spanN (C : Finset ((Fin n → Ω) → ℂ)) (Q : (Fin n → Ω) → ℂ)
    (h : Q ∈ spanN C) (k : ℕ) : Q ^ k ∈ spanN C := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨fun P => a P * k, by rw [← Finset.prod_pow]; simp [pow_mul]⟩

theorem mem_spanN_of_mem (C : Finset ((Fin n → Ω) → ℂ)) (P : (Fin n → Ω) → ℂ) (hP : P ∈ C) :
    P ∈ spanN C := by
  refine ⟨fun Q => if Q = P then 1 else 0, ?_⟩
  rw [Finset.prod_eq_single P]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd hP h

theorem prod_mem_spanN {ι : Type*} (C : Finset ((Fin n → Ω) → ℂ)) (s : Finset ι)
    (f : ι → (Fin n → Ω) → ℂ) (hf : ∀ i ∈ s, f i ∈ spanN C) : (∏ i ∈ s, f i) ∈ spanN C :=
  Finset.prod_induction f (· ∈ spanN C) (fun a b ha hb => mul_mem_spanN C a b ha hb)
    (one_mem_spanN C) hf

theorem distToSpan_le (P Q : (Fin n → Ω) → ℂ) (C : Finset ((Fin n → Ω) → ℂ))
    (hQ : Q ∈ spanN C) (k : ℕ) (h : symbolicDist P Q ≤ k) : distToSpan P C ≤ k :=
  (Nat.sInf_le (Set.mem_image_of_mem (fun Q => symbolicDist P Q) hQ)).trans h

/-! ## S5: agreement off a set of coordinates -/

/-- The components of `P` and `Q` agree outside `J`. -/
def EqOff (σs : Sig) (J : Finset (Fin n)) (P Q : (Fin n → Sig) → ℂ) : Prop :=
  ∀ i, i ∉ J → component σs P i = component σs Q i

theorem EqOff.refl (σs : Sig) (J : Finset (Fin n)) (P : (Fin n → Sig) → ℂ) : EqOff σs J P P :=
  fun _ _ => rfl

theorem EqOff.symm {σs : Sig} {J : Finset (Fin n)} {P Q : (Fin n → Sig) → ℂ}
    (h : EqOff σs J P Q) : EqOff σs J Q P :=
  fun i hi => (h i hi).symm

theorem EqOff.mul {σs : Sig} {J : Finset (Fin n)} {P Q P' Q' : (Fin n → Sig) → ℂ}
    (h : EqOff σs J P P') (h' : EqOff σs J Q Q') : EqOff σs J (P * Q) (P' * Q') := by
  intro i hi; rw [component_mul, component_mul, h i hi, h' i hi]

theorem EqOff.pow {σs : Sig} {J : Finset (Fin n)} {P Q : (Fin n → Sig) → ℂ}
    (h : EqOff σs J P Q) (k : ℕ) : EqOff σs J (P ^ k) (Q ^ k) := by
  intro i hi; rw [component_npow, component_npow, h i hi]

/-- If every member of `C` agrees off `J` with an element of `span C'`, so does every element
of `span C`. -/
theorem cover_spanN (σs : Sig) (J : Finset (Fin n)) (C C' : Finset ((Fin n → Sig) → ℂ))
    (h : ∀ P ∈ C, ∃ Q ∈ spanN C', EqOff σs J P Q) :
    ∀ S ∈ spanN C, ∃ Q ∈ spanN C', EqOff σs J S Q := by
  rintro S ⟨a, rfl⟩
  refine Finset.prod_induction _ (fun S => ∃ Q ∈ spanN C', EqOff σs J S Q) ?_ ?_ ?_
  · rintro S₁ S₂ ⟨Q₁, hQ₁, h₁⟩ ⟨Q₂, hQ₂, h₂⟩
    exact ⟨Q₁ * Q₂, mul_mem_spanN C' _ _ hQ₁ hQ₂, h₁.mul h₂⟩
  · exact ⟨1, one_mem_spanN C', EqOff.refl σs J 1⟩
  · intro P hP
    obtain ⟨Q, hQ, hPQ⟩ := h P hP
    exact ⟨Q ^ a P, pow_mem_spanN C' Q hQ _, hPQ.pow _⟩

/-! ## S6: closeness of spans -/

/-- Every element of `span C` is within `b` of an element of `span C'`. -/
def Close (C C' : Finset ((Fin n → Ω) → ℂ)) (b : ℤ) : Prop :=
  ∀ Q ∈ spanN C, ∃ Q' ∈ spanN C', (symbolicDist Q Q' : ℤ) ≤ b

theorem Close.refl (σs : Sig) (C : Finset ((Fin n → Sig) → ℂ))
    (hC : ∀ P ∈ C, IsProductFunction σs P) : Close C C 0 := by
  intro Q hQ
  refine ⟨Q, hQ, ?_⟩
  rw [symbolicDist_self σs Q (isProductFunction_of_mem_spanN σs C hC Q hQ)]
  simp

theorem Close.mono {C C' : Finset ((Fin n → Ω) → ℂ)} {b b' : ℤ} (h : Close C C' b)
    (hb : b ≤ b') : Close C C' b' := by
  intro Q hQ
  obtain ⟨Q', hQ', hd⟩ := h Q hQ
  exact ⟨Q', hQ', hd.trans hb⟩

theorem Close.trans (σs : Sig) {A B C : Finset ((Fin n → Sig) → ℂ)}
    (hA : ∀ P ∈ A, IsProductFunction σs P) (hB : ∀ P ∈ B, IsProductFunction σs P)
    (hC : ∀ P ∈ C, IsProductFunction σs P) {b c : ℤ}
    (h₁ : Close A B b) (h₂ : Close B C c) : Close A C (b + c) := by
  intro Q hQ
  obtain ⟨Q', hQ', hd⟩ := h₁ Q hQ
  obtain ⟨Q'', hQ'', hd'⟩ := h₂ Q' hQ'
  refine ⟨Q'', hQ'', ?_⟩
  have := symbolicDist_triangle σs Q Q' Q'' (isProductFunction_of_mem_spanN σs A hA Q hQ)
    (isProductFunction_of_mem_spanN σs B hB Q' hQ')
    (isProductFunction_of_mem_spanN σs C hC Q'' hQ'')
  have : (symbolicDist Q Q'' : ℤ) ≤ symbolicDist Q Q' + symbolicDist Q' Q'' := by exact_mod_cast this
  omega

/-- A cover off `J` gives closeness `|J|`. -/
theorem close_of_cover (σs : Sig) (J : Finset (Fin n)) (C C' : Finset ((Fin n → Sig) → ℂ))
    (hC : ∀ P ∈ C, IsProductFunction σs P) (hC' : ∀ P ∈ C', IsProductFunction σs P)
    (h : ∀ P ∈ C, ∃ Q ∈ spanN C', EqOff σs J P Q) : Close C C' (J.card : ℤ) := by
  intro S hS
  obtain ⟨Q, hQ, hSQ⟩ := cover_spanN σs J C C' h S hS
  refine ⟨Q, hQ, ?_⟩
  exact_mod_cast symbolicDist_le_of_eqOn σs S Q (isProductFunction_of_mem_spanN σs C hC S hS)
    (isProductFunction_of_mem_spanN σs C' hC' Q hQ) J hSQ

/-- `Close C C' b` bounds `distToSpan P C'` for every member `P` of `C`. -/
theorem distToSpan_le_of_close {C C' : Finset ((Fin n → Ω) → ℂ)} {b : ℤ} (h : Close C C' b)
    (P : (Fin n → Ω) → ℂ) (hP : P ∈ C) : (distToSpan P C' : ℤ) ≤ b := by
  obtain ⟨Q', hQ', hd⟩ := h P (mem_spanN_of_mem C P hP)
  have := distToSpan_le P Q' C' hQ' _ le_rfl
  have : (distToSpan P C' : ℤ) ≤ symbolicDist P Q' := by exact_mod_cast this
  omega

end RestrictedAP.Counting.Dev.SymDist
end

section
set_option autoImplicit false

/-!
# Lemma 3.2 (with Claim 3.1)

* `claim31`: if `C` is a collection of normalized, cyclic, `M`-discrete product functions with
  `¬ rk(C) ≥ D`, there is `C'` of the same kind with `|C'| ≤ |C|`, strictly smaller order sum,
  and spans within `k < D` of each other in both directions.
* `iter`: the iteration of Claim 3.1 (strong induction on the order sum).
-/

namespace RestrictedAP.Counting.Dev.L32
open RestrictedAP.Counting RestrictedAP.Counting.Dev.ProdBasics RestrictedAP.Counting.Dev.SymDist

open Classical

variable {Sig : Type*} [DecidableEq Sig] {n : ℕ}

/-- Normalized, cyclic, `M`-discrete product function. -/
def Good (σs : Sig) (M : ℕ) (P : (Fin n → Sig) → ℂ) : Prop :=
  IsProductFunction σs P ∧ IsCyclic P ∧ IsDiscrete M P

/-- `P^{β γ} · P^{(ord P - 1) β γ} = 1`. -/
theorem pow_mul_pow_pred_orderOf {G : Type*} [Monoid G] (P : G) (hP : 0 < orderOf P) (e : ℕ) :
    P ^ e * P ^ ((orderOf P - 1) * e) = 1 := by
  rw [← pow_add]
  obtain ⟨o, ho⟩ : ∃ o, orderOf P = o + 1 := ⟨orderOf P - 1, by omega⟩
  have : e + (orderOf P - 1) * e = orderOf P * e := by rw [ho]; simp; ring
  rw [this, pow_mul, pow_orderOf_eq_one, one_pow]

/-- **Claim 3.1.** -/
theorem claim31 (σs : Sig) (M : ℕ) (C : Finset ((Fin n → Sig) → ℂ))
    (hC : ∀ P ∈ C, Good σs M P) (D : ℤ) (hrk : ¬ RankAtLeast C (D : ℝ)) :
    ∃ C' : Finset ((Fin n → Sig) → ℂ), (∀ P ∈ C', Good σs M P) ∧ C'.card ≤ C.card ∧
      ∑ P ∈ C', orderOf P < ∑ P ∈ C, orderOf P ∧
      ∃ k : ℕ, (k : ℤ) < D ∧ Close C C' k ∧ Close C' C k := by
  have hCp : ∀ P ∈ C, IsProductFunction σs P := fun P hP => (hC P hP).1
  have hpos : ∀ P ∈ C, 0 < orderOf P := fun P hP => (hC P hP).2.2.1
  unfold RankAtLeast at hrk
  push Not at hrk
  obtain ⟨a, ha_lt', ⟨P₀, hP₀C, haP₀⟩, hsd⟩ := hrk
  have ha_lt : ∀ P ∈ C, a P < orderOf P := fun P hP =>
    (ha_lt' P hP).resolve_left (hpos P hP).ne'
  set R := ∏ P ∈ C, P ^ a P with hRdef
  have hR : IsProductFunction σs R :=
    isProductFunction_prod σs C _ fun P hP => isProductFunction_pow σs P (hCp P hP) _
  set J : Finset (Fin n) := Finset.univ.filter (fun i => component σs R i ≠ 1) with hJdef
  have hJD : (J.card : ℤ) < D := by
    have h1 := symbolicDist_one_eq_card σs R hR
    rw [h1] at hsd
    exact_mod_cast hsd
  have hRoff : ∀ i, i ∉ J → component σs R i = 1 := by
    intro i hi; simpa [hJdef] using hi
  obtain ⟨p, r0, hp, hord0⟩ := (hC P₀ hP₀C).2.1
  -- the distinguished element `P⋆ = Ps`: minimal `p`-adic valuation of its exponent
  set S := C.filter (fun P => a P ≠ 0 ∧ ∃ t, orderOf P = p ^ t) with hSdef
  have hSne : S.Nonempty := ⟨P₀, Finset.mem_filter.2 ⟨hP₀C, haP₀, r0, hord0⟩⟩
  obtain ⟨Ps, hPsS, hmin⟩ := S.exists_min_image (fun P => (a P).factorization p) hSne
  obtain ⟨hPsC, haPs, tPs, hordPs⟩ := Finset.mem_filter.1 hPsS
  set κ := (a Ps).factorization p with hκ
  -- exponents `β` with `P^{p^κ β_P} = P^{a_P}`
  have hdiv : ∀ P, ∃ β : ℕ, P ∈ C →
      P ^ (p ^ κ * β) = P ^ a P ∧ (p ^ κ ∣ a P → β = a P / p ^ κ) := by
    intro P
    by_cases hPC : P ∈ C
    swap
    · exact ⟨0, fun h => absurd h hPC⟩
    by_cases hd : p ^ κ ∣ a P
    · exact ⟨a P / p ^ κ, fun _ => ⟨by rw [Nat.mul_div_cancel' hd], fun _ => rfl⟩⟩
    · have hnot : ¬ ∃ t, orderOf P = p ^ t := by
        rintro ⟨t, ht⟩
        apply hd
        by_cases ha0 : a P = 0
        · rw [ha0]; exact dvd_zero _
        · have hPS : P ∈ S := Finset.mem_filter.2 ⟨hPC, ha0, t, ht⟩
          have := hmin P hPS
          exact (pow_dvd_pow p this).trans (Nat.ordProj_dvd (a P) p)
      obtain ⟨q, t, hq, hqt⟩ := (hC P hPC).2.1
      have hqp : p ≠ q := by rintro rfl; exact hnot ⟨t, hqt⟩
      have hcop : Nat.Coprime (p ^ κ) (orderOf P) := by
        rw [hqt]; exact Nat.Coprime.pow κ t ((Nat.coprime_primes hp hq).2 hqp)
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
      refine ⟨m * a P, fun _ => ⟨?_, fun h => absurd h hd⟩⟩
      rw [← mul_assoc, pow_mul, pow_mul, hm]
  choose β hβ using hdiv
  set R' := ∏ P ∈ C, P ^ β P with hR'def
  have hR' : IsProductFunction σs R' :=
    isProductFunction_prod σs C _ fun P hP => isProductFunction_pow σs P (hCp P hP) _
  have hR'mem : R' ∈ spanN C := ⟨β, rfl⟩
  have hR'pow : R' ^ (p ^ κ) = R := by
    rw [hR'def, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun P hP => ?_
    rw [← pow_mul, mul_comm, (hβ P hP).1]
  -- the new function `P' = R'|_{J^c}`
  set P' := proj σs Jᶜ R' with hP'def
  have hP' : IsProductFunction σs P' := proj_isProductFunction σs Jᶜ R' hR'
  have hP'pow : P' ^ (p ^ κ) = 1 := by
    funext x
    simp only [Pi.pow_apply, Pi.one_apply, hP'def, proj]
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun i hi => ?_
    have hiJ : i ∉ J := Finset.mem_compl.1 hi
    have := congrFun (hRoff i hiJ) (x i)
    rw [← hR'pow, component_npow_apply] at this
    simpa using this
  have hP'R' : EqOff σs J P' R' := by
    intro i hi
    funext a'
    rw [hP'def, component_proj σs Jᶜ R' hR' i a', if_pos (Finset.mem_compl.2 hi)]
  -- orders
  have haPs_lt := ha_lt Ps hPsC
  have hκle : p ^ κ ≤ a Ps :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero haPs) (Nat.ordProj_dvd (a Ps) p)
  have hP'dvd : orderOf P' ∣ p ^ κ := orderOf_dvd_of_pow_eq_one hP'pow
  have hP'le : orderOf P' ≤ p ^ κ := Nat.le_of_dvd (pow_pos hp.pos _) hP'dvd
  have hP'lt : orderOf P' < orderOf Ps := by omega
  have hP'good : Good σs M P' := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hP'dvd
    refine ⟨hP', ⟨p, j, hp, hj⟩, ?_, ?_⟩
    · rw [hj]; exact pow_pos hp.pos _
    · have := (hC Ps hPsC).2.2.2; omega
  -- `β_{P⋆}` is coprime to `ord P⋆`
  have hβPs : β Ps = a Ps / p ^ κ := (hβ Ps hPsC).2 (Nat.ordProj_dvd (a Ps) p)
  have hcopPs : Nat.Coprime (β Ps) (orderOf Ps) := by
    rw [hordPs, hβPs]
    exact Nat.Coprime.pow_right _ (Nat.coprime_ordCompl hp haPs).symm
  obtain ⟨γ, hγ⟩ := exists_pow_eq_self_of_coprime hcopPs
  set X := ∏ P ∈ C.erase Ps, P ^ ((orderOf P - 1) * (β P * γ)) with hXdef
  have hPsEq : R' ^ γ * X = Ps := by
    rw [hR'def, ← Finset.prod_pow, ← Finset.mul_prod_erase C (fun P => (P ^ β P) ^ γ) hPsC,
      hXdef, mul_assoc, ← Finset.prod_mul_distrib, hγ]
    rw [Finset.prod_eq_one, mul_one]
    intro P hP
    rw [← pow_mul]
    exact pow_mul_pow_pred_orderOf P (hpos P (Finset.mem_of_mem_erase hP)) _
  -- the new collection
  set C' := insert P' (C.erase Ps) with hC'def
  have hC'good : ∀ P ∈ C', Good σs M P := by
    intro P hP
    rcases Finset.mem_insert.1 hP with rfl | hP
    · exact hP'good
    · exact hC P (Finset.mem_of_mem_erase hP)
  have hC'p : ∀ P ∈ C', IsProductFunction σs P := fun P hP => (hC'good P hP).1
  have hcov1 : ∀ P ∈ C, ∃ Q ∈ spanN C', EqOff σs J P Q := by
    intro P hP
    by_cases hPPs : P = Ps
    · subst hPPs
      refine ⟨P' ^ γ * X, ?_, ?_⟩
      · refine mul_mem_spanN C' _ _
          (pow_mem_spanN C' _ (mem_spanN_of_mem C' _ (Finset.mem_insert_self _ _)) _) ?_
        exact prod_mem_spanN C' _ _ fun Q hQ => pow_mem_spanN C' _
          (mem_spanN_of_mem C' _ (Finset.mem_insert_of_mem hQ)) _
      · have h := (hP'R'.symm.pow γ).mul (EqOff.refl σs J X)
        rw [hPsEq] at h
        exact h
    · exact ⟨P, mem_spanN_of_mem C' _ (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hPPs, hP⟩)),
        EqOff.refl σs J P⟩
  have hcov2 : ∀ P ∈ C', ∃ Q ∈ spanN C, EqOff σs J P Q := by
    intro P hP
    rcases Finset.mem_insert.1 hP with rfl | hP
    · exact ⟨R', hR'mem, hP'R'⟩
    · exact ⟨P, mem_spanN_of_mem C _ (Finset.mem_of_mem_erase hP), EqOff.refl σs J P⟩
  refine ⟨C', hC'good, ?_, ?_, J.card, hJD, close_of_cover σs J C C' hCp hC'p hcov1,
    close_of_cover σs J C' C hC'p hCp hcov2⟩
  · rw [hC'def]
    have h1 := Finset.card_insert_le P' (C.erase Ps)
    have h2 := Finset.card_erase_of_mem hPsC
    have h3 : 0 < C.card := Finset.card_pos.2 ⟨Ps, hPsC⟩
    omega
  · have h1 : ∑ P ∈ C', orderOf P ≤ orderOf P' + ∑ P ∈ C.erase Ps, orderOf P := by
      by_cases hm : P' ∈ C.erase Ps
      · rw [hC'def, Finset.insert_eq_of_mem hm]; omega
      · rw [hC'def, Finset.sum_insert hm]
    have h2 := Finset.add_sum_erase C (fun P => orderOf P) hPsC
    omega

/-- The iteration in the proof of Lemma 3.2, by strong induction on the order sum. -/
theorem iter (σs : Sig) (M : ℕ) (PP : Finset ((Fin n → Sig) → ℂ))
    (hPP : ∀ P ∈ PP, Good σs M P) (D : ℕ → ℤ) :
    ∀ m : ℕ, ∀ (C : Finset ((Fin n → Sig) → ℂ)) (i : ℕ), ∑ P ∈ C, orderOf P = m →
      (∀ P ∈ C, Good σs M P) → C.card ≤ PP.card → 1 ≤ i → m + i ≤ M * PP.card + 1 →
      Close PP C (∑ j ∈ Finset.Ico 1 i, D j) → Close C PP (∑ j ∈ Finset.Ico 1 i, D j) →
      ∃ PP' : Finset ((Fin n → Sig) → ℂ),
        (∀ P ∈ PP', IsProductFunction σs P ∧ IsCyclic P ∧ IsDiscrete M P) ∧
        PP'.card ≤ PP.card ∧
        ∃ i : ℕ, 1 ≤ i ∧ i ≤ M * PP.card + 1 ∧
          RankAtLeast PP' (D i : ℝ) ∧
          (∀ P ∈ PP, (distToSpan P PP' : ℤ) ≤ ∑ j ∈ Finset.Ico 1 i, D j) ∧
          (∀ P ∈ PP', (distToSpan P PP : ℤ) ≤ ∑ j ∈ Finset.Ico 1 i, D j) := by
  have hPPp : ∀ P ∈ PP, IsProductFunction σs P := fun P hP => (hPP P hP).1
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro C i hm hC hcard hi hbound h1 h2
  have hCp : ∀ P ∈ C, IsProductFunction σs P := fun P hP => (hC P hP).1
  by_cases hr : RankAtLeast C (D i : ℝ)
  · exact ⟨C, hC, hcard, i, hi, by omega, hr, fun P hP => distToSpan_le_of_close h1 P hP,
      fun P hP => distToSpan_le_of_close h2 P hP⟩
  · obtain ⟨C', hC', hcard', hsum, k, hk, hc1, hc2⟩ := claim31 σs M C hC (D i) hr
    have hC'p : ∀ P ∈ C', IsProductFunction σs P := fun P hP => (hC' P hP).1
    have hsum_eq : ∑ j ∈ Finset.Ico 1 (i + 1), D j = (∑ j ∈ Finset.Ico 1 i, D j) + D i :=
      Finset.sum_Ico_succ_top hi _
    refine ih _ (hm ▸ hsum) C' (i + 1) rfl hC' (hcard'.trans hcard) (by omega) (by omega) ?_ ?_
    · rw [hsum_eq]; exact (Close.trans σs hPPp hCp hC'p h1 hc1).mono (by omega)
    · rw [hsum_eq]; exact (Close.trans σs hC'p hCp hPPp hc2 h2).mono (by omega)

end RestrictedAP.Counting.Dev.L32

namespace RestrictedAP.Counting

open RestrictedAP.Counting.Dev.L32 RestrictedAP.Counting.Dev.SymDist in
theorem chk_lemma_3_2 (Sig : Type) [Fintype Sig] [DecidableEq Sig] (σs : Sig) (n M : ℕ)
    (PP : Finset ((Fin n → Sig) → ℂ))
    (hPP : ∀ P ∈ PP, IsProductFunction σs P ∧ IsCyclic P ∧ IsDiscrete M P)
    (D : ℕ → ℤ) (hD : ∀ j, 1 ≤ j → j < M * PP.card + 1 → D j ≤ D (j + 1)) :
    ∃ PP' : Finset ((Fin n → Sig) → ℂ),
      (∀ P ∈ PP', IsProductFunction σs P ∧ IsCyclic P ∧ IsDiscrete M P) ∧
      PP'.card ≤ PP.card ∧
      ∃ i : ℕ, 1 ≤ i ∧ i ≤ M * PP.card + 1 ∧
        RankAtLeast PP' (D i : ℝ) ∧
        (∀ P ∈ PP, (distToSpan P PP' : ℤ) ≤ ∑ j ∈ Finset.Ico 1 i, D j) ∧
        (∀ P ∈ PP', (distToSpan P PP : ℤ) ≤ ∑ j ∈ Finset.Ico 1 i, D j) := by
  have hPPp : ∀ P ∈ PP, IsProductFunction σs P := fun P hP => (hPP P hP).1
  have hsum : ∑ P ∈ PP, orderOf P ≤ PP.card • M :=
    Finset.sum_le_card_nsmul PP (fun P => orderOf P) M fun P hP => (hPP P hP).2.2.2
  rw [smul_eq_mul] at hsum
  have h0 : Close PP PP (∑ j ∈ Finset.Ico 1 1, D j) := by
    simpa using Close.refl σs PP hPPp
  exact iter σs M PP hPP D _ PP 1 rfl hPP le_rfl le_rfl
    (by rw [Nat.mul_comm M]; omega) h0 h0


end RestrictedAP.Counting
end

theorem solution : type_of% @RestrictedAP.Counting.chk_lemma_3_2 := @RestrictedAP.Counting.chk_lemma_3_2
