-- Prove2me | solution 1 for RestrictedAP.Counting.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:56:09.314199+00:00
-- url     : https://prove2.me/submissions/28055ea5-5436-450f-b8d5-e26355962b49

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_ProductFunctions
import Theorems.Thm_RestrictedAP_Counting_lemma_3_2
import Theorems.Thm_RestrictedAP_Counting_lemma_3_3

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

theorem pow_apply_eq_one {α : Type*} (P : α → ℂ) (N : ℕ) (h : P ^ N = 1) (x : α) :
    P x ^ N = 1 := by
  have := congrFun h x; simpa using this

theorem component_pow (σs : Sig) (P : (Fin n → Sig) → ℂ) (N : ℕ) (h : P ^ N = 1) (i : Fin n)
    (a : Sig) : component σs P i a ^ N = 1 :=
  pow_apply_eq_one P N h _

theorem proj_pow_apply (σs : Sig) (K : Finset (Fin n)) (P : (Fin n → Sig) → ℂ) (N : ℕ)
    (h : P ^ N = 1) (x : Fin n → Sig) : proj σs K P x ^ N = 1 := by
  unfold proj
  rw [← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => component_pow σs P N h i (x i)

theorem proj_pow (σs : Sig) (K : Finset (Fin n)) (P : (Fin n → Sig) → ℂ) (N : ℕ)
    (h : P ^ N = 1) : proj σs K P ^ N = 1 := by
  funext x; simpa using proj_pow_apply σs K P N h x

theorem orderOf_proj_dvd (σs : Sig) (K : Finset (Fin n)) (P : (Fin n → Sig) → ℂ) :
    orderOf (proj σs K P) ∣ orderOf P :=
  orderOf_dvd_of_pow_eq_one (proj_pow σs K P _ (pow_orderOf_eq_one P))

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

theorem symbolicDist_comm (σs : Sig) (P Q : (Fin n → Sig) → ℂ)
    (hP : IsProductFunction σs P) (hQ : IsProductFunction σs Q) :
    symbolicDist P Q = symbolicDist Q P := by
  rw [symbolicDist_eq_card σs P Q hP hQ, symbolicDist_eq_card σs Q P hQ hP]
  unfold diffSet
  congr 1
  ext i; simp [ne_comm]

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

/-- `distToSpan` is realized by an element of the span. -/
theorem exists_distToSpan_eq (P : (Fin n → Ω) → ℂ) (C : Finset ((Fin n → Ω) → ℂ)) :
    ∃ Q ∈ spanN C, symbolicDist P Q = distToSpan P C := by
  have hne : ((fun Q => symbolicDist P Q) '' spanN C).Nonempty :=
    Set.Nonempty.image _ ⟨1, one_mem_spanN C⟩
  obtain ⟨Q, hQ, hQe⟩ := (Set.mem_image _ _ _).1 (Nat.sInf_mem hne)
  exact ⟨Q, hQ, hQe⟩

/-! ## S5: agreement off a set of coordinates -/

/-! ## S6: closeness of spans -/

end RestrictedAP.Counting.Dev.SymDist
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RestrictedAP.Counting.Dev.L34
open RestrictedAP.Counting RestrictedAP.Counting.Dev.ProdBasics RestrictedAP.Counting.Dev.SymDist

open Classical

variable {Sig : Type*} [DecidableEq Sig] {n : ℕ}

/-! ## Projection is a monoid homomorphism -/

theorem proj_one' (σs : Sig) (K : Finset (Fin n)) :
    proj σs K (1 : (Fin n → Sig) → ℂ) = 1 := by
  funext x; simp [proj, component]

theorem proj_mul' (σs : Sig) (K : Finset (Fin n)) (P Q : (Fin n → Sig) → ℂ) :
    proj σs K (P * Q) = proj σs K P * proj σs K Q := by
  funext x; simp [proj, component, Finset.prod_mul_distrib]

/-- `proj σs K` as a monoid homomorphism. -/
noncomputable def projHom (σs : Sig) (K : Finset (Fin n)) :
    ((Fin n → Sig) → ℂ) →* ((Fin n → Sig) → ℂ) where
  toFun := proj σs K
  map_one' := proj_one' σs K
  map_mul' := proj_mul' σs K

theorem proj_prod_pow (σs : Sig) (K : Finset (Fin n)) (C : Finset ((Fin n → Sig) → ℂ))
    (a : ((Fin n → Sig) → ℂ) → ℕ) :
    proj σs K (∏ P ∈ C, P ^ a P) = ∏ P ∈ C, proj σs K P ^ a P := by
  rw [show proj σs K = ⇑(projHom σs K) from rfl, map_prod]
  simp only [map_pow]

/-- Projecting off `J` changes a normalized product function in at most `|J|` coordinates. -/
theorem symbolicDist_proj_le (σs : Sig) (J : Finset (Fin n)) (P : (Fin n → Sig) → ℂ)
    (hP : IsProductFunction σs P) : symbolicDist P (proj σs Jᶜ P) ≤ J.card := by
  refine symbolicDist_le_of_eqOn σs P _ hP (proj_isProductFunction σs Jᶜ P hP) J ?_
  intro i hi
  funext b
  rw [component_proj σs Jᶜ P hP i b, if_pos (Finset.mem_compl.mpr hi)]

theorem symbolicDist_proj_le' (σs : Sig) (J : Finset (Fin n)) (P : (Fin n → Sig) → ℂ)
    (hP : IsProductFunction σs P) : symbolicDist (proj σs Jᶜ P) P ≤ J.card := by
  rw [symbolicDist_comm σs _ _ (proj_isProductFunction σs Jᶜ P hP) hP]
  exact symbolicDist_proj_le σs J P hP

theorem proj_mem_spanN (σs : Sig) (J : Finset (Fin n)) (C : Finset ((Fin n → Sig) → ℂ))
    (Q : (Fin n → Sig) → ℂ) (hQ : Q ∈ spanN C) : proj σs Jᶜ Q ∈ spanN (projColl σs Jᶜ C) := by
  obtain ⟨a, rfl⟩ := hQ
  rw [proj_prod_pow]
  refine prod_mem_spanN _ C _ fun P hP => pow_mem_spanN _ _ (mem_spanN_of_mem _ _ ?_) _
  exact Finset.mem_image_of_mem _ hP

/-! ## Properties of the projected collection -/

theorem projColl_props (σs : Sig) (J : Finset (Fin n)) (M : ℕ) (C : Finset ((Fin n → Sig) → ℂ))
    (hC : ∀ P ∈ C, IsProductFunction σs P ∧ IsCyclic P ∧ IsDiscrete M P) :
    ∀ f ∈ projColl σs Jᶜ C, IsProductFunction σs f ∧ IsCyclic f ∧ IsDiscrete M f := by
  intro f hf
  obtain ⟨P, hPC, rfl⟩ := Finset.mem_image.mp hf
  obtain ⟨hP1, ⟨p, r, hp, hpr⟩, hpos, hle⟩ := hC P hPC
  have hdvd := orderOf_proj_dvd σs Jᶜ P
  refine ⟨proj_isProductFunction σs Jᶜ P hP1, ?_, ?_, ?_⟩
  · rw [hpr] at hdvd
    obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    exact ⟨p, s, hp, hs⟩
  · exact Nat.pos_of_dvd_of_pos hdvd hpos
  · exact (Nat.le_of_dvd hpos hdvd).trans hle

theorem rank_projColl (σs : Sig) (J : Finset (Fin n)) (C : Finset ((Fin n → Sig) → ℂ))
    (hC : ∀ P ∈ C, IsProductFunction σs P ∧ 0 < orderOf P) (d : ℝ) (h : RankAtLeast C d) :
    RankAtLeast (projColl σs Jᶜ C) (d - J.card) := by
  classical
  intro a ha hne
  have hpre : ∀ f ∈ projColl σs Jᶜ C, ∃ P ∈ C, proj σs Jᶜ P = f := fun f hf =>
    Finset.mem_image.mp hf
  choose! g hgC hg using hpre
  set T := (projColl σs Jᶜ C).image g with hT
  have hTC : T ⊆ C := by
    intro P hP
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hP
    exact hgC f hf
  have hginj : Set.InjOn g (projColl σs Jᶜ C) := fun f hf f' hf' e => by
    rw [← hg f hf, ← hg f' hf', e]
  let a' : ((Fin n → Sig) → ℂ) → ℕ := fun P => if P ∈ T then a (proj σs Jᶜ P) else 0
  have key : proj σs Jᶜ (∏ P ∈ C, P ^ a' P) = ∏ f ∈ projColl σs Jᶜ C, f ^ a f := by
    rw [proj_prod_pow]
    rw [← Finset.prod_subset hTC (fun P _ hPT => by simp [a', hPT])]
    rw [hT, Finset.prod_image (fun f hf f' hf' e => hginj hf hf' e)]
    refine Finset.prod_congr rfl fun f hf => ?_
    have hgT : g f ∈ T := Finset.mem_image_of_mem g hf
    simp only [a', if_pos hgT, hg f hf]
  have ha' : ∀ P ∈ C, orderOf P = 0 ∨ a' P < orderOf P := by
    intro P hPC
    right
    have hpos := (hC P hPC).2
    by_cases hPT : P ∈ T
    · simp only [a', if_pos hPT]
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hPT
      rw [hg f hf]
      have hdvd : orderOf f ∣ orderOf (g f) := by
        have := orderOf_proj_dvd σs Jᶜ (g f); rwa [hg f hf] at this
      rcases ha f hf with h0 | hlt
      · exact absurd (Nat.pos_of_dvd_of_pos hdvd hpos) (by omega)
      · exact lt_of_lt_of_le hlt (Nat.le_of_dvd hpos hdvd)
    · simp only [a', if_neg hPT]; exact hpos
  have hne' : ∃ P ∈ C, a' P ≠ 0 := by
    obtain ⟨f, hf, hfa⟩ := hne
    refine ⟨g f, hgC f hf, ?_⟩
    show (if g f ∈ T then a (proj σs Jᶜ (g f)) else 0) ≠ 0
    rw [if_pos (Finset.mem_image_of_mem g hf), hg f hf]
    exact hfa
  have hS := h a' ha' hne'
  set S := ∏ P ∈ C, P ^ a' P
  have hSp : IsProductFunction σs S :=
    isProductFunction_prod σs C _ fun P hP => isProductFunction_pow σs P (hC P hP).1 _
  have htri := symbolicDist_triangle σs S (proj σs Jᶜ S) 1 hSp
    (proj_isProductFunction σs Jᶜ S hSp) (isProductFunction_one σs)
  have hJ := symbolicDist_proj_le σs J S hSp
  rw [← key]
  have : (symbolicDist S 1 : ℝ) ≤ J.card + symbolicDist (proj σs Jᶜ S) 1 := by
    exact_mod_cast htri.trans (Nat.add_le_add_right hJ _)
  linarith

theorem card_projColl_le (σs : Sig) (K : Finset (Fin n)) (C : Finset ((Fin n → Sig) → ℂ)) :
    (projColl σs K C).card ≤ C.card := Finset.card_image_le

theorem mem_projColl (σs : Sig) (K : Finset (Fin n)) (C : Finset ((Fin n → Sig) → ℂ))
    (f : (Fin n → Sig) → ℂ) (hf : f ∈ projColl σs K C) : ∃ P ∈ C, proj σs K P = f :=
  Finset.mem_image.mp hf

theorem rank_mono {Ω : Type*} (C : Finset ((Fin n → Ω) → ℂ)) (d d' : ℝ) (h : RankAtLeast C d)
    (hd : d' ≤ d) : RankAtLeast C d' := fun a ha hne => hd.trans (h a ha hne)

theorem softRank_mono {Ω : Type*} (μ : Ω × Ω × Ω → ℝ) (C : Finset ((Fin n → Ω) → ℂ)) (d d' : ℝ)
    (h : SoftRankMuAtLeast μ C d) (hd : d' ≤ d) : SoftRankMuAtLeast μ C d' := fun a =>
  (h a).imp id fun h' => hd.trans h'

/-! ## Arithmetic -/

theorem sum_comp_le (D : ℕ → ℤ) (f : ℕ → ℕ) (s t : Finset ℕ) (hf : Set.InjOn f s)
    (hst : ∀ x ∈ s, f x ∈ t) (hD : ∀ m ∈ t, 0 ≤ D m) :
    ∑ x ∈ s, D (f x) ≤ ∑ m ∈ t, D m := by
  classical
  rw [← Finset.sum_image (f := D) (fun x hx y hy e => hf hx hy e)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m hm _ => hD m hm
  intro m hm
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm
  exact hst x hx

theorem mono_of_step (D : ℕ → ℤ) (k : ℕ) (hD : ∀ j, 1 ≤ j → j < k → D j ≤ D (j + 1)) :
    ∀ b a, 1 ≤ a → a ≤ b → b ≤ k → D a ≤ D b := by
  intro b
  induction b with
  | zero => intro a ha hab _; omega
  | succ b ih =>
    intro a ha hab hbk
    rcases Nat.eq_or_lt_of_le hab with h | h
    · rw [h]
    · exact (ih a ha (by omega) (by omega)).trans (hD b (by omega) (by omega))

end RestrictedAP.Counting.Dev.L34

namespace RestrictedAP.Counting
open RestrictedAP.Counting.Dev.L34 RestrictedAP.Counting.Dev.ProdBasics
  RestrictedAP.Counting.Dev.SymDist in
theorem chk_lemma_3_4 (r M : ℕ) :
    ∃ k : ℕ, ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig] (σs : Sig)
      (μ : Sig × Sig × Sig → ℝ) (n : ℕ) (PP : Finset ((Fin n → Sig) → ℂ)),
      IsDist μ → PP.card = r →
      (∀ P ∈ PP, IsProductFunction σs P ∧ IsCyclic P ∧ IsDiscrete M P) →
      ∀ D : ℕ → ℤ, (∀ j, 1 ≤ j → j < k → D j ≤ D (j + 1)) →
      ∃ i : ℕ, 1 ≤ i ∧ i ≤ k ∧
        ∃ PP' : Finset ((Fin n → Sig) → ℂ),
          (∀ P ∈ PP', IsProductFunction σs P ∧ IsCyclic P ∧ IsDiscrete M P) ∧
          PP'.card ≤ PP.card ∧
          SoftRankMuAtLeast μ PP' ((D i - ∑ j ∈ Finset.Ico 1 i, D j : ℤ) : ℝ) ∧
          RankAtLeast PP' ((D i - ∑ j ∈ Finset.Ico 1 i, D j : ℤ) : ℝ) ∧
          (∀ P ∈ PP, (distToSpan P PP' : ℤ) ≤ 2 * ∑ j ∈ Finset.Ico 1 i, D j) ∧
          (∀ P ∈ PP', (distToSpan P PP : ℤ) ≤ 2 * ∑ j ∈ Finset.Ico 1 i, D j) := by
  set k₁ := M * r + 1 with hk₁
  set k₂ := (M + 1) ^ (3 * r) with hk₂
  have hk₂pos : 1 ≤ k₂ := Nat.one_le_pow _ _ (Nat.succ_pos M)
  refine ⟨k₁ * k₂, ?_⟩
  intro Sig _ _ σs μ n PP hμ hcard hPP D hD
  have hk : 1 ≤ k₁ * k₂ := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hmono := mono_of_step D _ hD
  by_cases hD1 : D 1 ≤ 0
  · -- trivial case: `i = 1`, `PP' = PP`
    refine ⟨1, le_rfl, hk, PP, hPP, le_rfl, ?_, ?_, ?_, ?_⟩
    · intro a
      right
      simp only [Finset.Ico_self, Finset.sum_empty, sub_zero]
      have : ((D 1 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hD1
      exact this.trans (Nat.cast_nonneg _)
    · intro a _ _
      simp only [Finset.Ico_self, Finset.sum_empty, sub_zero]
      have : ((D 1 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hD1
      exact this.trans (Nat.cast_nonneg _)
    · intro P hP
      simp only [Finset.Ico_self, Finset.sum_empty, mul_zero]
      have := distToSpan_le P P PP (mem_spanN_of_mem PP P hP) 0
        (symbolicDist_self σs P (hPP P hP).1).le
      omega
    · intro P hP
      simp only [Finset.Ico_self, Finset.sum_empty, mul_zero]
      have := distToSpan_le P P PP (mem_spanN_of_mem PP P hP) 0
        (symbolicDist_self σs P (hPP P hP).1).le
      omega
  replace hD1 : 0 < D 1 := by omega
  have hpos : ∀ m, 1 ≤ m → m ≤ k₁ * k₂ → 1 ≤ D m := fun m h1 h2 =>
    (show (1 : ℤ) ≤ D 1 by omega).trans (hmono m 1 le_rfl h1 h2)
  -- Lemma 3.2 on `PP` with `E j = D (j k₂)`
  obtain ⟨PPt, hPPt, hcardt, j, hj1, hjk, hrank, hd1, hd2⟩ :=
    RestrictedAP.Counting.lemma_3_2 Sig σs n M PP hPP (fun j => D (j * k₂)) (by
      intro j h1 h2
      rw [hcard] at h2
      refine hmono _ _ ?_ ?_ ?_
      · nlinarith
      · nlinarith
      · exact Nat.mul_le_mul_right _ (by omega))
  rw [hcard] at hjk
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hpowle : M ^ (3 * PPt.card) ≤ k₂ :=
    (Nat.pow_le_pow_left (Nat.le_succ M) _).trans
      (Nat.pow_le_pow_right (Nat.succ_pos M) (by omega))
  have hjk₂ : (j' + 1) * k₂ ≤ k₁ * k₂ := Nat.mul_le_mul_right _ hjk
  -- Lemma 3.3 on `PPt` with `E' ℓ = D (j' k₂ + ℓ)`
  obtain ⟨ℓ, hℓ1, hℓM, J, hJ, hsoft⟩ :=
    RestrictedAP.Counting.lemma_3_3 Sig σs μ hμ n M PPt hPPt (fun ℓ => D (j' * k₂ + ℓ)) (by
      intro l h1 h2
      refine hmono _ _ (by omega) (by omega) ?_
      have : j' * k₂ + l + 1 ≤ j' * k₂ + k₂ := by omega
      nlinarith)
  have hℓk : ℓ ≤ k₂ := hℓM.trans hpowle
  set i := j' * k₂ + ℓ with hi
  have hik : i ≤ (j' + 1) * k₂ := by rw [hi]; nlinarith
  have hik' : i ≤ k₁ * k₂ := hik.trans hjk₂
  set Ssum := ∑ m ∈ Finset.Ico 1 i, D m with hSsum
  have hnonneg : ∀ m ∈ Finset.Ico 1 i, 0 ≤ D m := fun m hm => by
    rw [Finset.mem_Ico] at hm
    have := hpos m hm.1 (by omega); omega
  have hS0 : 0 ≤ Ssum := Finset.sum_nonneg hnonneg
  have hA : ∑ l ∈ Finset.Ico 1 (j' + 1), D (l * k₂) ≤ Ssum := by
    refine sum_comp_le D (fun l => l * k₂) _ _ ?_ ?_ hnonneg
    · intro x _ y _ e
      exact Nat.eq_of_mul_eq_mul_right (by omega) e
    · intro x hx
      rw [Finset.mem_Ico] at hx ⊢
      constructor
      · nlinarith
      · have : x * k₂ ≤ j' * k₂ := Nat.mul_le_mul_right _ (by omega)
        omega
  have hB : (J.card : ℤ) ≤ Ssum := by
    refine hJ.trans (sum_comp_le D (fun l => j' * k₂ + l) _ _ ?_ ?_ hnonneg)
    · intro x _ y _ e
      simpa using e
    · intro x hx
      rw [Finset.mem_Ico] at hx ⊢
      omega
  have hDi : D i ≤ D ((j' + 1) * k₂) := hmono _ _ (by omega) hik hjk₂
  -- the new collection
  have hPPt1 : ∀ P ∈ PPt, IsProductFunction σs P := fun P hP => (hPPt P hP).1
  have hPP1 : ∀ P ∈ PP, IsProductFunction σs P := fun P hP => (hPP P hP).1
  refine ⟨i, by omega, hik', projColl σs Jᶜ PPt, projColl_props σs J M PPt hPPt,
    (card_projColl_le σs Jᶜ PPt).trans hcardt, ?_, ?_, ?_, ?_⟩
  · refine softRank_mono μ _ _ _ hsoft ?_
    have : (0 : ℝ) ≤ (Ssum : ℝ) := by exact_mod_cast hS0
    rw [Int.cast_sub]; linarith
  · have hr := rank_projColl σs J PPt (fun P hP => ⟨(hPPt P hP).1, (hPPt P hP).2.2.1⟩) _ hrank
    refine rank_mono _ _ _ hr ?_
    have h1 : ((D i : ℤ) : ℝ) ≤ ((D ((j' + 1) * k₂) : ℤ) : ℝ) := by exact_mod_cast hDi
    have h2 : ((J.card : ℤ) : ℝ) ≤ (Ssum : ℝ) := by exact_mod_cast hB
    rw [Int.cast_sub]; push_cast at h2; linarith
  · intro P hP
    obtain ⟨Q, hQ, hPQ⟩ := exists_distToSpan_eq P PPt
    have hQp := isProductFunction_of_mem_spanN σs PPt hPPt1 Q hQ
    have hle := distToSpan_le P (proj σs Jᶜ Q) (projColl σs Jᶜ PPt)
      (proj_mem_spanN σs J PPt Q hQ) _ le_rfl
    have htri := symbolicDist_triangle σs P Q (proj σs Jᶜ Q) (hPP1 P hP) hQp
      (proj_isProductFunction σs Jᶜ Q hQp)
    have hJQ := symbolicDist_proj_le σs J Q hQp
    have h1 := hd1 P hP
    have : (distToSpan P (projColl σs Jᶜ PPt) : ℤ) ≤ distToSpan P PPt + J.card := by
      rw [← hPQ]; exact_mod_cast hle.trans (htri.trans (Nat.add_le_add_left hJQ _))
    linarith
  · intro f hf
    obtain ⟨P₀, hP₀, rfl⟩ := mem_projColl σs Jᶜ PPt f hf
    obtain ⟨Q, hQ, hPQ⟩ := exists_distToSpan_eq P₀ PP
    have hQp := isProductFunction_of_mem_spanN σs PP hPP1 Q hQ
    have hP₀p := hPPt1 P₀ hP₀
    have hle := distToSpan_le (proj σs Jᶜ P₀) Q PP hQ _ le_rfl
    have htri := symbolicDist_triangle σs (proj σs Jᶜ P₀) P₀ Q
      (proj_isProductFunction σs Jᶜ P₀ hP₀p) hP₀p hQp
    have hJP := symbolicDist_proj_le' σs J P₀ hP₀p
    have h2 := hd2 P₀ hP₀
    have : (distToSpan (proj σs Jᶜ P₀) PP : ℤ) ≤ J.card + distToSpan P₀ PP := by
      rw [← hPQ]; exact_mod_cast hle.trans (htri.trans (Nat.add_le_add_right hJP _))
    linarith

end RestrictedAP.Counting
end

theorem solution : type_of% @RestrictedAP.Counting.chk_lemma_3_4 := @RestrictedAP.Counting.chk_lemma_3_4
