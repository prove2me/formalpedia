-- Prove2me | solution 1 for UniformADProbes.Trace.principal_moment_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T20:29:13.798203+00:00
-- url     : https://prove2.me/submissions/a5942793-d353-48f1-89d0-c2112418dab4

import Mathlib
import Definitions.Def_UniformADProbes_Trace_algebra

section
set_option autoImplicit false

namespace UniformADProbes.Trace.Dev.PMR

open scoped Classical

/-! Basic definitions: coloured graphs, the word-algebra representation and moment functional. -/

/-- adjacency matrix over `ℚ` -/
noncomputable def adjQ {V : Type} (G : SimpleGraph V) : Matrix V V ℚ :=
  fun i j => if G.Adj i j then 1 else 0

/-- degree -/
noncomputable def dg {V : Type} [Fintype V] (G : SimpleGraph V) (v : V) : ℕ := G.degree v

/-- the diagonal projection onto the colour class `c` -/
noncomputable def indE {V κ : Type} [DecidableEq V] [DecidableEq κ] (col : V → κ) (c : κ) : Matrix V V ℚ :=
  Matrix.diagonal fun v => if col v = c then 1 else 0

noncomputable def letterMat {V κ : Type} [DecidableEq V] [DecidableEq κ] (G : SimpleGraph V) (col : V → κ) :
    Option κ → Matrix V V ℚ
  | none => adjQ G
  | some c => indE col c

noncomputable def rho {V κ : Type} [Fintype V] [DecidableEq V] [DecidableEq κ] (G : SimpleGraph V) (col : V → κ) :
    FreeAlgebra ℚ (Option κ) →ₐ[ℚ] Matrix V V ℚ :=
  FreeAlgebra.lift ℚ (letterMat G col)

/-- sum of all entries as a linear map -/
noncomputable def momL (V : Type) [Fintype V] : Matrix V V ℚ →ₗ[ℚ] ℚ where
  toFun M := ∑ i, ∑ j, M i j
  map_add' M N := by
    simp [Finset.sum_add_distrib]
  map_smul' r M := by
    simp [Finset.mul_sum]

noncomputable def phi {V κ : Type} [Fintype V] [DecidableEq V] [DecidableEq κ] (G : SimpleGraph V) (col : V → κ)
    (a : FreeAlgebra ℚ (Option κ)) : ℚ :=
  momL V (rho G col a)

/-! Bridge from the word moments of the statement to `FreeAlgebra ℚ Bool`. -/

noncomputable def rhoAD {V : Type} [Fintype V] [DecidableEq V] (H K : Matrix V V ℚ) :
    FreeAlgebra ℚ Bool →ₐ[ℚ] Matrix V V ℚ :=
  FreeAlgebra.lift ℚ (fun b => if b then K else H)

def wordAlg (l : List Bool) : FreeAlgebra ℚ Bool :=
  l.foldr (fun b z => FreeAlgebra.ι ℚ b * z) 1

lemma wordAlg_append (l₁ l₂ : List Bool) : wordAlg (l₁ ++ l₂) = wordAlg l₁ * wordAlg l₂ := by
  induction l₁ with
  | nil => simp [wordAlg]
  | cons b l ih => simp only [List.cons_append, wordAlg, List.foldr_cons] at ih ⊢; rw [ih, mul_assoc]

lemma span_wordAlg : Submodule.span ℚ (Set.range wordAlg) = ⊤ := by
  rw [eq_top_iff]
  intro a ha
  clear ha
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    have : (algebraMap ℚ (FreeAlgebra ℚ Bool)) r = r • wordAlg [] := by
      simp [wordAlg, Algebra.algebraMap_eq_smul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], rfl⟩)
  | grade1 b =>
    have : FreeAlgebra.ι ℚ b = wordAlg [b] := by simp [wordAlg]
    rw [this]
    exact Submodule.subset_span ⟨[b], rfl⟩
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | mul x y hx hy =>
    have h := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨_, ⟨l₁, rfl⟩, _, ⟨l₂, rfl⟩, rfl⟩
    exact ⟨l₁ ++ l₂, (wordAlg_append l₁ l₂)⟩

lemma rhoAD_wordAlg {V : Type} [Fintype V] [DecidableEq V] (H K : Matrix V V ℚ) (l : List Bool) :
    rhoAD H K (wordAlg l) = l.foldr (fun (b : Bool) z => (if b = true then K else H) * z) 1 := by
  induction l with
  | nil => simp [wordAlg]
  | cons b l ih =>
    simp only [wordAlg, List.foldr_cons] at ih ⊢
    rw [map_mul, ih]
    simp [rhoAD]

lemma foldr_map_int {V : Type} [Fintype V] [DecidableEq V] (H K : Matrix V V ℤ) (l : List Bool) :
    (l.foldr (fun (b : Bool) z => (if b = true then K else H) * z) 1).map (Int.cast : ℤ → ℚ) =
      l.foldr (fun (b : Bool) z => (if b = true then K.map (Int.cast : ℤ → ℚ) else H.map (Int.cast : ℤ → ℚ)) * z) 1 := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldr_cons]
    rw [← ih]
    have := (Int.castRingHom ℚ).mapMatrix.map_mul (if b then K else H) (l.foldr (fun (b : Bool) z => (if b = true then K else H) * z) 1)
    simp only [RingHom.mapMatrix_apply] at this
    refine this.trans ?_
    split_ifs <;> rfl

/-- moments agree on every element of the free algebra, given agreement on words. -/
lemma moments_free {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H K : Matrix V V ℤ) (H' K' : Matrix W W ℤ)
    (h : ∀ w : Word, (∑ i, ∑ j, wordEval H K w i j) = ∑ i, ∑ j, wordEval H' K' w i j)
    (b : FreeAlgebra ℚ Bool) :
    momL V (rhoAD (H.map (Int.cast : ℤ → ℚ)) (K.map (Int.cast : ℤ → ℚ)) b) =
      momL W (rhoAD (H'.map (Int.cast : ℤ → ℚ)) (K'.map (Int.cast : ℤ → ℚ)) b) := by
  let f : FreeAlgebra ℚ Bool →ₗ[ℚ] ℚ :=
    (momL V).comp (rhoAD (H.map (Int.cast : ℤ → ℚ)) (K.map (Int.cast : ℤ → ℚ))).toLinearMap -
    (momL W).comp (rhoAD (H'.map (Int.cast : ℤ → ℚ)) (K'.map (Int.cast : ℤ → ℚ))).toLinearMap
  have hker : Submodule.span ℚ (Set.range wordAlg) ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, f, LinearMap.sub_apply, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, sub_eq_zero]
    rw [rhoAD_wordAlg, rhoAD_wordAlg, ← foldr_map_int, ← foldr_map_int]
    have := h (FreeMonoid.ofList l)
    simp only [wordEval, FreeMonoid.toList_ofList] at this
    simp only [momL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.map_apply]
    exact_mod_cast this
  have : b ∈ LinearMap.ker f := hker (by rw [span_wordAlg]; trivial)
  simpa [f, sub_eq_zero] using this

end UniformADProbes.Trace.Dev.PMR
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UniformADProbes.Trace.Dev.PMR

open scoped Classical

section graphs

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma dg_eq_one_iff {v : V} : dg G v = 1 ↔ ∃! w : V, G.Adj v w :=
  SimpleGraph.degree_eq_one_iff_existsUnique_adj

/-- a set closed under adjacency contains everything reachable from it -/
lemma walk_closed {u v : V} (p : G.Walk u v) (S : Set V) (hS : ∀ a ∈ S, ∀ b, G.Adj a b → b ∈ S)
    (hu : u ∈ S) : v ∈ S := by
  induction p with
  | nil => exact hu
  | cons h p ih => exact ih (hS _ hu _ h)

lemma two_of_leaf_adj_leaf (hc : G.Connected) {a b : V} (ha : dg G a = 1) (hb : dg G b = 1)
    (hab : G.Adj a b) : Fintype.card V ≤ 2 := by
  obtain ⟨b', hb'1, hb'2⟩ := dg_eq_one_iff.1 ha
  obtain ⟨a', ha'1, ha'2⟩ := dg_eq_one_iff.1 hb
  have hS : ∀ x ∈ ({a, b} : Set V), ∀ y, G.Adj x y → y ∈ ({a, b} : Set V) := by
    rintro x (rfl | rfl) y hxy
    · have := hb'2 y hxy
      have := hb'2 b hab
      simp_all
    · have := ha'2 y hxy
      have := ha'2 a hab.symm
      simp_all
  have hall : ∀ x : V, x ∈ ({a, b} : Set V) := by
    intro x
    obtain ⟨p⟩ := hc.preconnected a x
    exact walk_closed p _ hS (by simp)
  calc Fintype.card V ≤ ({a, b} : Finset V).card := by
        apply Finset.card_le_card
        intro x _
        simpa using hall x
    _ ≤ 2 := Finset.card_le_two

lemma leaf_nbr_nonleaf (hc : G.Connected) (h3 : 3 ≤ Fintype.card V) {a b : V} (ha : dg G a = 1)
    (hab : G.Adj a b) : dg G b ≠ 1 := by
  intro hb
  have := two_of_leaf_adj_leaf hc ha hb hab
  omega

lemma leaf_unique_nbr {a b c : V} (ha : dg G a = 1) (hb : G.Adj a b) (hc : G.Adj a c) : b = c := by
  obtain ⟨w, _, hw⟩ := dg_eq_one_iff.1 ha
  rw [hw b hb, hw c hc]

lemma exists_leaf (hT : G.IsTree) (h2 : 2 ≤ Fintype.card V) : ∃ v, dg G v = 1 := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  exact hT.exists_vert_degree_one_of_nontrivial

/-- non-leaves -/
abbrev NL (G : SimpleGraph V) : Type := {v : V // dg G v ≠ 1}

noncomputable def pruneG (G : SimpleGraph V) : SimpleGraph (NL G) := G.comap Subtype.val

lemma NL_nonempty (hc : G.Connected) (h3 : 3 ≤ Fintype.card V) (hT : G.IsTree) :
    Nonempty (NL G) := by
  obtain ⟨a, ha⟩ := exists_leaf hT (by omega)
  obtain ⟨b, hb, _⟩ := dg_eq_one_iff.1 ha
  exact ⟨⟨b, leaf_nbr_nonleaf hc h3 ha hb⟩⟩

lemma prune_tree (hT : G.IsTree) (h3 : 3 ≤ Fintype.card V) : (pruneG G).IsTree := by
  have hne := NL_nonempty hT.connected h3 hT
  have hpre : (G.induce {v | dg G v ≠ 1}).Preconnected := by
    apply SimpleGraph.Preconnected.induce_of_degree_eq_one hT.connected.preconnected
    intro v hv
    have : dg G v = 1 := by simpa using hv
    obtain ⟨w, hw, hu⟩ := dg_eq_one_iff.1 this
    intro a ha b hb
    have h1 := hu a ha
    have h2 := hu b hb
    rw [h1, h2]
  haveI := hne
  refine ⟨⟨hpre⟩, ?_⟩
  exact hT.isAcyclic.induce _

lemma card_NL_lt (hT : G.IsTree) (h3 : 3 ≤ Fintype.card V) : Fintype.card (NL G) < Fintype.card V := by
  obtain ⟨a, ha⟩ := exists_leaf hT (by omega)
  have : ¬ Function.Surjective (Subtype.val : NL G → V) := by
    intro hs
    obtain ⟨x, hx⟩ := hs a
    exact x.2 (hx ▸ ha)
  exact Fintype.card_lt_of_injective_not_surjective _ Subtype.val_injective this

lemma adj_top_of_card_le_two (hc : G.Connected) (h2 : Fintype.card V ≤ 2) {u v : V} (huv : u ≠ v) :
    G.Adj u v := by
  obtain ⟨p⟩ := hc.preconnected u v
  cases p with
  | nil => exact absurd rfl huv
  | cons h q =>
    rename_i w
    by_cases hw : w = v
    · subst hw; exact h
    · exfalso
      have h3 : 3 ≤ Fintype.card V := by
        have hu : u ≠ w := h.ne
        have : ({u, v, w} : Finset V).card = 3 := by
          rw [Finset.card_eq_three]
          exact ⟨u, v, w, huv, hu, fun h' => hw h'.symm, rfl⟩
        calc 3 = ({u, v, w} : Finset V).card := this.symm
          _ ≤ Fintype.card V := Finset.card_le_univ _
      omega

end graphs

end UniformADProbes.Trace.Dev.PMR
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace UniformADProbes.Trace.Dev.PMR

open scoped Classical
open Polynomial

section alg

variable {κ : Type} [Fintype κ] [DecidableEq κ]

noncomputable def Ea (c : κ) : FreeAlgebra ℚ (Option κ) := FreeAlgebra.ι ℚ (some c)
noncomputable def Aa : FreeAlgebra ℚ (Option κ) := FreeAlgebra.ι ℚ none

noncomputable def Pa (δ : κ → ℕ) : FreeAlgebra ℚ (Option κ) :=
  ∑ c, if δ c = 1 then 0 else Ea c

noncomputable def Nt (δ : κ → ℕ) (c : κ) : FreeAlgebra ℚ (Option κ) :=
  if δ c = 1 then Pa δ * Aa * Ea c * Aa * Pa δ else 0

noncomputable def indPoly (N j : ℕ) : ℚ[X] :=
  ∏ i ∈ (Finset.range N).erase j, ((X - C (i : ℚ)) * C (1 / ((j : ℚ) - i)))

lemma eval_indPoly {N j k : ℕ} (hj : j < N) (hk : k < N) :
    (indPoly N j).eval (k : ℚ) = if k = j then 1 else 0 := by
  unfold indPoly
  rw [eval_prod]
  split_ifs with h
  · subst h
    apply Finset.prod_eq_one
    intro i hi
    have hne : i ≠ k := (Finset.mem_erase.1 hi).1
    have : (k : ℚ) - i ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hne.symm)
    simp [this]
  · apply Finset.prod_eq_zero (i := k)
    · exact Finset.mem_erase.2 ⟨h, Finset.mem_range.2 hk⟩
    · simp

/-- product of a finite family of algebra elements -/
noncomputable def Qa (δ : κ → ℕ) (N : ℕ) (m : κ → Fin N) : FreeAlgebra ℚ (Option κ) :=
  ((Finset.univ : Finset κ).toList.map fun c => Polynomial.aeval (Nt δ c) (indPoly N (m c))).prod

noncomputable def tauL (δ : κ → ℕ) (N : ℕ) : Option (κ × (κ → Fin N)) → FreeAlgebra ℚ (Option κ)
  | none => Pa δ * Aa * Pa δ
  | some (c, m) => Pa δ * Ea c * Qa δ N m * Pa δ

noncomputable def tau (δ : κ → ℕ) (N : ℕ) :
    FreeAlgebra ℚ (Option (κ × (κ → Fin N))) →ₐ[ℚ] FreeAlgebra ℚ (Option κ) :=
  FreeAlgebra.lift ℚ (tauL δ N)

end alg

section mat

variable {V : Type} [Fintype V] [DecidableEq V] {κ : Type} [Fintype κ] [DecidableEq κ]

/-- projection onto non-leaves -/
noncomputable def Pm (G : SimpleGraph V) : Matrix V V ℚ :=
  Matrix.diagonal fun v => if dg G v = 1 then 0 else 1

/-- number of leaf neighbours of colour `c` -/
noncomputable def lcount (G : SimpleGraph V) (col : V → κ) (δ : κ → ℕ) (c : κ) (v : V) : ℕ :=
  (Finset.univ.filter fun ℓ => G.Adj v ℓ ∧ col ℓ = c ∧ δ c = 1).card

/-- the diagonal of the leaf count matrix -/
noncomputable def ndiag (G : SimpleGraph V) (col : V → κ) (δ : κ → ℕ) (c : κ) (v : V) : ℚ :=
  if dg G v = 1 then 0 else (lcount G col δ c v : ℚ)

variable (G : SimpleGraph V) (col : V → κ) (δ : κ → ℕ) (hd : ∀ v, dg G v = δ (col v))
include hd

lemma rho_Ea (c : κ) : rho G col (Ea c) = indE col c := by
  simp [Ea, rho, letterMat]

lemma rho_Aa : rho G col (Aa : FreeAlgebra ℚ (Option κ)) = adjQ G := by
  simp [Aa, rho, letterMat]

lemma rho_Pa : rho G col (Pa δ) = Pm G := by
  unfold Pa Pm
  rw [map_sum]
  have : ∀ c : κ, rho G col (if δ c = 1 then 0 else Ea c) = if δ c = 1 then 0 else indE col c := by
    intro c
    split_ifs <;> simp [rho_Ea G col δ hd]
  simp_rw [this]
  ext x y
  have h2 : ∀ c : κ, (if δ c = 1 then (0 : Matrix V V ℚ) else indE col c) x y =
      if δ c = 1 then 0 else (if x = y then (if col x = c then 1 else 0) else 0) := by
    intro c
    split_ifs <;> simp_all [indE, Matrix.diagonal_apply]
  simp only [Matrix.sum_apply, h2, Pm, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [Finset.sum_eq_single (col x)]
    · simp [hd x]
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · simp [hxy]

lemma sum_leaf_path (c : κ) (hc : δ c = 1) (x y : V) :
    (∑ z, adjQ G x z * (if col z = c then (1 : ℚ) else 0) * adjQ G z y) =
      if x = y then (lcount G col δ c x : ℚ) else 0 := by
  by_cases hxy : x = y
  · subst hxy
    simp only [if_true, lcount, adjQ]
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro z _
    by_cases h1 : G.Adj x z <;> by_cases h2 : col z = c <;> simp [h1, h2, hc, G.adj_comm z x]
  · simp only [hxy, if_false]
    apply Finset.sum_eq_zero
    intro z _
    by_cases h1 : G.Adj x z
    · by_cases h2 : col z = c
      · by_cases h3 : G.Adj z y
        · exfalso
          have hz : dg G z = 1 := by rw [hd z, h2, hc]
          exact hxy (leaf_unique_nbr hz h1.symm h3)
        · simp [adjQ, h3]
      · simp [h2]
    · simp [adjQ, h1]

lemma rho_Nt (c : κ) :
    rho G col (Nt δ c) = Matrix.diagonal fun v => if dg G v = 1 then 0 else (lcount G col δ c v : ℚ) := by
  unfold Nt
  by_cases hc : δ c = 1
  · simp only [hc, if_true]
    simp only [map_mul, rho_Pa G col δ hd, rho_Aa G col δ hd, rho_Ea G col δ hd]
    ext x y
    have : Pm G * adjQ G * indE col c * adjQ G * Pm G = Pm G * (adjQ G * indE col c * adjQ G) * Pm G := by
      simp only [mul_assoc]
    rw [this, Pm, Matrix.mul_diagonal, Matrix.diagonal_mul]
    have hmid : (adjQ G * indE col c * adjQ G) x y =
        ∑ z, adjQ G x z * (if col z = c then (1 : ℚ) else 0) * adjQ G z y := by
      simp [Matrix.mul_apply, indE, Matrix.mul_diagonal, Matrix.diagonal_apply]
    rw [hmid, sum_leaf_path G col δ hd c hc x y]
    by_cases hxy : x = y
    · subst hxy
      by_cases hx : dg G x = 1 <;> simp [hx]
    · simp [hxy]
  · simp [hc, lcount]

omit hd in
lemma aeval_diagonal (d : V → ℚ) (p : ℚ[X]) :
    Polynomial.aeval (Matrix.diagonal d) p = Matrix.diagonal (fun v => p.eval (d v)) := by
  have h1 : Matrix.diagonal d = Matrix.diagonalAlgHom ℚ d := rfl
  rw [h1, Polynomial.aeval_algHom_apply, Polynomial.aeval_pi_apply]
  rfl

omit hd in
lemma diagAlg_list_prod (l : List κ) (g : κ → V → ℚ) :
    (l.map fun c => Matrix.diagonalAlgHom ℚ (g c)).prod =
      Matrix.diagonalAlgHom ℚ (fun v => (l.map fun c => g c v).prod) := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    rw [show (fun v : V => (1 : ℚ)) = 1 from rfl, map_one]
  | cons c l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih, ← map_mul]
    rfl

lemma rho_Qa (N : ℕ) (m : κ → Fin N) :
    rho G col (Qa δ N m) = Matrix.diagonal fun v =>
      ((Finset.univ : Finset κ).toList.map fun c => (indPoly N (m c)).eval (ndiag G col δ c v)).prod := by
  unfold Qa
  rw [map_list_prod (rho G col), List.map_map]
  have : ∀ c : κ, (rho G col) (Polynomial.aeval (Nt δ c) (indPoly N (m c))) =
      Matrix.diagonalAlgHom ℚ (fun v => (indPoly N (m c)).eval (ndiag G col δ c v)) := by
    intro c
    have key := Polynomial.aeval_algHom_apply (rho G col) (Nt δ c) (indPoly N (m c))
    rw [← key, rho_Nt G col δ hd c, aeval_diagonal]
    rfl
  have h2 : (rho G col) ∘ (fun c => Polynomial.aeval (Nt δ c) (indPoly N (m c))) =
      fun c => Matrix.diagonalAlgHom ℚ (fun v => (indPoly N (m c)).eval (ndiag G col δ c v)) := by
    funext c
    exact this c
  rw [h2, diagAlg_list_prod]
  rfl

lemma Qval_eq (N : ℕ) (m : κ → Fin N) (hN : ∀ c v, lcount G col δ c v < N) (v : V)
    (hv : dg G v ≠ 1) :
    ((Finset.univ : Finset κ).toList.map fun c => (indPoly N (m c)).eval (ndiag G col δ c v)).prod =
      if ∀ c, lcount G col δ c v = (m c : ℕ) then 1 else 0 := by
  rw [Finset.prod_map_toList]
  have : ∀ c ∈ (Finset.univ : Finset κ), (indPoly N (m c)).eval (ndiag G col δ c v) =
      if lcount G col δ c v = (m c : ℕ) then 1 else 0 := by
    intro c _
    have h1 : ndiag G col δ c v = ((lcount G col δ c v : ℕ) : ℚ) := by simp [ndiag, hv]
    rw [h1, eval_indPoly (m c).2 (hN c v)]
  rw [Finset.prod_congr rfl this, Finset.prod_boole]
  simp

end mat

section restr

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- restriction of a matrix to the non-leaves -/
def rst (X : Matrix V V ℚ) : Matrix (NL G) (NL G) ℚ := fun x y => X x.1 y.1

lemma rst_add (X Y : Matrix V V ℚ) : rst G (X + Y) = rst G X + rst G Y := by
  ext x y; simp [rst]

lemma rst_smul (r : ℚ) (X : Matrix V V ℚ) : rst G (r • X) = r • rst G X := by
  ext x y; simp [rst]

lemma sum_NL (f : V → ℚ) (hf : ∀ z, dg G z = 1 → f z = 0) :
    ∑ z : NL G, f z.1 = ∑ z, f z := by
  calc ∑ z : NL G, f z.1 = ∑ x ∈ (Finset.univ : Finset V).subtype (fun z => dg G z ≠ 1), f x := by
        rw [Finset.subtype_univ]
    _ = ∑ x ∈ Finset.univ.filter (fun z => dg G z ≠ 1), f x := Finset.sum_subtype_eq_sum_filter f
    _ = ∑ x, f x := Finset.sum_filter_of_ne (fun x _ hx => by
          by_contra h
          exact hx (hf x (by simpa using h)))

lemma Pm_mul_self : Pm G * Pm G = Pm G := by
  simp only [Pm, Matrix.diagonal_mul_diagonal]
  congr 1
  funext v
  split_ifs <;> simp

lemma Pm_entry (z : V) : (Pm G) z z = if dg G z = 1 then 0 else 1 := by
  simp [Pm]

lemma rst_mul (X Y : Matrix V V ℚ) (hX : X * Pm G = X) : rst G (X * Y) = rst G X * rst G Y := by
  ext x y
  simp only [rst, Matrix.mul_apply]
  rw [sum_NL G (fun z => X x.1 z * Y z y.1)]
  intro z hz
  have : X x.1 z = X x.1 z * (Pm G) z z := by
    conv_lhs => rw [← hX]
    simp [Pm, Matrix.mul_diagonal]
  rw [this, Pm_entry, if_pos hz]
  simp

lemma rst_Pm : rst G (Pm G) = 1 := by
  ext x y
  simp only [rst, Pm, Matrix.diagonal_apply, Matrix.one_apply, Subtype.ext_iff]
  by_cases h1 : x.1 = y.1
  · have hy : dg G y.1 ≠ 1 := y.2
    simp [h1, hy]
  · simp [h1]

lemma mom_rst (X : Matrix V V ℚ) (h1 : Pm G * X = X) (h2 : X * Pm G = X) :
    momL (NL G) (rst G X) = momL V X := by
  simp only [momL, LinearMap.coe_mk, AddHom.coe_mk, rst]
  rw [sum_NL G (fun x => ∑ y : NL G, X x y.1)]
  · apply Finset.sum_congr rfl
    intro x _
    apply sum_NL G (fun y => X x y)
    intro z hz
    have : X x z = X x z * (Pm G) z z := by
      conv_lhs => rw [← h2]
      simp [Pm, Matrix.mul_diagonal]
    rw [this, Pm_entry, if_pos hz]
    simp
  · intro z hz
    apply Finset.sum_eq_zero
    intro y _
    have : X z y = (Pm G) z z * X z y := by
      conv_lhs => rw [← h1]
      simp [Pm, Matrix.diagonal_mul]
    rw [this, Pm_entry, if_pos hz]
    simp

end restr

section prune

variable {V : Type} [Fintype V] [DecidableEq V] {κ : Type} [Fintype κ] [DecidableEq κ]
  (G : SimpleGraph V) (col : V → κ) (δ : κ → ℕ) (n : ℕ)

/-- colour of a non-leaf in the pruned tree: old colour and leaf counts -/
noncomputable def newCol (x : NL G) : κ × (κ → Fin (n + 1)) :=
  (col x.1, fun c => Fin.ofNat (n + 1) (lcount G col δ c x.1))

lemma rho_iota {W : Type} [Fintype W] [DecidableEq W] {ι : Type} [DecidableEq ι]
    (H : SimpleGraph W) (c : W → ι) (o : Option ι) :
    rho H c (FreeAlgebra.ι ℚ o) = letterMat H c o := by
  simp [rho]

lemma tau_iota (o : Option (κ × (κ → Fin (n + 1)))) :
    tau δ (n + 1) (FreeAlgebra.ι ℚ o) = tauL δ (n + 1) o := by
  simp [tau]

variable (hd : ∀ v, dg G v = δ (col v))
include hd

lemma rho_tauL_none :
    rho G col (tauL δ (n + 1) none) = Pm G * adjQ G * Pm G := by
  simp [tauL, rho_Pa G col δ hd, rho_Aa G col δ hd]

lemma rho_tauL_some (c : κ) (m : κ → Fin (n + 1)) :
    rho G col (tauL δ (n + 1) (some (c, m))) =
      Pm G * indE col c * rho G col (Qa δ (n + 1) m) * Pm G := by
  simp [tauL, rho_Pa G col δ hd, rho_Ea G col δ hd, mul_assoc]

omit hd in
lemma Pm_comm_corner (Y : Matrix V V ℚ) : Pm G * (Pm G * Y * Pm G) = (Pm G * Y * Pm G) * Pm G := by
  have h1 : Pm G * (Pm G * Y * Pm G) = Pm G * Y * Pm G := by
    rw [← mul_assoc, ← mul_assoc, Pm_mul_self]
  have h2 : (Pm G * Y * Pm G) * Pm G = Pm G * Y * Pm G := by
    rw [mul_assoc, Pm_mul_self]
  rw [h1, h2]

lemma comm_tau (a : FreeAlgebra ℚ (Option (κ × (κ → Fin (n + 1))))) :
    Pm G * rho G col (tau δ (n + 1) a) = rho G col (tau δ (n + 1) a) * Pm G := by
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    simp only [AlgHom.commutes]
    exact (Algebra.commutes r (Pm G)).symm
  | grade1 o =>
    rw [tau_iota]
    cases o with
    | none => rw [rho_tauL_none G col δ n hd]; exact Pm_comm_corner G _
    | some cm =>
      obtain ⟨c, m⟩ := cm
      rw [rho_tauL_some G col δ n hd]
      have := Pm_comm_corner G (indE col c * rho G col (Qa δ (n + 1) m))
      simp only [mul_assoc] at this ⊢
      exact this
  | add x y hx hy => simp [mul_add, add_mul, hx, hy]
  | mul x y hx hy =>
    rw [map_mul, map_mul, ← mul_assoc, hx, mul_assoc, hy, mul_assoc]

lemma Pm_one (x : NL G) : (if dg G x.1 = 1 then (0 : ℚ) else 1) = 1 := by
  have := x.2
  simp [this]

omit hd in
lemma newCol_eq_iff (hN : ∀ c v, lcount G col δ c v < n + 1) (x : NL G) (c : κ)
    (m : κ → Fin (n + 1)) :
    newCol G col δ n x = (c, m) ↔ col x.1 = c ∧ ∀ c', lcount G col δ c' x.1 = (m c' : ℕ) := by
  simp only [newCol, Prod.mk.injEq, funext_iff, Fin.ext_iff, Fin.val_ofNat]
  refine and_congr Iff.rfl (forall_congr' fun c' => ?_)
  rw [Nat.mod_eq_of_lt (hN c' x.1)]

lemma rst_tau (hN : ∀ c v, lcount G col δ c v < n + 1) (a : FreeAlgebra ℚ (Option (κ × (κ → Fin (n + 1))))) :
    rst G (rho G col (tau δ (n + 1) a) * Pm G) = rho (pruneG G) (newCol G col δ n) a := by
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    have h1 : rho G col (tau δ (n + 1) (algebraMap ℚ _ r)) = algebraMap ℚ (Matrix V V ℚ) r := by
      rw [AlgHom.commutes, AlgHom.commutes]
    rw [h1, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, rst_smul, rst_Pm]
  | grade1 o =>
    rw [tau_iota, rho_iota]
    cases o with
    | none =>
      rw [rho_tauL_none G col δ n hd]
      have : Pm G * adjQ G * Pm G * Pm G = Pm G * adjQ G * Pm G := by
        rw [mul_assoc, Pm_mul_self]
      rw [this]
      ext x y
      simp only [rst, Pm, Matrix.mul_diagonal, Matrix.diagonal_mul, Pm_one, letterMat, adjQ,
        pruneG, SimpleGraph.comap_adj]
      simp [x.2, y.2]
    | some cm =>
      obtain ⟨c, m⟩ := cm
      rw [rho_tauL_some G col δ n hd, rho_Qa G col δ hd]
      have : Pm G * indE col c * (Matrix.diagonal fun v =>
          ((Finset.univ : Finset κ).toList.map fun c' =>
            (indPoly (n + 1) (m c')).eval (ndiag G col δ c' v)).prod) * Pm G * Pm G =
          Matrix.diagonal (fun v => (if dg G v = 1 then (0 : ℚ) else 1) * (if col v = c then 1 else 0) *
            ((Finset.univ : Finset κ).toList.map fun c' =>
            (indPoly (n + 1) (m c')).eval (ndiag G col δ c' v)).prod *
            (if dg G v = 1 then (0 : ℚ) else 1) * (if dg G v = 1 then (0 : ℚ) else 1)) := by
        simp only [Pm, indE, Matrix.diagonal_mul_diagonal]
      rw [this]
      ext x y
      simp only [rst, letterMat, indE, Matrix.diagonal_apply]
      by_cases hxy : x.1 = y.1
      · have hxy' : x = y := Subtype.ext hxy
        subst hxy'
        have hx : dg G x.1 ≠ 1 := x.2
        simp only [hx, if_false, if_true, one_mul, mul_one, Qval_eq G col δ hd (n + 1) m hN x.1 hx]
        by_cases h1 : col x.1 = c <;> by_cases h2 : ∀ c', lcount G col δ c' x.1 = (m c' : ℕ) <;>
          simp [(newCol_eq_iff G col δ n hN x c m), h1, h2]
      · have : x ≠ y := fun h => hxy (congrArg Subtype.val h)
        simp [hxy, this]
  | add x y hx hy => rw [map_add, map_add, add_mul, rst_add, hx, hy, map_add]
  | mul x y hx hy =>
    have hc := comm_tau G col δ n hd y
    have e : rho G col (tau δ (n + 1) (x * y)) * Pm G =
        (rho G col (tau δ (n + 1) x) * Pm G) * (rho G col (tau δ (n + 1) y) * Pm G) := by
      have h2 : Pm G * (rho G col (tau δ (n + 1) y) * Pm G) =
          rho G col (tau δ (n + 1) y) * (Pm G * Pm G) := by
        rw [← mul_assoc, hc, mul_assoc]
      simp only [map_mul]
      calc _ = rho G col (tau δ (n + 1) x) * (rho G col (tau δ (n + 1) y) * (Pm G * Pm G)) := by
            rw [Pm_mul_self, mul_assoc]
        _ = rho G col (tau δ (n + 1) x) * (Pm G * (rho G col (tau δ (n + 1) y) * Pm G)) := by
            rw [h2]
        _ = _ := by simp only [mul_assoc]
    rw [e, rst_mul G _ _ (by rw [mul_assoc, Pm_mul_self]), hx, hy, map_mul]

lemma phi_prune (hN : ∀ c v, lcount G col δ c v < n + 1)
    (a : FreeAlgebra ℚ (Option (κ × (κ → Fin (n + 1))))) :
    phi (pruneG G) (newCol G col δ n) a =
      phi G col (Pa δ * tau δ (n + 1) a * Pa δ) := by
  have hc := comm_tau G col δ n hd a
  have h1 : Pm G * (rho G col (tau δ (n + 1) a) * Pm G) = rho G col (tau δ (n + 1) a) * Pm G := by
    rw [← mul_assoc, hc, mul_assoc, Pm_mul_self]
  have h2 : rho G col (tau δ (n + 1) a) * Pm G * Pm G = rho G col (tau δ (n + 1) a) * Pm G := by
    rw [mul_assoc, Pm_mul_self]
  have h3 : rho G col (Pa δ * tau δ (n + 1) a * Pa δ) = rho G col (tau δ (n + 1) a) * Pm G := by
    rw [map_mul, map_mul, rho_Pa G col δ hd, hc, mul_assoc, Pm_mul_self]
  unfold phi
  rw [← rst_tau G col δ n hd hN a, mom_rst G _ h1 h2, h3]

end prune

section degs

variable {V : Type} [Fintype V] [DecidableEq V] {κ : Type} [Fintype κ] [DecidableEq κ]
  (G : SimpleGraph V) (col : V → κ) (δ : κ → ℕ)

lemma dg_eq_card (v : V) : dg G v = (Finset.univ.filter fun w => G.Adj v w).card := by
  unfold dg
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp

lemma dg_prune (x : NL G) :
    dg (pruneG G) x = (Finset.univ.filter fun w => G.Adj x.1 w ∧ dg G w ≠ 1).card := by
  rw [dg_eq_card]
  apply Finset.card_bij (fun (w : NL G) _ => w.1)
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact ⟨hw, w.2⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact ⟨⟨w, hw.2⟩, by simpa [pruneG] using hw.1, rfl⟩

lemma lcount_sum (hd : ∀ v, dg G v = δ (col v)) (v : V) :
    ∑ c, lcount G col δ c v = (Finset.univ.filter fun w => G.Adj v w ∧ dg G w = 1).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := col) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro c _
  unfold lcount
  congr 1
  ext ℓ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h3, h2⟩
    exact ⟨⟨h1, by rw [hd ℓ, h3, h2]⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h3, by rw [← h3, ← hd ℓ, h2]⟩

lemma dg_split (v : V) :
    dg G v = (Finset.univ.filter fun w => G.Adj v w ∧ dg G w ≠ 1).card +
      (Finset.univ.filter fun w => G.Adj v w ∧ dg G w = 1).card := by
  rw [dg_eq_card, ← Finset.card_union_of_disjoint]
  · congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    tauto
  · rw [Finset.disjoint_filter]
    intro w _ h1 h2
    exact h1.2 h2.2

/-- degree after pruning, as a function of the new colour -/
def delta' (δ : κ → ℕ) (n : ℕ) (p : κ × (κ → Fin (n + 1))) : ℕ := δ p.1 - ∑ c, (p.2 c : ℕ)

lemma dg_prune_newCol (n : ℕ) (hd : ∀ v, dg G v = δ (col v))
    (hN : ∀ c v, lcount G col δ c v < n + 1) (x : NL G) :
    dg (pruneG G) x = delta' δ n (newCol G col δ n x) := by
  have h1 := dg_split G x.1
  have h2 := lcount_sum G col δ hd x.1
  have h3 : ∑ c, ((newCol G col δ n x).2 c : ℕ) = ∑ c, lcount G col δ c x.1 := by
    apply Finset.sum_congr rfl
    intro c _
    simp only [newCol, Fin.val_ofNat]
    exact Nat.mod_eq_of_lt (hN c x.1)
  rw [dg_prune, delta', h3, h2]
  have : δ (newCol G col δ n x).1 = dg G x.1 := by simp [newCol, hd]
  rw [this]
  omega

lemma lcount_le (c : κ) (v : V) : lcount G col δ c v ≤ Fintype.card V := by
  unfold lcount
  exact Finset.card_le_univ _

end degs

end UniformADProbes.Trace.Dev.PMR
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace UniformADProbes.Trace.Dev.PMR

open scoped Classical

section lift

variable {V : Type} [Fintype V] [DecidableEq V] {κ : Type} [Fintype κ] [DecidableEq κ]

/-- the leaves -/
abbrev LF (G : SimpleGraph V) : Type := {v : V // dg G v = 1}

section par

variable {G : SimpleGraph V} (hT : G.IsTree) (h3 : 3 ≤ Fintype.card V)
include hT h3

lemma leaf_nbr_ex (ℓ : LF G) : ∃ x : NL G, G.Adj ℓ.1 x.1 ∧ ∀ w, G.Adj ℓ.1 w → w = x.1 := by
  obtain ⟨w, hw, hu⟩ := dg_eq_one_iff.1 ℓ.2
  exact ⟨⟨w, leaf_nbr_nonleaf hT.connected h3 ℓ.2 hw⟩, hw, hu⟩

/-- the unique neighbour of a leaf -/
noncomputable def par (ℓ : LF G) : NL G := Classical.choose (leaf_nbr_ex hT h3 ℓ)

lemma par_adj (ℓ : LF G) : G.Adj ℓ.1 (par hT h3 ℓ).1 :=
  (Classical.choose_spec (leaf_nbr_ex hT h3 ℓ)).1

lemma par_eq (ℓ : LF G) (x : NL G) (h : G.Adj ℓ.1 x.1) : par hT h3 ℓ = x :=
  Subtype.ext ((Classical.choose_spec (leaf_nbr_ex hT h3 ℓ)).2 _ h).symm.symm |>.symm

variable (col : V → κ) (δ : κ → ℕ) (hd : ∀ v, dg G v = δ (col v))
include hd

lemma card_fibre (x : NL G) (c : κ) :
    Fintype.card {ℓ : LF G // par hT h3 ℓ = x ∧ col ℓ.1 = c} = lcount G col δ c x.1 := by
  rw [Fintype.card_subtype, lcount]
  apply Finset.card_bij (fun (ℓ : LF G) _ => ℓ.1)
  · intro ℓ hℓ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hℓ ⊢
    obtain ⟨h1, h2⟩ := hℓ
    refine ⟨?_, h2, ?_⟩
    · have := par_adj hT h3 ℓ
      rw [h1] at this
      exact this.symm
    · have := ℓ.2
      rw [hd ℓ.1, h2] at this
      exact this
  · intro a _ b _ h
    exact Subtype.ext h
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨h1, h2, h3'⟩ := hw
    have hl : dg G w = 1 := by rw [hd w, h2, h3']
    refine ⟨⟨w, hl⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨par_eq hT h3 ⟨w, hl⟩ x h1.symm, h2⟩


omit hd in
lemma adj_leaf_iff (ℓ : LF G) (x : NL G) : G.Adj ℓ.1 x.1 ↔ par hT h3 ℓ = x := by
  constructor
  · exact par_eq hT h3 ℓ x
  · intro h
    have := par_adj hT h3 ℓ
    rwa [h] at this

end par

theorem lift_iso {V₂ : Type} [Fintype V₂] [DecidableEq V₂]
    (G : SimpleGraph V) (G₂ : SimpleGraph V₂) (hT : G.IsTree) (hT₂ : G₂.IsTree)
    (h3 : 3 ≤ Fintype.card V) (h3₂ : 3 ≤ Fintype.card V₂)
    (col : V → κ) (col₂ : V₂ → κ) (δ : κ → ℕ)
    (hd : ∀ v, dg G v = δ (col v)) (hd₂ : ∀ v, dg G₂ v = δ (col₂ v)) (n : ℕ)
    (hN : ∀ c v, lcount G col δ c v < n + 1) (hN₂ : ∀ c v, lcount G₂ col₂ δ c v < n + 1)
    (f : pruneG G ≃g pruneG G₂) (hf : ∀ x, newCol G₂ col₂ δ n (f x) = newCol G col δ n x) :
    ∃ F : G ≃g G₂, ∀ v, col₂ (F v) = col v := by
  have hcol : ∀ x : NL G, col₂ (f x).1 = col x.1 := fun x => congrArg Prod.fst (hf x)
  have hcnt : ∀ (x : NL G) (c : κ), lcount G₂ col₂ δ c (f x).1 = lcount G col δ c x.1 := by
    intro x c
    have := congrFun (congrArg Prod.snd (hf x)) c
    simp only [newCol, Fin.ext_iff, Fin.val_ofNat] at this
    rwa [Nat.mod_eq_of_lt (hN₂ c _), Nat.mod_eq_of_lt (hN c _)] at this
  let φ : LF G → NL G × κ := fun ℓ => (par hT h3 ℓ, col ℓ.1)
  let φ₂ : LF G₂ → NL G × κ := fun ℓ => (f.symm (par hT₂ h3₂ ℓ), col₂ ℓ.1)
  have hcard : ∀ q : NL G × κ, Fintype.card {ℓ // φ ℓ = q} = Fintype.card {ℓ // φ₂ ℓ = q} := by
    intro q
    obtain ⟨x, c⟩ := q
    have e1 : Fintype.card {ℓ // φ ℓ = (x, c)} = lcount G col δ c x.1 := by
      rw [← card_fibre hT h3 col δ hd x c]
      exact Fintype.card_congr (Equiv.subtypeEquivRight (fun ℓ => by simp [φ, Prod.ext_iff]))
    have e2 : Fintype.card {ℓ // φ₂ ℓ = (x, c)} = lcount G₂ col₂ δ c (f x).1 := by
      rw [← card_fibre hT₂ h3₂ col₂ δ hd₂ (f x) c]
      refine Fintype.card_congr (Equiv.subtypeEquivRight (fun ℓ => ?_))
      simp only [φ₂, Prod.ext_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rw [← h1]; simp
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rw [h1]; simp
    rw [e1, e2, hcnt]
  let E : LF G ≃ LF G₂ := Equiv.ofFiberEquiv (f := φ) (g := φ₂) fun q => Fintype.equivOfCardEq (hcard q)
  have hE : ∀ ℓ, φ₂ (E ℓ) = φ ℓ := fun ℓ => Equiv.ofFiberEquiv_map _ ℓ
  have hEpar : ∀ ℓ, par hT₂ h3₂ (E ℓ) = f (par hT h3 ℓ) := by
    intro ℓ
    have := congrArg Prod.fst (hE ℓ)
    simp only [φ, φ₂] at this
    rw [← this]
    simp
  have hEcol : ∀ ℓ, col₂ (E ℓ).1 = col ℓ.1 := fun ℓ => congrArg Prod.snd (hE ℓ)
  let F : V → V₂ := fun v => if h : dg G v = 1 then (E ⟨v, h⟩).1 else (f ⟨v, h⟩).1
  let F' : V₂ → V := fun w => if h : dg G₂ w = 1 then (E.symm ⟨w, h⟩).1 else (f.symm ⟨w, h⟩).1
  have hFl : ∀ v (h : dg G v = 1), F v = (E ⟨v, h⟩).1 := fun v h => by simp [F, h]
  have hFn : ∀ v (h : ¬ dg G v = 1), F v = (f ⟨v, h⟩).1 := fun v h => by simp [F, h]
  have hF'l : ∀ w (h : dg G₂ w = 1), F' w = (E.symm ⟨w, h⟩).1 := fun w h => by simp [F', h]
  have hF'n : ∀ w (h : ¬ dg G₂ w = 1), F' w = (f.symm ⟨w, h⟩).1 := fun w h => by simp [F', h]
  have hleft : ∀ v, F' (F v) = v := by
    intro v
    by_cases h : dg G v = 1
    · have hl : dg G₂ (E ⟨v, h⟩).1 = 1 := (E ⟨v, h⟩).2
      rw [hFl v h, hF'l _ hl]
      have : (⟨(E ⟨v, h⟩).1, hl⟩ : LF G₂) = E ⟨v, h⟩ := rfl
      rw [this, E.symm_apply_apply]
    · have hl : ¬ dg G₂ (f ⟨v, h⟩).1 = 1 := (f ⟨v, h⟩).2
      rw [hFn v h, hF'n _ hl]
      have : (⟨(f ⟨v, h⟩).1, hl⟩ : NL G₂) = f ⟨v, h⟩ := rfl
      rw [this, f.symm_apply_apply]
  have hright : ∀ w, F (F' w) = w := by
    intro w
    by_cases h : dg G₂ w = 1
    · have hl : dg G (E.symm ⟨w, h⟩).1 = 1 := (E.symm ⟨w, h⟩).2
      rw [hF'l w h, hFl _ hl]
      have : (⟨(E.symm ⟨w, h⟩).1, hl⟩ : LF G) = E.symm ⟨w, h⟩ := rfl
      rw [this, E.apply_symm_apply]
    · have hl : ¬ dg G (f.symm ⟨w, h⟩).1 = 1 := (f.symm ⟨w, h⟩).2
      rw [hF'n w h, hFn _ hl]
      have : (⟨(f.symm ⟨w, h⟩).1, hl⟩ : NL G) = f.symm ⟨w, h⟩ := rfl
      rw [this, f.apply_symm_apply]
  have hadj : ∀ v w, G₂.Adj (F v) (F w) ↔ G.Adj v w := by
    intro v w
    by_cases hv : dg G v = 1 <;> by_cases hw : dg G w = 1
    · have h1 : ¬ G.Adj v w := fun h => leaf_nbr_nonleaf hT.connected h3 hv h hw
      have h2 : ¬ G₂.Adj (F v) (F w) := by
        rw [hFl v hv, hFl w hw]
        intro h
        exact leaf_nbr_nonleaf hT₂.connected h3₂ (E ⟨v, hv⟩).2 h (E ⟨w, hw⟩).2
      simp [h1, h2]
    · rw [hFl v hv, hFn w hw, adj_leaf_iff hT₂ h3₂ (E ⟨v, hv⟩) (f ⟨w, hw⟩), hEpar,
        adj_leaf_iff hT h3 ⟨v, hv⟩ ⟨w, hw⟩]
      exact f.injective.eq_iff
    · rw [hFn v hv, hFl w hw, SimpleGraph.adj_comm, SimpleGraph.adj_comm G v w,
        adj_leaf_iff hT₂ h3₂ (E ⟨w, hw⟩) (f ⟨v, hv⟩), hEpar,
        adj_leaf_iff hT h3 ⟨w, hw⟩ ⟨v, hv⟩]
      exact f.injective.eq_iff
    · rw [hFn v hv, hFn w hw]
      show (pruneG G₂).Adj (f ⟨v, hv⟩) (f ⟨w, hw⟩) ↔ (pruneG G).Adj ⟨v, hv⟩ ⟨w, hw⟩
      exact f.map_rel_iff
  refine ⟨⟨⟨F, F', hleft, hright⟩, fun {v w} => hadj v w⟩, ?_⟩
  intro v
  show col₂ (F v) = col v
  by_cases h : dg G v = 1
  · rw [hFl v h, hEcol]
  · rw [hFn v h, hcol]

end lift

end UniformADProbes.Trace.Dev.PMR
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace UniformADProbes.Trace.Dev.PMR

open scoped Classical

section general

variable {V : Type} [Fintype V] [DecidableEq V] {κ : Type} [Fintype κ] [DecidableEq κ]

lemma phi_one (G : SimpleGraph V) (col : V → κ) : phi G col 1 = (Fintype.card V : ℚ) := by
  simp [phi, momL, Matrix.one_apply]

lemma phi_Ea (G : SimpleGraph V) (col : V → κ) (c : κ) :
    phi G col (Ea c) = (Fintype.card {v // col v = c} : ℚ) := by
  have : rho G col (Ea c) = indE col c := by simp [Ea, rho, letterMat]
  rw [Fintype.card_subtype]
  simp only [phi, this, momL, LinearMap.coe_mk, AddHom.coe_mk, indE, Matrix.diagonal_apply]
  simp [Finset.sum_boole]

end general

theorem general (n : ℕ) :
    ∀ {V V₂ : Type} [Fintype V] [DecidableEq V] [Fintype V₂] [DecidableEq V₂]
      {κ : Type} [Fintype κ] [DecidableEq κ] (δ : κ → ℕ)
      (G : SimpleGraph V) (G₂ : SimpleGraph V₂) (_hT : G.IsTree) (_hT₂ : G₂.IsTree)
      (col : V → κ) (col₂ : V₂ → κ)
      (_hd : ∀ v, dg G v = δ (col v)) (_hd₂ : ∀ v, dg G₂ v = δ (col₂ v)),
      Fintype.card V = n → (∀ a, phi G col a = phi G₂ col₂ a) →
      ∃ F : G ≃g G₂, ∀ v, col₂ (F v) = col v := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V V₂ _ _ _ _ κ _ _ δ G G₂ hT hT₂ col col₂ hd hd₂ hn hφ
  have hcard : Fintype.card V₂ = n := by
    have := hφ 1
    rw [phi_one, phi_one] at this
    have h : Fintype.card V = Fintype.card V₂ := by exact_mod_cast this
    omega
  by_cases h3 : 3 ≤ n
  · -- pruning step
    have h3V : 3 ≤ Fintype.card V := by omega
    have h3V₂ : 3 ≤ Fintype.card V₂ := by omega
    have hN : ∀ c v, lcount G col δ c v < n + 1 := fun c v => by
      have := lcount_le G col δ c v; omega
    have hN₂ : ∀ c v, lcount G₂ col₂ δ c v < n + 1 := fun c v => by
      have := lcount_le G₂ col₂ δ c v; omega
    have hlt : Fintype.card (NL G) < n := hn ▸ card_NL_lt hT h3V
    have hφ' : ∀ a, phi (pruneG G) (newCol G col δ n) a =
        phi (pruneG G₂) (newCol G₂ col₂ δ n) a := by
      intro a
      rw [phi_prune G col δ n hd hN, phi_prune G₂ col₂ δ n hd₂ hN₂]
      exact hφ _
    obtain ⟨f, hf⟩ := ih _ hlt (delta' δ n) (pruneG G) (pruneG G₂) (prune_tree hT h3V)
      (prune_tree hT₂ h3V₂) (newCol G col δ n) (newCol G₂ col₂ δ n)
      (fun x => dg_prune_newCol G col δ n hd hN x) (fun x => dg_prune_newCol G₂ col₂ δ n hd₂ hN₂ x)
      rfl hφ'
    exact lift_iso G G₂ hT hT₂ h3V h3V₂ col col₂ δ hd hd₂ n hN hN₂ f hf
  · -- small case
    have h2 : Fintype.card V ≤ 2 := by omega
    have h2' : Fintype.card V₂ ≤ 2 := by omega
    have hc : ∀ c, Fintype.card {v // col v = c} = Fintype.card {w // col₂ w = c} := by
      intro c
      have := hφ (Ea c)
      rw [phi_Ea, phi_Ea] at this
      exact_mod_cast this
    let e : V ≃ V₂ := Equiv.ofFiberEquiv (f := col) (g := col₂) fun c => Fintype.equivOfCardEq (hc c)
    have he : ∀ v, col₂ (e v) = col v := fun v => Equiv.ofFiberEquiv_map _ v
    refine ⟨⟨e, fun {v w} => ?_⟩, he⟩
    by_cases hvw : v = w
    · subst hvw
      simp
    · have hne : e v ≠ e w := fun h => hvw (e.injective h)
      have h1 := adj_top_of_card_le_two hT.connected h2 hvw
      have h2 := adj_top_of_card_le_two hT₂.connected h2' hne
      exact ⟨fun _ => h1, fun _ => h2⟩

end UniformADProbes.Trace.Dev.PMR
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace UniformADProbes.Trace.Dev.PMR

open scoped Classical
open Polynomial

lemma adjacency_map {n : ℕ} (T : SimpleGraph (Fin n)) :
    (adjacency T).map (Int.cast : ℤ → ℚ) = adjQ T := by
  ext i j
  simp only [adjacency, adjQ, Matrix.map_apply]
  split_ifs <;> simp

lemma ncard_eq_dg {n : ℕ} (T : SimpleGraph (Fin n)) (v : Fin n) :
    (T.neighborSet v).ncard = dg T v := by
  rw [dg, ← SimpleGraph.card_neighborSet_eq_degree, Set.ncard_eq_toFinset_card']
  simp

lemma degreeMatrix_map {n : ℕ} (T : SimpleGraph (Fin n)) :
    (degreeMatrix T).map (Int.cast : ℤ → ℚ) = Matrix.diagonal fun v => (dg T v : ℚ) := by
  ext i j
  simp only [degreeMatrix, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs with h
  · subst h; simp [ncard_eq_dg]
  · simp

lemma dg_lt {n : ℕ} (T : SimpleGraph (Fin n)) (v : Fin n) : dg T v < n := by
  have := SimpleGraph.degree_lt_card_verts (G := T) v
  rw [Fintype.card_fin] at this
  exact this

/-- starting colouring: the degree -/
noncomputable def degCol {n : ℕ} (T : SimpleGraph (Fin n)) (v : Fin n) : Fin n := ⟨dg T v, dg_lt T v⟩

noncomputable def tau0 (n : ℕ) : FreeAlgebra ℚ (Option (Fin n)) →ₐ[ℚ] FreeAlgebra ℚ Bool :=
  FreeAlgebra.lift ℚ fun o => match o with
    | none => FreeAlgebra.ι ℚ false
    | some c => Polynomial.aeval (FreeAlgebra.ι ℚ true) (indPoly n c)

lemma rho_eq_comp {n : ℕ} (T : SimpleGraph (Fin n)) :
    rho T (degCol T) =
      (rhoAD (adjQ T) (Matrix.diagonal fun v => (dg T v : ℚ))).comp (tau0 n) := by
  apply FreeAlgebra.hom_ext
  funext o
  cases o with
  | none =>
    simp [rho, letterMat, tau0, rhoAD]
  | some c =>
    have h1 : (rhoAD (adjQ T) (Matrix.diagonal fun v => (dg T v : ℚ)))
        (Polynomial.aeval (FreeAlgebra.ι ℚ true) (indPoly n c)) =
        Polynomial.aeval (Matrix.diagonal fun v => (dg T v : ℚ)) (indPoly n c) := by
      rw [← Polynomial.aeval_algHom_apply]
      simp [rhoAD]
    simp only [rho, FreeAlgebra.lift_ι_apply, letterMat, AlgHom.comp_apply, tau0, Function.comp_apply]
    rw [h1, aeval_diagonal]
    ext i j
    simp only [indE, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      rw [eval_indPoly c.2 (dg_lt T i)]
      simp [degCol, Fin.ext_iff, eq_comm]
    · simp [hij]

theorem pmr_main (n m : ℕ) (T : SimpleGraph (Fin n)) (T' : SimpleGraph (Fin m))
    (hT : T.IsTree) (hT' : T'.IsTree)
    (hmom : ∀ w : Word,
      (∑ i, ∑ j, wordEval (adjacency T) (degreeMatrix T) w i j) =
      (∑ i, ∑ j, wordEval (adjacency T') (degreeMatrix T') w i j)) :
    Nonempty (T ≃g T') := by
  have hnm : n = m := by
    have h1 : ∀ k : ℕ, ∑ i : Fin k, ∑ j : Fin k, (1 : Matrix (Fin k) (Fin k) ℤ) i j = k := by
      intro k
      simp [Matrix.one_apply]
    have e : ∀ {k : ℕ} (H K : Matrix (Fin k) (Fin k) ℤ), wordEval H K 1 = 1 := by
      intro k H K
      simp [wordEval]
    have := hmom 1
    rw [e, e, h1, h1] at this
    exact_mod_cast this
  subst hnm
  have hφ : ∀ a, phi T (degCol T) a = phi T' (degCol T') a := by
    intro a
    have := moments_free (adjacency T) (degreeMatrix T) (adjacency T') (degreeMatrix T') hmom
      (tau0 n a)
    rw [adjacency_map, degreeMatrix_map, adjacency_map, degreeMatrix_map] at this
    simpa [phi, rho_eq_comp] using this
  obtain ⟨F, _⟩ := general n (fun c : Fin n => (c : ℕ)) T T' hT hT' (degCol T) (degCol T')
    (fun v => rfl) (fun v => rfl) (Fintype.card_fin n) hφ
  exact ⟨F⟩

end UniformADProbes.Trace.Dev.PMR

namespace UniformADProbes.Trace
open UniformADProbes.Trace.Dev.PMR in
theorem chk_principal_moment_reconstruction (n m : ℕ)
    (T : SimpleGraph (Fin n)) (T' : SimpleGraph (Fin m))
    (hT : T.IsTree) (hT' : T'.IsTree)
    (hmom : ∀ w : Word,
      (∑ i, ∑ j, wordEval (adjacency T) (degreeMatrix T) w i j) =
      (∑ i, ∑ j, wordEval (adjacency T') (degreeMatrix T') w i j)) :
    Nonempty (T ≃g T') := pmr_main n m T T' hT hT' hmom

end UniformADProbes.Trace
end

theorem solution : type_of% @UniformADProbes.Trace.chk_principal_moment_reconstruction := @UniformADProbes.Trace.chk_principal_moment_reconstruction
