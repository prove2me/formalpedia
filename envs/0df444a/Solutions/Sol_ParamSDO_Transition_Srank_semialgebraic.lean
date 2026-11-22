-- Prove2me | solution 1 for ParamSDO.Transition.Srank_semialgebraic
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T18:57:19.086112+00:00
-- url     : https://prove2.me/submissions/894bd884-ec9d-4a7d-8271-027adc1955c5

import Mathlib
import Definitions.Def_ParamSDO_Transition_Setting
import Theorems.Thm_ParamSDO_Transition_domE_interval
import Theorems.Thm_ParamSDO_Transition_optimality_conditions_1
import Theorems.Thm_ParamSDO_Transition_ranks_maximal
import Theorems.Thm_ParamSDO_Transition_eq_19
import Theorems.Thm_NonsmoothLojasiewicz_Continuous_tarski_seidenberg_parametric

section SemialgHelpers

open ParamSDO.Transition

/-! ### Part 1: Boolean algebra and Tarski–Seidenberg projection for `IsSemialgebraicSet` -/

private def basicSet {N : ℕ} (eqs lts : Finset (MvPolynomial (Fin N) ℝ)) : Set (Fin N → ℝ) :=
  {v | (∀ p ∈ eqs, MvPolynomial.eval v p = 0) ∧ ∀ g ∈ lts, MvPolynomial.eval v g < 0}

private lemma isSemialgebraicSet_empty {N : ℕ} :
    IsSemialgebraicSet (∅ : Set (Fin N → ℝ)) :=
  ⟨0, Fin.elim0, Fin.elim0, by simp⟩

private lemma isSemialgebraicSet_basic {N : ℕ} (eqs lts : Finset (MvPolynomial (Fin N) ℝ)) :
    IsSemialgebraicSet (basicSet eqs lts) :=
  ⟨1, fun _ => eqs, fun _ => lts, by ext v; simp [basicSet]⟩

private lemma isSemialgebraicSet_univ {N : ℕ} :
    IsSemialgebraicSet (Set.univ : Set (Fin N → ℝ)) := by
  simpa [basicSet] using isSemialgebraicSet_basic (N := N) ∅ ∅

private lemma isSemialgebraicSet_zero {N : ℕ} (p : MvPolynomial (Fin N) ℝ) :
    IsSemialgebraicSet {v : Fin N → ℝ | MvPolynomial.eval v p = 0} := by
  simpa [basicSet] using isSemialgebraicSet_basic {p} ∅

private lemma isSemialgebraicSet_lt {N : ℕ} (g : MvPolynomial (Fin N) ℝ) :
    IsSemialgebraicSet {v : Fin N → ℝ | MvPolynomial.eval v g < 0} := by
  simpa [basicSet] using isSemialgebraicSet_basic ∅ {g}

private lemma isSemialgebraicSet_pos {N : ℕ} (g : MvPolynomial (Fin N) ℝ) :
    IsSemialgebraicSet {v : Fin N → ℝ | 0 < MvPolynomial.eval v g} := by
  have h : {v : Fin N → ℝ | 0 < MvPolynomial.eval v g} =
      {v : Fin N → ℝ | MvPolynomial.eval v (-g) < 0} := by
    ext v
    simp [map_neg]
  rw [h]
  exact isSemialgebraicSet_lt (-g)

private lemma isSemialgebraicSet_union {N : ℕ} {S T : Set (Fin N → ℝ)}
    (hS : IsSemialgebraicSet S) (hT : IsSemialgebraicSet T) :
    IsSemialgebraicSet (S ∪ T) := by
  rcases hS with ⟨K₁, E₁, L₁, rfl⟩
  rcases hT with ⟨K₂, E₂, L₂, rfl⟩
  refine ⟨K₁ + K₂, Fin.addCases E₁ E₂, Fin.addCases L₁ L₂, ?_⟩
  ext v
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
    · exact ⟨Fin.castAdd K₂ i, by simpa [Fin.addCases_left] using hi⟩
    · exact ⟨Fin.natAdd K₁ j, by simpa [Fin.addCases_right] using hj⟩
  · rintro ⟨k, hk⟩
    refine Fin.addCases (fun i hi => Or.inl ⟨i, ?_⟩) (fun j hj => Or.inr ⟨j, ?_⟩) k hk
    · simpa [Fin.addCases_left] using hi
    · simpa [Fin.addCases_right] using hj

private lemma isSemialgebraicSet_biUnion {N : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Set (Fin N → ℝ)) (hf : ∀ i ∈ s, IsSemialgebraicSet (f i)) :
    IsSemialgebraicSet (⋃ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using isSemialgebraicSet_empty (N := N)
  | @insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    exact isSemialgebraicSet_union (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma isSemialgebraicSet_iUnion {N : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → Set (Fin N → ℝ)) (hf : ∀ i, IsSemialgebraicSet (f i)) :
    IsSemialgebraicSet (⋃ i, f i) := by
  have h : (⋃ i, f i) = ⋃ i ∈ (Finset.univ : Finset ι), f i := by simp
  rw [h]
  exact isSemialgebraicSet_biUnion Finset.univ f fun i _ => hf i

private lemma isSemialgebraicSet_inter {N : ℕ} {S T : Set (Fin N → ℝ)}
    (hS : IsSemialgebraicSet S) (hT : IsSemialgebraicSet T) :
    IsSemialgebraicSet (S ∩ T) := by
  classical
  rcases hS with ⟨K₁, E₁, L₁, rfl⟩
  rcases hT with ⟨K₂, E₂, L₂, rfl⟩
  have h : (⋃ i, basicSet (E₁ i) (L₁ i)) ∩ (⋃ j, basicSet (E₂ j) (L₂ j)) =
      ⋃ p : Fin K₁ × Fin K₂, basicSet (E₁ p.1 ∪ E₂ p.2) (L₁ p.1 ∪ L₂ p.2) := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_iUnion, basicSet, Set.mem_ofPred_eq, Finset.mem_union,
      Prod.exists]
    constructor
    · rintro ⟨⟨i, hi1, hi2⟩, ⟨j, hj1, hj2⟩⟩
      refine ⟨i, j, fun p hp => hp.elim (hi1 p) (hj1 p), fun g hg => hg.elim (hi2 g) (hj2 g)⟩
    · rintro ⟨i, j, h1, h2⟩
      exact ⟨⟨i, fun p hp => h1 p (Or.inl hp), fun g hg => h2 g (Or.inl hg)⟩,
        ⟨j, fun p hp => h1 p (Or.inr hp), fun g hg => h2 g (Or.inr hg)⟩⟩
  change IsSemialgebraicSet ((⋃ i, basicSet (E₁ i) (L₁ i)) ∩ (⋃ j, basicSet (E₂ j) (L₂ j)))
  rw [h]
  exact isSemialgebraicSet_iUnion _ fun p => isSemialgebraicSet_basic _ _

private lemma isSemialgebraicSet_biInter {N : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Set (Fin N → ℝ)) (hf : ∀ i ∈ s, IsSemialgebraicSet (f i)) :
    IsSemialgebraicSet (⋂ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using isSemialgebraicSet_univ (N := N)
  | @insert a s ha ih =>
    rw [Finset.set_biInter_insert]
    exact isSemialgebraicSet_inter (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma isSemialgebraicSet_iInter {N : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → Set (Fin N → ℝ)) (hf : ∀ i, IsSemialgebraicSet (f i)) :
    IsSemialgebraicSet (⋂ i, f i) := by
  have h : (⋂ i, f i) = ⋂ i ∈ (Finset.univ : Finset ι), f i := by simp
  rw [h]
  exact isSemialgebraicSet_biInter Finset.univ f fun i _ => hf i

private lemma isSemialgebraicSet_compl_basic {N : ℕ}
    (E L : Finset (MvPolynomial (Fin N) ℝ)) :
    IsSemialgebraicSet (basicSet E L)ᶜ := by
  have h : (basicSet E L)ᶜ =
      (⋃ p ∈ E, ({v : Fin N → ℝ | MvPolynomial.eval v p < 0} ∪
        {v : Fin N → ℝ | MvPolynomial.eval v (-p) < 0})) ∪
      (⋃ g ∈ L, ({v : Fin N → ℝ | MvPolynomial.eval v g = 0} ∪
        {v : Fin N → ℝ | MvPolynomial.eval v (-g) < 0})) := by
    ext v
    simp only [Set.mem_compl_iff, basicSet, Set.mem_ofPred_eq, not_and_or, not_forall,
      Set.mem_union, Set.mem_iUnion, map_neg, neg_lt_zero]
    constructor
    · rintro (⟨p, hp, hne⟩ | ⟨g, hg, hge⟩)
      · left
        refine ⟨p, hp, ?_⟩
        exact lt_or_gt_of_ne hne
      · right
        refine ⟨g, hg, ?_⟩
        rcases eq_or_lt_of_le (not_lt.mp hge) with h0 | hpos
        · exact Or.inl h0.symm
        · exact Or.inr hpos
    · rintro (⟨p, hp, hlt | hgt⟩ | ⟨g, hg, h0 | hpos⟩)
      · exact Or.inl ⟨p, hp, ne_of_lt hlt⟩
      · exact Or.inl ⟨p, hp, ne_of_gt hgt⟩
      · exact Or.inr ⟨g, hg, by rw [h0]; exact lt_irrefl 0⟩
      · exact Or.inr ⟨g, hg, not_lt.mpr (le_of_lt hpos)⟩
  rw [h]
  exact isSemialgebraicSet_union
    (isSemialgebraicSet_biUnion E _ fun p _ =>
      isSemialgebraicSet_union (isSemialgebraicSet_lt p) (isSemialgebraicSet_lt (-p)))
    (isSemialgebraicSet_biUnion L _ fun g _ =>
      isSemialgebraicSet_union (isSemialgebraicSet_zero g) (isSemialgebraicSet_lt (-g)))

private lemma isSemialgebraicSet_compl {N : ℕ} {S : Set (Fin N → ℝ)}
    (hS : IsSemialgebraicSet S) : IsSemialgebraicSet Sᶜ := by
  rcases hS with ⟨K, E, L, rfl⟩
  change IsSemialgebraicSet (⋃ i, basicSet (E i) (L i))ᶜ
  rw [Set.compl_iUnion]
  exact isSemialgebraicSet_iInter _ fun i => isSemialgebraicSet_compl_basic (E i) (L i)

private lemma isSemialgebraicSet_diff {N : ℕ} {S T : Set (Fin N → ℝ)}
    (hS : IsSemialgebraicSet S) (hT : IsSemialgebraicSet T) :
    IsSemialgebraicSet (S \ T) := by
  rw [Set.sdiff_eq]
  exact isSemialgebraicSet_inter hS (isSemialgebraicSet_compl hT)

private lemma isSemialgebraicSet_reindex {M N : ℕ} (e : Fin M ≃ Fin N)
    {S : Set (Fin N → ℝ)} (hS : IsSemialgebraicSet S) :
    IsSemialgebraicSet {v : Fin M → ℝ | v ∘ e.symm ∈ S} := by
  classical
  rcases hS with ⟨K, E, L, rfl⟩
  refine ⟨K, fun i => (E i).image (MvPolynomial.rename e.symm),
    fun i => (L i).image (MvPolynomial.rename e.symm), ?_⟩
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_image, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, MvPolynomial.eval_rename]

private lemma isSemialgebraicSet_proj_cons_basic {N : ℕ}
    (E L : Finset (MvPolynomial (Fin (N + 1)) ℝ)) :
    IsSemialgebraicSet {a : Fin N → ℝ | ∃ x : ℝ, Fin.cons x a ∈ basicSet E L} := by
  let evalHom : MvPolynomial (Fin N) ℝ →+* ((Fin N → ℝ) → ℝ) :=
    RingHom.pi fun a => MvPolynomial.eval a
  let R : Subring ((Fin N → ℝ) → ℝ) := evalHom.range
  let Fam : Set (Set (Fin N → ℝ)) := {T | IsSemialgebraicSet T}
  have hpos : ∀ f ∈ R, {a : Fin N → ℝ | 0 < f a} ∈ Fam := by
    rintro f ⟨p, rfl⟩
    exact isSemialgebraicSet_pos p
  have hcompl : ∀ S ∈ Fam, Sᶜ ∈ Fam := fun _ hS => isSemialgebraicSet_compl hS
  have hinter : ∀ S ∈ Fam, ∀ T ∈ Fam, S ∩ T ∈ Fam :=
    fun _ hS _ hT => isSemialgebraicSet_inter hS hT
  let toPoly : MvPolynomial (Fin (N + 1)) ℝ → Polynomial R :=
    fun q => (MvPolynomial.finSuccEquiv ℝ N q).map evalHom.rangeRestrict
  let F : Finset (MvPolynomial (Fin (N + 1)) ℝ ⊕ MvPolynomial (Fin (N + 1)) ℝ) := E.disjSum L
  let ev : MvPolynomial (Fin (N + 1)) ℝ ⊕ MvPolynomial (Fin (N + 1)) ℝ → Polynomial R :=
    Sum.elim toPoly toPoly
  let ν : MvPolynomial (Fin (N + 1)) ℝ ⊕ MvPolynomial (Fin (N + 1)) ℝ → SignType :=
    Sum.elim (fun _ => 0) (fun _ => -1)
  have hTS := NonsmoothLojasiewicz.Continuous.tarski_seidenberg_parametric
    R F ev ν Fam hpos hcompl hinter
  have heval : ∀ (a : Fin N → ℝ) (x : ℝ) (q : MvPolynomial (Fin (N + 1)) ℝ),
      ((toPoly q).map ((Pi.evalRingHom (fun _ : Fin N → ℝ => ℝ) a).comp R.subtype)).eval x =
        MvPolynomial.eval (Fin.cons x a) q := by
    intro a x q
    dsimp only [toPoly]
    rw [Polynomial.map_map]
    have hcomp : ((Pi.evalRingHom (fun _ : Fin N → ℝ => ℝ) a).comp R.subtype).comp
        evalHom.rangeRestrict = MvPolynomial.eval a :=
      RingHom.ext fun _ => rfl
    rw [hcomp, ← MvPolynomial.eval_eq_eval_mv_eval' a x q]
  have hset :
      {a : Fin N → ℝ | ∃ x : ℝ, ∀ i ∈ F, SignType.sign
        (((ev i).map ((Pi.evalRingHom (fun _ : Fin N → ℝ => ℝ) a).comp R.subtype)).eval x) = ν i} =
      {a : Fin N → ℝ | ∃ x : ℝ, Fin.cons x a ∈ basicSet E L} := by
    ext a
    simp only [Set.mem_ofPred_eq, basicSet, F, Finset.mem_disjSum, ev, ν]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_, ?_⟩
      · intro p hp
        have h1 := hx (Sum.inl p) (Or.inl ⟨p, hp, rfl⟩)
        simp only [Sum.elim_inl] at h1
        rw [heval, sign_eq_zero_iff] at h1
        exact h1
      · intro g hg
        have h1 := hx (Sum.inr g) (Or.inr ⟨g, hg, rfl⟩)
        simp only [Sum.elim_inr] at h1
        rw [heval, sign_eq_neg_one_iff] at h1
        exact h1
    · rintro ⟨x, hE, hL⟩
      refine ⟨x, ?_⟩
      rintro (p | g) hi
      · rcases hi with ⟨p', hp', hEq⟩ | ⟨g', _, hEq⟩
        · cases hEq
          simp only [Sum.elim_inl]
          rw [heval, sign_eq_zero_iff]
          exact hE p hp'
        · cases hEq
      · rcases hi with ⟨p', _, hEq⟩ | ⟨g', hg', hEq⟩
        · cases hEq
        · cases hEq
          simp only [Sum.elim_inr]
          rw [heval, sign_eq_neg_one_iff]
          exact hL g hg'
  rw [← hset]
  exact hTS

private lemma isSemialgebraicSet_proj_cons {N : ℕ} {S : Set (Fin (N + 1) → ℝ)}
    (hS : IsSemialgebraicSet S) :
    IsSemialgebraicSet {a : Fin N → ℝ | ∃ x : ℝ, Fin.cons x a ∈ S} := by
  rcases hS with ⟨K, E, L, rfl⟩
  have h : {a : Fin N → ℝ | ∃ x : ℝ, Fin.cons x a ∈ ⋃ i, basicSet (E i) (L i)} =
      ⋃ i : Fin K, {a : Fin N → ℝ | ∃ x : ℝ, Fin.cons x a ∈ basicSet (E i) (L i)} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨fun ⟨x, i, h⟩ => ⟨i, x, h⟩, fun ⟨i, x, h⟩ => ⟨x, i, h⟩⟩
  change IsSemialgebraicSet {a : Fin N → ℝ | ∃ x : ℝ, Fin.cons x a ∈ ⋃ i, basicSet (E i) (L i)}
  rw [h]
  exact isSemialgebraicSet_iUnion _ fun i => isSemialgebraicSet_proj_cons_basic (E i) (L i)

private lemma isSemialgebraicSet_proj_snoc {N : ℕ} {S : Set (Fin (N + 1) → ℝ)}
    (hS : IsSemialgebraicSet S) :
    IsSemialgebraicSet {a : Fin N → ℝ | ∃ x : ℝ, Fin.snoc a x ∈ S} := by
  let e : Fin (N + 1) ≃ Fin (N + 1) :=
    { toFun := Fin.cases (Fin.last N) Fin.castSucc
      invFun := Fin.lastCases 0 Fin.succ
      left_inv := fun i => by
        refine Fin.cases ?_ ?_ i
        · simp
        · intro j; simp
      right_inv := fun i => by
        refine Fin.lastCases ?_ ?_ i
        · simp
        · intro j; simp }
  have hcomp : ∀ (a : Fin N → ℝ) (x : ℝ), Fin.cons x a ∘ e.symm = Fin.snoc a x := by
    intro a x
    funext i
    refine Fin.lastCases ?_ ?_ i
    · simp [e]
    · intro j; simp [e]
  have hS' : IsSemialgebraicSet {v : Fin (N + 1) → ℝ | v ∘ e.symm ∈ S} :=
    isSemialgebraicSet_reindex e hS
  have heq : {a : Fin N → ℝ | ∃ x : ℝ, Fin.snoc a x ∈ S} =
      {a : Fin N → ℝ | ∃ x : ℝ, Fin.cons x a ∈ {v : Fin (N + 1) → ℝ | v ∘ e.symm ∈ S}} := by
    ext a
    simp only [Set.mem_ofPred_eq, hcomp]
  rw [heq]
  exact isSemialgebraicSet_proj_cons hS'

private lemma isSemialgebraicSet_proj_add {N D : ℕ} {S : Set (Fin (N + D) → ℝ)}
    (hS : IsSemialgebraicSet S) :
    IsSemialgebraicSet {a : Fin N → ℝ | ∃ z : Fin D → ℝ, Fin.append a z ∈ S} := by
  induction D with
  | zero =>
    have heq : {a : Fin N → ℝ | ∃ z : Fin 0 → ℝ, Fin.append a z ∈ S} = S := by
      ext a
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨z, hz⟩
        have ha : Fin.append a z = a := by
          funext i
          simpa using Fin.append_left a z i
        rwa [ha] at hz
      · intro ha
        refine ⟨Fin.elim0, ?_⟩
        have ha' : Fin.append a Fin.elim0 = a := by
          funext i
          simp
        rwa [ha']
    rw [heq]
    exact hS
  | succ D ih =>
    have hS1 : IsSemialgebraicSet {b : Fin (N + D) → ℝ | ∃ x : ℝ, Fin.snoc b x ∈ S} :=
      isSemialgebraicSet_proj_snoc hS
    have heq : {a : Fin N → ℝ | ∃ z : Fin (D + 1) → ℝ, Fin.append a z ∈ S} =
        {a : Fin N → ℝ | ∃ z' : Fin D → ℝ,
          Fin.append a z' ∈ {b : Fin (N + D) → ℝ | ∃ x : ℝ, Fin.snoc b x ∈ S}} := by
      ext a
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨z, hz⟩
        refine ⟨Fin.init z, z (Fin.last D), ?_⟩
        rwa [← Fin.append_snoc, Fin.snoc_init_self]
      · rintro ⟨z', x, hx⟩
        refine ⟨Fin.snoc z' x, ?_⟩
        rwa [Fin.append_snoc]
    rw [heq]
    exact ih hS1

private lemma isSemialgebraicReal_of_exists_forall_poly_eq_zero
    {ι α : Type} [Fintype ι] [Fintype α]
    (P : α → MvPolynomial (Option ι) ℝ) :
    IsSemialgebraicReal
      {ϵ : ℝ | ∃ w : ι → ℝ, ∀ a : α, MvPolynomial.eval (Option.elim' ϵ w) (P a) = 0} := by
  classical
  let D := Fintype.card ι
  let e : ι ≃ Fin D := Fintype.equivFin ι
  let φ : Option ι ≃ Fin (1 + D) :=
    { toFun := Option.elim' (Fin.castAdd D 0) (fun i => Fin.natAdd 1 (e i))
      invFun := fun k => Fin.addCases (fun _ => none) (fun j => some (e.symm j)) k
      left_inv := fun o => by
        cases o with
        | none => simp
        | some i => simp
      right_inv := fun k => by
        refine Fin.addCases (fun i => ?_) (fun j => ?_) k
        · fin_cases i; simp
        · simp }
  let E : Finset (MvPolynomial (Fin (1 + D)) ℝ) :=
    Finset.univ.image (fun a => MvPolynomial.rename φ (P a))
  have hS : IsSemialgebraicSet (basicSet E ∅) := isSemialgebraicSet_basic E ∅
  have hproj := isSemialgebraicSet_proj_add (N := 1) (D := D) hS
  have heval_comp : ∀ (x : Fin 1 → ℝ) (z : Fin D → ℝ),
      Fin.append x z ∘ φ = Option.elim' (x 0) (z ∘ e) := by
    intro x z
    funext o
    cases o with
    | none => simp [φ, Fin.append_left]
    | some i => simp [φ, Fin.append_right]
  have hset : (fun x : Fin 1 → ℝ => x 0) ⁻¹'
      {ϵ : ℝ | ∃ w : ι → ℝ, ∀ a : α, MvPolynomial.eval (Option.elim' ϵ w) (P a) = 0} =
      {x : Fin 1 → ℝ | ∃ z : Fin D → ℝ, Fin.append x z ∈ basicSet E ∅} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, basicSet, E, Finset.mem_image,
      Finset.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff,
      Finset.notMem_empty, false_implies, implies_true, and_true, MvPolynomial.eval_rename,
      heval_comp]
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨w ∘ e.symm, fun a => ?_⟩
      have hcomp : (w ∘ e.symm) ∘ e = w := by funext i; simp
      rw [hcomp]
      exact hw a
    · rintro ⟨z, hz⟩
      exact ⟨z ∘ e, hz⟩
  unfold IsSemialgebraicReal
  rw [hset]
  exact hproj

private lemma isSemialgebraicReal_inter {S T : Set ℝ}
    (hS : IsSemialgebraicReal S) (hT : IsSemialgebraicReal T) :
    IsSemialgebraicReal (S ∩ T) := by
  unfold IsSemialgebraicReal at *
  rw [Set.preimage_inter]
  exact isSemialgebraicSet_inter hS hT

private lemma isSemialgebraicReal_diff {S T : Set ℝ}
    (hS : IsSemialgebraicReal S) (hT : IsSemialgebraicReal T) :
    IsSemialgebraicReal (S \ T) := by
  unfold IsSemialgebraicReal at *
  rw [Set.preimage_sdiff]
  exact isSemialgebraicSet_diff hS hT

/-! ### Part 2: Every open convex subset of `ℝ` is semi-algebraic -/

private lemma isSemialgebraicReal_Ioi (a : ℝ) : IsSemialgebraicReal (Set.Ioi a) := by
  unfold IsSemialgebraicReal
  have h : (fun x : Fin 1 → ℝ => x 0) ⁻¹' Set.Ioi a =
      {x : Fin 1 → ℝ | MvPolynomial.eval x (MvPolynomial.C a - MvPolynomial.X 0) < 0} := by
    ext x
    simp
  rw [h]
  exact isSemialgebraicSet_lt _

private lemma isSemialgebraicReal_Iio (b : ℝ) : IsSemialgebraicReal (Set.Iio b) := by
  unfold IsSemialgebraicReal
  have h : (fun x : Fin 1 → ℝ => x 0) ⁻¹' Set.Iio b =
      {x : Fin 1 → ℝ | MvPolynomial.eval x (MvPolynomial.X 0 - MvPolynomial.C b) < 0} := by
    ext x
    simp
  rw [h]
  exact isSemialgebraicSet_lt _

private lemma isSemialgebraicReal_of_isOpen_convex {U : Set ℝ}
    (hopen : IsOpen U) (hconv : Convex ℝ U) : IsSemialgebraicReal U := by
  rcases U.eq_empty_or_nonempty with rfl | hne
  · exact isSemialgebraicSet_empty
  have hmem_gt_sInf : ∀ x ∈ U, BddBelow U → sInf U < x := by
    intro x hx hbb
    rcases Metric.isOpen_iff.mp hopen x hx with ⟨δ, hδ, hball⟩
    have hx' : x - δ / 2 ∈ U := hball (by
      rw [Metric.mem_ball, Real.dist_eq]
      rw [show x - δ / 2 - x = -(δ / 2) by ring, abs_neg, abs_of_pos (half_pos hδ)]
      linarith)
    exact lt_of_le_of_lt (csInf_le hbb hx') (by linarith)
  have hmem_lt_sSup : ∀ x ∈ U, BddAbove U → x < sSup U := by
    intro x hx hba
    rcases Metric.isOpen_iff.mp hopen x hx with ⟨δ, hδ, hball⟩
    have hx' : x + δ / 2 ∈ U := hball (by
      rw [Metric.mem_ball, Real.dist_eq]
      rw [show x + δ / 2 - x = δ / 2 by ring, abs_of_pos (half_pos hδ)]
      linarith)
    exact lt_of_lt_of_le (by linarith) (le_csSup hba hx')
  by_cases hbb : BddBelow U <;> by_cases hba : BddAbove U
  · have hU : U = Set.Ioi (sInf U) ∩ Set.Iio (sSup U) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio]
      constructor
      · intro hx
        exact ⟨hmem_gt_sInf x hx hbb, hmem_lt_sSup x hx hba⟩
      · rintro ⟨h1, h2⟩
        rcases exists_lt_of_csInf_lt hne h1 with ⟨u, hu, hux⟩
        rcases exists_lt_of_lt_csSup hne h2 with ⟨v, hv, hxv⟩
        exact hconv.ordConnected.out hu hv ⟨le_of_lt hux, le_of_lt hxv⟩
    rw [hU]
    exact isSemialgebraicReal_inter (isSemialgebraicReal_Ioi _) (isSemialgebraicReal_Iio _)
  · have hU : U = Set.Ioi (sInf U) := by
      ext x
      simp only [Set.mem_Ioi]
      constructor
      · intro hx
        exact hmem_gt_sInf x hx hbb
      · intro h1
        rcases exists_lt_of_csInf_lt hne h1 with ⟨u, hu, hux⟩
        have ⟨v, hv, hxv⟩ : ∃ v ∈ U, x < v := by
          by_contra hall
          push Not at hall
          exact hba ⟨x, hall⟩
        exact hconv.ordConnected.out hu hv ⟨le_of_lt hux, le_of_lt hxv⟩
    rw [hU]
    exact isSemialgebraicReal_Ioi _
  · have hU : U = Set.Iio (sSup U) := by
      ext x
      simp only [Set.mem_Iio]
      constructor
      · intro hx
        exact hmem_lt_sSup x hx hba
      · intro h2
        have ⟨u, hu, hux⟩ : ∃ u ∈ U, u < x := by
          by_contra hall
          push Not at hall
          exact hbb ⟨x, hall⟩
        rcases exists_lt_of_lt_csSup hne h2 with ⟨v, hv, hxv⟩
        exact hconv.ordConnected.out hu hv ⟨le_of_lt hux, le_of_lt hxv⟩
    rw [hU]
    exact isSemialgebraicReal_Iio _
  · have hU : U = Set.univ := by
      ext x
      simp only [Set.mem_univ, iff_true]
      have ⟨u, hu, hux⟩ : ∃ u ∈ U, u < x := by
        by_contra hall
        push Not at hall
        exact hbb ⟨x, hall⟩
      have ⟨v, hv, hxv⟩ : ∃ v ∈ U, x < v := by
        by_contra hall
        push Not at hall
        exact hba ⟨x, hall⟩
      exact hconv.ordConnected.out hu hv ⟨le_of_lt hux, le_of_lt hxv⟩
    rw [hU]
    exact isSemialgebraicSet_univ

/-! ### Part 3: Algebraic characterizations of `PosSemidef` and `k ≤ rank` -/

private lemma posSemidef_iff_exists_transpose_mul_self {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    M.PosSemidef ↔ ∃ L : Matrix (Fin n) (Fin n) ℝ, M = L.transpose * L := by
  constructor
  · intro hM
    let U : Matrix (Fin n) (Fin n) ℝ := (hM.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i => Real.sqrt (hM.1.eigenvalues i))
    refine ⟨D * U.transpose, ?_⟩
    have hDD : D * D = Matrix.diagonal hM.1.eigenvalues := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact Real.mul_self_sqrt (hM.eigenvalues_nonneg i)
    have hspec : M = U * Matrix.diagonal hM.1.eigenvalues * U.transpose := by
      have hs := hM.1.spectral_theorem
      simpa [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial] using hs
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc D D U.transpose, hDD, ← Matrix.mul_assoc, ← hspec]
  · rintro ⟨L, rfl⟩
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self L

private lemma le_rank_iff_exists_mul_eq_one {n k : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    k ≤ M.rank ↔
      ∃ (U : Matrix (Fin n) (Fin k) ℝ) (V : Matrix (Fin k) (Fin n) ℝ), V * M * U = 1 := by
  constructor
  · intro hk
    let b := Module.finBasis ℝ (LinearMap.range M.mulVecLin)
    have hcard : k ≤ Module.finrank ℝ (LinearMap.range M.mulVecLin) := hk
    have hu : ∀ j : Fin k, ∃ u : Fin n → ℝ, M.mulVec u = (b (Fin.castLE hcard j)).1 := fun j =>
      (b (Fin.castLE hcard j)).2
    choose u hu using hu
    let U : Matrix (Fin n) (Fin k) ℝ := Matrix.of fun r j => u j r
    have hMU_single : ∀ j : Fin k, (M * U).mulVec (Pi.single j 1) = (b (Fin.castLE hcard j)).1 := by
      intro j
      rw [← Matrix.mulVec_mulVec]
      have hU_single : U.mulVec (Pi.single j 1) = u j := by
        ext r
        simp [U, Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hU_single, hu j]
    have hker : LinearMap.ker (M * U).mulVecLin = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx
      have hx_expand : (M * U).mulVec x = ∑ j : Fin k, x j • (b (Fin.castLE hcard j)).1 := by
        have hx' : x = ∑ j : Fin k, x j • Pi.single j (1 : ℝ) := by
          ext i
          simp [Finset.sum_apply, Pi.single_apply]
        conv_lhs => rw [hx']
        rw [Matrix.mulVec_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.mulVec_smul, hMU_single j]
      rw [hx_expand] at hx
      have hsum_sub : (∑ j : Fin k, x j • b (Fin.castLE hcard j)) = 0 := by
        apply Subtype.ext
        simpa [Submodule.coe_sum, Submodule.coe_smul_of_tower] using hx
      have hli : LinearIndependent ℝ (fun j : Fin k => b (Fin.castLE hcard j)) :=
        b.linearIndependent.comp (Fin.castLE hcard) (Fin.castLE_injective hcard)
      have hzero := Fintype.linearIndependent_iff.mp hli x hsum_sub
      ext j
      exact hzero j
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (M * U).mulVecLin hker
    let V : Matrix (Fin k) (Fin n) ℝ := LinearMap.toMatrix' g
    refine ⟨U, V, ?_⟩
    apply LinearMap.toMatrix'.symm.injective
    have hV : V.mulVecLin = g := Matrix.toLin'_toMatrix' g
    change (V * M * U).mulVecLin = (1 : Matrix (Fin k) (Fin k) ℝ).mulVecLin
    rw [Matrix.mul_assoc, Matrix.mulVecLin_mul, hV, hg, Matrix.mulVecLin_one]
  · rintro ⟨U, V, hVU⟩
    have h1 : k = (V * M * U).rank := by
      rw [hVU, Matrix.rank_one, Fintype.card_fin]
    calc
      k = (V * M * U).rank := h1
      _ ≤ (V * M).rank := Matrix.rank_mul_le_left (V * M) U
      _ ≤ M.rank := Matrix.rank_mul_le_right V M

/-! ### Part 4: Polynomial encoding of optimal solutions of rank ≥ k -/

private abbrev VarIdx (n m k : ℕ) : Type :=
  (Fin n × Fin n) ⊕ Fin m ⊕ (Fin n × Fin n) ⊕ (Fin n × Fin n) ⊕ (Fin n × Fin n) ⊕
    (Fin n × Fin k) ⊕ (Fin k × Fin n)

private abbrev EqIdx (n m k : ℕ) : Type :=
  (Fin n × Fin n) ⊕ (Fin n × Fin n) ⊕ Fin m ⊕ (Fin n × Fin n) ⊕ (Fin n × Fin n) ⊕
    (Fin k × Fin k)

private lemma isSemialgebraicReal_rankGe {n m : ℕ}
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ) (isS : Bool) (k : ℕ) :
    IsSemialgebraicReal
      {ϵ : ℝ | ∃ (X : Matrix (Fin n) (Fin n) ℝ) (y : Fin m → ℝ) (S : Matrix (Fin n) (Fin n) ℝ),
        X ∈ Pfeas A b ∧ (y, S) ∈ Dfeas A C Cbar ϵ ∧ X * S = 0 ∧
        k ≤ (if isS then S else X).rank} := by
  let pEps : MvPolynomial (Option (VarIdx n m k)) ℝ := MvPolynomial.X none
  let pX (i j : Fin n) : MvPolynomial (Option (VarIdx n m k)) ℝ :=
    MvPolynomial.X (some (Sum.inl (i, j)))
  let py (r : Fin m) : MvPolynomial (Option (VarIdx n m k)) ℝ :=
    MvPolynomial.X (some (Sum.inr (Sum.inl r)))
  let pS (i j : Fin n) : MvPolynomial (Option (VarIdx n m k)) ℝ :=
    MvPolynomial.X (some (Sum.inr (Sum.inr (Sum.inl (i, j)))))
  let pLX (i j : Fin n) : MvPolynomial (Option (VarIdx n m k)) ℝ :=
    MvPolynomial.X (some (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j))))))
  let pLS (i j : Fin n) : MvPolynomial (Option (VarIdx n m k)) ℝ :=
    MvPolynomial.X (some (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j)))))))
  let pU (i : Fin n) (j : Fin k) : MvPolynomial (Option (VarIdx n m k)) ℝ :=
    MvPolynomial.X (some (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j))))))))
  let pV (i : Fin k) (j : Fin n) : MvPolynomial (Option (VarIdx n m k)) ℝ :=
    MvPolynomial.X (some (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, j))))))))
  let pT (i j : Fin n) : MvPolynomial (Option (VarIdx n m k)) ℝ :=
    if isS then pS i j else pX i j
  let P : EqIdx n m k → MvPolynomial (Option (VarIdx n m k)) ℝ :=
    Sum.elim
      (fun ij => pX ij.1 ij.2 - ∑ r : Fin n, pLX r ij.1 * pLX r ij.2)
      (Sum.elim
        (fun ij => pS ij.1 ij.2 - ∑ r : Fin n, pLS r ij.1 * pLS r ij.2)
        (Sum.elim
          (fun r => (∑ i : Fin n, ∑ j : Fin n, MvPolynomial.C (A r i j) * pX j i) -
            MvPolynomial.C (b r))
          (Sum.elim
            (fun ij => (∑ r : Fin m, py r * MvPolynomial.C (A r ij.1 ij.2)) + pS ij.1 ij.2 -
              MvPolynomial.C (C ij.1 ij.2) - pEps * MvPolynomial.C (Cbar ij.1 ij.2))
            (Sum.elim
              (fun ij => ∑ r : Fin n, pX ij.1 r * pS r ij.2)
              (fun ab => (∑ r : Fin n, ∑ c : Fin n, pV ab.1 r * pT r c * pU c ab.2) -
                MvPolynomial.C (if ab.1 = ab.2 then (1 : ℝ) else 0))))))
  have hset :
      {ϵ : ℝ | ∃ (X : Matrix (Fin n) (Fin n) ℝ) (y : Fin m → ℝ) (S : Matrix (Fin n) (Fin n) ℝ),
        X ∈ Pfeas A b ∧ (y, S) ∈ Dfeas A C Cbar ϵ ∧ X * S = 0 ∧
        k ≤ (if isS then S else X).rank} =
      {ϵ : ℝ | ∃ w : VarIdx n m k → ℝ,
        ∀ a : EqIdx n m k, MvPolynomial.eval (Option.elim' ϵ w) (P a) = 0} := by
    ext ϵ
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨X, y, S, hXfeas, hDfeas, hXS, hrk⟩
      obtain ⟨LX, hLX⟩ := (posSemidef_iff_exists_transpose_mul_self X).mp hXfeas.1
      obtain ⟨LS, hLS⟩ := (posSemidef_iff_exists_transpose_mul_self S).mp hDfeas.2
      obtain ⟨U, V, hUV⟩ := (le_rank_iff_exists_mul_eq_one (if isS then S else X)).mp hrk
      let w : VarIdx n m k → ℝ :=
        Sum.elim (fun ij => X ij.1 ij.2)
          (Sum.elim y
            (Sum.elim (fun ij => S ij.1 ij.2)
              (Sum.elim (fun ij => LX ij.1 ij.2)
                (Sum.elim (fun ij => LS ij.1 ij.2)
                  (Sum.elim (fun ij => U ij.1 ij.2) (fun ij => V ij.1 ij.2))))))
      refine ⟨w, fun a => ?_⟩
      rcases a with ⟨i, j⟩ | ⟨i, j⟩ | r | ⟨i, j⟩ | ⟨i, j⟩ | ⟨a, b'⟩
      · have h := congr_fun (congr_fun hLX i) j
        simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
        simp [P, pX, pLX, w, h]
      · have h := congr_fun (congr_fun hLS i) j
        simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
        simp [P, pS, pLS, w, h]
      · have h := hXfeas.2 r
        simp only [pair, Matrix.trace, Matrix.diag, Matrix.mul_apply] at h
        simp [P, pX, w, h]
      · have h := congr_fun (congr_fun hDfeas.1 i) j
        simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h
        simp only [P, Sum.elim_inr, Sum.elim_inl, pEps, py, pS, w, map_sub, map_add, map_sum,
          map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, Option.elim'_none, Option.elim'_some]
        linarith
      · have h := congr_fun (congr_fun hXS i) j
        simp only [Matrix.mul_apply, Matrix.zero_apply] at h
        simp [P, pX, pS, w, h]
      · have h := congr_fun (congr_fun hUV a) b'
        simp only [Matrix.mul_apply, Matrix.one_apply] at h
        have hT : ∀ r c, MvPolynomial.eval (Option.elim' ϵ w) (pT r c) =
            (if isS then S else X) r c := by
          intro r c; cases isS <;> simp [pT, pX, pS, w]
        simp only [P, Sum.elim_inr, Sum.elim_inl, pV, pU, w, map_sub, map_sum, map_mul,
          MvPolynomial.eval_X, MvPolynomial.eval_C, Option.elim'_some, hT, sub_eq_zero]
        have hre : (∑ r : Fin n, ∑ c : Fin n, V a r * (if isS then S else X) r c * U c b') =
            ∑ c : Fin n, (∑ r : Fin n, V a r * (if isS then S else X) r c) * U c b' := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.sum_mul]
        rw [hre]
        exact h
    · rintro ⟨w, hw⟩
      let X : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => w (Sum.inl (i, j))
      let y : Fin m → ℝ := fun r => w (Sum.inr (Sum.inl r))
      let S : Matrix (Fin n) (Fin n) ℝ :=
        Matrix.of fun i j => w (Sum.inr (Sum.inr (Sum.inl (i, j))))
      let LX : Matrix (Fin n) (Fin n) ℝ :=
        Matrix.of fun i j => w (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j)))))
      let LS : Matrix (Fin n) (Fin n) ℝ :=
        Matrix.of fun i j => w (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j))))))
      let U : Matrix (Fin n) (Fin k) ℝ :=
        Matrix.of fun i j => w (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j)))))))
      let V : Matrix (Fin k) (Fin n) ℝ :=
        Matrix.of fun i j => w (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, j)))))))
      refine ⟨X, y, S, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
      · rw [posSemidef_iff_exists_transpose_mul_self]
        refine ⟨LX, ?_⟩
        ext i j
        have h := hw (Sum.inl (i, j))
        simp only [P, Sum.elim_inl, pX, pLX, map_sub, map_sum, map_mul, MvPolynomial.eval_X,
          Option.elim'_some, sub_eq_zero] at h
        simpa [X, LX, Matrix.mul_apply, Matrix.transpose_apply] using h
      · intro r
        have h := hw (Sum.inr (Sum.inr (Sum.inl r)))
        simp only [P, Sum.elim_inr, Sum.elim_inl, pX, map_sub, map_sum, map_mul,
          MvPolynomial.eval_X, MvPolynomial.eval_C, Option.elim'_some, sub_eq_zero] at h
        simpa [pair, Matrix.trace, Matrix.diag, Matrix.mul_apply, X] using h
      · ext i j
        have h := hw (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j)))))
        simp only [P, Sum.elim_inr, Sum.elim_inl, pEps, py, pS, map_sub, map_add, map_sum,
          map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, Option.elim'_none,
          Option.elim'_some] at h
        simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, y, S,
          Matrix.of_apply]
        linarith
      · rw [posSemidef_iff_exists_transpose_mul_self]
        refine ⟨LS, ?_⟩
        ext i j
        have h := hw (Sum.inr (Sum.inl (i, j)))
        simp only [P, Sum.elim_inr, Sum.elim_inl, pS, pLS, map_sub, map_sum, map_mul,
          MvPolynomial.eval_X, Option.elim'_some, sub_eq_zero] at h
        simpa [S, LS, Matrix.mul_apply, Matrix.transpose_apply] using h
      · ext i j
        have h := hw (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j))))))
        simp only [P, Sum.elim_inr, Sum.elim_inl, pX, pS, map_sum, map_mul,
          MvPolynomial.eval_X, Option.elim'_some] at h
        simpa [X, S, Matrix.mul_apply] using h
      · rw [le_rank_iff_exists_mul_eq_one]
        refine ⟨U, V, ?_⟩
        ext a b'
        have h := hw (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (a, b'))))))
        have hT : ∀ r c, MvPolynomial.eval (Option.elim' ϵ w) (pT r c) =
            (if isS then S else X) r c := by
          intro r c; cases isS <;> simp [pT, pX, pS, X, S]
        simp only [P, Sum.elim_inr, pV, pU, map_sub, map_sum, map_mul, MvPolynomial.eval_X,
          MvPolynomial.eval_C, Option.elim'_some, hT, sub_eq_zero] at h
        simp only [Matrix.mul_apply, Matrix.one_apply, U, V, Matrix.of_apply]
        have hre : (∑ c : Fin n, (∑ r : Fin n,
            w (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (a, r))))))) *
              (if isS then S else X) r c) *
            w (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, b')))))))) =
            ∑ r : Fin n, ∑ c : Fin n,
              w (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (a, r))))))) *
                (if isS then S else X) r c *
                w (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, b'))))))) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_mul]
        rw [hre]
        exact h
  rw [hset]
  exact isSemialgebraicReal_of_exists_forall_poly_eq_zero P

end SemialgHelpers

open ParamSDO.Transition in
theorem solution {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian) (hCbar : Cbar.IsHermitian)
    (h1 : Assumption1 A) (h2 : Assumption2 A b C Cbar) :
    ∀ θ σ : ℕ, IsSemialgebraicReal (Srank A b C Cbar θ σ) := by
  intro θ σ
  let U : Set ℝ := interior (domE A b C Cbar)
  let AX (k : ℕ) : Set ℝ :=
    {ϵ | ∃ (X : Matrix (Fin n) (Fin n) ℝ) (y : Fin m → ℝ) (S : Matrix (Fin n) (Fin n) ℝ),
      X ∈ Pfeas A b ∧ (y, S) ∈ Dfeas A C Cbar ϵ ∧ X * S = 0 ∧ k ≤ X.rank}
  let BS (l : ℕ) : Set ℝ :=
    {ϵ | ∃ (X : Matrix (Fin n) (Fin n) ℝ) (y : Fin m → ℝ) (S : Matrix (Fin n) (Fin n) ℝ),
      X ∈ Pfeas A b ∧ (y, S) ∈ Dfeas A C Cbar ϵ ∧ X * S = 0 ∧ l ≤ S.rank}
  have hSrank_eq : Srank A b C Cbar θ σ = U ∩ (AX θ \ AX (θ + 1)) ∩ (BS σ \ BS (σ + 1)) := by
    ext ϵ
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Srank, Set.mem_ofPred_eq]
    by_cases hϵ : ϵ ∈ interior (domE A b C Cbar)
    · have hϵU : ϵ ∈ U := hϵ
      simp only [hϵ, hϵU, and_true, true_and]
      have hopt := optimality_conditions_1 A b C Cbar hA hC hCbar h1 h2 ϵ hϵ
      have hrm := ranks_maximal A b C Cbar hA hC hCbar h1 h2 ϵ hϵ
      have heq19 := eq_19 A b C Cbar hA hC hCbar h1 h2
      have hϵ_mem : ϵ ∈ ⋃ (θ₀ : ℕ) (σ₀ : ℕ) (_ : θ₀ + σ₀ ≤ n), Srank A b C Cbar θ₀ σ₀ := by
        rw [← heq19]; exact hϵ
      simp only [Set.mem_iUnion, exists_prop] at hϵ_mem
      rcases hϵ_mem with ⟨θ₀, σ₀, _, ⟨X₀, p₀, hX₀p₀, _, _⟩, _⟩
      rw [intrinsicInterior_prod_eq, Set.mem_prod] at hX₀p₀
      have hX₀_max := hrm.1 X₀ hX₀p₀.1
      have hp₀_max := hrm.2 p₀ hX₀p₀.2
      have hX₀_star : X₀ ∈ Pstar A b C Cbar ϵ := intrinsicInterior_subset hX₀p₀.1
      have hp₀_star : p₀ ∈ Dstar A b C Cbar ϵ := intrinsicInterior_subset hX₀p₀.2
      have hAX_iff : ∀ k : ℕ, ϵ ∈ AX k ↔ k ≤ rkX A b C Cbar ϵ := by
        intro k
        constructor
        · rintro ⟨X, y, S, hXf, hDf, hXS, hkr⟩
          have hXP : X ∈ Pstar A b C Cbar ϵ := ((hopt X y S).mpr ⟨hXf, hDf, hXS⟩).1
          calc
            k ≤ X.rank := hkr
            _ ≤ X₀.rank := hX₀_max.1 X hXP
            _ = rkX A b C Cbar ϵ := hX₀_max.2
        · intro hkr
          have hfeas := (hopt X₀ p₀.1 p₀.2).mp ⟨hX₀_star, hp₀_star⟩
          exact ⟨X₀, p₀.1, p₀.2, hfeas.1, hfeas.2.1, hfeas.2.2, hX₀_max.2 ▸ hkr⟩
      have hBS_iff : ∀ l : ℕ, ϵ ∈ BS l ↔ l ≤ rkS A b C Cbar ϵ := by
        intro l
        constructor
        · rintro ⟨X, y, S, hXf, hDf, hXS, hlr⟩
          have hSD : (y, S) ∈ Dstar A b C Cbar ϵ := ((hopt X y S).mpr ⟨hXf, hDf, hXS⟩).2
          calc
            l ≤ S.rank := hlr
            _ ≤ p₀.2.rank := hp₀_max.1 (y, S) hSD
            _ = rkS A b C Cbar ϵ := hp₀_max.2
        · intro hlr
          have hfeas := (hopt X₀ p₀.1 p₀.2).mp ⟨hX₀_star, hp₀_star⟩
          exact ⟨X₀, p₀.1, p₀.2, hfeas.1, hfeas.2.1, hfeas.2.2, hp₀_max.2 ▸ hlr⟩
      rw [hAX_iff θ, hAX_iff (θ + 1), hBS_iff σ, hBS_iff (σ + 1)]
      constructor
      · rintro ⟨X, p, hXp, hXrk, hSrk⟩
        rw [intrinsicInterior_prod_eq, Set.mem_prod] at hXp
        have h1' : rkX A b C Cbar ϵ = θ := (hrm.1 X hXp.1).2.symm.trans hXrk
        have h2' : rkS A b C Cbar ϵ = σ := (hrm.2 p hXp.2).2.symm.trans hSrk
        omega
      · rintro ⟨⟨hθ1, hθ2⟩, ⟨hσ1, hσ2⟩⟩
        refine ⟨X₀, p₀, ?_, ?_, ?_⟩
        · rw [intrinsicInterior_prod_eq, Set.mem_prod]
          exact hX₀p₀
        · omega
        · omega
    · have hϵU : ϵ ∉ U := hϵ
      simp [hϵ, hϵU]
  rw [hSrank_eq]
  have hU_sa : IsSemialgebraicReal U :=
    isSemialgebraicReal_of_isOpen_convex isOpen_interior
      (domE_interval A b C Cbar hA hC hCbar h1 h2).1.interior
  have hAX_sa : ∀ k : ℕ, IsSemialgebraicReal (AX k) := fun k => by
    simpa [AX] using isSemialgebraicReal_rankGe A b C Cbar false k
  have hBS_sa : ∀ l : ℕ, IsSemialgebraicReal (BS l) := fun l => by
    simpa [BS] using isSemialgebraicReal_rankGe A b C Cbar true l
  exact isSemialgebraicReal_inter
    (isSemialgebraicReal_inter hU_sa (isSemialgebraicReal_diff (hAX_sa θ) (hAX_sa (θ + 1))))
    (isSemialgebraicReal_diff (hBS_sa σ) (hBS_sa (σ + 1)))
