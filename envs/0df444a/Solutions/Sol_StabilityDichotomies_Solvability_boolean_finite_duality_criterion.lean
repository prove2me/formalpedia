-- Prove2me | solution 1 for StabilityDichotomies.Solvability.boolean_finite_duality_criterion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:01:41.249207+00:00
-- url     : https://prove2.me/submissions/7167aed1-b98b-45de-9cff-b3fd93a2e060

import Mathlib
import Definitions.Def_StabilityDichotomies_Solvability_LinksSquares
import Definitions.Def_StabilityDichotomies_Solvability_FiniteDuality

section
set_option autoImplicit false

namespace StabilityDichotomies.Dev.Links

open StabilityDichotomies.Solvability
open scoped Classical

theorem mem_links {Γ : Language} {N : ℕ} (c : Constraint Γ (LinkVertex N))
    (hc : c ∈ (linksSquares Γ N).constraints) :
    ∃ (R : Γ.Member) (a b : Fin R.val.arity → Bool) (j : Fin N) (lam : Fin R.val.arity → Bool),
      a ∈ R.val.tuples ∧ b ∈ R.val.tuples ∧
      c = ⟨R, fun t => linkVar N
        ⟨if lam t then j.val + 1 else j.val, by
          split
          · exact Nat.succ_lt_succ j.isLt
          · exact Nat.lt_succ_of_lt j.isLt⟩ (a t) (b t)⟩ := by
  simp only [linksSquares, Multiset.mem_bind, Multiset.mem_map, Finset.mem_val,
    Finset.mem_univ, true_and] at hc
  obtain ⟨R, a, ha, b, hb, j, lam, rfl⟩ := hc
  exact ⟨R, a, b, j, lam, ha, hb, rfl⟩

theorem links_mem {Γ : Language} {N : ℕ} (R : Γ.Member) (a b : Fin R.val.arity → Bool)
    (ha : a ∈ R.val.tuples) (hb : b ∈ R.val.tuples) (j : Fin N) (lam : Fin R.val.arity → Bool) :
    (⟨R, fun t => linkVar N
        ⟨if lam t then j.val + 1 else j.val, by
          split
          · exact Nat.succ_lt_succ j.isLt
          · exact Nat.lt_succ_of_lt j.isLt⟩ (a t) (b t)⟩ : Constraint Γ (LinkVertex N)) ∈
      (linksSquares Γ N).constraints := by
  simp only [linksSquares, Multiset.mem_bind, Multiset.mem_map, Finset.mem_val,
    Finset.mem_univ, true_and]
  exact ⟨R, a, ha, b, hb, j, lam, rfl⟩

/-! ### Part (ii) -/

theorem layer_removed_sat (Γ : Language) (N : ℕ) (hN : 1 ≤ N) (k : Fin (N + 1)) :
    Satisfiable ((linksSquares Γ N).induce (Finset.univ \ linkLayer N k)) := by
  refine ⟨fun v => if v.1.1.1.val < k.val then v.1.1.2.1 else v.1.1.2.2, ?_⟩
  intro c hc
  simp only [Instance.induce, Multiset.mem_bind] at hc
  obtain ⟨c0, hc0, hc⟩ := hc
  obtain ⟨R, a, b, j, lam, ha, hb, rfl⟩ := mem_links c0 hc0
  split_ifs at hc with h
  · rw [Multiset.mem_singleton] at hc
    subst hc
    have hk : ∀ t, (⟨if lam t then j.val + 1 else j.val, by
          split
          · exact Nat.succ_lt_succ j.isLt
          · exact Nat.lt_succ_of_lt j.isLt⟩ : Fin (N + 1)) ≠ k := by
      intro t hkt
      have := h t
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, linkLayer, Finset.mem_filter,
        not_and] at this
      exact this (by simpa [linkVar] using hkt)
    by_cases hjk : j.val < k.val
    · show (fun i => _) ∈ R.val.tuples
      convert ha using 1
      funext t
      have h1 := hk t
      have h1' : (if lam t then j.val + 1 else j.val) ≠ k.val := fun e => h1 (Fin.ext e)
      have h2 : (if lam t then j.val + 1 else j.val) < k.val := by
        by_cases hl : lam t
        · simp only [hl, if_true] at h1' ⊢; omega
        · simp only [hl] at h1' ⊢; simpa using hjk
      have h3 : (if lam t then j.val + 1 else j.val) ≠ N := by omega
      simp [linkVar, h2, h3]
    · show (fun i => _) ∈ R.val.tuples
      convert hb using 1
      funext t
      have h1 := hk t
      have h1' : (if lam t then j.val + 1 else j.val) ≠ k.val := fun e => h1 (Fin.ext e)
      have h2 : ¬ (if lam t then j.val + 1 else j.val) < k.val := by
        by_cases hl : lam t
        · simp only [hl, if_true] at h1' ⊢; omega
        · simp only [hl] at h1' ⊢; simpa using hjk
      have h3 : (if lam t then j.val + 1 else j.val) ≠ 0 := by
        by_cases hl : lam t
        · simp [hl]
        · simp [hl] at h1' ⊢; omega
      simp [linkVar, h2, h3]
  · simp at hc

/-! ### Closure implies strict essential -/

theorem strict_of_closure (R : Relation) (G : Bool → Bool → Bool) (p : Bool)
    (hG : G (!p) p = p)
    (H : ∀ a ∈ R.tuples, ∀ b ∈ R.tuples, ∀ S : Fin R.arity → Bool,
      (fun i => if S i = true then G (a i) (b i) else a i) ∈ R.tuples) :
    StrictEssential p R := by
  obtain ⟨c, hcR, hcmax⟩ := Finset.exists_max_image R.tuples
    (fun d : Fin R.arity → Bool => (Finset.univ.filter fun i => d i = p).card)
    R.tuples_nonempty
  have claim1 : ∀ d ∈ R.tuples, ∀ i, d i = p → c i = p := by
    intro d hd i hdi
    by_contra hci
    have hci' : c i = !p := by
      revert hci; cases p <;> cases h : c i <;> simp
    have hmem := H c hcR d hd (fun j => decide (j = i))
    have hle := hcmax _ hmem
    have hlt : (Finset.univ.filter fun j => c j = p).card <
        (Finset.univ.filter fun j => (fun j => if decide (j = i) = true then G (c j) (d j)
          else c j) j = p).card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨i, ?_, ?_⟩
        · simp [hci', hdi, hG]
        · simp [hci]
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        by_cases hji : j = i
        · subst hji; exact absurd hj hci
        · simp [hji, hj]
    exact absurd (lt_of_lt_of_le hlt hle) (lt_irrefl _)
  have claim2 : ∀ a ∈ R.tuples, ∀ a' : Fin R.arity → Bool, (∀ i, a i = p → a' i = p) →
      (∀ i, a' i = p → c i = p) → a' ∈ R.tuples := by
    intro a ha a' h1 h2
    have hmem := H a ha c hcR (fun i => decide (a i = !p ∧ a' i = p))
    convert hmem using 1
    funext i
    have e1 := h1 i
    have e2 := h2 i
    revert e1 e2 hG
    cases p <;> cases a i <;> cases a' i <;> cases c i <;> simp
  refine ⟨(((List.finRange R.arity).filter (fun i => c i = !p)).map (fun i => [(i, !p)])) ++
    ((Finset.univ.filter (fun t : Fin R.arity → Bool =>
        (∀ i, t i = p → c i = p) ∧ t ∉ R.tuples)).toList.map (fun t =>
      ((List.finRange R.arity).filter (fun i => t i = !p ∧ c i = p)).map (fun i => (i, p)))),
    ?_, ?_⟩
  · intro cl hcl
    simp only [List.mem_append, List.mem_map] at hcl
    rcases hcl with ⟨i, _, rfl⟩ | ⟨t, _, rfl⟩
    · left; rfl
    · right
      intro l hl
      simp only [List.mem_map] at hl
      obtain ⟨i, _, rfl⟩ := hl
      rfl
  · intro x
    constructor
    · intro hx cl hcl
      simp only [List.mem_append, List.mem_map] at hcl
      rcases hcl with ⟨i, hi, rfl⟩ | ⟨t, ht, rfl⟩
      · simp only [List.mem_filter, decide_eq_true_eq] at hi
        refine ⟨(i, !p), by simp, ?_⟩
        by_contra hne
        have hxp : x i = p := by revert hne; cases p <;> cases x i <;> simp
        have := claim1 x hx i hxp
        rw [hi.2] at this
        revert this; cases p <;> simp
      · simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at ht
        by_contra hno
        apply ht.2
        apply claim2 x hx t _ ht.1
        intro i hxi
        have hci := claim1 x hx i hxi
        by_contra hti
        apply hno
        refine ⟨(i, p), ?_, hxi⟩
        simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and,
          decide_eq_true_eq]
        refine ⟨i, ⟨?_, hci⟩, rfl⟩
        revert hti; cases p <;> cases t i <;> simp
    · intro hx
      by_contra hxn
      have hle : ∀ i, x i = p → c i = p := by
        intro i hxi
        by_contra hci
        have hci' : c i = !p := by revert hci; cases p <;> cases h : c i <;> simp
        have := hx [(i, !p)] (by
          simp only [List.mem_append, List.mem_map, List.mem_filter, List.mem_finRange,
            true_and, decide_eq_true_eq]
          left; exact ⟨i, hci', rfl⟩)
        obtain ⟨l, hl, hl2⟩ := this
        simp only [List.mem_singleton] at hl
        subst hl
        revert hl2 hxi; cases p <;> cases x i <;> simp
      have := hx _ (by
        simp only [List.mem_append, List.mem_map, Finset.mem_toList, Finset.mem_filter,
          Finset.mem_univ, true_and]
        right; exact ⟨x, ⟨hle, hxn⟩, rfl⟩)
      obtain ⟨l, hl, hl2⟩ := this
      simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and,
        decide_eq_true_eq] at hl
      obtain ⟨i, ⟨h1, _⟩, rfl⟩ := hl
      revert hl2 h1; cases p <;> cases x i <;> simp

/-! ### Part (i) -/

theorem step (Γ : Language) (N : ℕ) (hN : 1 ≤ N) (g : ℕ → Bool → Bool → Bool)
    (hg0 : ∀ a b, g 0 a b = a) (hgN : ∀ a b, g N a b = b)
    (Pg : ∀ R ∈ Γ.relations, ∀ a ∈ R.tuples, ∀ b ∈ R.tuples, ∀ j < N,
      ∀ lam : Fin R.arity → Bool,
      (fun t => g (if lam t = true then j + 1 else j) (a t) (b t)) ∈ R.tuples) :
    Valid Γ true ∨ Valid Γ false ∨ StrictEssentialLanguage Γ true ∨
      StrictEssentialLanguage Γ false := by
  have hex : ∃ j, ∃ a b, g j a b ≠ a := ⟨N, false, true, by simp [hgN]⟩
  obtain ⟨a0, b0, hne⟩ := Nat.find_spec hex
  have hj0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hne
    exact hne (hg0 _ _)
  obtain ⟨j', hj'⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hjN : Nat.find hex ≤ N := Nat.find_min' hex ⟨false, true, by simp [hgN]⟩
  have hmin : ∀ a b, g j' a b = a := by
    intro a b
    have := Nat.find_min hex (show j' < Nat.find hex by omega)
    push_neg at this
    exact this a b
  rw [hj'] at hne
  set G := g (j' + 1) with hGdef
  have H : ∀ R ∈ Γ.relations, ∀ a ∈ R.tuples, ∀ b ∈ R.tuples, ∀ S : Fin R.arity → Bool,
      (fun i => if S i = true then G (a i) (b i) else a i) ∈ R.tuples := by
    intro R hR a ha b hb S
    have := Pg R hR a ha b hb j' (by omega) S
    convert this using 1
    funext i
    by_cases hS : S i = true
    · simp [hS, hGdef]
    · simp [hS, hmin]
  by_cases h1 : G false false = true
  · left
    intro R hR
    obtain ⟨a, ha⟩ := R.tuples_nonempty
    have := H R hR a ha a ha (fun i => !a i)
    convert this using 1
    funext i
    cases hai : a i <;> simp [h1]
  by_cases h2 : G true true = false
  · right; left
    intro R hR
    obtain ⟨a, ha⟩ := R.tuples_nonempty
    have := H R hR a ha a ha (fun i => a i)
    convert this using 1
    funext i
    cases hai : a i <;> simp [h2]
  by_cases h3 : G false true = true
  · right; right; left
    intro R hR
    exact strict_of_closure R G true h3 (H R hR)
  by_cases h4 : G true false = false
  · right; right; right
    intro R hR
    exact strict_of_closure R G false h4 (H R hR)
  exfalso
  simp only [Bool.not_eq_true, Bool.not_eq_false] at h1 h2 h3 h4
  apply hne
  cases a0 <;> cases b0 <;> simp_all

def F (N : ℕ) (x : LinkVertex N → Bool) (i : ℕ) (a b : Bool) : Bool :=
  if h : i < N + 1 then x (linkVar N ⟨i, h⟩ a b) else false

theorem rel_prop {Γ : Language} {N : ℕ} {x : LinkVertex N → Bool}
    (hx : Solution (linksSquares Γ N) x) (R : Γ.Member) (a b : Fin R.val.arity → Bool)
    (ha : a ∈ R.val.tuples) (hb : b ∈ R.val.tuples) (j : ℕ) (hj : j < N)
    (lam : Fin R.val.arity → Bool) :
    (fun t => F N x (if lam t = true then j + 1 else j) (a t) (b t)) ∈ R.val.tuples := by
  have := hx _ (links_mem R a b ha hb ⟨j, hj⟩ lam)
  unfold Constraint.Satisfied at this
  have e : (fun t => F N x (if lam t = true then j + 1 else j) (a t) (b t)) = fun i => x
      (linkVar N ⟨if lam i then (⟨j, hj⟩ : Fin N).val + 1 else (⟨j, hj⟩ : Fin N).val, by
          split
          · exact Nat.succ_lt_succ (⟨j, hj⟩ : Fin N).isLt
          · exact Nat.lt_succ_of_lt (⟨j, hj⟩ : Fin N).isLt⟩ (a i) (b i)) := by
    funext t
    have hlt : (if lam t = true then j + 1 else j) < N + 1 := by split <;> omega
    simp only [F, dif_pos hlt]
  rw [e]
  exact this

theorem F_zero (N : ℕ) (x : LinkVertex N → Bool) (a b : Bool) :
    F N x 0 a b = F N x 0 a false := by
  simp [F, linkVar]

theorem F_last (N : ℕ) (hN : 1 ≤ N) (x : LinkVertex N → Bool) (a b : Bool) :
    F N x N a b = F N x N false b := by
  have : ¬ N = 0 := by omega
  simp [F, linkVar, this]

theorem invol (Γ : Language) (φ : Bool → Bool)
    (hφ : ∀ R ∈ Γ.relations, ∀ a ∈ R.tuples, (fun t => φ (a t)) ∈ R.tuples)
    (h0 : ¬ Valid Γ false) (h1 : ¬ Valid Γ true) : ∀ s, φ (φ s) = s := by
  have key : ∀ c, φ false = c → φ true = c → Valid Γ c := by
    intro c e1 e2 R hR
    obtain ⟨a, ha⟩ := R.tuples_nonempty
    have := hφ R hR a ha
    convert this using 1
    funext t
    cases a t <;> simp [e1, e2]
  intro s
  cases hf : φ false <;> cases ht : φ true
  · exact absurd (key false hf ht) h0
  · cases s <;> simp [hf, ht]
  · cases s <;> simp [hf, ht]
  · exact absurd (key true hf ht) h1

theorem unsat_of_not_classes (Γ : Language)
    (h0 : ¬ Valid Γ false) (h1 : ¬ Valid Γ true)
    (hp : ¬ StrictEssentialLanguage Γ true) (hn : ¬ StrictEssentialLanguage Γ false)
    (N : ℕ) (hN : 1 ≤ N) : ¬ Satisfiable (linksSquares Γ N) := by
  rintro ⟨x, hx⟩
  have P := rel_prop hx
  have hα : ∀ R ∈ Γ.relations, ∀ a ∈ R.tuples,
      (fun t => F N x 0 (a t) false) ∈ R.tuples := by
    intro R hR a ha
    have := P ⟨R, hR⟩ a a ha ha 0 (by omega) (fun _ => false)
    simpa [F_zero N x _ (a _)] using this
  have hβ : ∀ R ∈ Γ.relations, ∀ a ∈ R.tuples,
      (fun t => F N x N false (a t)) ∈ R.tuples := by
    intro R hR a ha
    have := P ⟨R, hR⟩ a a ha ha (N - 1) (by omega) (fun _ => true)
    have e : N - 1 + 1 = N := by omega
    simpa [e, F_last N hN x (a _)] using this
  have iα := invol Γ (fun a => F N x 0 a false) hα h0 h1
  have iβ := invol Γ (fun b => F N x N false b) hβ h0 h1
  rcases step Γ N hN (fun i a b => F N x i (F N x 0 a false) (F N x N false b))
    (fun a b => by simp only [F_zero N x _ _, iα])
    (fun a b => by simp only [F_last N hN x _ _, iβ])
    (by
      intro R hR a ha b hb j hj lam
      exact P ⟨R, hR⟩ _ _ (hα R hR a ha) (hβ R hR b hb) j hj lam) with h | h | h | h
  · exact h1 h
  · exact h0 h
  · exact hp h
  · exact hn h

end StabilityDichotomies.Dev.Links
end

section
set_option autoImplicit false

namespace StabilityDichotomies.Dev.CritBack

open StabilityDichotomies.Solvability

open scoped Classical

/-- Transfer a solution of the induced instance to a global assignment. -/
lemma transfer {Γ : Language} {V : Type} (I : Instance Γ V) (U : Finset V)
    (y : U → Bool) (hy : Solution (I.induce U) y) (c : Constraint Γ V)
    (hc : c ∈ I.constraints) (h : ∀ i, c.scope i ∈ U) :
    c.Satisfied (fun v => if hv : v ∈ U then y ⟨v, hv⟩ else false) := by
  have hmem : (⟨c.rel, fun i => ⟨c.scope i, h i⟩⟩ : Constraint Γ U) ∈
      (I.induce U).constraints := by
    unfold Instance.induce
    rw [Multiset.mem_bind]
    exact ⟨c, hc, by simp [h]⟩
  have := hy _ hmem
  unfold Constraint.Satisfied at this ⊢
  have e : (fun i => (fun v => if hv : v ∈ U then y ⟨v, hv⟩ else false) (c.scope i)) =
      (fun i => y ((⟨c.rel, fun i => ⟨c.scope i, h i⟩⟩ : Constraint Γ U).scope i)) := by
    funext i
    simp [h i]
  rw [e]
  exact this

lemma valid_dual {Γ : Language} (b : Bool) (hv : Valid Γ b) {V : Type} (I : Instance Γ V) :
    Satisfiable I :=
  ⟨fun _ => b, fun c _ => hv c.rel.val c.rel.property⟩

/-- Chosen CNF. -/
noncomputable def cnf {Γ : Language} {pos : Bool} (hSE : StrictEssentialLanguage Γ pos) {V : Type}
    (c : Constraint Γ V) : CNF c.rel.val.arity :=
  Classical.choose (hSE c.rel.val c.rel.property)

lemma cnf_shape {Γ : Language} {pos : Bool} (hSE : StrictEssentialLanguage Γ pos) {V : Type}
    (c : Constraint Γ V) :
    ∀ cl ∈ cnf hSE c, cl.length = 1 ∨ ∀ l ∈ cl, l.2 = pos :=
  (Classical.choose_spec (hSE c.rel.val c.rel.property)).1

lemma sat_iff {Γ : Language} {pos : Bool} (hSE : StrictEssentialLanguage Γ pos) {V : Type}
    (c : Constraint Γ V) (x : V → Bool) :
    c.Satisfied x ↔ CNFHolds (cnf hSE c) (fun i => x (c.scope i)) :=
  (Classical.choose_spec (hSE c.rel.val c.rel.property)).2 _

lemma arity_le {Γ : Language} {V : Type} (c : Constraint Γ V) :
    c.rel.val.arity ≤ maxArity Γ :=
  Finset.le_sup (f := Relation.arity) c.rel.property

theorem strict_case (Γ : Language) (pos : Bool) (hSE : StrictEssentialLanguage Γ pos) :
    FiniteDuality Γ := by
  refine ⟨maxArity Γ * (maxArity Γ + 1), ?_⟩
  intro V _ I hI
  let Zp : V → Prop := fun v => ∃ c ∈ I.constraints, ∃ i,
    [(i, !pos)] ∈ cnf hSE c ∧ c.scope i = v
  let x : V → Bool := fun v => if Zp v then !pos else pos
  have key : ∃ c ∈ I.constraints, ∃ cl ∈ cnf hSE c,
      ¬ ClauseHolds cl (fun i => x (c.scope i)) := by
    by_contra h
    push Not at h
    exact hI ⟨x, fun c hc => (sat_iff hSE c x).2 (fun cl hcl => h c hc cl hcl)⟩
  obtain ⟨c, hc, cl, hcl, hviol⟩ := key
  have hZ : ∀ l ∈ cl, l.2 = pos ∧ Zp (c.scope l.1) := by
    intro l hl
    have hne : x (c.scope l.1) ≠ l.2 := fun he => hviol ⟨l, hl, he⟩
    by_cases hz : Zp (c.scope l.1)
    · refine ⟨?_, hz⟩
      have : x (c.scope l.1) = !pos := by simp [x, hz]
      rw [this] at hne
      cases pos <;> cases h2 : l.2 <;> simp_all
    · exfalso
      have hx : x (c.scope l.1) = pos := by simp [x, hz]
      rw [hx] at hne
      have hl2 : l.2 = !pos := by
        cases pos <;> cases h2 : l.2 <;> simp_all
      rcases cnf_shape hSE c cl hcl with hlen | hall
      · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hlen
        have : l = a := by simpa using hl
        subst this
        exact hz ⟨c, hc, l.1, by simpa [← hl2] using hcl, rfl⟩
      · have := hall l hl
        rw [hl2] at this
        cases pos <;> simp_all
  have hW : ∀ i : Fin c.rel.val.arity, ∃ c' ∈ I.constraints,
      (Zp (c.scope i) → ∃ i', [(i', !pos)] ∈ cnf hSE c' ∧ c'.scope i' = c.scope i) := by
    intro i
    by_cases hz : Zp (c.scope i)
    · obtain ⟨c', hc', i', h1, h2⟩ := hz
      exact ⟨c', hc', fun _ => ⟨i', h1, h2⟩⟩
    · exact ⟨c, hc, fun h => absurd h hz⟩
  choose W hWmem hWspec using hW
  let U : Finset V := Finset.univ.image c.scope ∪
    Finset.univ.biUnion (fun i => Finset.univ.image (W i).scope)
  refine ⟨U, ?_, ?_⟩
  · have h1 : (Finset.univ.image c.scope).card ≤ maxArity Γ :=
      (Finset.card_image_le).trans (by simpa using arity_le c)
    have h2 : (Finset.univ.biUnion (fun i => Finset.univ.image (W i).scope)).card
        ≤ c.rel.val.arity * maxArity Γ := by
      refine (Finset.card_biUnion_le_card_mul _ _ (maxArity Γ) ?_).trans (by simp)
      intro i _
      exact (Finset.card_image_le).trans (by simpa using arity_le (W i))
    have h3 : c.rel.val.arity * maxArity Γ ≤ maxArity Γ * maxArity Γ :=
      Nat.mul_le_mul_right _ (arity_le c)
    calc U.card ≤ _ := Finset.card_union_le _ _
      _ ≤ maxArity Γ + maxArity Γ * maxArity Γ := by omega
      _ = maxArity Γ * (maxArity Γ + 1) := by ring
  · rintro ⟨y, hy⟩
    let y' : V → Bool := fun v => if hv : v ∈ U then y ⟨v, hv⟩ else false
    have hcU : ∀ i, c.scope i ∈ U := fun i =>
      Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
    have hc' : c.Satisfied y' := transfer I U y hy c hc hcU
    have hy'Z : ∀ i, Zp (c.scope i) → y' (c.scope i) = !pos := by
      intro i hz
      obtain ⟨i', hmem, he⟩ := hWspec i hz
      have hWU : ∀ j, (W i).scope j ∈ U := fun j =>
        Finset.mem_union_right _ (Finset.mem_biUnion.2
          ⟨i, Finset.mem_univ _, Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩⟩)
      have hs := (sat_iff hSE (W i) y').1 (transfer I U y hy (W i) (hWmem i) hWU)
        _ hmem
      obtain ⟨l, hl, hl2⟩ := hs
      have : l = (i', !pos) := by simpa using hl
      subst this
      simpa [he] using hl2
    obtain ⟨l, hl, hl2⟩ := (sat_iff hSE c y').1 hc' cl hcl
    obtain ⟨hp, hz⟩ := hZ l hl
    have := hy'Z l.1 hz
    have hl2' : y' (c.scope l.1) = l.2 := hl2
    rw [this, hp] at hl2'
    cases pos <;> simp at hl2'

theorem finiteDuality_of_classes (Γ : Language)
    (h : Valid Γ false ∨ Valid Γ true ∨ StrictEssentialLanguage Γ true ∨ StrictEssentialLanguage Γ false) :
    FiniteDuality Γ := by
  rcases h with h | h | h | h
  · exact ⟨0, fun V _ I hI => absurd (valid_dual false h I) hI⟩
  · exact ⟨0, fun V _ I hI => absurd (valid_dual true h I) hI⟩
  · exact strict_case Γ true h
  · exact strict_case Γ false h

end StabilityDichotomies.Dev.CritBack
end

section
set_option autoImplicit false

namespace StabilityDichotomies.Dev.Crit

open StabilityDichotomies.Solvability
open scoped Classical

lemma induce_mono {Γ : Language} {V : Type} {I : Instance Γ V} {U S : Finset V} (h : U ⊆ S) :
    Satisfiable (I.induce S) → Satisfiable (I.induce U) := by
  rintro ⟨y, hy⟩
  refine ⟨fun u => y ⟨u.1, h u.2⟩, ?_⟩
  intro d hd
  simp only [Instance.induce, Multiset.mem_bind] at hd
  obtain ⟨c, hc, hdc⟩ := hd
  split_ifs at hdc with hU
  swap
  · simp at hdc
  rw [Multiset.mem_singleton] at hdc
  subst hdc
  have hmem : (⟨c.rel, fun i => ⟨c.scope i, h (hU i)⟩⟩ : Constraint Γ S) ∈ (I.induce S).constraints := by
    simp only [Instance.induce, Multiset.mem_bind]
    refine ⟨c, hc, ?_⟩
    rw [dif_pos (fun i => h (hU i))]
    simp
  exact hy _ hmem

theorem forward (Γ : Language) (hFD : FiniteDuality Γ) :
    Valid Γ false ∨ Valid Γ true ∨
      StrictEssentialLanguage Γ true ∨ StrictEssentialLanguage Γ false := by
  by_contra hne
  push Not at hne
  obtain ⟨h0, h1, hp, hn⟩ := hne
  obtain ⟨d, hd⟩ := hFD
  have hun := StabilityDichotomies.Dev.Links.unsat_of_not_classes Γ h0 h1 hp hn (d + 1) (by omega)
  obtain ⟨U, hU, hunsat⟩ := hd _ _ hun
  have : ∃ k : Fin (d + 2), ∀ u ∈ U, u.val.1 ≠ k := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin (d + 2))) ⊆ U.image (fun u => u.val.1) := by
      intro k _
      obtain ⟨u, hu, hk⟩ := hcon k
      exact Finset.mem_image.mpr ⟨u, hu, hk⟩
    have := Finset.card_le_card hsub
    have := Finset.card_image_le (s := U) (f := fun u => u.val.1)
    simp at *
    omega
  obtain ⟨k, hk⟩ := this
  apply hunsat
  apply induce_mono (S := Finset.univ \ linkLayer (d + 1) k) _
    (StabilityDichotomies.Dev.Links.layer_removed_sat Γ (d + 1) (by omega) k)
  intro u hu
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, linkLayer, Finset.mem_filter]
  exact hk u hu

end StabilityDichotomies.Dev.Crit

namespace StabilityDichotomies.Solvability

theorem chk_boolean_finite_duality_criterion (Γ : Language) :
    FiniteDuality Γ ↔
      Valid Γ false ∨ Valid Γ true ∨
      StrictEssentialLanguage Γ true ∨ StrictEssentialLanguage Γ false :=
  ⟨StabilityDichotomies.Dev.Crit.forward Γ,
    StabilityDichotomies.Dev.CritBack.finiteDuality_of_classes Γ⟩

end StabilityDichotomies.Solvability
end

theorem solution : type_of% @StabilityDichotomies.Solvability.chk_boolean_finite_duality_criterion := @StabilityDichotomies.Solvability.chk_boolean_finite_duality_criterion
