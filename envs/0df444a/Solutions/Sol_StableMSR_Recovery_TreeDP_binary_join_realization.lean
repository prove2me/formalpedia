-- Prove2me | solution 1 for StableMSR.Recovery.TreeDP.binary_join_realization
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-14T02:25:45.702762+00:00
-- url     : https://prove2.me/submissions/b0a02f97-e3fe-4e8d-a7dc-6d97afb25b89

import Definitions.Def_StableMSR_BinaryTreeDP_Plan
import Mathlib.Data.Finset.Card
open StableMSR.Recovery.TreeDP
namespace StableMSR.Recovery.TreeDP
/-- A duplicate bag enforces no extra constraint and contributes neither count nor cost. -/
def BagData.neutral {V X : Type*} (d : BagData V X) : BagData V X :=
  ⟨d.bag,d.choices,fun _ => True,fun _ => 0,fun _ => 0⟩
/-- Explicit binary conversion of a finite family of child plans. The original parent
record occurs once, at the final leaf; the extra join records are neutral copies. -/
def joinForest {V X : Type*} (d : BagData V X) : List (Plan V X) → Plan V X
  | [] => .leaf d
  | p :: ps => .branch d.neutral p (joinForest d ps)
@[simp] theorem joinForest_root_bag {V X : Type*} (d : BagData V X) (ps : List (Plan V X)) :
    (joinForest d ps).root.bag = d.bag := by cases ps <;> rfl
@[simp] theorem joinForest_root_choices {V X : Type*} (d : BagData V X) (ps : List (Plan V X)) :
    (joinForest d ps).root.choices = d.choices := by cases ps <;> rfl
/-- Binary conversion preserves exactly the union of the parent and child scopes. -/
theorem mem_joinForest_scope {V X : Type*} [DecidableEq V]
    (d : BagData V X) (ps : List (Plan V X)) (v : V) :
    v ∈ (joinForest d ps).scope ↔ v ∈ d.bag ∨ ∃ p ∈ ps, v ∈ p.scope := by
  induction ps with
  | nil => simp [joinForest,Plan.scope]
  | cons p ps ih =>
    simp only [joinForest,Plan.scope,BagData.neutral,Finset.mem_union,ih,List.mem_cons]
    constructor
    · rintro ((hd | hp) | hd | ⟨q,hq,hv⟩)
      · exact Or.inl hd
      · exact Or.inr ⟨p,Or.inl rfl,hp⟩
      · exact Or.inl hd
      · exact Or.inr ⟨q,Or.inr hq,hv⟩
    · rintro (hd | ⟨q,hq,hv⟩)
      · exact Or.inl (Or.inl hd)
      · rcases hq with rfl | hq
        · exact Or.inl (Or.inr hv)
        · exact Or.inr (Or.inr ⟨q,hq,hv⟩)
/-- Arbitrary fanout can be converted to a coherent binary plan without changing bags. -/
theorem joinForest_coherent {V X : Type*} [DecidableEq V]
    (d : BagData V X) (ps : List (Plan V X))
    (hc : ∀ p ∈ ps, p.Coherent)
    (hb : ∀ p ∈ ps, p.scope ∩ d.bag ⊆ p.root.bag)
    (hpair : ps.Pairwise (fun p q => p.scope ∩ q.scope ⊆ d.bag)) :
    (joinForest d ps).Coherent := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    obtain ⟨hp,hps⟩ := List.pairwise_cons.mp hpair
    refine ⟨hc p (by simp),ih (fun q hq => hc q (by simp [hq]))
      (fun q hq => hb q (by simp [hq])) hps,hb p (by simp),?_,?_⟩
    · rw [joinForest_root_bag]
      exact Finset.inter_subset_right
    · intro v hv
      obtain ⟨hvp,hvr⟩ := Finset.mem_inter.mp hv
      rcases (mem_joinForest_scope d ps v).mp hvr with hd | ⟨q,hq,hvq⟩
      · exact hd
      · exact hp q hq (Finset.mem_inter.mpr ⟨hvp,hvq⟩)
@[simp] theorem neutral_local {V X : Type*} (d : BagData V X) : d.neutral.Local := by
  intro a b hab
  exact ⟨Iff.rfl,rfl,rfl⟩
theorem joinForest_local {V X : Type*} (d : BagData V X) (ps : List (Plan V X))
    (hd : d.Local) (hp : ∀ p ∈ ps, p.Local) : (joinForest d ps).Local := by
  induction ps with
  | nil => exact hd
  | cons p ps ih =>
    exact ⟨neutral_local d,hp p (by simp),ih (fun q hq => hp q (by simp [hq]))⟩
/-- Neutral copies neither repeat nor remove any constraint. -/
theorem joinForest_valid_iff {V X : Type*} (d : BagData V X) (ps : List (Plan V X))
    (a : V → X) :
    (joinForest d ps).AllValid a ↔ d.valid a ∧ ∀ p ∈ ps, p.AllValid a := by
  induction ps with
  | nil => simp [joinForest,Plan.AllValid]
  | cons p ps ih =>
    simp only [joinForest,Plan.AllValid,BagData.neutral,ih,true_and,List.forall_mem_cons]
    constructor
    · rintro ⟨hp,hd,hps⟩; exact ⟨hd,hp,hps⟩
    · rintro ⟨hd,hp,hps⟩; exact ⟨hp,hd,hps⟩
/-- The original count contribution occurs once, regardless of fanout. -/
theorem joinForest_count {V X : Type*} (d : BagData V X) (ps : List (Plan V X))
    (a : V → X) : (joinForest d ps).totalCount a =
      d.count a + (ps.map (fun p => p.totalCount a)).sum := by
  induction ps with
  | nil => simp [joinForest,Plan.totalCount]
  | cons p ps ih => simp [joinForest,Plan.totalCount,BagData.neutral,ih,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
/-- The original objective contribution occurs once, regardless of fanout. -/
theorem joinForest_weight {V X : Type*} (d : BagData V X) (ps : List (Plan V X))
    (a : V → X) : (joinForest d ps).totalWeight a =
      d.weight a + (ps.map (fun p => p.totalWeight a)).sum := by
  induction ps with
  | nil => simp [joinForest,Plan.totalWeight]
  | cons p ps ih => simp [joinForest,Plan.totalWeight,BagData.neutral,ih,add_comm,add_left_comm,add_assoc]
/-- Exactly one extra binary join per original child, with no hidden combinatorial blowup. -/
theorem joinForest_nodes {V X : Type*} (d : BagData V X) (ps : List (Plan V X)) :
    (joinForest d ps).nodes = 1 + ps.length + (ps.map Plan.nodes).sum := by
  induction ps with
  | nil => simp [joinForest,Plan.nodes]
  | cons p ps ih => simp [joinForest,Plan.nodes,ih]; omega
/-- A predicate about every bag record; useful for preserving width and table bounds. -/
lemma joinForest_allData {V X : Type*} (d : BagData V X) (ps : List (Plan V X))
    (P : BagData V X → Prop) (hd : P d) (hn : P d.neutral)
    (hps : ∀ p ∈ ps, p.AllData P) : (joinForest d ps).AllData P := by
  induction ps with
  | nil => exact hd
  | cons p ps ih => exact ⟨hn,hps p (by simp),ih (fun q hq => hps q (by simp [hq]))⟩
theorem joinForest_bag_bounds {V X : Type*} (d : BagData V X) (ps : List (Plan V X))
    (width choices : ℕ) (hd : d.bag.card ≤ width ∧ d.choices.card ≤ choices)
    (hps : ∀ p ∈ ps, p.AllData (fun d => d.bag.card ≤ width ∧ d.choices.card ≤ choices)) :
    (joinForest d ps).AllData (fun d => d.bag.card ≤ width ∧ d.choices.card ≤ choices) :=
  joinForest_allData d ps _ hd hd hps
end StableMSR.Recovery.TreeDP

/-- An arbitrary finite child family has a coherent binary realization preserving
all semantic contributions, widths and assignment bounds, with linear node overhead. -/
theorem solution {V X : Type*} [DecidableEq V]
    (d : BagData V X) (children : List (Plan V X)) (width choices : ℕ)
    (hdlocal : d.Local)
    (hcoherent : ∀ p ∈ children, p.Coherent)
    (hlocal : ∀ p ∈ children, p.Local)
    (hparent : ∀ p ∈ children, p.scope ∩ d.bag ⊆ p.root.bag)
    (hpair : children.Pairwise (fun p q => p.scope ∩ q.scope ⊆ d.bag))
    (hdbound : d.bag.card ≤ width ∧ d.choices.card ≤ choices)
    (hbound : ∀ p ∈ children,
      p.AllData (fun a => a.bag.card ≤ width ∧ a.choices.card ≤ choices)) :
    ∃ p : Plan V X,
      p.Coherent ∧ p.Local ∧ p.root.bag = d.bag ∧ p.root.choices = d.choices ∧
      (∀ v, v ∈ p.scope ↔ v ∈ d.bag ∨ ∃ child ∈ children, v ∈ child.scope) ∧
      (∀ a : V → X,
        (p.AllValid a ↔ d.valid a ∧ ∀ child ∈ children, child.AllValid a) ∧
        p.totalCount a = d.count a + (children.map (fun child => child.totalCount a)).sum ∧
        p.totalWeight a = d.weight a + (children.map (fun child => child.totalWeight a)).sum) ∧
      p.nodes = 1 + children.length + (children.map Plan.nodes).sum ∧
      p.AllData (fun a => a.bag.card ≤ width ∧ a.choices.card ≤ choices) := by
  refine ⟨joinForest d children,joinForest_coherent d children hcoherent hparent hpair,
    joinForest_local d children hdlocal hlocal,joinForest_root_bag d children,
    joinForest_root_choices d children,mem_joinForest_scope d children,?_,
    joinForest_nodes d children,joinForest_bag_bounds d children width choices hdbound hbound⟩
  intro a
  exact ⟨joinForest_valid_iff d children a,joinForest_count d children a,joinForest_weight d children a⟩

