-- Prove2me | solution 1 for TenChallenges.challenge_10_locallyFinite
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T22:45:12.454201+00:00
-- url     : https://prove2.me/submissions/66770353-ef36-4f19-8665-d7e04850ed98

import Definitions.Def_TenChallenges_Challenge_10
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Discrete
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

universe u v

namespace Aux_TC10_LocFin

open Classical SimpleGraph
open scoped Cardinal

variable {W : Type u} [Fintype W] (H : SimpleGraph W)

noncomputable def mono (c : W → Bool) (x y : W) : ℤ := if H.Adj x y ∧ c x = c y then 1 else 0

noncomputable def M (c : W → Bool) : ℤ := ∑ x, ∑ y, mono H c x y

noncomputable def E (c : W → Bool) (v y : W) : ℤ :=
  (if H.Adj v y ∧ c y ≠ c v then 1 else 0) - (if H.Adj v y ∧ c y = c v then 1 else 0)

theorem flip_diff (c : W → Bool) (v : W) :
    M H (Function.update c v (!c v)) - M H c = 2 * ∑ y, E H c v y := by
  set c' := Function.update c v (!c v)
  have hc'v : c' v = !c v := Function.update_self _ _ _
  have hc'o : ∀ x, x ≠ v → c' x = c x := fun x hx => Function.update_of_ne hx _ _
  have hD : ∀ x y, mono H c' x y - mono H c x y =
      if x = v then E H c v y else if y = v then E H c v x else 0 := by
    intro x y
    by_cases hx : x = v
    · subst hx
      rw [if_pos rfl]
      by_cases hy : y = x
      · subst hy
        simp [mono, E]
      · unfold mono E
        rw [hc'v, hc'o y hy]
        cases c x <;> cases c y <;> simp
    · rw [if_neg hx]
      by_cases hy : y = v
      · subst hy
        rw [if_pos rfl]
        unfold mono E
        rw [hc'v, hc'o x hx]
        have hadj : H.Adj x y ↔ H.Adj y x := H.adj_comm x y
        cases c x <;> cases c y <;> simp [hadj]
      · rw [if_neg hy]
        unfold mono
        rw [hc'o x hx, hc'o y hy]
        ring
  have hEv : E H c v v = 0 := by simp [E]
  unfold M
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, hD]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
  simp only [if_true]
  have h2 : ∑ x ∈ Finset.univ.erase v, ∑ y, (if x = v then E H c v y else
      if y = v then E H c v x else 0) = ∑ x ∈ Finset.univ.erase v, E H c v x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxv : x ≠ v := Finset.ne_of_mem_erase hx
    simp only [hxv, if_false]
    rw [Finset.sum_ite_eq']
    simp
  rw [h2, Finset.sum_erase _ hEv]
  ring

theorem exists_unfriendly_finite [Nonempty W] : ∃ c : W → Bool, ∀ v,
    (Finset.univ.filter (fun w => H.Adj v w ∧ c w = c v)).card ≤
      (Finset.univ.filter (fun w => H.Adj v w ∧ c w ≠ c v)).card := by
  obtain ⟨c0, -, hmin⟩ := Finset.exists_min_image Finset.univ (M H) Finset.univ_nonempty
  refine ⟨c0, fun v => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hd := flip_diff H c0 v
  have hsum : ∑ y, E H c0 v y =
      ((Finset.univ.filter (fun w => H.Adj v w ∧ c0 w ≠ c0 v)).card : ℤ) -
        (Finset.univ.filter (fun w => H.Adj v w ∧ c0 w = c0 v)).card := by
    unfold E
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]
  have hm := hmin (Function.update c0 v (!c0 v)) (Finset.mem_univ _)
  have hlt' : ((Finset.univ.filter (fun w => H.Adj v w ∧ c0 w ≠ c0 v)).card : ℤ) <
      (Finset.univ.filter (fun w => H.Adj v w ∧ c0 w = c0 v)).card := by exact_mod_cast hlt
  linarith

section LocallyFinite

variable {V : Type u} (G : SimpleGraph V) (hloc : ∀ v, (G.neighborSet v).Finite)

noncomputable def N (v : V) : Finset V := (hloc v).toFinset

lemma mem_N_iff (v w : V) : w ∈ N G hloc v ↔ G.Adj v w := by
  simp [N, Set.Finite.mem_toFinset, mem_neighborSet]

def UnfAtC (c : V → Bool) (v : V) : Prop :=
  ((N G hloc v).filter (fun w => c w = c v)).card ≤
    ((N G hloc v).filter (fun w => c w ≠ c v)).card

lemma exists_global_unfriendly : ∃ c : V → Bool, ∀ v : V, UnfAtC G hloc c v := by
  let _ : TopologicalSpace Bool := ⊥
  have _ : DiscreteTopology Bool := ⟨rfl⟩
  have _ : CompactSpace (V → Bool) := inferInstance
  let U : V → Set (V → Bool) := fun v => {c | UnfAtC G hloc c v}
  have hU_closed : ∀ v : V, IsClosed (U v) := by
    intro v
    let Sv : Finset V := insert v (N G hloc v)
    let res : (V → Bool) → (Sv → Bool) := fun c x => c x.1
    have hres : Continuous res := continuous_pi fun x => continuous_apply x.1
    let P : Set (Sv → Bool) := {c' |
      UnfAtC G hloc (fun x => if hx : x ∈ Sv then c' ⟨x, hx⟩ else false) v}
    have heq : U v = res ⁻¹' P := by
      ext c
      change UnfAtC G hloc c v ↔
        UnfAtC G hloc (fun x => if hx : x ∈ Sv then c x else false) v
      unfold UnfAtC
      have hvSv : v ∈ Sv := Finset.mem_insert_self v _
      have hf1 : (N G hloc v).filter (fun w => c w = c v) =
          (N G hloc v).filter (fun w =>
            (if hx : w ∈ Sv then c w else false) = (if hx : v ∈ Sv then c v else false)) := by
        apply Finset.filter_congr
        intro w hw
        have hwSv : w ∈ Sv := Finset.mem_insert_of_mem hw
        simp [hvSv, hwSv]
      have hf2 : (N G hloc v).filter (fun w => c w ≠ c v) =
          (N G hloc v).filter (fun w =>
            (if hx : w ∈ Sv then c w else false) ≠ (if hx : v ∈ Sv then c v else false)) := by
        apply Finset.filter_congr
        intro w hw
        have hwSv : w ∈ Sv := Finset.mem_insert_of_mem hw
        simp [hvSv, hwSv]
      rw [hf1, hf2]
    rw [heq]
    exact (isClosed_discrete P).preimage hres
  let t : Finset V → Set (V → Bool) := fun F => ⋂ v ∈ F, U v
  have htd : Directed (· ⊇ ·) t := by
    intro F₁ F₂
    refine ⟨F₁ ∪ F₂, ?_, ?_⟩
    · intro c hc
      simp only [t, Set.mem_iInter, Finset.mem_union] at hc ⊢
      exact fun v hv => hc v (Or.inl hv)
    · intro c hc
      simp only [t, Set.mem_iInter, Finset.mem_union] at hc ⊢
      exact fun v hv => hc v (Or.inr hv)
  have htcl : ∀ F : Finset V, IsClosed (t F) := fun F =>
    isClosed_biInter fun v _ => hU_closed v
  have htc : ∀ F : Finset V, IsCompact (t F) := fun F => (htcl F).isCompact
  have htn : ∀ F : Finset V, (t F).Nonempty := by
    intro F
    by_cases hF : F.Nonempty
    · let S : Finset V := F ∪ F.biUnion (N G hloc)
      have hS : S.Nonempty := hF.mono Finset.subset_union_left
      haveI : Nonempty S := Finset.Nonempty.coe_sort hS
      obtain ⟨c0, hc0⟩ := exists_unfriendly_finite (G.induce (S : Set V))
      let c : V → Bool := fun x => if hx : x ∈ S then c0 ⟨x, hx⟩ else false
      refine ⟨c, ?_⟩
      simp only [t, Set.mem_iInter]
      intro v hv
      have hvS : v ∈ S := Finset.mem_union_left _ hv
      have hv0 := hc0 ⟨v, hvS⟩
      change UnfAtC G hloc c v
      unfold UnfAtC
      have hbij_eq : ((N G hloc v).filter (fun w => c w = c v)).card =
          (Finset.univ.filter (fun w : S => (G.induce (S : Set V)).Adj ⟨v, hvS⟩ w ∧
            c0 w = c0 ⟨v, hvS⟩)).card := by
        refine Finset.card_bij (fun w hw => ⟨w, ?_⟩) ?_ ?_ ?_
        · have hwN : w ∈ N G hloc v := (Finset.mem_filter.mp hw).1
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v, hv, hwN⟩)
        · intro w hw
          rcases Finset.mem_filter.mp hw with ⟨hwN, hcw⟩
          have hwS : w ∈ S := Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v, hv, hwN⟩)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, comap_adj,
            Function.Embedding.coe_subtype]
          refine ⟨(mem_N_iff G hloc v w).mp hwN, ?_⟩
          simpa [c, hvS, hwS] using hcw
        · intro w₁ w₂ _ _ h
          exact congrArg Subtype.val h
        · intro ⟨w, hwS⟩ hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, comap_adj,
            Function.Embedding.coe_subtype] at hw
          refine ⟨w, Finset.mem_filter.mpr ⟨(mem_N_iff G hloc v w).mpr hw.1, ?_⟩, rfl⟩
          simpa [c, hvS, hwS] using hw.2
      have hbij_ne : ((N G hloc v).filter (fun w => c w ≠ c v)).card =
          (Finset.univ.filter (fun w : S => (G.induce (S : Set V)).Adj ⟨v, hvS⟩ w ∧
            c0 w ≠ c0 ⟨v, hvS⟩)).card := by
        refine Finset.card_bij (fun w hw => ⟨w, ?_⟩) ?_ ?_ ?_
        · have hwN : w ∈ N G hloc v := (Finset.mem_filter.mp hw).1
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v, hv, hwN⟩)
        · intro w hw
          rcases Finset.mem_filter.mp hw with ⟨hwN, hcw⟩
          have hwS : w ∈ S := Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v, hv, hwN⟩)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, comap_adj,
            Function.Embedding.coe_subtype]
          refine ⟨(mem_N_iff G hloc v w).mp hwN, ?_⟩
          simpa [c, hvS, hwS] using hcw
        · intro w₁ w₂ _ _ h
          exact congrArg Subtype.val h
        · intro ⟨w, hwS⟩ hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, comap_adj,
            Function.Embedding.coe_subtype] at hw
          refine ⟨w, Finset.mem_filter.mpr ⟨(mem_N_iff G hloc v w).mpr hw.1, ?_⟩, rfl⟩
          simpa [c, hvS, hwS] using hw.2
      rw [hbij_eq, hbij_ne]
      exact hv0
    · rw [Finset.not_nonempty_iff_eq_empty] at hF
      subst hF
      exact ⟨fun _ => false, by simp [t]⟩
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    t htd htn htc htcl
  refine ⟨c, fun v => ?_⟩
  have hv := Set.mem_iInter.mp hc {v}
  simpa [t, U] using hv

end LocallyFinite
end Aux_TC10_LocFin

open Classical Aux_TC10_LocFin SimpleGraph
open scoped Cardinal

theorem solution : ∀ {V : Type u} [Countable V] (G : SimpleGraph V),
    (∀ v, (G.neighborSet v).Finite) → ∀ r : Ordinal.{v}, PartitionerWins G (emptyPartition V) r := by
  intro V _ G hloc r
  obtain ⟨c, hc⟩ := exists_global_unfriendly G hloc
  have hwin : ∀ (α : Ordinal.{v}) (f : V → Option Bool),
      HasFiniteDomain f → (∀ x b, f x = some b → c x = b) → PartitionerWins G f α := by
    intro α
    induction α using Ordinal.induction with
    | h α ih =>
      intro f hfin hcons
      unfold HasFiniteDomain at hfin
      rw [PartitionerWins]
      intro v β hβ
      let D : Finset V := hfin.toFinset ∪ {v} ∪ N G hloc v
      let g : V → Option Bool := fun x => if x ∈ D then some (c x) else none
      have hg_ext : Extends f g := by
        intro x b hfx
        have hxD : x ∈ D := by
          apply Finset.mem_union_left
          apply Finset.mem_union_left
          rw [Set.Finite.mem_toFinset]
          simp [hfx]
        simp only [g, hxD, ↓reduceIte, Option.some.injEq]
        exact hcons x b hfx
      have hg_fin : HasFiniteDomain g := by
        refine (D.finite_toSet).subset fun x hx => ?_
        by_contra hxD
        have hxD' : x ∉ D := hxD
        exact hx (by simp [g, hxD'])
      have hg_cons : ∀ x b, g x = some b → c x = b := by
        intro x b hgx
        by_cases hxD : x ∈ D
        · simpa [g, hxD] using hgx
        · simp [g, hxD] at hgx
      have hg_unf : UnfriendlyAt G g v := by
        have hvD : v ∈ D := Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self v))
        refine ⟨c v, by simp [g, hvD], ?_⟩
        have hcard : ∀ b : Bool,
            #(NeighColored G g v (some b)) =
              (((N G hloc v).filter (fun w => c w = b)).card : Cardinal) := by
          intro b
          have heq : G.neighborSet v ∩ g ⁻¹' {some b} =
              ((N G hloc v).filter (fun w => c w = b) : Set V) := by
            ext w
            simp only [Set.mem_inter_iff, mem_neighborSet, Set.mem_preimage,
              Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_filter, mem_N_iff]
            constructor
            · rintro ⟨hadj, hgw⟩
              exact ⟨hadj, hg_cons w b hgw⟩
            · rintro ⟨hadj, hcw⟩
              have hwD : w ∈ D := Finset.mem_union_right _ ((mem_N_iff G hloc v w).mpr hadj)
              exact ⟨hadj, by simp [g, hwD, hcw]⟩
          unfold NeighColored
          rw [heq, Cardinal.mk_fintype]
          simp
        rw [hcard (c v), hcard (!c v)]
        have hcv := hc v
        unfold UnfAtC at hcv
        have hfilt : (N G hloc v).filter (fun w => c w = !c v) =
            (N G hloc v).filter (fun w => c w ≠ c v) := by
          apply Finset.filter_congr
          intro w _
          cases c w <;> cases c v <;> simp
        rw [hfilt]
        exact_mod_cast hcv
      exact ⟨g, ⟨hg_ext, hg_fin, hg_unf⟩, ih β hβ g hg_fin hg_cons⟩
  refine hwin r (emptyPartition V) ?_ ?_
  · simp [HasFiniteDomain, emptyPartition]
  · intro x b h
    simp [emptyPartition] at h
