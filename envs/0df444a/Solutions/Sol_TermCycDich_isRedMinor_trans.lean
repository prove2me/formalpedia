-- Prove2me | solution 1 for TermCycDich.isRedMinor_trans
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:48:47.416563+00:00
-- url     : https://prove2.me/submissions/83532c01-318c-4972-94c7-6eacf3dd73ff

import Mathlib
import Definitions.Def_TermCycDich_IsRedMinor

namespace AuxRedMinorTrans

lemma induce_reachable_of_subset {V : Type} {K : SimpleGraph V} {S₁ S₂ : Set V}
    (hsub : S₁ ⊆ S₂) {x y : S₁} (h : (K.induce S₁).Reachable x y) :
    (K.induce S₂).Reachable ⟨x.1, hsub x.2⟩ ⟨y.1, hsub y.2⟩ := by
  rcases h with ⟨p⟩
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hadj _ ih =>
    have hadj₂ : (K.induce S₂).Adj ⟨a.1, hsub a.2⟩ ⟨b.1, hsub b.2⟩ := hadj
    exact (SimpleGraph.Adj.reachable hadj₂).trans ih

end AuxRedMinorTrans

theorem solution {U W V : Type} {H : SimpleGraph U} {B : Set U} {G : SimpleGraph W}
    {R : Set W} {K : SimpleGraph V} {T : Set V} (h₁ : TermCycDich.IsRedMinor H B G R)
    (h₂ : TermCycDich.IsRedMinor G R K T) : TermCycDich.IsRedMinor H B K T := by
  rcases h₁ with ⟨β₁, hconn₁, hdisj₁, hadj₁, hred₁⟩
  rcases h₂ with ⟨β₂, hconn₂, hdisj₂, hadj₂, hred₂⟩
  let β : U → Set V := fun u => ⋃ w ∈ β₁ u, β₂ w
  refine ⟨β, ?_, ?_, ?_, ?_⟩
  · intro u
    obtain ⟨w₀, hw₀⟩ := (hconn₁ u).1
    obtain ⟨v₀, hv₀⟩ := (hconn₂ w₀).1
    have hne : (β u).Nonempty := ⟨v₀, Set.mem_biUnion hw₀ hv₀⟩
    refine ⟨hne, ?_⟩
    have hsame : ∀ {w : W} (hw : w ∈ β₁ u) {x y : V} (hx : x ∈ β₂ w) (hy : y ∈ β₂ w),
        (K.induce (β u)).Reachable ⟨x, Set.mem_biUnion hw hx⟩ ⟨y, Set.mem_biUnion hw hy⟩ := by
      intro w hw x y hx hy
      exact AuxRedMinorTrans.induce_reachable_of_subset
        (fun z hz => Set.mem_biUnion hw hz) ((hconn₂ w).2.preconnected ⟨x, hx⟩ ⟨y, hy⟩)
    have hwalk : ∀ {a b : β₁ u} (p : (G.induce (β₁ u)).Walk a b)
        {x y : V} (hx : x ∈ β₂ a.1) (hy : y ∈ β₂ b.1),
        (K.induce (β u)).Reachable
          ⟨x, Set.mem_biUnion a.2 hx⟩ ⟨y, Set.mem_biUnion b.2 hy⟩ := by
      intro a b p
      induction p with
      | @nil d =>
        intro x y hx hy
        exact hsame d.2 hx hy
      | @cons a b c hadj _ ih =>
        intro x y hx hy
        obtain ⟨z₁, hz₁, z₂, hz₂, hkz⟩ := hadj₂ a.1 b.1 hadj
        have r₁ := hsame a.2 hx hz₁
        have hadj_ind : (K.induce (β u)).Adj
            ⟨z₁, Set.mem_biUnion a.2 hz₁⟩ ⟨z₂, Set.mem_biUnion b.2 hz₂⟩ := hkz
        have r₂ := SimpleGraph.Adj.reachable hadj_ind
        have r₃ := ih hz₂ hy
        exact r₁.trans (r₂.trans r₃)
    have : Nonempty (β u) := ⟨⟨v₀, Set.mem_biUnion hw₀ hv₀⟩⟩
    refine SimpleGraph.Connected.mk ?_
    intro ⟨x, hx⟩ ⟨y, hy⟩
    rcases Set.mem_iUnion₂.mp hx with ⟨w₁, hw₁, hx₁⟩
    rcases Set.mem_iUnion₂.mp hy with ⟨w₂, hw₂, hy₂⟩
    rcases (hconn₁ u).2.preconnected ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ with ⟨p⟩
    exact hwalk p hx₁ hy₂
  · intro u₁ u₂ hu
    rw [Set.disjoint_left]
    intro v hv₁ hv₂
    rcases Set.mem_iUnion₂.mp hv₁ with ⟨w₁, hw₁, hvw₁⟩
    rcases Set.mem_iUnion₂.mp hv₂ with ⟨w₂, hw₂, hvw₂⟩
    by_cases hw : w₁ = w₂
    · subst hw
      exact Set.disjoint_left.mp (hdisj₁ hu) hw₁ hw₂
    · exact Set.disjoint_left.mp (hdisj₂ hw) hvw₁ hvw₂
  · intro u₁ u₂ hadj
    obtain ⟨w₁, hw₁, w₂, hw₂, hgw⟩ := hadj₁ u₁ u₂ hadj
    obtain ⟨x, hx, y, hy, hxy⟩ := hadj₂ w₁ w₂ hgw
    exact ⟨x, Set.mem_biUnion hw₁ hx, y, Set.mem_biUnion hw₂ hy, hxy⟩
  · intro u huB
    obtain ⟨w, hw₁, hwR⟩ := hred₁ u huB
    obtain ⟨v, hv₂, hvT⟩ := hred₂ w hwR
    exact ⟨v, Set.mem_biUnion hw₁ hv₂, hvT⟩
