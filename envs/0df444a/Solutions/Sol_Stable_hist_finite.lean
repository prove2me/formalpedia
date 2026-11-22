-- Prove2me | solution 1 for Stable.hist_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:49:12.822693+00:00
-- url     : https://prove2.me/submissions/08ac09ee-a44d-47b9-a2cd-2cac238e2b9e

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
import Theorems.Thm_Stable_hist_config
import Theorems.Thm_Stable_hist_least
import Theorems.Thm_Stable_hist_mem
import Theorems.Thm_Stable_hist_subset


set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
namespace Stable
theorem _root_.solution (G : GES L) (hF : Stable G.toFamily) {c : Set G.Event}
    (hc : G.isConf c) {x : G.Event} (hx : x ∈ c) :
    (hist G.toFamily c x).Finite := by
  induction hn : G.rank c x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    obtain ⟨k, hk⟩ : ∃ k, G.rank c x = k + 1 := by
      have : G.rank c x ≠ 0 := by
        intro h0
        have hmem := GES.rank_mem (hc.2 x hx)
        rw [h0] at hmem
        exact hmem
      exact ⟨G.rank c x - 1, by omega⟩
    obtain ⟨-, X, hXsub, hXen⟩ := hk ▸ GES.rank_mem (hc.2 x hx)
    have hXc : ∀ g ∈ X, g ∈ c := fun g hg => GES.secApprox_subset _ (hXsub hg)
    have hXlt : ∀ g ∈ X, G.rank c g < G.rank c x :=
      fun g hg => hk ▸ Nat.lt_succ_of_le (GES.rank_le (hXsub hg))
    set U : Set G.Event := ⋃ g ∈ X, hist G.toFamily c g with hU
    have hUfin : U.Finite :=
      Set.Finite.biUnion X.finite_toSet fun g hg =>
        ih _ (hn ▸ hXlt g hg) (hXc g hg) rfl
    have hUc : U ⊆ c := by
      rintro y ⟨-, ⟨g, rfl⟩, -, ⟨hg, rfl⟩, hy⟩
      exact hist_subset hc (hXc g hg) hy
    have hXU : (X : Set G.Event) ⊆ U := fun g hg => Set.mem_biUnion hg hist_mem
    have hconf : G.isConf (U ∪ {x}) := by
      refine ⟨fun W hW => hc.1 W (hW.trans ?_), ?_⟩
      · rintro y (hy | hy)
        · exact hUc hy
        · exact (Set.mem_singleton_iff.mp hy) ▸ hx
      · have hsec : ∀ y ∈ U, ∃ m, y ∈ G.secApprox (U ∪ {x}) m := by
          rintro y ⟨-, ⟨g, rfl⟩, -, ⟨hg, rfl⟩, hy⟩
          obtain ⟨m, hm⟩ := (hist_config hF hc (hXc g hg)).2 y hy
          exact ⟨m, GES.secApprox_mono_set
            (Set.Subset.trans (fun z hz => Set.mem_biUnion hg hz) Set.subset_union_left) m hm⟩
        rintro y (hy | hy)
        · exact hsec y hy
        · obtain ⟨N, hN⟩ := GES.exists_bound (X := X) fun g hg => hsec g (hXU hg)
          exact ⟨N + 1, (Set.mem_singleton_iff.mp hy) ▸ Or.inr rfl, X, hN,
            (Set.mem_singleton_iff.mp hy) ▸ hXen⟩
    exact (hUfin.union (Set.finite_singleton x)).subset
      (hist_least hconf (by
        rintro y (hy | hy)
        · exact hUc hy
        · exact (Set.mem_singleton_iff.mp hy) ▸ hx) (Or.inr rfl))
end Stable
