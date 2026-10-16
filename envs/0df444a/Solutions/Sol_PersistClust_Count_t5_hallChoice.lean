-- Prove2me | solution 1 for PersistClust.Count.t5_hallChoice
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-15T13:37:29.009346+00:00
-- url     : https://prove2.me/submissions/3d99714a-70d4-40fd-a59d-645428be6f2d

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

/-- Infinite Hall marriage by finite reduction: a family of finite fiber
sets G a over any type S satisfying the Hall condition on every finite
subset (each finite demand set s is covered in encard by the union of
its fibers) admits a globally injective choice function picking one
element from each fiber. Reduction: the finite Hall theorem applied to
the toFinsets, with encard-to-card transfers on both sides. -/
theorem solution {S T : Type} (G : S → Set T)
    (hfin : ∀ a, (G a).Finite)
    (hhall : ∀ s : Set S, s.Finite → s.encard ≤ (⋃ x ∈ s, G x).encard) :
    ∃ f : S → T, Function.Injective f ∧ ∀ a, f a ∈ G a := by
  classical
  have hballs : ∀ s : Finset S,
      s.card ≤ (s.biUnion (fun a => (hfin a).toFinset)).card := by
    intro s
    have hsub : (⋃ x ∈ (↑s : Set S), G x) ⊆
        (↑(s.biUnion (fun a => (hfin a).toFinset)) : Set T) := by
      intro y hy
      obtain ⟨x, hx, hgy⟩ := Set.mem_iUnion₂.1 hy
      exact Finset.mem_coe.2
        (Finset.mem_biUnion.2 ⟨x, Finset.mem_coe.1 hx,
          (Set.Finite.mem_toFinset (hfin x)).2 hgy⟩)
    have hball : (↑(s.card) : ℕ∞) ≤
        (↑((s.biUnion (fun a => (hfin a).toFinset)).card) : ℕ∞) :=
      calc (↑(s.card) : ℕ∞) = (↑s : Set S).encard :=
              (Set.encard_coe_eq_coe_finsetCard s).symm
        _ ≤ (⋃ x ∈ (↑s : Set S), G x).encard := hhall (↑s : Set S) s.finite_toSet
        _ ≤ (↑(s.biUnion (fun a => (hfin a).toFinset)) : Set T).encard :=
            Set.encard_le_encard hsub
        _ = (↑((s.biUnion (fun a => (hfin a).toFinset)).card) : ℕ∞) :=
            Set.encard_coe_eq_coe_finsetCard _
    exact ENat.natCast_le_natCast.1 hball
  obtain ⟨f, hfinj, hfmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective
      (t := fun a => (hfin a).toFinset)).mp hballs
  exact ⟨f, hfinj, fun a => (Set.Finite.mem_toFinset (hfin a)).mp (hfmem a)⟩
