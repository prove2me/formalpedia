-- Prove2me | solution 1 for PerfectGraph.isPerfect_iff_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:43:22.772979+00:00
-- url     : https://prove2.me/submissions/1622fe6a-6e22-450c-b339-d032aeb05dc5

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
public import Definitions.Def_PerfectLib_Perfect
public import Theorems.Thm_PerfectGraph_card_le_of_isColOn
public import Theorems.Thm_PerfectGraph_chromaticNumber_eq_iff_isColOn
public import Theorems.Thm_PerfectGraph_gasparian


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PerfectGraph
variable {V : Type*}
namespace PerfectGraph
theorem _root_.solution [Finite V] (G : SimpleGraph V) :
    IsPerfect G ↔ ∀ S : Finset V,
      S.card ≤ (G.induce (S : Set V)).indepNum * (G.induce (S : Set V)).cliqueNum := by
  classical
  have hP : IsPerfect G ↔ ∀ S : Finset V, IsColOn G S (G.induce (S : Set V)).cliqueNum := by
    constructor
    · intro h S
      exact (chromaticNumber_eq_iff_isColOn G S).1 (h S)
    · intro h S
      obtain ⟨F, rfl⟩ := S.toFinite.exists_finset_coe
      exact (chromaticNumber_eq_iff_isColOn G F).2 (h F)
  rw [hP]
  constructor
  · intro h S
    exact card_le_of_isColOn G (h S)
  · intro h S
    induction S using Finset.strongInduction with
    | H S ih =>
      by_contra hn
      have h1 := gasparian G hn ih
      have h2 := h S
      omega
end PerfectGraph
