-- Prove2me | solution 1 for SizeRamsey.k33MinusEdge_arrows_matching2_c4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:59.397422+00:00
-- url     : https://prove2.me/submissions/f653b89e-263a-40db-939c-d77aa89938ba

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper
public import Theorems.Thm_SizeRamsey_Plan_star_or_empty
public import Theorems.Thm_SizeRamsey_Plan_k33_square_avoids_vertex
public import Theorems.Thm_SizeRamsey_Plan_k33_triangle_free


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
namespace SizeRamsey
theorem _root_.solution :
    ∀ R : SimpleGraph (Fin 6), R ≤ k33MinusEdge →
      HasMatching2 R ∨ HasC4 (k33MinusEdge \ R) := by
  intro R hR
  by_cases hm : HasMatching2 R
  · exact Or.inl hm
  right
  have htri : ∀ a b c, R.Adj a b → R.Adj b c → ¬ R.Adj c a :=
    fun a b c hab hbc hca => Plan.k33_triangle_free a b c (hR hab) (hR hbc) (hR hca)
  rcases Plan.star_or_empty R htri hm with hbot | ⟨v, hv⟩
  · obtain ⟨f, ⟨hf, h01, h12, h23, h30⟩, -⟩ := Plan.k33_square_avoids_vertex 0
    subst hbot
    exact ⟨f, hf, by simpa using h01, by simpa using h12, by simpa using h23,
      by simpa using h30⟩
  · obtain ⟨f, ⟨hf, h01, h12, h23, h30⟩, hfv⟩ := Plan.k33_square_avoids_vertex v
    have blue : ∀ a b : Fin 4, k33MinusEdge.Adj (f a) (f b) →
        (k33MinusEdge \ R).Adj (f a) (f b) := fun a b h =>
      ⟨h, fun hr => (hv _ _ hr).elim (hfv a) (hfv b)⟩
    exact ⟨f, hf, blue _ _ h01, blue _ _ h12, blue _ _ h23, blue _ _ h30⟩
end SizeRamsey
