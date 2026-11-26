-- Prove2me | solution 1 for SemigroupBetti.GenData.pairsOf_antichain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:18:19.72327+00:00
-- url     : https://prove2.me/submissions/0cbbf628-6e5a-4e2d-87a8-47559b342375

module
public import Definitions.Def_SemigroupBetti_Arith
public import Definitions.Def_SemigroupBetti_Exceptional
public import Theorems.Thm_SemigroupBetti_GenData_sel_le_of_coords
public import Theorems.Thm_SemigroupBetti_GenData_sel_antichain


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {F : Finset ℕ} {K : Finset (Fin 4)} {i k : Fin 4} (hik : i ≠ k)
    (hKe : K = {i, k}) (hF : ∀ d ∈ F, G.IsSplit d K) : IsPairAntichain (G.pairsOf F K i k) := by
  have hK : K.card = 2 := by rw [hKe]; exact card_pair hik
  intro x hx y hy h1 h2
  obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
  obtain ⟨d', hd', rfl⟩ := mem_image.1 hy
  by_cases hne : d = d'
  · rw [hne]
  · exact absurd (G.sel_le_of_coords hKe hK (hF d hd) (hF d' hd') h1 h2)
      (G.sel_antichain hK (hF d hd) (hF d' hd') hne)
end SemigroupBetti.GenData
