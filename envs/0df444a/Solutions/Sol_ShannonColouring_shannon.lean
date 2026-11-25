-- Prove2me | solution 1 for ShannonColouring.shannon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:54:11.286485+00:00
-- url     : https://prove2.me/submissions/6106721f-6d5c-48e7-92f7-f369abce9883

module
public import Definitions.Def_ShannonColouring_Kempe
public import Definitions.Def_ShannonColouring_Shannon
public import Theorems.Thm_ShannonColouring_exists_properOn

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
open Classical
variable {V ι : Type*} [DecidableEq V] [Fintype ι]
namespace ShannonColouring
theorem _root_.solution {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] (ends : ι → V × V)
    (hloop : ∀ i, (ends i).1 ≠ (ends i).2) (Δ : ℕ) (hΔ : ∀ v, degree ends v ≤ Δ) :
    ∃ c : ι → Fin (3 * Δ / 2), IsProperEdgeColouring ends c := by
  obtain ⟨c, hc⟩ := exists_properOn hloop Δ hΔ Finset.univ
  exact ⟨c, fun i j hij hv => hc i (Finset.mem_univ i) j (Finset.mem_univ j) hij hv⟩
end ShannonColouring
