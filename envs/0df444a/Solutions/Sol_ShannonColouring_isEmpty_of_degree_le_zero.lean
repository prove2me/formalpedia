-- Prove2me | solution 1 for ShannonColouring.isEmpty_of_degree_le_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:02:11.803887+00:00
-- url     : https://prove2.me/submissions/7f54bcae-6910-4dc8-9661-a3b2449d9693

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity
public import Theorems.Thm_ShannonColouring_shannon


set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
namespace ShannonColouring
theorem _root_.solution {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (ends : ι → V × V) (hloop : ∀ i, (ends i).1 ≠ (ends i).2) (hΔ : ∀ v, degree ends v ≤ 0) :
    IsEmpty ι := by
  obtain ⟨c, -⟩ := shannon ends hloop 0 hΔ
  exact ⟨fun i => (c i).elim0⟩
end ShannonColouring
