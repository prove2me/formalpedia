-- Prove2me | solution 1 for SemigroupBetti.GenData.sel_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:09:37.179768+00:00
-- url     : https://prove2.me/submissions/12b27288-2b33-47fd-8b9b-ee00c35a7cbf

module
public import Definitions.Def_SemigroupBetti_Critical
public import Definitions.Def_SemigroupBetti_Partition

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} {K : Finset (Fin 4)} (h : ∃ z : Fin 4 → ℕ, G.nu z = d ∧ supp z = K) :
    G.nu (G.sel d K) = d ∧ supp (G.sel d K) = K := by
  classical
  unfold sel; rw [dif_pos h]; exact h.choose_spec
end SemigroupBetti.GenData
