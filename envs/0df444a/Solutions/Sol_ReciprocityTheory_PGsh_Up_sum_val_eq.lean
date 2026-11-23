-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.sum_val_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:18:15.84222+00:00
-- url     : https://prove2.me/submissions/3e181408-3c58-4085-9e64-1144c4816756

import Definitions.Def_ReciprocityTheory_DualLattices_DualLenStatement
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {n : ℕ} (j : ℕ) (f : Fin n → R) :
    ∑ k : Fin n, (if (k : ℕ) = j then f k else 0) = if h : j < n then f ⟨j, h⟩ else 0 := by
  split_ifs with h
  · rw [Fintype.sum_eq_single ⟨j, h⟩ (fun k hk => if_neg fun h' => hk (Fin.ext h'))]
    exact if_pos rfl
  · exact Finset.sum_eq_zero fun k _ => if_neg fun (h' : (k : ℕ) = j) => h (h' ▸ k.isLt)
end ReciprocityTheory.PGsh.Up
