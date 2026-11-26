-- Prove2me | solution 1 for QuadraticFloor.osum_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:21.227861+00:00
-- url     : https://prove2.me/submissions/5e85fe04-8c57-47a0-95af-41df38759d0e

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution {t : ℤ} {g g' : ℤ → ℤ} (h : ∀ j, |j| ≤ |t| → g j = g' j) :
    osum t g = osum t g' := by
  unfold osum
  split_ifs with ht
  · have ha := abs_of_nonneg ht
    exact sum_congr rfl fun j hj => h j (by
      rw [mem_Ico] at hj; rw [abs_le, ha]; constructor <;> omega)
  · have ha := abs_of_neg (show t < 0 by omega)
    congr 1
    exact sum_congr rfl fun j hj => h j (by
      rw [mem_Ico] at hj; rw [abs_le, ha]; constructor <;> omega)
end QuadraticFloor
