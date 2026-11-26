-- Prove2me | solution 1 for TunnellMap.OrderedGenerator.q_mem_search_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:18:03.649739+00:00
-- url     : https://prove2.me/submissions/91452172-2dfa-4a99-93b6-6d8af9bf32f7

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator

set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}
namespace TunnellMap.OrderedGenerator
theorem _root_.solution {n A q : ℤ} (hn : 0 < n) (hA : 0 < A)
    (hq : q ^ 2 * A < n) : -n ≤ q ∧ q ≤ n := by
  have hqSqLe : q ^ 2 ≤ q ^ 2 * A := by
    have hAone : 1 ≤ A := hA
    nlinarith [sq_nonneg q, mul_nonneg (sq_nonneg q) (sub_nonneg.mpr (by omega : 0 ≤ A - 1))]
  have hqSqLt : q ^ 2 < n := lt_of_le_of_lt hqSqLe hq
  have hnSq : n ≤ n ^ 2 := by
    nlinarith [sq_nonneg (n - 1)]
  have hsq : q ^ 2 < n ^ 2 := hqSqLt.trans_le hnSq
  have habs : |q| < n := abs_lt_of_sq_lt_sq hsq hn.le
  exact ⟨(abs_lt.mp habs).1.le, (abs_lt.mp habs).2.le⟩
end TunnellMap.OrderedGenerator
