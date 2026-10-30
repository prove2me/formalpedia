-- Prove2me | solution 1 for TaoBR.restrictionConjecture_of_bochnerRieszConjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T21:01:00.036675+00:00
-- url     : https://prove2.me/submissions/08fecafc-dfd7-44d9-b348-f63670f51884
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TaoBR
import Theorems.Thm_TaoBR_restr_zero_of_forall_br

namespace TaoBR

theorem restrictionConjecture_of_bochnerRieszConjecture_dev (n : ℕ) (hn : 2 ≤ n) :
    BochnerRieszConjecture n → RestrictionConjecture n := by
  intro hBR p hp1 hp
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 < ENNReal.ofReal (2 * n / (n + 1)) := by
    rw [ENNReal.one_lt_ofReal, lt_div_iff₀ (by positivity)]
    linarith
  exact restr_zero_of_forall_br n hn _ h1 le_rfl (fun ε hε => hBR _ h1.le ε hε) p hp1 hp

end TaoBR

theorem solution : type_of% @TaoBR.restrictionConjecture_of_bochnerRieszConjecture_dev := @TaoBR.restrictionConjecture_of_bochnerRieszConjecture_dev
