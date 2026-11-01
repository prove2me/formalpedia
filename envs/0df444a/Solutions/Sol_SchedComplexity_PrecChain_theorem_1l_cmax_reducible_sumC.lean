-- Prove2me | solution 1 for SchedComplexity.PrecChain.theorem_1l_cmax_reducible_sumC
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T12:08:40.95119+00:00
-- url     : https://prove2.me/submissions/9dd907dd-37bf-481a-a0c9-72ad1e0d1764
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SchedComplexity_PrecChain_Model
import Definitions.Def_SchedComplexity_PrecChain_Construction
import Definitions.Def_SchedComplexity_PrecChain_Languages
import Theorems.Thm_SchedComplexity_PrecChain_chainExtend_encoding_reduction
import Theorems.Thm_SchedComplexity_PrecChain_cmax_le_imp_sumC_le
import Theorems.Thm_SchedComplexity_PrecChain_cmax_gt_imp_sumC_gt
import Theorems.Thm_SchedComplexity_PrecChain_cmax_le_n_pstar

open SchedComplexity.PrecChain

theorem solution (pstar : ℕ) (hpstar : 1 ≤ pstar) :
    CookPvsNP.PolyReducible (cmaxLang pstar) (sumCLang pstar) := by
  rcases chainExtend_encoding_reduction pstar hpstar with ⟨f, hf_poly, hf⟩
  refine ⟨f, hf_poly, fun c => ?_⟩
  rw [← hf c]
  constructor
  · rintro ⟨I, y', hI, hcmax, rfl⟩
    by_cases hy' : y' ≤ I.n * pstar
    · exact Or.inl ⟨I, y', hI, hy', cmax_le_imp_sumC_le pstar I hI y' hy' hcmax, rfl⟩
    · exact Or.inr ⟨I, y', hI, Nat.lt_of_not_ge hy', rfl⟩
  · rintro (⟨I, y', hI, hy', ⟨σ, hfeas, htot⟩, rfl⟩ | ⟨I, y', hI, hy', rfl⟩)
    · refine ⟨I, y', hI, ?_, rfl⟩
      by_contra hnot
      have hgt := cmax_gt_imp_sumC_gt pstar I hI y' hy' hnot σ hfeas
      exact not_lt_of_ge htot hgt
    · refine ⟨I, y', hI, ?_, rfl⟩
      rcases cmax_le_n_pstar pstar I hI with ⟨σ, hfeas, hcomp⟩
      exact ⟨σ, hfeas, fun j => le_trans (hcomp j) (Nat.le_of_lt hy')⟩
