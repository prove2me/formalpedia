-- Prove2me | solution 1 for PrimalDualLDR.Multistage.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:12:47.60827+00:00
-- url     : https://prove2.me/submissions/748b62c2-174c-4d95-a644-361ef6c32c57

import Mathlib
import Definitions.Def_PrimalDualLDR_Multistage_Basic
import Definitions.Def_PrimalDualLDR_Multistage_Setting
import Definitions.Def_PrimalDualLDR_Multistage_Problems
import Theorems.Thm_PrimalDualLDR_Multistage_theorem_3_primal
import Theorems.Thm_PrimalDualLDR_Multistage_theorem_3_dual

open MeasureTheory Matrix

theorem solution (σ : PrimalDualLDR.Multistage.Setting) (hσ : σ.Standing) (hM : σ.LinearCondMean)
    (hsf : σ.StrictlyFeasible) :
    σ.valMSPu = σ.valLP42 ∧
      ((2 ≤ σ.k ∨ ∃ i : Fin σ.l, 2 ≤ i.val ∧ σ.W i ≠ 0) → σ.valMSPl = σ.valLP46) :=
  ⟨PrimalDualLDR.Multistage.theorem_3_primal σ hσ,
    fun hW => PrimalDualLDR.Multistage.theorem_3_dual σ hσ hM hsf hW⟩
