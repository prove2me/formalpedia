-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.ne_zero_of_toMK_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:22.0598+00:00
-- url     : https://prove2.me/submissions/4bd8061a-9363-4774-83a1-de92153d4700

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_Branch
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_BlockCombStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_Statement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.TR ReciprocityTheory.ChartRestriction.TR.Weyl
open ReciprocityTheory.ChartRestriction.DS.S7
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} (k : KG ε) {t : Fin n → ℂ}
    (hk : toMK k = Matrix.diagonal t) (i : Fin n) : t i ≠ 0 := by
  unfold toMK toM at hk
  have hu : IsUnit (Matrix.diagonal t) := by
    rw [← hk]
    first
    | exact Units.isUnit _
    | exact (unitary.toUnits _).isUnit
    | exact (Matrix.isUnit_iff_isUnit_det _).mpr (Units.isUnit _)
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hu
  rw [Matrix.det_diagonal] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet.ne_zero i (Finset.mem_univ i)
end ReciprocityTheory.ChartRestriction.TR.Weyl
