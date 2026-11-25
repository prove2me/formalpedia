-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionsGeneric_rowsPoly_ne_zero_3cd0323fbce7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:26:34.972011+00:00
-- url     : https://prove2.me/submissions/40351bd3-b05e-4c42-a06f-7dcc11454ec0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnitaryZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionsGeneric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionsGeneric_eval_rowsPoly_068165e19a30
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionsGeneric_exists_rows_eq_af6599633ba3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsGeneric
open MvPolynomial Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsGeneric
theorem _root_.solution {n d : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : F ∈ unitaryGroup (Fin n) ℂ)
    {s : Fin d → Fin n} (hs : Function.Injective s) {p : MvPolynomial (Fin d × Fin n) ℂ}
    {A : Matrix (Fin d) (Fin n) ℂ} (hA : eval (entries A) p ≠ 0) : rowsPoly F s p ≠ 0 := by
  obtain ⟨U, hU⟩ := exists_rows_eq hF hs A
  intro h
  apply hA
  rw [← hU, ← eval_rowsPoly, h, map_zero]
end GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsGeneric
