-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_rowsPoly_ne_zero_ff91ab6724f3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:59:26.714631+00:00
-- url     : https://prove2.me/submissions/de8b4d17-9cf6-4270-90c0-a7568e942887

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnitaryZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericProjectionFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_eval_rowsPoly_9010d8778d16
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_exists_rows_eq_5673bfa09b10

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution {n d : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : F ∈ unitaryGroup (Fin n) ℂ)
    {s : Fin d → Fin n} (hs : Function.Injective s) {p : MvPolynomial (Fin d × Fin n) ℂ}
    {A : Matrix (Fin d) (Fin n) ℂ} (hA : eval (entries A) p ≠ 0) : rowsPoly F s p ≠ 0 := by
  obtain ⟨U, hU⟩ := exists_rows_eq hF hs A
  intro h
  apply hA
  rw [← hU, ← eval_rowsPoly, h, map_zero]
end GroundTheory.Heights₂.Heights.ComplexSets
