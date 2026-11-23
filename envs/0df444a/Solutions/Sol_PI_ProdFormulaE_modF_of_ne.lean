-- Prove2me | solution 1 for PI.ProdFormulaE.modF_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:25:40.303832+00:00
-- url     : https://prove2.me/submissions/ed41585c-e987-4420-b477-2bb8cad28630

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormMod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel
open PI PI.ProdFormulaE
variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
namespace PI.ProdFormulaE
theorem _root_.solution {a : K} (h : a ≠ 0) :
    modF K a = ((distribHaarChar K (Units.mk0 a h) : NNReal) : ℝ) := by
  unfold modF
  rw [dif_neg h]
end PI.ProdFormulaE
