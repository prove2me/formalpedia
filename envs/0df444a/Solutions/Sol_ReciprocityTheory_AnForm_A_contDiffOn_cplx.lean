-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.contDiffOn_cplx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:04:12.939674+00:00
-- url     : https://prove2.me/submissions/89bf4d88-5390-468b-a53e-ca4c00e6aa04

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsIbp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} {a : (Fin D → ℂ) → ℝ} {U : Set (Fin D → ℂ)} {n : WithTop ℕ∞}
    (ha : ContDiffOn ℝ n a U) : ContDiffOn ℝ n (cplx a) U := by
    have h := Complex.ofRealCLM.contDiff.comp_contDiffOn ha
    refine h.congr fun z _ => ?_
    simp [cplx]
end ReciprocityTheory.AnForm.A
