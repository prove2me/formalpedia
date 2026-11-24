-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_sq_norm_eq_re_im_995b20f7781c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:48.413384+00:00
-- url     : https://prove2.me/submissions/651b2ff6-a1e0-4a2e-8b06-af5daa97e7c0

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_PGreenMassReplaceLevi
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open Filter Topology
open ReciprocityTheory.AnForm (levi levi_add_smul levi_re_analytic)
noncomputable section
variable {ι : Type} [Fintype ι]
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
theorem _root_.solution (c : ℂ) : ‖c‖ ^ 2 = c.re ^ 2 + 1 * c.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring
end GroundTheory.Heights₂.Heights.AnalyticLimit
