-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_le_tmax_639e995f5930
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:19.22104+00:00
-- url     : https://prove2.me/submissions/aafd0c19-fc47-4a72-942c-8bc8c0569791

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_RegMaxReindex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory
open ReciprocityTheory.AnForm.A (regMax tmax kθ)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {ι : Type*} [Fintype ι] [Nonempty ι] (t : ι → ℝ) (i : ι) : t i ≤ tmax t :=
  Finset.le_sup' t (Finset.mem_univ i)
end GroundTheory.Heights₂.Heights.Regular
