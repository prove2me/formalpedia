-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_tmax_comp_equiv_31ff04f21355
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:49:50.18864+00:00
-- url     : https://prove2.me/submissions/f4403ec3-b485-468d-b1c8-64466c5a87b8

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_RegMaxReindex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_le_tmax_639e995f5930
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_tmax_le_5df8adbdca5e

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
theorem _root_.solution {κ ι : Type*} [Fintype κ] [Nonempty κ] [Fintype ι] [Nonempty ι]
    (e : κ ≃ ι) (t : ι → ℝ) : tmax (t ∘ e) = tmax t := by
  refine le_antisymm (tmax_le fun k => le_tmax t (e k)) (tmax_le fun i => ?_)
  have := le_tmax (t ∘ e) (e.symm i)
  simpa using this
end GroundTheory.Heights₂.Heights.Regular
