-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_identity_frame_hyp_7561e60bfbde
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:07:46.129898+00:00
-- url     : https://prove2.me/submissions/3c1eac27-1b19-4cd3-8d1e-266ba3cd643c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements

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
open MeasureTheory Metric Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli coordDiv limsupExt regMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsCompatChart)
open ReciprocityTheory.AnForm (levi)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution (n g : ℕ) :
    (∀ p q, AnalyticOnNhd ℂ (fun _ : Fin n → ℂ => (1 : Matrix (Fin g) (Fin g) ℂ) p q) (ball 0 1)) ∧
      ∀ _z ∈ ball (0 : Fin n → ℂ) 1, (1 : Matrix (Fin g) (Fin g) ℂ).rank = g :=
  ⟨fun _ _ => analyticOnNhd_const, fun _ _ => by simp [Matrix.rank_one]⟩
end GroundTheory.Heights₂.Heights.Regular
