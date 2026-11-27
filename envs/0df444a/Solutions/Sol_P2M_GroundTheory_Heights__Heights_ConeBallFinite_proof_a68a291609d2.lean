-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeBallFinite_proof_a68a291609d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:54:27.704895+00:00
-- url     : https://prove2.me/submissions/ba426ddd-617b-4969-b0dc-63ccec6bcf34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowFormHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeBallFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ConeBallFinite
theorem _root_.solution (hMass : ConeIntegralMass.Statement) : ConeBallFinite.Statement := by
  intro n e h W f hW hf
  obtain ⟨δ, hδ1, hδ⟩ := hf.exists_multiHomog hW
  have hm := hMass n e δ h W f hW hf hδ
  rw [lt_top_iff_ne_top]
  intro hinf
  unfold coneIntegral at hm
  change (∫ y in coneBall h W, (1 : ℝ) ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))) / _ =
    (δ : ℝ) at hm
  rw [setIntegral_const, measureReal_def, hinf, ENNReal.toReal_top, zero_smul, zero_div] at hm
  have hδ0 : (δ : ℝ) ≠ 0 := by exact_mod_cast (by omega : δ ≠ 0)
  exact hδ0 hm.symm
end ConeBallFinite
end GroundTheory.Heights₂.Heights
