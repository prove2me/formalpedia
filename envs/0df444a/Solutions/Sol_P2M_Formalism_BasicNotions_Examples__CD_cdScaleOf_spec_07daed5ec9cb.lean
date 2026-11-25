-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_cdScaleOf_spec_07daed5ec9cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:58:53.084595+00:00
-- url     : https://prove2.me/submissions/53ba6f09-5bbd-47ec-8ba4-cf1915c1fa89

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_SignSplitEquivInl
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_phi_cont_8ff9fa0bcb35
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_phi_symm_cont_471bef33b37b
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_preimage_ball_8484a5535331
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_ball_meas_50812612218f
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_ball_ne_zero_4b25adaa3e5f
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_ball_ne_top_7f8ee292491b
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_eq_nT_b82156c5084c
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_eq_nF_0bc4fada971d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Matrix Formalism.REAL Formalism.UG.P Topology
open scoped ENNReal NNReal
variable (C : CDHaar)
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution {n P Q : ℕ} (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) :
    0 < cdScaleOf C n ε ∧ (C.cd P Q).map (phi ε e h1 h2) = cdScaleOf C n ε • muG ε := by
  obtain rfl := eq_nT ε e h1 h2
  obtain rfl := eq_nF ε e h1 h2
  haveI := C.haar (nT ε) (nF ε)
  haveI : (muG ε).IsHaarMeasure := by unfold muG; infer_instance
  haveI : ((C.cd (nT ε) (nF ε)).map (phi ε e h1 h2)).IsHaarMeasure :=
    (phi ε e h1 h2).isHaarMeasure_map (C.cd (nT ε) (nF ε)) (phi_cont ε e h1 h2)
      (phi_symm_cont ε e h1 h2)
  set ν := (C.cd (nT ε) (nF ε)).map (phi ε e h1 h2) with hν_def
  have hν : ν = Measure.haarScalarFactor ν (muG ε) • muG ε :=
    Measure.isMulLeftInvariant_eq_smul ν (muG ε)
  have hB : ν {a | hsG a ≤ rad n} = C.cd (nT ε) (nF ε) (TR (nT ε) (nF ε) (rad n)) := by
    rw [hν_def, Measure.map_apply (phi_cont ε e h1 h2).measurable (ball_meas ε _), preimage_ball]
  have hscale : cdScaleOf C n ε = Measure.haarScalarFactor ν (muG ε) := by
    unfold cdScaleOf
    rw [← hB]
    conv_lhs => rw [hν]
    rw [Measure.coe_nnreal_smul_apply, ENNReal.mul_div_cancel_right (ball_ne_zero ε) (ball_ne_top ε),
      ENNReal.toNNReal_coe]
  refine ⟨?_, ?_⟩
  · rw [hscale]
    exact Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  · rw [hscale]
    exact hν
end Formalism.BasicNotions.Examples₂.CD
