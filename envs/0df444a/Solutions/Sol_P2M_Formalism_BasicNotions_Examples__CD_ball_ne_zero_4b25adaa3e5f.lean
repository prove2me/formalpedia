-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_ball_ne_zero_4b25adaa3e5f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:40:35.872494+00:00
-- url     : https://prove2.me/submissions/976ccec2-fbf8-41e9-82e3-d11fdc9b0bae

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_SignSplitEquivInl
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_hsG_cont_78d108c224a1

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
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) : muG ε {a | hsG a ≤ rad n} ≠ 0 := by
  have hopen : IsOpen {a : UJ ε | hsG a < rad n} := isOpen_lt (hsG_cont ε) continuous_const
  have hne : ({a : UJ ε | hsG a < rad n}).Nonempty := ⟨1, by
    show hs (((1 : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) < rad n
    simp [rad]⟩
  have hpos : 0 < muG ε {a | hsG a < rad n} := by
    unfold muG
    exact hopen.measure_pos _ hne
  exact (hpos.trans_le (measure_mono fun a (ha : hsG a < rad n) => ha.le)).ne'
end Formalism.BasicNotions.Examples₂.CD
