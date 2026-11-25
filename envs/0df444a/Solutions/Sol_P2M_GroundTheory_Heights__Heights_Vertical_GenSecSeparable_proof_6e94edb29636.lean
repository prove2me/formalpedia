-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_proof_6e94edb29636
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:54:01.099804+00:00
-- url     : https://prove2.me/submissions/f73e1d73-be18-40c7-8c91-1631bc60dadd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChartPointTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecPointSeparable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecSeparable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_genPar_algIndep_ff1baf2020e4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_adjoin_secCoord_b7d33270686f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_secCoord_form_ecd479731ca9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_secCoord_chart_2b705866370f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_aeval_secCoord_5bd30c65c2d6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GenSecSeparable
namespace GroundTheory.Heights₂.Heights.Vertical
namespace GenSecSeparable
theorem _root_.solution (h₁ : SecAlgFinite.Statement) (h₂ : GenSecDomain.Statement)
    (h₃ : ChartPointTrdeg.Statement) (h₄ : SecPointSeparable.Statement) :
    GenSecSeparable.Statement := by
  intro k _ _ n e Q g hQ hg
  have : Module.Finite (GenParField k e n) (GenSec k e Q) :=
    h₁ k (GenParField k e n) n e Q g (genPar k e n) (genPar_algIndep k e n) hQ hg
  have : IsDomain (GenSec k e Q) := h₂ k n e Q g hQ hg
  let : Field (GenSec k e Q) :=
    (isField_of_isIntegral_of_isField' (R := GenParField k e n) (Field.toIsField _)).toField
  exact h₄ k n e (GenSec k e Q) _ (adjoin_secCoord _ _) (secCoord_form _ _) (secCoord_chart _ _)
    fun j₀ hj₀ => h₃ k (GenSec k e Q) n e Q g hQ hg _ j₀ (aeval_secCoord k e Q) hj₀
end GenSecSeparable
end GroundTheory.Heights₂.Heights.Vertical
