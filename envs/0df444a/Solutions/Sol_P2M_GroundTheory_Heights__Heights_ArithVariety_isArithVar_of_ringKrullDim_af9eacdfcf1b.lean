-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ArithVariety_isArithVar_of_ringKrullDim_af9eacdfcf1b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:09.633913+00:00
-- url     : https://prove2.me/submissions/9906ba36-6018-4d52-b59d-ef40ef3b9862

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsArithVarOfRingKrullDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_isHorizontal_cfaf0a26d8e3


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
namespace GroundTheory.Heights₂.Heights
namespace ArithVariety
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {n : ι → ℕ} (P : ArithVariety n) {D : ℕ}
    (hdim : ringKrullDim P.CoordRing = ((D + 1 + Fintype.card ι : ℕ) : WithBot ℕ∞)) :
    Geo.IsArithVar (ι := blockIdx n) P.ideal (D + 1) :=
  ⟨inferInstance, P.isMultiProjPrime, P.isHorizontal, hdim⟩
end ArithVariety
end GroundTheory.Heights₂.Heights
