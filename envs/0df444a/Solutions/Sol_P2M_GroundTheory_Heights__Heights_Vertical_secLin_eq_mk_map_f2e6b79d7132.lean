-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_secLin_eq_mk_map_f2e6b79d7132
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:29:16.931053+00:00
-- url     : https://prove2.me/submissions/6969c9f8-90f3-4697-9160-d6f115ff09d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_map_linForm_8400fbbc6c69

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
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {n e : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) (u : Fin n → 𝓞 K) :
    secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j)) =
      Ideal.Quotient.mk _ ((linForm u).map (algebraMap (𝓞 K) (ParDVR e n v))) := by
  rw [secLin, map_linForm]
end GroundTheory.Heights₂.Heights.Vertical
