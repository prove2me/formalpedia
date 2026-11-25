-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagClosureTrdeg_flagCoord_indep_ac93f669f26d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:59.556625+00:00
-- url     : https://prove2.me/submissions/a55284c6-cab0-418d-a71a-4878154ceebe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagConeAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PAdjoinTrdegAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairConeLinesIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosureTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeLinesIndep_linearChange_indep_964b7f140ee7


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureTrdeg
namespace GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureTrdeg
theorem _root_.solution {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ]
    [Algebra Ω Φ] {N k : ℕ} (hkN : k ≤ N) (w e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ)
    (ht : AlgebraicIndependent Ω t) :
    AlgebraicIndependent Ω (fun j : Fin k => flagCoord w e t k (Fin.castLE hkN j)) := by
  classical
  let _ := w.invertibleToMatrix e
  have hS := PairConeLinesIndep.linearChange_indep (w.toMatrix e) (isUnit_of_invertible _) t ht
  have h := hS.comp (Fin.castLE hkN) (Fin.castLE_injective hkN)
  convert h using 1
  funext j
  simp [flagCoord, Module.Basis.toMatrix_apply, j.isLt]
end GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureTrdeg
