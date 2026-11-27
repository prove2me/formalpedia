-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIncOrd_proof_1f9cd0a715a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:54:17.34916+00:00
-- url     : https://prove2.me/submissions/f26681c7-0af2-4f52-953c-ca937281711f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartIncOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartIncOrd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIncOrd_isPrime_map_C_94303c3811a1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIncOrd_ord_atPrime_ringEquiv_765759cdd22c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIncOrd_equiv_apply_ca034950f9d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIncOrd_map_equiv_8568df807ce0

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIncOrd
variable {F : Type} [Field F] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ)
namespace GroundTheory.Heights₂.Heights.ChartIncOrd
theorem _root_.solution (h₁ : OrdPolynomialLocalization.Statement) : ChartIncOrd.Statement := by
  intro F _ n e I W t _ _ x
  have := isPrime_map_C (Fin e × Fin n) (W.map (mkQ I t))
  have := isPrime_map_C (Fin e) (W.map (chartX I t e))
  have hIJ : (W.map (mkQ I t)).map (C : ChartQ I t →+* MvPolynomial (Fin e × Fin n) (ChartQ I t)) =
      ((W.map (chartX I t e)).map (C : ChartInc I t e →+* MvPolynomial (Fin e) (ChartInc I t e))).comap (equiv I t e) := by
    rw [← Ideal.comap_coe, ← map_equiv]
    exact (Ideal.comap_map_of_bijective _ (equiv I t e).bijective).symm
  have h2 := ord_atPrime_ringEquiv (equiv I t e) _ _ hIJ (C (mkQ I t x))
  rw [equiv_apply, fwd_C, toInc_mk] at h2
  exact (h₁ (ChartInc I t e) (Fin e) (W.map (chartX I t e)) (chartX I t e x)).symm.trans
    (h2.trans (h₁ (ChartQ I t) (Fin e × Fin n) (W.map (mkQ I t)) (mkQ I t x)))
end GroundTheory.Heights₂.Heights.ChartIncOrd
