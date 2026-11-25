-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIncOrd_ord_atPrime_ringEquiv_765759cdd22c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:36:20.104455+00:00
-- url     : https://prove2.me/submissions/8a5e0149-a030-414c-a42c-083ba6274618

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartIncOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartIncOrd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ord_ringEquiv_ad3b8618db20


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
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (f : R ≃+* S) (P : Ideal R) [P.IsPrime]
    (P' : Ideal S) [P'.IsPrime] (h : P = P'.comap f) (x : R) :
    Ring.ord (Localization.AtPrime P') (algebraMap S _ (f x)) =
      Ring.ord (Localization.AtPrime P) (algebraMap R _ x) := by
  have := ord_ringEquiv (Localization.localRingEquiv P P' f h) (algebraMap R _ x)
  exact (congrArg (Ring.ord (Localization.AtPrime P')) (Localization.localRingHom_to_map P P' (f : R →+* S) h x)).symm.trans this
end GroundTheory.Heights₂.Heights.ChartIncOrd
