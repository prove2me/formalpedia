-- Prove2me | solution 1 for PI.WAU.adUnimod_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:02:11.492494+00:00
-- url     : https://prove2.me/submissions/3159b322-a620-4235-bff2-1d8ab4e7c58f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularIndex_PairwiseDisjointCosets
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionD
import Theorems.Thm_PI_WAU_kset_open
import Theorems.Thm_PI_WAU_ksub_coe
import Theorems.Thm_PI_WAU_sigmaFinite_of_K
import Theorems.Thm_PI_UnimodIdxWork_unimodIdx_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open Formalism.MainNotions.S MeasureTheory Matrix Pointwise
namespace PI.WAU
theorem _root_.solution (hA : KgSubgroup) (hC : KCompact) (hQ : KCountable) (hI : IndexEq) :
    PI.AdUnimod := by
  intro I μ hμ
  haveI := sigmaFinite_of_K I μ hμ (hC I) (hQ I)
  choose U hU using fun n : ℕ => hA I (n + 1) (by omega)
  refine PI.UnimodIdxWork.unimodIdx_main I.Gf μ hμ U (fun n => ?_) (fun V hV => ?_) (Ksub I) ?_ ?_ (hI I)
  · rw [hU n]
    exact I.topf_open (n + 1) (by omega)
  · obtain ⟨g, hg1, hgV⟩ := I.topf_basis V hV
    refine ⟨g - 1, ?_⟩
    rw [hU (g - 1), show g - 1 + 1 = g by omega]
    exact hgV
  · rw [ksub_coe]
    exact kset_open I
  · rw [ksub_coe]
    exact hC I
end PI.WAU
