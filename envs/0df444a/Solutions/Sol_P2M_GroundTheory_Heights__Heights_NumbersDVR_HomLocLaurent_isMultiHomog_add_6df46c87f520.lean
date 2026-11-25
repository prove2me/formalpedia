-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_isMultiHomog_add_6df46c87f520
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:07:14.39121+00:00
-- url     : https://prove2.me/submissions/3b0fb6ec-0c45-4e34-96fa-4d1b516d7d11

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpFibreDegreeCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLocLaurent

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
open MvPolynomial
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
open GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
variable (P W : Ideal (MRing ι R)) [P.IsPrime]
variable {P W}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
theorem _root_.solution {f g : MRing ι R} {b : K → ℕ} (hf : IsMultiHomog f b)
    (hg : IsMultiHomog g b) : IsMultiHomog (f + g) b :=
  (mem_weightedHomogeneousSubmodule _ _ _ _).mp
    ((weightedHomogeneousSubmodule R (blockWeight ι) b).add_mem
      ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hf)
      ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hg))
end GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
