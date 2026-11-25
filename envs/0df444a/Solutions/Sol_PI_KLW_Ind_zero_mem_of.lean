-- Prove2me | solution 1 for PI.KLW.Ind.zero_mem_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:51:37.503794+00:00
-- url     : https://prove2.me/submissions/01e20c3d-cbcb-4c5a-be59-f13b784ae07a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Theorems.Thm_PI_KLW_Ind_rp_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.Ind
open PI.KLW
namespace PI.KLW.Ind
theorem _root_.solution {K : Type} [Field K] [NumberField K] {c : K →+* K} {p : ℕ} {ι : Type}
    [Fintype ι] {L : Set (ι → K)} (hL : Unimod K c p L) : (0 : ι → K) ∈ L :=
  (hL 0).2 fun w _ => by rw [hf_zero_left]; exact rp_zero p
end PI.KLW.Ind
