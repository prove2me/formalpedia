-- Prove2me | solution 1 for P2M_PI_KLW_Pair_add_mem__5e06d2fd9611
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:07:49.334956+00:00
-- url     : https://prove2.me/submissions/859cbaba-7bad-40f1-a4ae-14d837cbc082

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairOfEps
import Theorems.Thm_PI_KLW_Ind_add_smul_mem
import Theorems.Thm_PI_KLW_Ind_rp_one
import Theorems.Thm_PI_KLW_NO_rp_one


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
open PI PI.KLW PI.KLW.Pair
open PI.KLW
namespace PI.KLW.Pair
theorem _root_.solution {K : Type} [Field K] [NumberField K] {c : K →+* K} {p : ℕ} {ι : Type}
    [Fintype ι] {L : Set (ι → K)} (hL : Unimod K c p L) {a b : ι → K} (ha : a ∈ L) (hb : b ∈ L) :
    a + b ∈ L := by
  have h := Ind.add_smul_mem hL ha hb (Ind.rp_one p)
  rwa [one_smul] at h
end PI.KLW.Pair
