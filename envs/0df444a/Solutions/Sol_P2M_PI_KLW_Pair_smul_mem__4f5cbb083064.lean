-- Prove2me | solution 1 for P2M_PI_KLW_Pair_smul_mem__4f5cbb083064
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:59:18.778992+00:00
-- url     : https://prove2.me/submissions/f1190b24-ab3d-4be2-8a8e-fad553b31cd9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairOfEps
import Theorems.Thm_PI_KLW_Ind_add_smul_mem
import Theorems.Thm_PI_KLW_Ind_zero_mem_of


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
    [Fintype ι] {L : Set (ι → K)} (hL : Unimod K c p L) {b : ι → K} (hb : b ∈ L) {r : K}
    (hr : Rp K p r) : r • b ∈ L := by
  have h := Ind.add_smul_mem hL (Ind.zero_mem_of hL) hb hr
  rwa [zero_add] at h
end PI.KLW.Pair
