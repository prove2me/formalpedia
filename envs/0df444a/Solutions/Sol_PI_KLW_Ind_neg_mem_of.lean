-- Prove2me | solution 1 for PI.KLW.Ind.neg_mem_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:59:19.056531+00:00
-- url     : https://prove2.me/submissions/7f60bb69-eafb-4d77-8acd-0e77eb8f0a1b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Theorems.Thm_PI_KLW_Ind_rp_one
import Theorems.Thm_PI_KLW_Ind_rp_neg
import Theorems.Thm_PI_KLW_Ind_zero_mem_of
import Theorems.Thm_PI_KLW_Ind_add_smul_mem

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
    [Fintype ι] {L : Set (ι → K)} (hL : Unimod K c p L) {b : ι → K} (hb : b ∈ L) : -b ∈ L := by
  have h := add_smul_mem hL (zero_mem_of hL) hb (rp_neg (rp_one p))
  rwa [zero_add, neg_one_smul] at h
end PI.KLW.Ind
