-- Prove2me | solution 1 for P2M_GlobalTheory_CMVal_Model_splits_of_mem__40e3e115741c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:41:32.651554+00:00
-- url     : https://prove2.me/submissions/b6e98f98-84a3-42ce-97e1-a15cf8d9c9af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
import Theorems.Thm_GlobalTheory_CMVal_Model_exists_over
import Theorems.Thm_GlobalTheory_CMVal_Model_splits_of_absNorm
import Theorems.Thm_GlobalTheory_CMVal_Model_sub_conj_notMem
import Theorems.Thm_GlobalTheory_CMVal_Model_zeta_prim
import Theorems.Thm_P2M_GlobalTheory_CMVal_Model_absNorm_of_mem__93baf5adc7ea

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Model
namespace GlobalTheory.CMVal.Model
theorem _root_.solution (v : HeightOneSpectrum (OF K)) (h : ((127 : ℕ) : OF K) ∈ v.asIdeal) : Splits v := by
  obtain ⟨P, hP⟩ := exists_over v
  refine splits_of_absNorm (by norm_num : Nat.Prime 127) P v hP (absNorm_of_mem' P ?_) _
    (sub_conj_notMem zeta_prim P.isPrime.ne_top)
  rw [← hP, Ideal.mem_comap, map_natCast] at h
  exact h
end GlobalTheory.CMVal.Model
