-- Prove2me | solution 1 for P2M_GlobalTheory_CMVal_Model_absNorm_of_mem__93baf5adc7ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:50:32.805191+00:00
-- url     : https://prove2.me/submissions/14cc1c18-bf49-4feb-b1e9-d36e77a05bfa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Model
namespace GlobalTheory.CMVal.Model
theorem _root_.solution (P : HeightOneSpectrum (𝓞 K)) (h : ((127 : ℕ) : 𝓞 K) ∈ P.asIdeal) : Ideal.absNorm P.asIdeal = 127 := by
  haveI : Fact (Nat.Prime 127) := ⟨by norm_num⟩
  have := P.isPrime
  haveI : P.asIdeal.LiesOver (Ideal.span {((127 : ℕ) : ℤ)}) := by
    refine ⟨?_⟩
    have hmax : (Ideal.span {((127 : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 127
    refine hmax.eq_of_le (Ideal.IsPrime.under ℤ P.asIdeal).ne_top ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change algebraMap ℤ (𝓞 K) ((127 : ℕ) : ℤ) ∈ P.asIdeal
    simpa using h
  rw [← Ideal.pow_inertiaDeg 127 P.asIdeal,
    IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd (m := 21) 127 K P.asIdeal (by norm_num)]
  have : ((127 : ℕ) : ZMod 21) = 1 := by decide
  rw [this, orderOf_one, pow_one]
end GlobalTheory.CMVal.Model
