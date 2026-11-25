-- Prove2me | solution 1 for P2M_GlobalTheory_CMVal_Model_exists_place__00af12d7f4b9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:50:34.158911+00:00
-- url     : https://prove2.me/submissions/cb46971c-5f85-4a3e-a561-6edc2f868aff

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
theorem _root_.solution : ∃ v : HeightOneSpectrum (OF K), ((127 : ℕ) : OF K) ∈ v.asIdeal := by
  haveI : Fact (Nat.Prime 127) := ⟨by norm_num⟩
  have hmax : (Ideal.span {((127 : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 127
  obtain ⟨⟨P, hP, hl⟩⟩ := (Ideal.span {((127 : ℕ) : ℤ)}).nonempty_primesOver (S := OF K)
  refine ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {((127 : ℕ) : ℤ)}) (by simp) P⟩, ?_⟩
  have : ((127 : ℕ) : ℤ) ∈ P.under ℤ := hl.over ▸ Ideal.mem_span_singleton_self _
  simpa [Ideal.mem_comap] using this
end GlobalTheory.CMVal.Model
