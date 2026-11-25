-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_sup_eq_comap_c789fdbae33b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:26:18.831958+00:00
-- url     : https://prove2.me/submissions/d91151bb-8c72-4bdb-b796-19b6996e420d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlockAdjoinPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_X_of_mem_f7bd28ee701b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_sub_killB_mem_a8bd36cb094e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_mem_f445c92ececc

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
open GroundTheory.Heights₂.Heights.NumbersDVR.BlockAdjoinPrime
variable {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}
variable [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.BlockAdjoinPrime
theorem _root_.solution {Q : Ideal (MRing ι R)} (hQ : IsMultiHomogIdeal Q) (B : Set K) :
    Q ⊔ varIdeal B = Q.comap (killB B) := by
  apply le_antisymm
  · refine sup_le (fun q hq => killB_mem hQ B hq) ?_
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨v, hv, rfl⟩
    show killB B (X v) ∈ Q
    rw [killB_X_of_mem B hv]
    exact zero_mem _
  · intro p hp
    have : p = killB B p + (p - killB B p) := by ring
    rw [this]
    exact add_mem (Ideal.mem_sup_left hp) (Ideal.mem_sup_right (sub_killB_mem B p))
end GroundTheory.Heights₂.Heights.NumbersDVR.BlockAdjoinPrime
