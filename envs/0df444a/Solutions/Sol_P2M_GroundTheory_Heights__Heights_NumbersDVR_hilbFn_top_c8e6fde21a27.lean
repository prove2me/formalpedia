-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_hilbFn_top_c8e6fde21a27
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:18.854361+00:00
-- url     : https://prove2.me/submissions/e59b894c-2edb-4252-b5db-40228339d5df

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN

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
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {F : Type*} [Field F] {K : Type*} [DecidableEq K] {ι : K → Type*}
    (m : K → ℤ) : hilbFn (⊤ : Ideal (MRing ι F)) m = 0 := by
  unfold hilbFn
  split_ifs
  · have : Subsingleton (MRing ι F ⧸ (⊤ : Ideal (MRing ι F))) :=
      Ideal.Quotient.subsingleton_iff.mpr rfl
    rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero]
  · rfl
end GroundTheory.Heights₂.Heights.NumbersDVR
