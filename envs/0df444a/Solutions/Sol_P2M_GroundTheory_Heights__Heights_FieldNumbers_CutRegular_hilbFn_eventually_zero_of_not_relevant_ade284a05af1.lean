-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_hilbFn_eventually_zero_of_not_relevant_ade284a05af1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:46.053823+00:00
-- url     : https://prove2.me/submissions/312cf101-d192-4b89-9013-a9d026e9589e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumAdd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRegular
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_mem_of_block_le_44cca1003180

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
theorem _root_.solution {I : Ideal (MRing ι F)} (hI : ¬ IsRelevant I) :
    ∀ᶠ m in Filter.atTop, hilbFn I m = 0 := by
  unfold IsRelevant at hI
  push Not at hI
  obtain ⟨k, hk⟩ := hI
  filter_upwards [Filter.eventually_ge_atTop (fun _ : K => (1 : ℤ))] with m hm
  unfold hilbFn
  split_ifs with h0
  · have : gradedPiece I (fun k => (m k).toNat) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨f, hf, rfl⟩
      rw [Submodule.mem_bot]
      have hmk : (1 : ℤ) ≤ m k := hm k
      have hfk : 1 ≤ (m k).toNat := by omega
      have hfI := mem_of_block_le hk hfk ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hf)
      simpa [Ideal.Quotient.eq_zero_iff_mem] using hfI
    rw [this, finrank_bot, Nat.cast_zero]
  · rfl
end GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
