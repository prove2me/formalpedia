-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_domRing_self_le_54dbb7098c5f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:02:33.55651+00:00
-- url     : https://prove2.me/submissions/885869a2-fa57-46a2-a9ac-d8d7fc178ef6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_pullSys_self_aa64784590c1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {i : Fin (N + 1)} (hi : x i ≠ 0) :
    domRing S x x i ⊆ chartRing S x (singleChart hi) := by
  intro a ha
  rw [domRing, pullSys_self] at ha
  obtain ⟨n, hn⟩ := Set.mem_iInter.mp ha (singleChart hi)
  rw [one_mul] at hn
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp
    (pow_twistSys_one_le n (singleChart hi) (Finset.mem_singleton_self i) hn)
  rw [chartRing_smul_def] at hb
  have hab : a = b := (mul_right_cancel₀ (pow_ne_zero n hi) hb).symm
  rw [hab]; exact b.2
end GroundTheory.Heights₂.Heights.Kleiman
