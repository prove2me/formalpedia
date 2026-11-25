-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mul_mem_secs_of_pullSecs_875330939677
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:29:47.227831+00:00
-- url     : https://prove2.me/submissions/20c130a6-9c2e-417b-9129-1e302e5455e8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination

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
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.Domination
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.Domination
theorem _root_.solution {L L' : SubSystem S x Ω} {κ : Ω}
    (h : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∀ b ∈ domRing S x x' i, ∀ l ∈ L.sub (singleChart hi),
      κ * (b * l) ∈ L'.sub (singleChart hi)) :
    ∀ z ∈ pullSecs x' L, κ * z ∈ L'.secs := by
  intro z hz
  simp only [pullSecs, Submodule.mem_iInf] at hz
  simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem]
  intro I
  obtain ⟨i, hiI⟩ := I.2.1
  have hi : x i ≠ 0 := (mem_support x).mp (I.2.2 hiI)
  refine L'.mono (singleChart hi) I (Finset.singleton_subset_iff.mpr hiI) _ ?_
  have hz' := hz i hi
  clear hz
  induction hz' using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, hb, l, hl, rfl⟩ := hw
    exact h i hi b hb l hl
  | zero => rw [mul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | smul s a _ ha =>
    rw [mul_smul_comm]
    exact Submodule.smul_of_tower_mem _ s ha
end GroundTheory.Heights₂.Heights.Kleiman.Domination
