-- Prove2me | solution 1 for PI.AprimeInfG.mem_tubeS_mul_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:19:19.016266+00:00
-- url     : https://prove2.me/submissions/d3846ea8-023b-46d6-ac71-8600ca44f8b0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_GrpTube

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfG
open MeasureTheory Topology Filter Metric Set
open scoped ENNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace PI.AprimeInfG
theorem _root_.solution (H : Subgroup G) {V : Set G} (hV : ∀ a ∈ V, ∀ b ∈ V, a⁻¹ * b ∈ H → a = b)
    (S : Set H) {a : G} (ha : a ∈ V) (h0 h : H) :
    a * (h0 : G) * (h : G) ∈ tubeS H V S ↔ h0 * h ∈ S := by
  constructor
  · rintro ⟨a', ha', h', hh', he⟩
    have hmem : a⁻¹ * a' ∈ H := by
      have : a⁻¹ * a' = (h0 : G) * (h : G) * (h' : G)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← he, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]
      exact H.mul_mem (H.mul_mem h0.2 h.2) (H.inv_mem h'.2)
    have haa : a = a' := hV a ha a' ha' hmem
    subst haa
    have : h0 * h = h' := by
      apply Subtype.ext
      have := he
      rw [mul_assoc] at this
      simpa using mul_left_cancel this
    rw [this]
    exact hh'
  · intro hS
    exact ⟨a, ha, h0 * h, hS, by simp [mul_assoc]⟩
end PI.AprimeInfG
