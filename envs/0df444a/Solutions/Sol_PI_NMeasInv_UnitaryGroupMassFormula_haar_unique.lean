-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.haar_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:03:52.056926+00:00
-- url     : https://prove2.me/submissions/eeedf2f8-207c-4f06-8afd-de8b5bfd759c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_RightInvOfContract
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Topology
open scoped ENNReal NNReal
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
attribute [local instance] Classical.propDecidable
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution (S : Subgroup G) (hS : IsClosed (S : Set G)) (μ m : Measure G) (hμ0 : μ ≠ 0)
    (hμc : μ (S : Set G)ᶜ = 0) (hμi : ∀ s ∈ S, μ.map (fun x => s * x) = μ) (hμf : IsFiniteMeasureOnCompacts μ)
    (hmc : m (S : Set G)ᶜ = 0) (hmi : ∀ s ∈ S, m.map (fun x => s * x) = m) (hmf : IsFiniteMeasureOnCompacts m) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ m = c • μ := by
  haveI : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology S := inferInstanceAs (SecondCountableTopology (S : Set G))
  obtain ⟨hμL, hμF, hμM⟩ := pull S hS μ hμc hμi hμf
  obtain ⟨hmL, hmF, hmM⟩ := pull S hS m hmc hmi hmf
  haveI := hμL; haveI := hμF; haveI := hmL; haveI := hmF
  obtain ⟨a, ea⟩ : ∃ a : ℝ≥0, μ.comap (Subtype.val : S → G) = a • (haar : Measure S) :=
    ⟨_, isMulLeftInvariant_eq_smul _ _⟩
  obtain ⟨b, eb⟩ : ∃ b : ℝ≥0, m.comap (Subtype.val : S → G) = b • (haar : Measure S) :=
    ⟨_, isMulLeftInvariant_eq_smul _ _⟩
  have hμ' : μ = a • (haar : Measure S).map Subtype.val := by
    calc μ = (μ.comap (Subtype.val : S → G)).map Subtype.val := hμM.symm
      _ = (a • (haar : Measure S)).map Subtype.val := by rw [ea]
      _ = _ := by rw [Measure.map_smul]
  have hm' : m = b • (haar : Measure S).map Subtype.val := by
    calc m = (m.comap (Subtype.val : S → G)).map Subtype.val := hmM.symm
      _ = (b • (haar : Measure S)).map Subtype.val := by rw [eb]
      _ = _ := by rw [Measure.map_smul]
  have ha0 : a ≠ 0 := by rintro rfl; apply hμ0; rw [hμ', zero_smul]
  refine ⟨((b / a : ℝ≥0) : ℝ≥0∞), ENNReal.coe_ne_top, ?_⟩
  rw [hm', hμ']
  ext s hs
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def]
  rw [← mul_assoc, ← ENNReal.coe_mul, div_mul_cancel₀ b ha0]
end PI.NMeasInv.UnitaryGroupMassFormula
