-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.isFractionRing_subringInclusion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:37:45.138823+00:00
-- url     : https://prove2.me/submissions/88360f29-db5c-4128-8324-054191997519

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsExtendEndomorphismFractions
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_subringInclusionSubfield_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
variable {K : Type*} [Field K] (R : Subring K) (F : Subfield K) (h : R ≤ F.toSubring)
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (hf : ∀ x ∈ F, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x = a / b) :
    @IsFractionRing R _ F _ (subringInclusionSubfield R F h).toAlgebra := by
  let _ : Algebra R F := (subringInclusionSubfield R F h).toAlgebra
  have : FaithfulSMul R F :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (subringInclusionSubfield_injective R F h)
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, ha, b, hb, -, e⟩ := hf z z.2
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, Subtype.ext ?_⟩
  rw [Subfield.coe_div, e]
  rfl
end ReciprocityTheory.ChartRestriction.L1
