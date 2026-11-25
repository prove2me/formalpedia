-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.exists_extend_endomorphism_fractions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:45:59.71112+00:00
-- url     : https://prove2.me/submissions/75123cd1-d73f-4056-b922-3ecb0f10790f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsExtendEndomorphismFractions
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_subringInclusionSubfield_coe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_subringInclusionSubfield_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_isFractionRing_subringInclusion

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
theorem _root_.solution (h : R ≤ F.toSubring) (hf : ∀ x ∈ F, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x = a / b)
    (s : R →+* R) (hsinj : Function.Injective s) :
    ∃ σ : F →+* F, ∀ (x : F) (a b : R), (x : K) * b = a →
      ((σ x : F) : K) * (s b : R) = (s a : R) := by
  let _ : Algebra R F := (subringInclusionSubfield R F h).toAlgebra
  have : IsFractionRing R F := isFractionRing_subringInclusion R F h hf
  have hg : Function.Injective ((subringInclusionSubfield R F h).comp s) := (subringInclusionSubfield_injective R F h).comp hsinj
  have hσ : ∀ x : R, IsFractionRing.lift hg (subringInclusionSubfield R F h x) = subringInclusionSubfield R F h (s x) :=
    fun x => IsFractionRing.lift_algebraMap hg x
  refine ⟨IsFractionRing.lift hg, fun x a b e => ?_⟩
  have h' : x * subringInclusionSubfield R F h b = subringInclusionSubfield R F h a :=
    Subtype.ext (by rw [Subfield.coe_mul, subringInclusionSubfield_coe, subringInclusionSubfield_coe, e])
  have h2 := congrArg (IsFractionRing.lift hg) h'
  rw [map_mul, hσ, hσ] at h2
  rw [← subringInclusionSubfield_coe R F h, ← subringInclusionSubfield_coe R F h, ← Subfield.coe_mul, h2]
end ReciprocityTheory.ChartRestriction.L1
