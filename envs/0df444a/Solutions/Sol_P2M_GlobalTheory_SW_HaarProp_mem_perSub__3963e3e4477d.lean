-- Prove2me | solution 1 for P2M_GlobalTheory_SW_HaarProp_mem_perSub__3963e3e4477d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:31:43.669722+00:00
-- url     : https://prove2.me/submissions/5ebcad52-a19e-4a5d-b296-e775bae0a1a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatRationalCoordsIntegralProportional
import Theorems.Thm_GlobalTheory_SW_HaarLevel_intM_iff
import Theorems.Thm_GlobalTheory_SW_HaarLevel_mem_perSub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarProp
open HaarLevel
namespace GlobalTheory.SW.HaarProp
theorem _root_.solution {K κ ι : Type} [Field K] (R : ℕ) (x : Matrix κ ι K) :
    x ∈ perSub K κ ι R ↔ ∃ y, IntM y ∧ R • y = x := by
  rw [mem_perSub]
  simp only [intM_iff]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨_, ⟨y, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩; exact ⟨y, rfl⟩
end GlobalTheory.SW.HaarProp
