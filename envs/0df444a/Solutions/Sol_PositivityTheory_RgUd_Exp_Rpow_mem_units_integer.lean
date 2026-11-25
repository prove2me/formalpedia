-- Prove2me | solution 1 for PositivityTheory.RgUd.Exp.Rpow.mem_units_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:55:27.203831+00:00
-- url     : https://prove2.me/submissions/898d763d-878c-4e71-9cfa-9245f67cb78b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_GenericIrreducibility_GenericUnitary_NormEqOneOfValuationEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.Exp PositivityTheory.RgUd.Exp.Rpow
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace PositivityTheory.RgUd.Exp.Rpow
theorem _root_.solution {u : kˣ} (hu : valuation k (u : k) = 1) :
    u ∈ (𝒪[k]).toSubmonoid.units := by
  refine ⟨?_, ?_⟩
  · show (u : k) ∈ 𝒪[k]
    exact (Valuation.mem_integer_iff _ _).2 hu.le
  · show ((u⁻¹ : kˣ) : k) ∈ 𝒪[k]
    rw [Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
end PositivityTheory.RgUd.Exp.Rpow
