-- Prove2me | solution 1 for PositivityTheory.RgUd.Exp.Rpow.exists_unit_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:56:33.897989+00:00
-- url     : https://prove2.me/submissions/95322cf8-dd23-4ba0-9c7d-f8db6e1e32f6

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
variable (k)
namespace PositivityTheory.RgUd.Exp.Rpow
theorem _root_.solution : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact (show uniformizer k ≠ 0 by simp) hx.symm
  exact ⟨Units.mk0 x hx0, hx⟩
end PositivityTheory.RgUd.Exp.Rpow
