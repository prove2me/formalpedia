-- Prove2me | solution 1 for PositivityTheory.RgUd.Exp.Rpow.norm_eq_one_of_valuation_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:04.893517+00:00
-- url     : https://prove2.me/submissions/2b3738cc-43ee-45ed-9c06-9a167882fe02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_GenericIrreducibility_GenericUnitary_NormEqOneOfValuationEqOne
import Theorems.Thm_PositivityTheory_RgUd_Exp_Rpow_mem_units_integer

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
namespace PositivityTheory.RgUd.Exp.Rpow
theorem _root_.solution (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) {u : kˣ}
    (hu : valuation k (u : k) = 1) : ‖(χ u : ℂ)‖ = 1 := by
  have : T1Space k := IsTopologicalAddGroup.t1Space k (by
    convert (valuation k).isClosed_closedBall (R := k) 0 using 1
    ext x
    simp)
  set S : Submonoid k := (𝒪[k]).toSubmonoid
  have hS : IsCompact (S : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have hG : IsCompact (S.units : Set kˣ) := Submonoid.units_isCompact hS
  have : CompactSpace S.units := isCompact_iff_compactSpace.mp hG
  set H : Subgroup S.units := χ.ker.comap S.units.subtype
  have hH : IsOpen (H : Set S.units) := hχ.preimage continuous_subtype_val
  have : Finite (S.units ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  have hn : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmem : (⟨u, mem_units_integer hu⟩ : S.units) ^ H.index ∈ H := Subgroup.pow_index_mem H _
  have h1 : χ (u ^ H.index) = 1 := hmem
  have h2 : ‖(χ u : ℂ)‖ ^ H.index = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, ← map_pow, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h2
end PositivityTheory.RgUd.Exp.Rpow
