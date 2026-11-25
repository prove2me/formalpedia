-- Prove2me | solution 1 for P2M_GlobalTheory_SW_ExpSum_form_dir__8ff127926bb4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:31:16.851976+00:00
-- url     : https://prove2.me/submissions/55c6359d-48e1-46bf-9d06-b5833b14ed9e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThH
import Theorems.Thm_GlobalTheory_SW_ExpSum_form_apply

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ExpSum
variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
namespace GlobalTheory.SW.ExpSum
theorem _root_.solution (x : Matrix (Fin n) (Fin N) E) (τ : Ψ) (k : Fin n) (a : Fin N) :
    form Ψ x (0, dir Ψ τ k a, 0) = 2 * π * I * τ.1 (x k a) := by
  classical
  rw [form_apply, expo_eq, Finset.sum_eq_single τ]
  · simp [dir]
  · intro σ _ h
    simp [dir, h]
  · simp
end GlobalTheory.SW.ExpSum
