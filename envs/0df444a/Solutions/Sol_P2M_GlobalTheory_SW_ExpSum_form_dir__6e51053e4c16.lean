-- Prove2me | solution 1 for P2M_GlobalTheory_SW_ExpSum_form_dir__6e51053e4c16
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:31:14.23514+00:00
-- url     : https://prove2.me/submissions/485ae760-12e3-4fec-8b97-f36e457a4a22

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
theorem _root_.solution (x : Matrix (Fin n) (Fin N) E) (τ : Ψ) (a b : Fin N) :
    form Ψ x (dir Ψ τ a b, 0, 0) = 2 * π * I * ∑ k, τ.1 (x k a) * conj (τ.1 (x k b)) := by
  classical
  rw [form_apply, expo_eq, Finset.sum_eq_single τ]
  · simp [dir]
  · intro σ _ h
    simp [dir, h]
  · simp
end GlobalTheory.SW.ExpSum
