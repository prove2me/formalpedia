-- Prove2me | solution 1 for P2M_GlobalTheory_DiscEval_BoundedOnFrames_norm_coeff_bind__le_90ad7e439400
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:36:42.535079+00:00
-- url     : https://prove2.me/submissions/e1ff7dbf-b047-4fd8-8772-561b261b7f13

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Theorems.Thm_P2M_GlobalTheory_DiscEval_coeffPoly_bind__ea251764de75
import Theorems.Thm_GlobalTheory_DiscEval_isHomogeneous_coeffPoly
import Theorems.Thm_P2M_GlobalTheory_DiscEval_norm_coeff_bind__le_6e00ba114732
import Theorems.Thm_GlobalTheory_DiscEval_BoundedOnFrames_coeffPoly_integral
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_C
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_X



set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscEval
open Filter Topology IsLocalRing
open scoped PowerSeries LaurentSeries
variable (p : ℕ) [Fact p.Prime]
variable {p}
open MvPolynomial
variable {O : Type*} [CommRing O] (i : O →+* ℂ_[p]) (hi : ∀ x, ‖i x‖ ≤ 1) {π : O} (hπ : i π ≠ 0)
  {A : Type*} [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]
  {ι : Type} [Fintype ι] {n : ι → Type} [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)]
variable {i hi hπ} {F : MvPolynomial (EntryIndex n n) A}
namespace GlobalTheory.DiscEval
namespace BoundedOnFrames
theorem _root_.solution (hF : BoundedOnFrames i hi hπ F) {d : ℕ}
    (hd : F.IsHomogeneous d) {τ : Type*} {g : EntryIndex n n → MvPolynomial τ ℂ_[p]} {c : ℝ}
    (hc : 0 ≤ c) (hg : ∀ k μ, ‖coeff μ (g k)‖ ≤ c) (μ : τ →₀ ℕ) (m : ℤ) :
    ‖(coeff μ (bind₁ (fun k => map HahnSeries.C (g k)) (map (laurent π A i hπ) F))).coeff m‖ ≤
        c ^ d ∧
      (m < 0 → (coeff μ (bind₁ (fun k => map HahnSeries.C (g k))
        (map (laurent π A i hπ) F))).coeff m = 0) := by
  rw [← coeff_coeffPoly, coeffPoly_bind₁]
  exact ⟨DiscEval.norm_coeff_bind₁_le (isHomogeneous_coeffPoly m (hd.map _))
    (hF.coeffPoly_integral m).1 hc hg μ, fun hm => by simp [(hF.coeffPoly_integral m).2 hm]⟩
end BoundedOnFrames
end GlobalTheory.DiscEval
