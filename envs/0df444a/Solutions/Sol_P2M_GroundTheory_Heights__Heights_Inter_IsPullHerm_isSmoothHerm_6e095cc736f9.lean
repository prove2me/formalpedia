-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_IsPullHerm_isSmoothHerm_6e095cc736f9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:30:07.884165+00:00
-- url     : https://prove2.me/submissions/4d132b10-8a33-4f55-bd06-9f5dbeb5a3b6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogFirstCoordinate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_blocks_ne_zero_restrict_c2698d5c05ab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.Inter
namespace IsPullHerm
theorem _root_.solution {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {A : HermLine ι} {A' : HermLine ι'} (h : IsPullHerm κ v A A') (hA : IsSmoothHerm A) :
    IsSmoothHerm A' := by
  have e : A'.h = A.h ∘ fun (z : (Σ k', ι' k') → ℂ) (p : Σ k, ι k) => z (v p) := funext h.2
  have hR : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun (z : (Σ k', ι' k') → ℂ) (p : Σ k, ι k) => z (v p)) :=
    contDiff_pi.2 fun p => contDiff_apply ℝ ℂ (v p)
  unfold IsSmoothHerm
  rw [e]
  exact hA.comp hR.contDiffOn fun z hz => blocks_ne_zero_restrict hv hz
end IsPullHerm
end GroundTheory.Heights₂.Heights.Inter
