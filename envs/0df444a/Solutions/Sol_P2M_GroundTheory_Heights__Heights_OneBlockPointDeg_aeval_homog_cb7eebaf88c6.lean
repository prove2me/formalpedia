-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OneBlockPointDeg_aeval_homog_cb7eebaf88c6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:15:53.709101+00:00
-- url     : https://prove2.me/submissions/936669ad-d07e-44d9-8a62-18abce8a3f02

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartRankAdjoin
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_POneBlockPointDeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OneBlockPointDeg_isMultiHomog_of_isHomogeneous_03061861cacf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartRankAdjoin_aeval_mul_of_isMultiHomog_e86f9b353a4e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
noncomputable section
open GroundTheory.Heights₂.Heights.OneBlockPointDeg
variable {Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ'] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {k₀ : K}
namespace GroundTheory.Heights₂.Heights.OneBlockPointDeg
theorem _root_.solution (hK : ∀ k, k = k₀) {w : (Σ k, ι k) → Φ'} {c : ∀ k, ι k} (hc : w ⟨k₀, c k₀⟩ ≠ 0)
    {g : MRingOver Φ ι} {n : ℕ} (hg : g.IsHomogeneous n) :
    aeval (fun p => w p / w ⟨k₀, c k₀⟩) g * w ⟨k₀, c k₀⟩ ^ n = aeval w g := by
  classical
  have hz : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => by obtain rfl := hK k; exact hc
  have e : (fun p : Σ k, ι k => w p / w ⟨k₀, c k₀⟩) = Inter.ChartRankAdjoin.affCoord w c := by
    funext ⟨k, i⟩; obtain rfl := hK k; rfl
  have h := Inter.ChartRankAdjoin.aeval_mul_of_isMultiHomog hz (isMultiHomog_of_isHomogeneous hK hg)
  rwa [Fintype.prod_eq_single k₀ (fun k hk => absurd (hK k) hk), ← e] at h
end GroundTheory.Heights₂.Heights.OneBlockPointDeg
