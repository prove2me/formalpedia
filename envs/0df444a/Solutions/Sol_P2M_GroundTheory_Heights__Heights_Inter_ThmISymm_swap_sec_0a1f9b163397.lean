-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_swap_sec_0a1f9b163397
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:32:55.721943+00:00
-- url     : https://prove2.me/submissions/d9b7f93b-30c5-4de4-98b5-38d968898395

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsWellDefined
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChoice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmISymm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_smooth_snoc_5c463b110c20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_rAt_87cee1e706cb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmISymm
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
namespace GroundTheory.Heights₂.Heights.Inter.ThmISymm
theorem _root_.solution (hR : IsRFamily I) (hSwap : Swap.Statement) {P : Ideal (MRing ι)} {m : ℕ}
    (hP : IsArithVar P (m + 1 + 1)) {L : Fin m → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {X Y : HermLine ι} (hX : IsSmoothHerm X) (hY : IsSmoothHerm Y) {x y : MRing ι}
    (hx : IsSectionOn P X x) (hy : IsSectionOn P Y y) (hd : ∀ W, W ∈ divSupp P y → W ∉ divSupp P x) :
    I P (m + 1 + 1) (Fin.snoc (Fin.snoc L X) Y) = I P (m + 1 + 1) (Fin.snoc (Fin.snoc L Y) X) := by
  rw [rAt I hR hP (smooth_snoc hL hX) hY hy, rAt I hR hP (smooth_snoc hL hY) hX hx]
  exact hSwap K ι I P m L Y X y x (fun P' L' A' s' hP' hL' hA' hs' => rAt I hR hP' hL' hA' hs')
    hP hL hY hX hy hx hd
end GroundTheory.Heights₂.Heights.Inter.ThmISymm
