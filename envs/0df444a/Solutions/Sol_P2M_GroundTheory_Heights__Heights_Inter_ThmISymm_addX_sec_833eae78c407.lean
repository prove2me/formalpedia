-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_addX_sec_833eae78c407
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:11.160509+00:00
-- url     : https://prove2.me/submissions/71c93243-79a7-40ab-b53f-7c7b6edda3e7

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_smooth_tensor_f6b0ee1175f1


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
theorem _root_.solution (hR : IsRFamily I) (hRS : RPositionAdd.Statement) {P : Ideal (MRing ι)} {m : ℕ}
    (hP : IsArithVar P (m + 1 + 1)) {L : Fin m → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {A C Y : HermLine ι} (hA : IsSmoothHerm A) (hC : IsSmoothHerm C) (hY : IsSmoothHerm Y) {y : MRing ι}
    (hy : IsSectionOn P Y y) :
    I P (m + 1 + 1) (Fin.snoc (Fin.snoc L (A.tensor C)) Y) =
      I P (m + 1 + 1) (Fin.snoc (Fin.snoc L A) Y) + I P (m + 1 + 1) (Fin.snoc (Fin.snoc L C) Y) := by
  rw [rAt I hR hP (smooth_snoc hL (ThmIExists.smooth_tensor hA hC)) hY hy,
    rAt I hR hP (smooth_snoc hL hA) hY hy, rAt I hR hP (smooth_snoc hL hC) hY hy]
  exact hRS K ι I P m L A C Y y (fun W L' A' C' hW hL' hA' hC' => hR.1 W m L' A' C' hW hL' hA' hC')
    hP hL hA hC hY hy
end GroundTheory.Heights₂.Heights.Inter.ThmISymm
