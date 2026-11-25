-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_addX_ae8c7cbc3b7d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:58:33.478192+00:00
-- url     : https://prove2.me/submissions/0301ee51-ce85-4a08-b7d5-eaa55913fc16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsWellDefined
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChoice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmISymm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_smooth_snoc_5c463b110c20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_addX_sec_833eae78c407
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isSectionOn_segre_f966ae4bfd55
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isSectionOn_up_95943556fabe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isSmoothHerm_segreLine_1e1d36fff7ac
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
    {A C Y : HermLine ι} (hA : IsSmoothHerm A) (hC : IsSmoothHerm C) (hY : IsSmoothHerm Y) :
    I P (m + 1 + 1) (Fin.snoc (Fin.snoc L (A.tensor C)) Y) =
      I P (m + 1 + 1) (Fin.snoc (Fin.snoc L A) Y) + I P (m + 1 + 1) (Fin.snoc (Fin.snoc L C) Y) := by
  set H : HermLine ι := ThmIExists.segreLine (ThmIExists.shift Y)
  have hH : IsSmoothHerm H := ThmIExists.isSmoothHerm_segreLine _
  have ht := ThmIExists.isSectionOn_up hP Y
  have hu := ThmIExists.isSectionOn_segre hP (ThmIExists.shift Y)
  have e : ∀ Z, IsSmoothHerm Z → I P (m + 1 + 1) (Fin.snoc (Fin.snoc L Z) (Y.tensor H)) =
      I P (m + 1 + 1) (Fin.snoc (Fin.snoc L Z) Y) + I P (m + 1 + 1) (Fin.snoc (Fin.snoc L Z) H) :=
    fun Z hZ => hR.1 P (m + 1) (Fin.snoc L Z) Y H hP (smooth_snoc hL hZ) hY hH
  have h1 := addX_sec I hR hRS hP hL hA hC (ThmIExists.smooth_tensor hY hH) ht
  have h2 := addX_sec I hR hRS hP hL hA hC hH hu
  have e1 := e _ (ThmIExists.smooth_tensor hA hC)
  have e2 := e A hA
  have e3 := e C hC
  linarith
end GroundTheory.Heights₂.Heights.Inter.ThmISymm
