-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_snoc_snoc_comp_swap_2783ae7a74db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:57:49.176648+00:00
-- url     : https://prove2.me/submissions/fcaa59f6-6114-4551-ab63-b8e271125e9e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsWellDefined
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChoice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmISymm

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
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.ThmISymm
theorem _root_.solution {m : ℕ} (L : Fin m → HermLine ι) (X Y : HermLine ι) :
    (Fin.snoc (Fin.snoc L X) Y : Fin (m + 1 + 1) → HermLine ι) ∘
        Equiv.swap (Fin.last m).castSucc (Fin.last (m + 1)) =
      Fin.snoc (Fin.snoc L Y) X := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp
    · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne
        (fun h => (Fin.castSucc_lt_last j).ne (Fin.castSucc_injective _ h))
        (Fin.castSucc_lt_last _).ne]
      simp
end GroundTheory.Heights₂.Heights.Inter.ThmISymm
