-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_snoc_comp_swap_d689c6061328
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:57:44.457869+00:00
-- url     : https://prove2.me/submissions/fa7fe480-ed22-49e2-99fb-02f713fe5154

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
theorem _root_.solution {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι) (a b : Fin n) :
    (Fin.snoc L A : Fin (n + 1) → HermLine ι) ∘ Equiv.swap a.castSucc b.castSucc =
      Fin.snoc (L ∘ Equiv.swap a b) A := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_lt_last a).ne'
      (Fin.castSucc_lt_last b).ne']
    simp
  · have h : Equiv.swap a.castSucc b.castSucc j.castSucc = (Equiv.swap a b j).castSucc := by
      simp only [Equiv.swap_apply_def, Fin.castSucc_inj]
      split_ifs <;> rfl
    rw [Function.comp_apply, h]
    simp
end GroundTheory.Heights₂.Heights.Inter.ThmISymm
