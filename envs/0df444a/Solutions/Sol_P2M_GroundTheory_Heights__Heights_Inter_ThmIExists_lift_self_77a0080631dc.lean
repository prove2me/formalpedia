-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_lift_self_77a0080631dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:57:29.544803+00:00
-- url     : https://prove2.me/submissions/4903f151-0b4a-4b5f-8d12-8e7b61d4cb9b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily

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
open GroundTheory.Heights₂.Heights.Inter.ThmIExists
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.ThmIExists
theorem _root_.solution {n : ℕ} (J : Ideal (MRing ι) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι))
    (L : Fin n → HermLine ι) : lift J W n L = J W L := by
  simp only [lift]
  rfl
end GroundTheory.Heights₂.Heights.Inter.ThmIExists
