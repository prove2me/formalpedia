-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_vNum_vecCons_zero_22688d6f4d59
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:44:46.073174+00:00
-- url     : https://prove2.me/submissions/d24d0b1b-2508-4196-911b-5863f8d3f81d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CycEvalEqAddMulOfCycle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (W : Ideal (MRing ι O)) {d : ℕ} (L : Fin d → K → ℤ) :
    vNum W (Matrix.vecCons (0 : K → ℤ) L) = 0 := by
  unfold vNum intNum
  have hm : mixedDiff (Matrix.vecCons (0 : K → ℤ) L) (hilbFn (specialIdeal W)) = fun _ => 0 := by
    funext m
    simp [mixedDiff, List.ofFn_succ, diffStep]
  rw [hm]
  unfold eventualValue
  have hex : ∃ c, ∀ᶠ m in Filter.atTop, (fun _ : K → ℤ => (0 : ℤ)) m = c :=
    ⟨0, Filter.Eventually.of_forall fun _ => rfl⟩
  rw [dif_pos hex]
  obtain ⟨m, hm'⟩ := hex.choose_spec.exists
  exact hm'.symm
end GroundTheory.Heights₂.Heights.NumbersDVR
