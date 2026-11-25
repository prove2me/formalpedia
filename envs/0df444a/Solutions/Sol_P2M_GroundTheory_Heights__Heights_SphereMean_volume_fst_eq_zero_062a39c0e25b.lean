-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_volume_fst_eq_zero_062a39c0e25b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:18:35.215802+00:00
-- url     : https://prove2.me/submissions/9852681b-ff97-452f-9ca2-c9e6659e6fcb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean

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
open MeasureTheory Measure Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean
namespace GroundTheory.Heights₂.Heights.SphereMean
theorem _root_.solution (m : ℕ) : volume {y : Fin (m + 1) → ℂ | y 0 = 0} = 0 := by
  let K : Submodule ℝ (Fin (m + 1) → ℂ) :=
    LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℂ) 0)
  have hK : (K : Set (Fin (m + 1) → ℂ)) = {y | y 0 = 0} := by
    ext y
    simp only [K, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply, mem_ofPred_eq]
  have hne : K ≠ ⊤ := by
    intro h
    have : (Pi.single 0 1 : Fin (m + 1) → ℂ) ∈ K := h ▸ Submodule.mem_top
    simp only [K, LinearMap.mem_ker, LinearMap.proj_apply, Pi.single_eq_same] at this
    exact one_ne_zero this
  rw [← hK]
  exact addHaar_submodule _ _ hne
end GroundTheory.Heights₂.Heights.SphereMean
