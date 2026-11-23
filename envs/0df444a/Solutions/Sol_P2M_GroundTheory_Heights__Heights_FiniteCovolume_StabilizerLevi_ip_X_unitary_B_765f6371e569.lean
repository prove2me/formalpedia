-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_X_unitary_B_765f6371e569
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:52.761787+00:00
-- url     : https://prove2.me/submissions/5c9644bb-0364-4cd0-8de1-2c6cc6635974

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_unitary_881309351cf8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_B_right_bdac4345363f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
open Matrix
noncomputable section
set_option linter.unusedSectionVars false
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {H : Matrix ι ι ℂ} {B : Matrix ι κ ℂ} {X Y : ι → ℂ}
variable (hH : Hᴴ = H) (hG : IsUnit (Bᴴ * H * B).det) (hBX : Bᴴ *ᵥ (H *ᵥ X) = 0)
    (hBY : Bᴴ *ᵥ (H *ᵥ Y) = 0) (hXX : star X ⬝ᵥ (H *ᵥ X) = 0) (hYY : star Y ⬝ᵥ (H *ᵥ Y) = 0)
    (hXY : star X ⬝ᵥ (H *ᵥ Y) = 1) (hspan : ∀ z, ∃ (a b : ℂ) (c : κ → ℂ), z = a • X + b • Y + B *ᵥ c)
include hH hG hBX hBY hXX hYY hXY hspan
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
theorem _root_.solution {g : Matrix ι ι ℂ} (hg : gᴴ * H * g = H) (hgX : g *ᵥ X = X) (c : κ → ℂ) :
    star X ⬝ᵥ (H *ᵥ (g *ᵥ (B *ᵥ c))) = 0 := by
  conv_lhs => rw [← hgX]
  rw [ip_unitary hg, ip_B_right hH hBX]
end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
