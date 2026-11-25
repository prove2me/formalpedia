-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isMultiHomog_colon_aec907bf3062
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:56:43.948221+00:00
-- url     : https://prove2.me/submissions/bf7a5b2f-7f90-481f-908d-931164462b44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultigradedFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_degZ_injective_e61244d735be
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_decompose_smul_4dfe6150b6e0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {M : Type v} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M] {piece : (K → ℤ) → Submodule F M}
variable [DecidableEq (K → ℤ)] [DirectSum.Decomposition piece]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
theorem _root_.solution (hM : IsMultigrading ι M piece) {N : Submodule (MRing ι F) M}
    (hN : IsGradedSub piece N) {c : K → ℤ} {x : M} (hx : x ∈ piece c) :
    IsMultiHomogIdeal (N.colon {x}) := by
  intro f hf b
  rw [Submodule.mem_colon_singleton] at hf ⊢
  have h := hN _ hf (c + degZ b)
  rw [decompose_smul hM f hx] at h
  convert h using 2
  rw [weightedHomogeneousComponent_apply]
  refine Finset.sum_congr (Finset.filter_congr fun d _ => ?_) fun _ _ => rfl
  exact ⟨fun h => by rw [h], fun h => degZ_injective (add_left_cancel h)⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
