-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_exists_step_90568b34aa57
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:26:10.096148+00:00
-- url     : https://prove2.me/submissions/b29768bc-cfba-4067-85ac-2b3a68ea7a74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultigradedFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isMultiHomog_colon_aec907bf3062
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_exists_homog_not_mem_09e7af4d2347
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isPrime_colon_7f6c5895fe4c

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
    (hN : IsGradedSub piece N) (hNt : N ≠ ⊤) :
    ∃ (c : K → ℤ) (x : M), x ∈ piece c ∧ x ∉ N ∧ (N.colon {x}).IsPrime ∧
      IsMultiHomogIdeal (N.colon {x}) := by
  obtain ⟨c₀, x₀, hx₀, hx₀N⟩ := exists_homog_not_mem (piece := piece) hNt
  obtain ⟨I, ⟨c, x, hx, hxN, rfl⟩, hI⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian (MRing ι F) (MRing ι F))
      {I | ∃ (c : K → ℤ) (x : M), x ∈ piece c ∧ x ∉ N ∧ N.colon {x} = I}
      ⟨_, c₀, x₀, hx₀, hx₀N, rfl⟩
  exact ⟨c, x, hx, hxN,
    isPrime_colon hM hN hx hxN fun c' y hy hyN => hI _ ⟨c', y, hy, hyN, rfl⟩,
    isMultiHomog_colon hM hN hx⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
