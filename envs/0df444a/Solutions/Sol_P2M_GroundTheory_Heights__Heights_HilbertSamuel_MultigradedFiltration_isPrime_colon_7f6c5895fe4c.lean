-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isPrime_colon_7f6c5895fe4c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:06:41.287596+00:00
-- url     : https://prove2.me/submissions/6a94ed0a-14e8-400e-8f98-fba5de0b3041

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultigradedFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_homog_smul_mem_798312d8528d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isMultiHomog_colon_aec907bf3062
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_isPrime_of_forms_48f55a7aabc8

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
    (hN : IsGradedSub piece N) {c : K → ℤ} {x : M} (hx : x ∈ piece c) (hxN : x ∉ N)
    (hmax : ∀ (c' : K → ℤ) (y : M), y ∈ piece c' → y ∉ N → ¬ N.colon {x} < N.colon {y}) :
    (N.colon {x}).IsPrime := by
  refine isPrime_of_forms _ (isMultiHomog_colon hM hN hx) ?_ ?_
  · intro htop
    apply hxN
    have h1 : (1 : MRing ι F) ∈ N.colon {x} := htop ▸ Submodule.mem_top
    rwa [Submodule.mem_colon_singleton, one_smul] at h1
  · rintro a b - ⟨j, hj⟩ hab
    by_cases hb : b ∈ N.colon {x}
    · exact Or.inr hb
    left
    rw [Submodule.mem_colon_singleton] at hb hab
    have hbx : b • x ∈ piece (c + degZ j) := homog_smul_mem hM hj hx
    have hle : N.colon {x} ≤ N.colon {b • x} := by
      intro s hs
      rw [Submodule.mem_colon_singleton] at hs ⊢
      rw [smul_comm]
      exact N.smul_mem b hs
    have heq := eq_of_le_of_not_lt hle (hmax _ _ hbx hb)
    have ha : a ∈ N.colon {b • x} := by
      rw [Submodule.mem_colon_singleton, ← mul_smul]
      exact hab
    rwa [← heq] at ha
end GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
