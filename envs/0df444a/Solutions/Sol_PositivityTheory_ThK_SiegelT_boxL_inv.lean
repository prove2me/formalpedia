-- Prove2me | solution 1 for PositivityTheory.ThK.SiegelT.boxL_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:38.003124+00:00
-- url     : https://prove2.me/submissions/558d41b5-2994-4db5-88b9-a7cc6618876a

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAn
import Theorems.Thm_PositivityTheory_ThK_SiegelT_conj_psi
import Theorems.Thm_PositivityTheory_ThK_SiegelT_slice_mem
import Theorems.Thm_PositivityTheory_ThK_SiegelT_partial_mem
import Theorems.Thm_PositivityTheory_ThK_SiegelT_star_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SiegelT
open Matrix GlobalTheory.WeilM Topology Filter
variable {R : Type} [TopologicalSpace R] [T2Space R] {κ κ' : Type}
namespace PositivityTheory.ThK.SiegelT
theorem _root_.solution {A : Type} [CommRing A] [Invertible (2 : A)] [TopologicalSpace A] [T2Space A] [Fintype κ] {ψ : AddChar A ℂ}
    (hψ : ∀ x, ‖ψ x‖ = 1) {l : ((κ → A) → ℂ) →ₗ[ℂ] ℂ} {w₁ w₂ : (κ → A) × (κ → A)}
    (h₁ : ∀ φ ∈ SB (κ → A), l (schr ψ w₁ φ) = l φ) (h₂ : ∀ φ ∈ SB (κ → A), l (schr ψ w₂ φ) = l φ)
    {Φ : (κ ⊕ κ → A) → ℂ} (hΦ : Φ ∈ SB (κ ⊕ κ → A)) :
    boxL l (conjL l) (schr ψ (Sum.elim w₁.1 w₂.1, Sum.elim w₁.2 (-w₂.2)) Φ) = boxL l (conjL l) Φ := by
  show star (l (star _)) = star (l (star _))
  rw [← h₂ _ (star_mem (partial_mem hΦ l))]
  congr 2
  funext y
  simp only [Pi.star_apply, schr]
  rw [← h₁ _ (slice_mem hΦ (y + w₂.1)), ← star_star (ψ (y ⬝ᵥ w₂.2 + _)), ← star_mul', conj_psi hψ,
    ← smul_eq_mul (ψ (-_)) (l _), ← map_smul]
  congr 2
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, schr]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  · simp only [sumElim_dotProduct_sumElim, dotProduct_neg]
    ring
  · funext i
    rcases i with i | i <;> rfl
end PositivityTheory.ThK.SiegelT
