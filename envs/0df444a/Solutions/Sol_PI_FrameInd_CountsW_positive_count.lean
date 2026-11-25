-- Prove2me | solution 1 for PI.FrameInd.CountsW.positive_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:56:33.552293+00:00
-- url     : https://prove2.me/submissions/af61551d-08ca-40c9-a557-f312119be804

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NonposCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_Counts
import Theorems.Thm_PI_FrameInd_CountsW_extZ_apply
import Theorems.Thm_PI_FrameInd_CountsW_re_diag
import Theorems.Thm_PI_FrameInd_CountsW_blockA_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.FrameInd PI.FrameInd.CountsW
open PI.FrameInd
namespace PI.FrameInd.CountsW
theorem _root_.solution : PosCount := by
  intro k r z z' γ hs hp hdet
  set hA := isHerm k r z z' γ with hhA
  let p : Fin (r + 1) ⊕ Fin (r + 1) → Prop := fun i => 0 < hA.eigenvalues i
  let ψ : ({i // p i} → ℂ) →ₗ[ℂ] (Fin (r + 1) → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Sum.inr : Fin (r + 1) → Fin (r + 1) ⊕ Fin (r + 1))).comp
      ((Matrix.mulVecLin (hA.eigenvectorUnitary : Matrix _ _ ℂ)).comp (extZ p))
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hinr : ∀ b, ((hA.eigenvectorUnitary : Matrix (Fin (r + 1) ⊕ Fin (r + 1))
        (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) *ᵥ extZ p y) (Sum.inr b) = 0 := by
      intro b
      have := congrFun hy b
      simpa [ψ, LinearMap.funLeft_apply] using this
    have h1 := re_diag hA (extZ p y)
    rw [blockA_re k r z z' γ hs.2.1.1 _ hinr] at h1
    have hT : (herm (Hpk k r) z z).re < 0 := by
      have := hs.2.1.2; simp only [Tz] at this; linarith
    have hl : (herm (Hpk k r) z z).re *
        Complex.normSq (((hA.eigenvectorUnitary : Matrix (Fin (r + 1) ⊕ Fin (r + 1))
          (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) *ᵥ extZ p y) (Sum.inl (Fin.last r))) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hT.le (Complex.normSq_nonneg _)
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin (r + 1) ⊕ Fin (r + 1))),
        0 ≤ hA.eigenvalues i * Complex.normSq (extZ p y i) := by
      intro i _
      rw [extZ_apply]
      split_ifs with h
      · exact mul_nonneg h.le (Complex.normSq_nonneg _)
      · simp
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1
      (le_antisymm (h1 ▸ hl) (Finset.sum_nonneg hnn))
    funext t
    have := hz t.1 (Finset.mem_univ _)
    rw [extZ_apply, dif_pos t.2] at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (ne_of_gt t.2)
    · simpa [Complex.normSq_eq_zero] using h
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_fintype_fun_eq_card] using this
end PI.FrameInd.CountsW
