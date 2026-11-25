-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.CycF.coeff_sum_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:39:03.782973+00:00
-- url     : https://prove2.me/submissions/8e6a4ece-9147-44b2-b2ef-3cbedad8ac98

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.CycF
variable {m n : ℕ} (ε : Fin m → Bool)
variable {ε}
namespace PositivityTheory.Rg.Sw.FFTSteps.CycF
theorem _root_.solution {σ R : Type*} [CommSemiring R] [DecidableEq σ] (S : Finset (σ →₀ ℕ)) (f : (σ →₀ ℕ) → R) (μ : σ →₀ ℕ) :
    coeff μ (∑ ν ∈ S, monomial ν (f ν)) = if μ ∈ S then f μ else 0 := by
  rw [coeff_sum]
  simp only [coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single μ]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h'
      exact absurd h h'
  · apply Finset.sum_eq_zero
    intro b hb
    have : b ≠ μ := fun e => h (e ▸ hb)
    simp [this]
end PositivityTheory.Rg.Sw.FFTSteps.CycF
