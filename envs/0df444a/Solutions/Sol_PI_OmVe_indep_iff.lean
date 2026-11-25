-- Prove2me | solution 1 for PI.OmVe.indep_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:13:01.23863+00:00
-- url     : https://prove2.me/submissions/0feb1bea-43c5-47ff-b214-7e5a6a035a37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_SingleMulVec
import Theorems.Thm_PI_OmVe_ffH_zero_right
import Theorems.Thm_PI_OmVe_ffH_sum_right
import Theorems.Thm_P2M_PI_OmVe_single_mulVec__f4c35258ac1e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmVe
open PI.VolStabSW Matrix
variable {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
namespace PI.OmVe
theorem _root_.solution {a : ℕ} {T : Matrix (Fin a) (Fin a) K} (i₀ : Fin a) (hc : ∀ j, T j i₀ = 0)
    (hu : IsUnit (T + Matrix.single i₀ i₀ 1).det) (X : Fin a → Fin M → K) (hX : ffGram σ J X = T) :
    LinearIndependent K X ↔ ∀ c : K, c • X i₀ = 0 → c = 0 := by
  classical
  constructor
  · intro hli c hc0
    have := Fintype.linearIndependent_iff.1 hli (Pi.single i₀ c) (by simp [Pi.single_apply, hc0])
    simpa using this i₀
  · intro h
    rw [Fintype.linearIndependent_iff]
    intro g hg

    have hT : T *ᵥ g = 0 := by
      funext j
      have := congrArg (ffH σ J (X j)) hg
      rw [ffH_sum_right σ J Finset.univ g (X j) X, ffH_zero_right] at this
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← hX]
      simpa [ffGram, mul_comm] using this
    have hTe : T *ᵥ Pi.single i₀ (g i₀) = 0 := by
      funext j
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, hc]
    have heq : (T + Matrix.single i₀ i₀ (1 : K)) *ᵥ g =
        (T + Matrix.single i₀ i₀ (1 : K)) *ᵥ Pi.single i₀ (g i₀) := by
      rw [Matrix.add_mulVec, Matrix.add_mulVec, hT, hTe, single_mulVec', single_mulVec', Pi.single_eq_same]

    have hinv : (T + Matrix.single i₀ i₀ (1 : K))⁻¹ * (T + Matrix.single i₀ i₀ (1 : K)) = 1 :=
      Matrix.nonsing_inv_mul _ hu
    have hg' : g = Pi.single i₀ (g i₀) := by
      calc g = ((T + Matrix.single i₀ i₀ (1 : K))⁻¹ * (T + Matrix.single i₀ i₀ (1 : K))) *ᵥ g := by
            rw [hinv, Matrix.one_mulVec]
        _ = (T + Matrix.single i₀ i₀ (1 : K))⁻¹ *ᵥ ((T + Matrix.single i₀ i₀ (1 : K)) *ᵥ g) := by
            rw [Matrix.mulVec_mulVec]
        _ = (T + Matrix.single i₀ i₀ (1 : K))⁻¹ *ᵥ ((T + Matrix.single i₀ i₀ (1 : K)) *ᵥ
              Pi.single i₀ (g i₀)) := by rw [heq]
        _ = Pi.single i₀ (g i₀) := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    have hsum : ∑ i, g i • X i = g i₀ • X i₀ := by
      rw [hg']
      simp [Pi.single_apply]
    have h0 : g i₀ = 0 := h _ (hsum ▸ hg)
    intro i
    rw [hg', h0]
    simp
end PI.OmVe
