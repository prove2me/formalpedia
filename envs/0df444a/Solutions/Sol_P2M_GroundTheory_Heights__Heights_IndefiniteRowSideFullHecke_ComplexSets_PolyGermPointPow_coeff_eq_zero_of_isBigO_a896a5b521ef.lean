-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyGermPointPow_coeff_eq_zero_of_isBigO_a896a5b521ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:31:53.202142+00:00
-- url     : https://prove2.me/submissions/ef801dea-f3db-4a3f-8e87-7cafae719d1e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolyGermPointPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalSmulOfIsHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolyGermPointPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Filter Asymptotics
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolyGermPointPow
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolyGermPointPow
theorem _root_.solution {P : Polynomial ℂ} {k : ℕ}
    (h : (fun t => P.eval t) =O[𝓝 0] fun t : ℂ => ‖t‖ ^ k) : ∀ d < k, P.coeff d = 0 := by
  induction k with
  | zero => intro d hd; exact absurd hd (Nat.not_lt_zero _)
  | succ k ih =>
    have hn : (fun t : ℂ => ‖t‖) =O[𝓝 0] fun _ => (1 : ℝ) := (continuous_norm.tendsto (0 : ℂ)).isBigO_one ℝ
    have hk := ih (h.trans (by simpa [pow_succ] using (isBigO_refl (fun t : ℂ => ‖t‖ ^ k) _).mul hn))
    obtain ⟨Q, hQ⟩ := Polynomial.X_pow_dvd_iff.mpr hk
    intro d hd
    rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd | hd
    · exact hk d hd
    rw [hd, hQ, Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, Polynomial.coeff_zero_eq_eval_zero]
    obtain ⟨c, hc⟩ := h.bound
    have h1 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖Q.eval t‖ ≤ c * ‖t‖ := by
      filter_upwards [nhdsWithin_le_nhds hc, self_mem_nhdsWithin] with t ht ht0
      rw [hQ, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, norm_mul, norm_pow, norm_pow,
        norm_norm, pow_succ] at ht
      have hp : 0 < ‖t‖ ^ k := pow_pos (norm_pos_iff.mpr ht0) k
      exact le_of_mul_le_mul_left (by linarith) hp
    have h2 : Tendsto (fun t => ‖Q.eval t‖) (𝓝[≠] 0) (𝓝 ‖Q.eval 0‖) :=
      ((Q.continuous.tendsto 0).norm).mono_left nhdsWithin_le_nhds
    have h3 : Tendsto (fun t : ℂ => c * ‖t‖) (𝓝[≠] 0) (𝓝 0) := by
      simpa using ((continuous_norm.tendsto (0 : ℂ)).const_mul c).mono_left nhdsWithin_le_nhds
    exact norm_le_zero_iff.mp (le_of_tendsto_of_tendsto h2 h3 h1)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolyGermPointPow
