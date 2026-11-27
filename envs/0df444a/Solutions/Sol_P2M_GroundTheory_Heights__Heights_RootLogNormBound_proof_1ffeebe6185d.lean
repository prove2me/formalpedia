-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootLogNormBound_proof_1ffeebe6185d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:07:50.405233+00:00
-- url     : https://prove2.me/submissions/7939bc69-6ef0-4d98-bdd5-956ff961f955

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootLogNormBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootLogNormBoundAlt_log_block_d4d21477d1a4

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open RootLogNormBoundAlt
namespace GroundTheory.Heights₂.Heights
namespace RootLogNormBound
theorem _root_.solution (h₁ : RootAnchorNonzero.Statement) (h₂ : RootPointConj.Statement)
    (h₃ : PlueckerKernel.Statement) : RootLogNormBound.Statement := by
  intro f j m ζ hζ z hz
  have hpos : ∀ τ : Fin f, 0 < ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖ := fun τ =>
    (fsMetric (PlIdx j m)).pos _ fun h0 => by
      obtain ⟨i, hi⟩ := hz.1 τ
      exact hi (congrFun h0 i)
  have key : ∀ τ : Fin f, -((j : ℝ) / 2 * Real.log (1 + m)) ≤
      Real.log (‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖) := by
    intro τ
    obtain ⟨ζ', hζ', hz'⟩ := h₂ f j m ζ hζ z hz τ
    exact log_block h₃ j m ζ' (fun a b => by
        obtain ⟨k, hk, h⟩ := hζ' a b
        exact Complex.norm_eq_one_of_pow_eq_one h hk.ne')
      _ (h₁ f j m ζ hζ z hz τ) _ hz' (hpos τ)
  have hne : ∀ τ ∈ (Finset.univ : Finset (Fin f)),
      ‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖ ≠ 0 := fun τ _ =>
    div_ne_zero (norm_ne_zero_iff.mpr (h₁ f j m ζ hζ z hz τ)) (hpos τ).ne'
  have e : logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) z =
      ∑ τ, Real.log (‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖) := by
    rw [← Real.log_prod hne]
    simp [logNorm, fsMulti, HermLine.ofMetrics, fsMetric, rootAnchorSection, Finset.prod_div_distrib]
  rw [e]
  calc -grassConst f j m = ∑ _τ : Fin f, -((j : ℝ) / 2 * Real.log (1 + m)) := by
        simp [grassConst]; ring
    _ ≤ _ := Finset.sum_le_sum fun τ _ => key τ
end RootLogNormBound
end GroundTheory.Heights₂.Heights
