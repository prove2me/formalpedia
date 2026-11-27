-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsBounded_proof_671503a58d50
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:57:39.889835+00:00
-- url     : https://prove2.me/submissions/cfe63ca2-bc73-4873-92e0-b0d06e202ae1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsBounded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRootsBounded
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsBounded_continuous_aeval_e3fd01398676

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
open MvPolynomial Filter Topology NNReal
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace RootsBounded
theorem _root_.solution : RootsBounded.Statement := by
  intro e G hG y₀
  set m := G.natDegree
  let a : ℕ → (Fin e → ℂ) → ℂ := fun k y => aeval y (G.coeff k)
  refine ⟨((1 + ∑ k ∈ Finset.range m, (‖a k y₀‖₊ + 1) : ℝ≥0) : ℝ), ?_⟩
  have hev : ∀ᶠ y in 𝓝 y₀, ∀ k ∈ Finset.range m, ‖a k y‖₊ ≤ ‖a k y₀‖₊ + 1 := by
    rw [eventually_all_finset]
    intro k _
    have hc : Continuous fun y => ‖a k y‖₊ :=
      (RootsBounded.continuous_aeval (G.coeff k)).nnnorm
    exact hc.continuousAt.eventually (gt_mem_nhds (lt_add_one _)) |>.mono fun _ h => h.le
  filter_upwards [hev] with y hy t ht
  set P : Polynomial ℂ := G.map (aeval y).toRingHom
  have hPm : P.Monic := hG.map _
  have hdeg : P.natDegree = m := hG.natDegree_map _
  have hroot : P.IsRoot t := by
    rw [Polynomial.IsRoot, Polynomial.eval_map]; exact ht
  have hlt := Polynomial.IsRoot.norm_lt_cauchyBound hPm.ne_zero hroot
  have hcb : Polynomial.cauchyBound P ≤ 1 + ∑ k ∈ Finset.range m, (‖a k y₀‖₊ + 1) := by
    rw [Polynomial.cauchyBound, hPm.leadingCoeff, nnnorm_one, div_one, add_comm]
    gcongr
    rw [hdeg]
    refine Finset.sup_le fun k hk => ?_
    have hcoeff : P.coeff k = a k y := by
      simp [P, a, Polynomial.coeff_map]
    rw [hcoeff]
    exact (hy k hk).trans (Finset.single_le_sum (f := fun k => ‖a k y₀‖₊ + 1)
      (fun _ _ => bot_le) hk)
  have : ‖t‖₊ ≤ 1 + ∑ k ∈ Finset.range m, (‖a k y₀‖₊ + 1) := (hlt.trans_le hcb).le
  exact_mod_cast this
end RootsBounded
end GroundTheory.Heights₂.Heights.HilbertSamuel
