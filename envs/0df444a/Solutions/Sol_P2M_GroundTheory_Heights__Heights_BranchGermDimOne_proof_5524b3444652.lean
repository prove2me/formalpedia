-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BranchGermDimOne_proof_5524b3444652
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:58:22.152396+00:00
-- url     : https://prove2.me/submissions/9772ec52-595d-4434-92ed-82cc4dbfdfac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchGermDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZeroSetOpenMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZeroDimIsolated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalDimComponentBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchGermDimOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarBranch_dimH_image_le_two_99601624bb5f

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
open MvPolynomial ComplexSets Filter Topology
open scoped NNReal ENNReal
namespace GroundTheory.Heights₂.Heights
namespace BranchGermDimOne
theorem _root_.solution (h₀ : LocalDimComponentBound.Statement) (h₁ : ZeroDimIsolated.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.Statement) : BranchGermDimOne.Statement := by
  intro n I q m c hm ⟨N, hN, hcov⟩
  let c₀ := c ⟨0, hm⟩
  have hq : q ∈ zeroSet I := c₀.map_zero ▸ c₀.mapsTo (Metric.mem_ball_self c₀.radius_pos)
  have hdimH : dimH (zeroSet I ∩ N) ≤ 2 :=
    (dimH_mono hcov).trans ((dimH_iUnion _).le.trans (iSup_le fun b ↦ (c b).dimH_image_le_two))
  apply le_antisymm
  · obtain ⟨W, hW, hIW, hqW, hle⟩ := h₀ n I q hq
    have hup : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ (n : ℕ) := by
      refine (ringKrullDim_quotient_le W).trans (le_of_eq ?_)
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    have hnn : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) := by
      have := hW
      exact ringKrullDim_nonneg_of_nontrivial
    obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = d := by
      revert hnn hup
      generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = x
      intro hup hnn
      induction x using WithBot.recBotCoe with
      | bot => exact absurd hnn (by simp)
      | coe e =>
        induction e using ENat.recTopCoe with
        | top => exact absurd hup (not_le.2 (WithBot.coe_lt_coe.2 (ENat.natCast_lt_top n)))
        | coe d => exact ⟨d, rfl⟩
    rw [hd] at hle
    refine hle.trans ?_
    by_contra hlt
    have h2 : 2 ≤ d := by
      by_contra h
      exact hlt (by exact_mod_cast (by omega : d ≤ 1))
    have hpos := h₂ n d W hW hd q (interior N) isOpen_interior (mem_interior_iff_mem_nhds.2 hN) hqW
    have hsub : zeroSet W ∩ interior N ⊆ zeroSet I ∩ N :=
      fun x hx ↦ ⟨fun f hf ↦ hx.1 f (hIW hf), interior_subset hx.2⟩
    have hlt' : dimH (zeroSet W ∩ interior N) < (((2 * d : ℕ) : ℝ≥0) : ℝ≥0∞) := by
      refine ((dimH_mono hsub).trans hdimH).trans_lt ?_
      rw [ENNReal.coe_natCast]
      exact_mod_cast (by omega : 2 < 2 * d)
    have h0 := hausdorffMeasure_of_dimH_lt hlt'
    rw [NNReal.coe_natCast] at h0
    exact hpos.ne' h0
  · by_contra hlt
    have h0 : ringKrullDim (curveLocalRing I q) ≤ 0 := by
      generalize ringKrullDim (curveLocalRing I q) = x at hlt
      induction x using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe e =>
        have he : e < 1 := by
          by_contra h'
          exact hlt (by exact_mod_cast not_lt.1 h')
        rw [Order.lt_one_iff] at he
        subst he
        exact le_rfl
    obtain ⟨N', hN', hiso⟩ := h₁ n I q h0
    have hcont : ContinuousAt c₀.toFun 0 :=
      c₀.differentiableOn.continuousOn.continuousAt (Metric.ball_mem_nhds 0 c₀.radius_pos)
    have hN'' : N' ∈ 𝓝 (c₀.toFun 0) := by rw [c₀.map_zero]; exact hN'
    have hev : ∀ᶠ t in 𝓝 (0 : Fin 1 → ℂ), t ∈ Metric.ball 0 c₀.radius ∧ c₀.toFun t ∈ N' :=
      Filter.Eventually.and (Metric.ball_mem_nhds 0 c₀.radius_pos) (hcont hN'')
    have hne : (𝓝[≠] (0 : Fin 1 → ℂ)).NeBot := inferInstance
    have hev' : ∀ᶠ t in 𝓝[≠] (0 : Fin 1 → ℂ), (t ∈ Metric.ball 0 c₀.radius ∧ c₀.toFun t ∈ N') ∧ t ≠ 0 :=
      (Filter.Eventually.filter_mono nhdsWithin_le_nhds hev).and self_mem_nhdsWithin
    obtain ⟨t, ⟨ht, htN⟩, ht0⟩ := hev'.exists
    have hx : c₀.toFun t = q := hiso ⟨c₀.mapsTo ht, htN⟩
    exact ht0 (c₀.injOn ht (Metric.mem_ball_self c₀.radius_pos) (hx.trans c₀.map_zero.symm))
end BranchGermDimOne
end GroundTheory.Heights₂.Heights
