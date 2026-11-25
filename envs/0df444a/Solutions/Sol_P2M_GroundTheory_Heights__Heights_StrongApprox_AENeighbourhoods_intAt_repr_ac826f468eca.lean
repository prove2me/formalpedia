-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_intAt_repr_ac826f468eca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:19:37.65633+00:00
-- url     : https://prove2.me/submissions/30e62f53-6312-4922-bf8a-a0ecc127739b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PAENeighbourhoods
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) {z : Kv E v} (hz : z ∈ intAt E v) :
    ∃ y : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletion F,
      (∀ l, y l ∈ v.adicCompletionIntegers F) ∧ z = ∑ l, y l ⊗ₜ[F] intBasis E l := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, rfl⟩ := hx
    refine ⟨fun l => (RingOfIntegers.basis E).repr b l • a, fun l => zsmul_mem ha _, ?_⟩
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr b]
    rw [map_sum, tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, ← smul_tmul]
    rfl
  | zero => exact ⟨0, fun l => zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨y₁, h₁, rfl⟩ := hx
    obtain ⟨y₂, h₂, rfl⟩ := hy
    exact ⟨y₁ + y₂, fun l => add_mem (h₁ l) (h₂ l), by simp [add_tmul, Finset.sum_add_distrib]⟩
  | neg x _ hx =>
    obtain ⟨y₁, h₁, rfl⟩ := hx
    exact ⟨-y₁, fun l => neg_mem (h₁ l), by simp [neg_tmul, Finset.sum_neg_distrib]⟩
end GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
