-- Prove2me | solution 1 for PositivityTheory.ThKR.Sieg.Heis.char_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:22:49.429828+00:00
-- url     : https://prove2.me/submissions/60c30712-39a1-4dc2-b4b0-bbd914e48c24

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_HaarProductClosedCompact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmulNn
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_SiegelHaar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory MeasureTheory.Measure Topology Set
open scoped NNReal ENNReal Pointwise
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Sieg
variable {A B : Type} [AddCommGroup A] [AddCommGroup B]
variable (β : A →+ A →+ B)
variable [TopologicalSpace A] [TopologicalSpace B]
variable [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]
variable [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
  [LocallyCompactSpace B] [SecondCountableTopology B] [T2Space B] [MeasurableSpace B] [BorelSpace B]
namespace PositivityTheory.ThKR.Sieg
namespace Heis
theorem _root_.solution [IsTopologicalGroup (Heis β)] (hβ : Continuous fun p : A × A => β p.1 p.2) (ψ : Heis β ≃ₜ* Heis β)
    (θ₁ : A ≃ₜ+ A) (θ₂ : B ≃ₜ+ B) (h : ∀ x, ψ x = (θ₁ x.1, θ₂ x.2)) :
    mulEquivHaarChar ψ = addEquivAddHaarChar θ₁ * addEquivAddHaarChar θ₂ := by
  let μ₁ : Measure A := addHaar
  let μ₂ : Measure B := addHaar
  let μ : Measure (Heis β) := μ₁.prod μ₂
  have : IsFiniteMeasureOnCompacts μ := inferInstanceAs (IsFiniteMeasureOnCompacts (μ₁.prod μ₂))
  have : IsOpenPosMeasure μ := inferInstanceAs (IsOpenPosMeasure (μ₁.prod μ₂))
  have : IsMulLeftInvariant μ := ⟨fun x => by
    refine (MeasurePreserving.skew_product (μa := μ₁) (μc := μ₂) (μd := μ₂) (measurePreserving_add_left μ₁ x.1)
      (g := fun a b => x.2 + b + β x.1 a) ?_ (.of_forall fun a => ?_)).map_eq
    · exact ((continuous_const.add continuous_snd).add (hβ.comp (continuous_const.prodMk continuous_fst))).measurable
    · rw [show (fun b => x.2 + b + β x.1 a) = fun b => (x.2 + β x.1 a) + b from funext fun b => by abel]
      exact map_add_left_eq_self μ₂ _⟩
  have : IsHaarMeasure μ := {}
  obtain ⟨U, hU, hU0⟩ := exists_compact_mem_nhds (0 : A)
  obtain ⟨V, hV, hV0⟩ := exists_compact_mem_nhds (0 : B)
  have e := mulEquivHaarChar_smul_preimage μ (X := (U ×ˢ V : Set (A × B))) ψ
  have e1 := addEquivAddHaarChar_smul_preimage μ₁ (X := U) θ₁
  have e2 := addEquivAddHaarChar_smul_preimage μ₂ (X := V) θ₂
  have e3 : ψ ⁻¹' (U ×ˢ V : Set (A × B)) = ((θ₁ ⁻¹' U) ×ˢ (θ₂ ⁻¹' V) : Set (A × B)) := by
    ext x
    change ψ x ∈ (U ×ˢ V : Set (A × B)) ↔ _
    rw [h]
    rfl
  rw [e3] at e
  change _ • (μ₁.prod μ₂) _ = (μ₁.prod μ₂) _ at e
  rw [prod_prod, prod_prod, ← e1, ← e2] at e
  simp only [ENNReal.smul_def, smul_eq_mul] at e
  rw [mul_mul_mul_comm, ← ENNReal.coe_mul] at e
  refine ENNReal.coe_injective ((ENNReal.mul_left_inj (mul_ne_zero ?_ ?_) (ENNReal.mul_ne_top ?_ ?_)).1 e)
  · exact (measure_pos_of_mem_nhds _ (θ₁.continuous.continuousAt.preimage_mem_nhds (x := 0) (by simpa using hU0))).ne'
  · exact (measure_pos_of_mem_nhds _ (θ₂.continuous.continuousAt.preimage_mem_nhds (x := 0) (by simpa using hV0))).ne'
  · exact (θ₁.toHomeomorph.isCompact_preimage.2 hU).measure_lt_top.ne
  · exact (θ₂.toHomeomorph.isCompact_preimage.2 hV).measure_lt_top.ne
end Heis
end PositivityTheory.ThKR.Sieg
