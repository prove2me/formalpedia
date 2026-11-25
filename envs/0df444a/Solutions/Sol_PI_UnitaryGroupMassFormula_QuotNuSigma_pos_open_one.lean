-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QuotNuSigma.pos_open_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:42:17.054933+00:00
-- url     : https://prove2.me/submissions/7b11a330-e0f6-459e-bbaa-da9a5beadd74

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotNuSigma
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientSigmaFiniteness_SigmaFiniteOfWeil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QuotNuSigma
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace PI.UnitaryGroupMassFormula.QuotNuSigma
theorem _root_.solution (A : Set G) (μA : Measure G) (h0 : μA ≠ 0) (hc : μA Aᶜ = 0)
    (hinv : ∀ s ∈ A, μA.map (fun x => s * x) = μA) (U : Set G) (hU : IsOpen U) (h1 : (1 : G) ∈ U) :
    0 < μA U := by
  by_contra hpos
  have hU0 : μA U = 0 := nonpos_iff_eq_zero.1 (not_lt.1 hpos)
  let F : A → Set G := fun s => (fun x => (s : G)⁻¹ * x) ⁻¹' U
  have hFo : ∀ s, IsOpen (F s) := fun s => hU.preimage (continuous_const.mul continuous_id)
  have hF0 : ∀ s, μA (F s) = 0 := by
    intro s
    have hm := congrArg (fun m : Measure G => m (F s)) (hinv s s.2)
    rw [← hm, Measure.map_apply (measurable_const_mul _) (hFo s).measurableSet]
    have hpre : (fun x => (s : G) * x) ⁻¹' F s = U := by
      ext x
      simp [F]
    rw [hpre, hU0]
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable F hFo
  have hcov : A ⊆ ⋃ s ∈ T, F s := by
    intro a ha
    rw [hTU]
    exact Set.mem_iUnion.2 ⟨⟨a, ha⟩, by simp [F, h1]⟩
  have hnull : μA (⋃ s ∈ T, F s) = 0 := (measure_biUnion_null_iff hT).2 fun s _ => hF0 s
  have huniv : μA Set.univ = 0 := by
    refine measure_mono_null (fun x _ => ?_) (measure_union_null hnull hc)
    by_cases hx : x ∈ A
    · exact Or.inl (hcov hx)
    · exact Or.inr hx
  exact h0 (Measure.measure_univ_eq_zero.1 huniv)
end PI.UnitaryGroupMassFormula.QuotNuSigma
