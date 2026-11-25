-- Prove2me | solution 1 for QPK.invOn_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:46.735239+00:00
-- url     : https://prove2.me/submissions/c2a565fd-8851-433f-b085-35a873cbba37

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_LintegralFintypeProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_WeilQuotientGlobalAssumptions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open QPK
variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, MeasurableSpace (G v)]
  [∀ v, MeasurableMul₂ (G v)]
namespace QPK
theorem _root_.solution (K : ∀ v, Set (G v)) (μ : ∀ v, Measure (G v)) (h : ∀ v, InvOn (μ v) (K v)) :
    InvOn (Measure.pi μ) (Set.pi univ K) := by
  haveI : ∀ v, SigmaFinite (μ v) := fun v => (h v).1
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun m : Measure (∀ v, G v) => m univ) h0
    simp only [Measure.pi_univ, Measure.coe_zero, Pi.zero_apply, Finset.prod_eq_zero_iff,
      Finset.mem_univ, true_and] at h1
    obtain ⟨v, hv⟩ := h1
    exact (h v).2.1 (Measure.measure_univ_eq_zero.1 hv)
  · have e : (Set.pi univ K)ᶜ = ⋃ v, (fun x : (∀ v, G v) => x v) ⁻¹' (K v)ᶜ := by
      ext x
      simp [Set.mem_pi]
    rw [e]
    exact measure_iUnion_null fun v => Measure.pi_eval_preimage_null μ ((h v).2.2.1)
  · intro s hs
    have hmap : ∀ v, (μ v).map (fun x => s v * x) = μ v := fun v => (h v).2.2.2 (s v) (hs v trivial)
    haveI : ∀ v, SigmaFinite ((μ v).map (fun x => s v * x)) := fun v => by
      rw [hmap v]
      infer_instance
    have e : (fun x : (∀ v, G v) => s * x) = fun x v => (fun y => s v * y) (x v) := rfl
    rw [e, Measure.pi_map_pi (fun v => (measurable_const_mul (s v)).aemeasurable)]
    simp only [hmap]
end QPK
