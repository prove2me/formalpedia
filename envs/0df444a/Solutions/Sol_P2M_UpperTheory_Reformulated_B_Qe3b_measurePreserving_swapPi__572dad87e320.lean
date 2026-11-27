-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qe3b_measurePreserving_swapPi__572dad87e320
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:14:33.372858+00:00
-- url     : https://prove2.me/submissions/8deef54a-3226-45d9-b46e-8e856f507751

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MeasurePreservingSwapPi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qe3b.measurePreserving_swapPi
open MeasureTheory
theorem _root_.solution.{u_1, u_2, u_3} :
    ∀ {ι : Type u_1} {κ : Type u_2} {X : Type u_3} [inst : Fintype ι] [inst_1 : Fintype κ]
    [inst_2 : MeasurableSpace X] (ν : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite ν],
    MeasureTheory.MeasurePreserving (fun (f : ι → κ → X) (k : κ) (i : ι) ↦ f i k)
      (MeasureTheory.Measure.pi fun (x : ι) ↦ MeasureTheory.Measure.pi fun (x : κ) ↦ ν)
      (MeasureTheory.Measure.pi fun (x : κ) ↦ MeasureTheory.Measure.pi fun (x : ι) ↦ ν) := by
  intro ι κ X _ _ _ ν _
  have mp_left :
      MeasurePreserving (fun (f : ι → κ → X) (p : ι × κ) ↦ f p.1 p.2)
        (Measure.pi fun (_ : ι) ↦ Measure.pi fun (_ : κ) ↦ ν)
        (Measure.pi fun (_ : ι × κ) ↦ ν) := by
    have hm : Measurable (fun (f : ι → κ → X) (p : ι × κ) ↦ f p.1 p.2) := by fun_prop
    refine ⟨hm, (Measure.pi_eq fun s hs ↦ ?_).symm⟩
    rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
    have h : (fun (f : ι → κ → X) (p : ι × κ) ↦ f p.1 p.2) ⁻¹' Set.univ.pi s
        = Set.univ.pi fun i ↦ Set.univ.pi fun k ↦ s (i, k) := by
      ext f
      simp [Set.mem_pi]
    rw [h, Measure.pi_pi, Fintype.prod_prod_type]
    exact Finset.prod_congr rfl fun i _ ↦ Measure.pi_pi _ _
  have mp_right :
      MeasurePreserving (fun (f : κ → ι → X) (p : ι × κ) ↦ f p.2 p.1)
        (Measure.pi fun (_ : κ) ↦ Measure.pi fun (_ : ι) ↦ ν)
        (Measure.pi fun (_ : ι × κ) ↦ ν) := by
    have hm : Measurable (fun (f : κ → ι → X) (p : ι × κ) ↦ f p.2 p.1) := by fun_prop
    refine ⟨hm, (Measure.pi_eq fun s hs ↦ ?_).symm⟩
    rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
    have h : (fun (f : κ → ι → X) (p : ι × κ) ↦ f p.2 p.1) ⁻¹' Set.univ.pi s
        = Set.univ.pi fun k ↦ Set.univ.pi fun i ↦ s (i, k) := by
      ext f
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Prod.forall]
      exact forall_comm
    rw [h, Measure.pi_pi, Fintype.prod_prod_type_right]
    exact Finset.prod_congr rfl fun i _ ↦ Measure.pi_pi _ _
  let e : (κ → ι → X) ≃ᵐ (ι × κ → X) :=
    { toFun := fun f p ↦ f p.2 p.1
      invFun := fun g k i ↦ g (i, k)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      measurable_toFun := by
        change Measurable (fun (f : κ → ι → X) (p : ι × κ) ↦ f p.2 p.1)
        fun_prop
      measurable_invFun := by
        change Measurable (fun (g : ι × κ → X) (k : κ) (i : ι) ↦ g (i, k))
        fun_prop }
  exact (MeasureTheory.MeasurePreserving.symm e
    (mp_right)).comp (mp_left)
end UpperTheory.Reformulated.B.Qe3b.measurePreserving_swapPi
