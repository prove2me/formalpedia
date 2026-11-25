-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_VolumePreservingUncurry_volume_preserving_uncurry__ff0a4f2b7d3b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:02:04.028802+00:00
-- url     : https://prove2.me/submissions/97c47677-9e4e-487b-9a6e-fad309318957

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VolumePreservingUncurry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.VolumePreservingUncurry.volume_preserving_uncurry
theorem _root_.solution.{u_1, u_2} :
    ∀ (ι : Type u_1) (κ : Type u_2) [inst : Fintype ι] [inst_1 : Fintype κ],
      @MeasureTheory.MeasurePreserving (ι → κ → Real) (Prod ι κ → Real)
        (@MeasureTheory.MeasureSpace.toMeasurableSpace (ι → κ → Real)
          (@MeasureTheory.MeasureSpace.pi ι inst (fun (a : ι) ↦ κ → Real) fun (i : ι) ↦
            @MeasureTheory.MeasureSpace.pi κ inst_1 (fun (a : κ) ↦ Real) fun (i : κ) ↦ Real.measureSpace))
        (@MeasureTheory.MeasureSpace.toMeasurableSpace (Prod ι κ → Real)
          (@MeasureTheory.MeasureSpace.pi (Prod ι κ) (@instFintypeProd ι κ inst inst_1) (fun (a : Prod ι κ) ↦ Real)
            fun (i : Prod ι κ) ↦ Real.measureSpace))
        (@Function.uncurry ι κ Real)
        (@MeasureTheory.MeasureSpace.volume (ι → κ → Real)
          (@MeasureTheory.MeasureSpace.pi ι inst (fun (a : ι) ↦ κ → Real) fun (i : ι) ↦
            @MeasureTheory.MeasureSpace.pi κ inst_1 (fun (a : κ) ↦ Real) fun (i : κ) ↦ Real.measureSpace))
        (@MeasureTheory.MeasureSpace.volume (Prod ι κ → Real)
          (@MeasureTheory.MeasureSpace.pi (Prod ι κ) (@instFintypeProd ι κ inst inst_1) (fun (a : Prod ι κ) ↦ Real)
            fun (i : Prod ι κ) ↦ Real.measureSpace)) := by
  intro ι κ _ _
  have hm : Measurable (@Function.uncurry ι κ ℝ) :=
    measurable_pi_lambda _ fun p ↦ (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  refine ⟨hm, ?_⟩
  symm
  refine MeasureTheory.Measure.pi_eq (μ := fun _ : ι × κ ↦ (MeasureTheory.volume : MeasureTheory.Measure ℝ)) ?_
  intro s hs
  rw [MeasureTheory.Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (@Function.uncurry ι κ ℝ) ⁻¹' (Set.univ.pi s)
      = Set.univ.pi fun i ↦ Set.univ.pi fun k ↦ s (i, k) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Prod.forall,
      Function.uncurry_apply_pair]
  rw [hpre, MeasureTheory.volume_pi_pi, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [MeasureTheory.volume_pi_pi]
end UpperTheory.Reformulated.B.VolumePreservingUncurry.volume_preserving_uncurry
