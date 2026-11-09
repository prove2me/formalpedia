-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P08.proposition3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T06:07:34.104478+00:00
-- url     : https://prove2.me/submissions/210e004e-5bb3-4975-80a2-04cf4742932f

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P08

open Set MeasureTheory

open scoped BigOperators Topology CompactlySupported

open QAlgorithms.Papers.Independent.Intakethird100.P08 in
theorem solution {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSpace A] [BorelSpace A]
    (rho : ContinuousModule G A) :
    locallyContinuousOneCocycles rho = continuousOneCocycles rho := by
  ext c
  constructor
  · rintro ⟨⟨_, U, hU, h1, hcU⟩, hc⟩
    refine ⟨?_, hc⟩
    rw [continuous_iff_continuousAt]
    intro g
    have hc1 : ContinuousAt c 1 := hcU.continuousAt (hU.mem_nhds h1)
    have hT : ContinuousAt (fun x : G => g⁻¹ * x) g :=
      (continuous_const.mul continuous_id).continuousAt
    have hcomp : ContinuousAt (fun x => c (g⁻¹ * x)) g :=
      ContinuousAt.comp_of_eq hc1 hT (inv_mul_cancel g)
    have hρ : Continuous (fun a => rho.action g a) :=
      rho.continuous_action.comp (continuous_const.prodMk continuous_id)
    have heq : c = fun x => c g + rho.action g (c (g⁻¹ * x)) := by
      funext x
      rw [← hc g (g⁻¹ * x), mul_inv_cancel_left]
    rw [heq]
    exact continuousAt_const.add (hρ.continuousAt.comp hcomp)
  · rintro ⟨hcont, hc⟩
    exact ⟨⟨hcont.measurable, univ, isOpen_univ, mem_univ _, hcont.continuousOn⟩, hc⟩
