-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P82.product_symmetries
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T19:22:04.383523+00:00
-- url     : https://prove2.me/submissions/0abcbd93-f837-473e-8bcc-27c15bd91254

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P82

open Filter MeasureTheory Set

open scoped Topology BigOperators ENNReal

attribute [local instance] Classical.propDecidable

noncomputable section

section CompactDynamics

variable {M : Type*} [instMetric : MetricSpace M] [instCompact : CompactSpace M]
  [instNonempty : Nonempty M] [instMeasurable : MeasurableSpace M] [instBorel : BorelSpace M]

include instCompact instNonempty instBorel

local instance : DecidableEq M := Classical.decEq M

open QAlgorithms.Papers.Independent.Intake100.P82 in
theorem solution (v : M → M) (hv : Continuous v) :
    (Continuous (fun z : M × M => (v z.1, v z.2)) ∧
      Symmetry (fun z : M × M => (v z.1, v z.2)) (Homeomorph.prodComm M M) false) ∧
    ∀ f : M ≃ₜ M,
      Continuous (fun z : M × M => (f z.1, f.symm z.2)) ∧
      Symmetry (fun z : M × M => (f z.1, f.symm z.2)) (Homeomorph.prodComm M M) true := by
  have hinv : Function.Involutive (Homeomorph.prodComm M M) := by
    intro z
    first | rfl | simp
  refine ⟨⟨(hv.comp continuous_fst).prodMk (hv.comp continuous_snd), hinv, ?_⟩, fun f => ?_⟩
  · rw [if_neg (by simp)]
    intro x
    first | rfl | simp
  · refine ⟨(f.continuous.comp continuous_fst).prodMk (f.symm.continuous.comp continuous_snd),
      hinv, ?_⟩
    rw [if_pos rfl]
    refine ⟨f.prodCongr f.symm, fun x => ?_, fun x => ?_⟩
    · first | rfl | simp
    · first | rfl | simp

end CompactDynamics

end
