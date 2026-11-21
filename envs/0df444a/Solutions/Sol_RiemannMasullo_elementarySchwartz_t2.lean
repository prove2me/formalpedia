-- Prove2me | solution 1 for RiemannMasullo.elementarySchwartz_t2
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:22:25.650168+00:00
-- url     : https://prove2.me/submissions/454e6018-64a1-437f-a359-4635c1bc92e5

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L439-L439
import Theorems.Thm_RiemannMasullo_elementarySchwartz_withSeminorms
import Theorems.Thm_RiemannMasullo_elementarySchwartzBound_zero
import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
open RiemannMasullo
open scoped ENNReal
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
theorem solution : T2Space (ElementarySchwartz m n r F) := by
  classical
  haveI : T1Space (ElementarySchwartz m n r F) :=
    elementarySchwartz_withSeminorms.T1_of_separating (by
      intro f hf
      refine ⟨(0,0,0,0), ?_⟩
      intro hz
      apply hf
      apply Subtype.ext
      funext g
      change (elementarySchwartzBound f.val (0,0,0,0)).toReal = 0 at hz
      have hfin := (f.property.2 (0,0,0,0)).ne
      have hzero : elementarySchwartzBound f.val (0,0,0,0) = 0 :=
        ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right hfin
      rw [elementarySchwartzBound_zero] at hzero
      have hb := le_iSup (fun x ↦ (‖f.val x‖₊ : ℝ≥0∞)) g
      rw [hzero] at hb
      change f.val g = 0
      simpa using (le_antisymm hb (by positivity)))
  infer_instance
