-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_frame_lines_not_in_zeroSet_ce830c4b1c26
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:16:23.043917+00:00
-- url     : https://prove2.me/submissions/867486aa-c405-4649-b759-fecab2f244e7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PolynomialFrame
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialFrame_exists_eval_line_ne_zero_0db500c9f83d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialFrame_homogeneousComponent_totalDegree_ne_zero_8d37d44c0148

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology
noncomputable section
open PolynomialFrame
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {k : ℕ} {P : MvPolynomial (Fin k) ℂ} (hP : P ≠ 0) :
    ∃ M : Matrix (Fin k) (Fin k) ℂ, M.det ≠ 0 ∧
      ∀ (i : Fin k) (w : Fin k → ℂ), ∃ t : ℂ, eval (w + t • fun j => M j i) P ≠ 0 := by
  set Pd := homogeneousComponent P.totalDegree P
  have hPd : Pd ≠ 0 := homogeneousComponent_totalDegree_ne_zero hP
  set F : MvPolynomial (Fin k × Fin k) ℂ :=
    (Matrix.mvPolynomialX (Fin k) (Fin k) ℂ).det * ∏ i, rename (fun j => (j, i)) Pd
  have hF : F ≠ 0 := by
    refine mul_ne_zero (Matrix.det_mvPolynomialX_ne_zero _ _) (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
    have hinj : Function.Injective (fun j : Fin k => (j, i)) := fun a b h => (Prod.ext_iff.mp h).1
    intro h
    exact hPd (rename_injective _ hinj (by rw [h, map_zero]))
  obtain ⟨s, hs⟩ : ∃ s : Fin k × Fin k → ℂ, eval s F ≠ 0 := by
    by_contra! hs
    exact hF (MvPolynomial.funext fun x => by rw [hs x, map_zero])
  refine ⟨Matrix.of fun i j => s (i, j), ?_, fun i w => exists_eval_line_ne_zero P _ ?_ w⟩
  · have h := hs
    rw [map_mul, Matrix.eval_det_mvPolynomialX] at h
    exact left_ne_zero_of_mul h
  · have h : eval s F ≠ 0 := hs
    rw [map_mul, map_prod] at h
    have h2 := (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul h)) i (Finset.mem_univ i)
    rw [eval_rename] at h2
    exact h2
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
