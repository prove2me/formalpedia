-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.det_map_C_add_X_sq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:07:11.407593+00:00
-- url     : https://prove2.me/submissions/642b4aff-d36d-4a54-8ddb-1efbfc6fcfb7

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Filter Topology Polynomial Matrix
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (M : Matrix n n ℂ[X]) :
    ∃ r : ℂ[X], (A.map C + (X ^ 2 : ℂ[X]) • M).det = C A.det + X ^ 2 * r := by
  have hmap : (A.map C + (X ^ 2 : ℂ[X]) • M).map (Ideal.Quotient.mk (Ideal.span {X ^ 2})) =
      (A.map C).map (Ideal.Quotient.mk (Ideal.span {(X : ℂ[X]) ^ 2})) := by
    ext i j
    simp [Ideal.Quotient.mk_singleton_self]
  have h := congrArg Matrix.det hmap
  have e1 : (Ideal.Quotient.mk (Ideal.span {(X : ℂ[X]) ^ 2})) (A.map C + (X ^ 2 : ℂ[X]) • M).det =
      (Ideal.Quotient.mk (Ideal.span {(X : ℂ[X]) ^ 2})) (A.map C).det := by
    rw [RingHom.map_det, RingHom.map_det]
    exact h
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at e1
  obtain ⟨r, hr⟩ := e1
  refine ⟨r, ?_⟩
  have hdet : (A.map C).det = C A.det := (RingHom.map_det C A).symm
  rw [hdet] at hr
  linear_combination hr
end ReciprocityTheory.AnForm.P
