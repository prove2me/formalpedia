-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AntisymDivisible_sub_rename_collapse_mem_70f922bc8132
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:43.871942+00:00
-- url     : https://prove2.me/submissions/dca60a73-ff3d-4ee7-9682-000142546190

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.AntisymDivisible
variable {σ : Type*} [DecidableEq σ]
namespace GroundTheory.Heights₂.Heights.AntisymDivisible
theorem _root_.solution (u v : σ) (P : MvPolynomial σ ℝ) :
    P - rename (collapse u v) P ∈ Ideal.span {(X u - X v : MvPolynomial σ ℝ)} := by
  set I := Ideal.span {(X u - X v : MvPolynomial σ ℝ)}
  have h : (Ideal.Quotient.mkₐ ℝ I).comp (rename (collapse u v)) = Ideal.Quotient.mkₐ ℝ I := by
    refine MvPolynomial.algHom_ext fun w => ?_
    simp only [AlgHom.comp_apply, rename_X, collapse, Ideal.Quotient.mkₐ_eq_mk]
    split_ifs with hw
    · subst hw
      exact (Ideal.Quotient.eq.2 (Ideal.subset_span (Set.mem_singleton _))).symm
    · rfl
  rw [← Ideal.Quotient.eq]
  have := congrArg (fun f => f P) h
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
  exact this.symm
end GroundTheory.Heights₂.Heights.AntisymDivisible
