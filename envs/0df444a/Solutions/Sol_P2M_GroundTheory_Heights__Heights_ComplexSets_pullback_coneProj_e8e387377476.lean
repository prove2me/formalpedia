-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_pullback_coneProj_e8e387377476
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:53:06.427104+00:00
-- url     : https://prove2.me/submissions/ca73d715-3284-41be-8dba-ccdf59bafc9e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Pointwise
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution (P : MvPolynomial (Fin 2) ℂ) :
    finSuccEquiv ℂ 2 (pullback coneProj P) = Polynomial.C P := by
  have h : ((finSuccEquiv ℂ 2).toAlgHom.comp (pullback coneProj) :
      MvPolynomial (Fin 2) ℂ →ₐ[ℂ] Polynomial (MvPolynomial (Fin 2) ℂ)) =
      (Algebra.ofId (MvPolynomial (Fin 2) ℂ) (Polynomial (MvPolynomial (Fin 2) ℂ))).restrictScalars ℂ := by
    apply MvPolynomial.algHom_ext
    intro i
    have h1 : (X 1 : MvPolynomial (Fin 3) ℂ) = X (Fin.succ 0) := rfl
    have h2 : (X 2 : MvPolynomial (Fin 3) ℂ) = X (Fin.succ 1) := rfl
    fin_cases i <;>
      simp [pullback, linPoly, coneProj, Fin.sum_univ_three, h1, h2, finSuccEquiv_X_succ]
  exact DFunLike.congr_fun h P
end GroundTheory.Heights₂.Heights.ComplexSets
