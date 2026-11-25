-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eval_const_of_lineDiagonalMap_eq_zero_2be97c4d1be3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:31.493013+00:00
-- url     : https://prove2.me/submissions/c74d2a42-0c5b-4fb0-a5b8-cddd70a11d54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (c : ℂ) (q : MvPolynomial (Fin 1 ⊕ Fin 1) ℂ)
    (hq : lineDiagonalMap q = 0) : eval (fun _ => c) q = 0 := by
  have h2 : ((aeval (fun _ : Fin 1 => c)).comp lineDiagonalMap) q = 0 := by
    rw [AlgHom.comp_apply, hq, map_zero]
  rw [lineDiagonalMap, MvPolynomial.comp_aeval] at h2
  have hpt : (fun i : Fin 1 ⊕ Fin 1 => (aeval (fun _ : Fin 1 => c) : MvPolynomial (Fin 1) ℂ →ₐ[ℂ] ℂ)
      (Sum.elim (X : Fin 1 → MvPolynomial (Fin 1) ℂ) (fun _ => X 0) i)) = fun _ => c := by
    funext s
    rcases s with i | i <;> simp
  rw [hpt] at h2
  rw [← coe_aeval_eq_eval]
  exact h2
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
