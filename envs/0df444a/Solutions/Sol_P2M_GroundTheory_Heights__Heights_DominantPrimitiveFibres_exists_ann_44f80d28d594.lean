-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_exists_ann_44f80d28d594
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:07:34.110778+00:00
-- url     : https://prove2.me/submissions/195e1dd7-932a-4e06-939f-511272e93e25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StDominantPrimitiveFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDominantFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDominantPrimitiveFibres
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_dim_eq_152f4491059c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DominantFibreBound_exists_poly_0a4987dfdbda


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
open MvPolynomial ComplexSets
open GroundTheory.Heights₂.Heights.DominantPrimitiveFibres
namespace GroundTheory.Heights₂.Heights.DominantPrimitiveFibres
theorem _root_.solution (hG : GenericProjectionFinite.Statement) {n d : ℕ} (Q : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin d) (Fin n) ℂ) (hQ : Q.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) ≤ ((d : ℕ) : WithBot ℕ∞))
    (hinj : Function.Injective (projHom Q A)) (b : MvPolynomial (Fin n) ℂ ⧸ Q) :
    letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ Q) := (projHom Q A).toRingHom.toAlgebra
    ∃ g : Polynomial (MvPolynomial (Fin d) ℂ), g ≠ 0 ∧ Polynomial.aeval b g = 0 := by
  letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ Q) := (projHom Q A).toRingHom.toAlgebra
  have hinj' : Function.Injective ((Ideal.Quotient.mkₐ ℂ Q).comp (aeval (linPoly A))) := hinj
  obtain ⟨g, hg0, hgb⟩ :=
    DominantFibreBound.exists_poly hG Q (linPoly A) hQ (dim_eq hG Q A hQ hdim hinj) hinj' b
  refine ⟨g, hg0, ?_⟩
  have hproj : projHom Q A = aeval (fun i => Ideal.Quotient.mk Q (linPoly A i)) := by
    rw [projHom, pullback, comp_aeval]
    rfl
  have hRB' : algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ Q) =
      (aeval fun i => Ideal.Quotient.mk Q (linPoly A i)).toRingHom := by
    rw [← hproj]
    rfl
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hRB']
  exact hgb
end GroundTheory.Heights₂.Heights.DominantPrimitiveFibres
