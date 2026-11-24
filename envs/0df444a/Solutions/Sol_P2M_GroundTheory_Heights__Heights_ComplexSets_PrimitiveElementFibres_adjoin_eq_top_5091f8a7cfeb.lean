-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveElementFibres_adjoin_eq_top_5091f8a7cfeb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:35.940348+00:00
-- url     : https://prove2.me/submissions/05217d12-8f93-4bf0-bffa-89d9e38a5c91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveElementFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PrimitiveLinearForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveElementFibres_algebraMap_C_eq_62e9e2c24ee5

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveElementFibres
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveElementFibres
theorem _root_.solution (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) :
    letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
      (projHom J A).toRingHom.toAlgebra
    Algebra.adjoin (MvPolynomial (Fin d) ℂ)
      (Set.range fun j : Fin n => Ideal.Quotient.mk J (X j)) = ⊤ := by
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  rw [eq_top_iff]
  rintro b -
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : Ideal.Quotient.mk J (C a) = algebraMap (MvPolynomial (Fin d) ℂ) _ (C a) :=
      (algebraMap_C_eq J A a).symm
    rw [h]
    exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp => rw [map_mul]; exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)
end GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveElementFibres
