-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericFreeness_proof_71d66b879eb6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:08:47.133686+00:00
-- url     : https://prove2.me/submissions/b667c780-b830-4601-b929-94c938bc05e8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFreeness
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericNoetherNormalisation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreenessLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreeness
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_of_primes_3d342de5f6a4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_quotient_e8d046524437

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
universe u v w
namespace GroundTheory.Heights₂.Heights
namespace GenericFreeness
theorem _root_.solution (hNN : GenericNoetherNormalisation.Statement.{u}) :
    GenericFreeness.Statement.{u, v, w} := by
  intro A _ _ _ B _ _ _ M _ _ _ _ _
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType A B›
  letI : Algebra (MvPolynomial (Fin n) A) B := g.toRingHom.toAlgebra
  letI : Module (MvPolynomial (Fin n) A) M := Module.compHom M (algebraMap (MvPolynomial (Fin n) A) B)
  have : IsScalarTower (MvPolynomial (Fin n) A) B M := ⟨fun x b m ↦ by
    show (g x * b) • m = g x • b • m
    rw [mul_smul]⟩
  have : IsScalarTower A (MvPolynomial (Fin n) A) M := ⟨fun a x m ↦ by
    show g (a • x) • m = a • g x • m
    rw [map_smul, smul_assoc]⟩
  have : Module.Finite (MvPolynomial (Fin n) A) B := RingHom.Finite.of_surjective g.toRingHom hg
  have : Module.Finite (MvPolynomial (Fin n) A) M := Module.Finite.trans B M
  exact GenericFreeness.isGenericallyFree_of_primes (R := MvPolynomial (Fin n) A)
    (fun p ↦ GenericFreeness.isGenericallyFree_quotient hNN n A p.asIdeal p.isPrime) M
end GenericFreeness
end GroundTheory.Heights₂.Heights
