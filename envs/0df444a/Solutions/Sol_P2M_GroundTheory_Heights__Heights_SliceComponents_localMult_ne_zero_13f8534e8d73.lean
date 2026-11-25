-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceComponents_localMult_ne_zero_13f8534e8d73
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:33:29.580355+00:00
-- url     : https://prove2.me/submissions/47fce80c-76e5-484c-a431-486f880c78df

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartHomogenise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartDehomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PMinimalPrimeHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLocalMultOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PDehomogOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_POrdPolynomialLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceComponents
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartDehomog_proof_43d0929de030
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHomogenise_proof_a08065262b6f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLocDomain_proof_34872f657b6a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLocalOrder_proof_c02df12483c9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSection_proof_5b1b05e34c1e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DehomogOrd_proof_95c60a838754
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalMultOrd_proof_21316c672e2e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimeHomog_proof_bf27ffa11a53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrdPolynomialLocalization_proof_d5922d801c8e


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
noncomputable section
open GroundTheory.Heights₂.Heights.SliceComponents
attribute [local instance] MvPolynomial.gradedAlgebra
variable {F : Type} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.SliceComponents
theorem _root_.solution {A : Type} [CommRing A] [IsNoetherianRing A] {J W : Ideal A} {x : A}
    (hW : W ∈ (J ⊔ Ideal.span {x}).minimalPrimes) : localMult (J ⊔ Ideal.span {x}) W ≠ 0 := by
  have := hW.1.1
  have hP : (W.map (Ideal.Quotient.mk J)).IsPrime := Ideal.map_isPrime_of_surjective
    Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact le_sup_left.trans hW.1.2)
  intro h0
  have e := LocalMultOrd.proof A J W x hW
  rw [h0, Nat.cast_zero, eq_comm, Ring.ord, Module.length_eq_zero_iff,
    Ideal.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top] at e
  have hx : Ideal.Quotient.mk J x ∈ W.map (Ideal.Quotient.mk J) :=
    Ideal.mem_map_of_mem _ (hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)))
  exact (IsLocalization.AtPrime.isUnit_to_map_iff _ _ _).mp e hx
end GroundTheory.Heights₂.Heights.SliceComponents
