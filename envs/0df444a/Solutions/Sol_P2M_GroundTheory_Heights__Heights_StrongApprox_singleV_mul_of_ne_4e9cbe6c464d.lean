-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_singleV_mul_of_ne_4e9cbe6c464d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:51.138906+00:00
-- url     : https://prove2.me/submissions/e406614d-e76a-456c-94ee-039e260bbe86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PTruncation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_singleF_mul_of_ne_afa740079f10
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open Classical
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox
theorem _root_.solution {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) (x : Kv E v) (y : Kv E w) :
    singleV E v x * singleV E w y = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' =>
      simp [singleV, Algebra.TensorProduct.tmul_mul_tmul, singleF_mul_of_ne h]
    | add y y' hy hy' => rw [map_add, mul_add, hy, hy', add_zero]
  | add x x' hx hx' => rw [map_add, add_mul, hx, hx', add_zero]
end GroundTheory.Heights₂.Heights.StrongApprox
