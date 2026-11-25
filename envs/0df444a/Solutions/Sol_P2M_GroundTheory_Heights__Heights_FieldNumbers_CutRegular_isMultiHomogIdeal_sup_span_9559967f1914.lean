-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_isMultiHomogIdeal_sup_span_9559967f1914
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:11:13.751058+00:00
-- url     : https://prove2.me/submissions/69e74816-954d-4b74-ae6b-af9c31b20939

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumAdd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRegular
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_component_mul_form_2d063eda04f4


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
theorem _root_.solution {P : Ideal (MRing ι F)} (hP : IsMultiHomogIdeal P)
    {c : K → ℕ} {s : MRing ι F} (hs : IsMultiHomog s c) :
    IsMultiHomogIdeal (P ⊔ Ideal.span {s}) := by
  classical
  intro f hf b
  obtain ⟨a, ha, t', ht', rfl⟩ := Submodule.mem_sup.mp hf
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp ht'
  rw [map_add, HilbExactDivide.component_mul_form hs]
  refine Ideal.add_mem _ (Ideal.mem_sup_left (hP a ha b)) ?_
  split_ifs
  · exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self s))
  · exact Ideal.zero_mem _
end GroundTheory.Heights₂.Heights.FieldNumbers.CutRegular
