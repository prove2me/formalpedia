-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_isMultiHomogIdeal_sup_X_69669440edab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:35.685292+00:00
-- url     : https://prove2.me/submissions/29df1d1a-ef52-418a-9b1c-3a4cf156c4fc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ColonSpanSingletonEqOfNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertIncrement
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement
theorem _root_.solution {q : Ideal (MRing ι F)} (hq : IsMultiHomogIdeal q)
    (v : Σ k, ι k) : IsMultiHomogIdeal (q ⊔ Ideal.span {(X v : MRing ι F)}) := by
  classical
  intro f hf n
  obtain ⟨p, hp, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have hX : IsMultiHomog (X v : MRing ι F) (blockWeight ι v) :=
    isWeightedHomogeneous_X F (blockWeight ι) v
  rw [map_add, GroundTheory.Heights₂.Heights.FieldNumbers.HilbExactDivide.component_mul_form hX t n]
  refine Ideal.add_mem _ (Ideal.mem_sup_left (hq p hp n)) ?_
  split_ifs
  · exact Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩)
  · exact zero_mem _
end GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement
