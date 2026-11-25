-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_exists_sub_component_mem_380caf9d8097
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:53:06.111752+00:00
-- url     : https://prove2.me/submissions/60d44318-d59c-46df-935f-f99431471f4e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide

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
open GroundTheory.Heights₂.Heights.FieldNumbers.HilbExactDivide
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.FieldNumbers.HilbExactDivide
theorem _root_.solution {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    {s f : MRing ι F} {n : K → ℕ} (hf : IsMultiHomog f n) (hfL : f ∈ I ⊔ Ideal.span {s}) :
    ∃ t : MRing ι F, f - weightedHomogeneousComponent (blockWeight ι) n (t * s) ∈ I := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hfL
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  refine ⟨t, ?_⟩
  have h1 : weightedHomogeneousComponent (blockWeight ι) n (a + t * s) = a + t * s :=
    IsWeightedHomogeneous.weightedHomogeneousComponent_same hf
  have e : a + t * s - weightedHomogeneousComponent (blockWeight ι) n (t * s) =
      weightedHomogeneousComponent (blockWeight ι) n a := by
    rw [sub_eq_iff_eq_add, ← map_add, h1]
  rw [e]
  exact hI a ha n
end GroundTheory.Heights₂.Heights.FieldNumbers.HilbExactDivide
