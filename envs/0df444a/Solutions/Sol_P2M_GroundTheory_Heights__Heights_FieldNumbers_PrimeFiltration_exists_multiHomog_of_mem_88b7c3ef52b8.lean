-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_exists_multiHomog_of_mem_88b7c3ef52b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:10:11.549394+00:00
-- url     : https://prove2.me/submissions/7006b1cf-24aa-4940-85ac-eda16966cab2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_lexEmb_injective_2e035ab13206
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_weight_lexWeight_8cd877a192d7

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
open GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance 2000] lexDecEq
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
theorem _root_.solution {s : MRing ι F} {m : Lex (Fin (Fintype.card K) → ℕ)}
    (hs : s ∈ lexGrading ι F m) (h0 : s ≠ 0) : ∃ c : K → ℕ, IsMultiHomog s c := by
  rw [mem_weightedHomogeneousSubmodule] at hs
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp h0
  refine ⟨Finsupp.weight (blockWeight ι) d, fun {d'} hd' => ?_⟩
  apply lexEmb_injective
  rw [← weight_lexWeight, ← weight_lexWeight, hs hd', hs hd]
end GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
