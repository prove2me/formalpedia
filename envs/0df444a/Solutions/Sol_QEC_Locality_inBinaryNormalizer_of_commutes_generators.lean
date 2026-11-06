-- Prove2me | solution 1 for QEC.Locality.inBinaryNormalizer_of_commutes_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:11:37.45124+00:00
-- url     : https://prove2.me/submissions/a0db44b3-5307-45ad-874a-9168a32460fd

import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Theorems.Thm_QEC_Coding_PauliSymplectic_commutes_binaryDagger_right
import Theorems.Thm_QEC_Coding_PauliSymplectic_commutes_binaryMul_right


set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open PauliSymplectic
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (E : Binary ι) (hcommutes : ∀ j : κ, Commutes E (P.generators j)) :
    P.code.1.InBinaryNormalizer E := by
  intro G hG
  rw [← P.generated_eq] at hG
  induction hG with
  | one => exact commutes_binaryOne_right E
  | generator j => exact hcommutes j
  | mul _ _ ihP ihQ => exact commutes_binaryMul_right ihP ihQ
  | dagger _ ihP => exact commutes_binaryDagger_right ihP
end QEC.Locality
