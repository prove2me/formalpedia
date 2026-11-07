-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.inBinaryNormalizer_of_commutes_selectedGenerators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:58:33.351345+00:00
-- url     : https://prove2.me/submissions/c6d11bcd-f83d-46fc-bcf4-db6b081b19fc

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Theorems.Thm_QEC_Coding_PauliSymplectic_commutes_binaryDagger_right
import Theorems.Thm_QEC_Coding_PauliSymplectic_commutes_binaryMul_right


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
theorem _root_.solution
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) (hcommutes : ∀ j, Commutes E (H.generators j)) :
    H.code.1.InBinaryNormalizer E := by
  intro G hG
  rw [← H.generated_eq] at hG
  induction hG with
  | one => exact commutes_binaryOne_right E
  | generator j => exact hcommutes j
  | mul _ _ ihP ihQ => exact commutes_binaryMul_right ihP ihQ
  | dagger _ ihP => exact commutes_binaryDagger_right ihP
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
