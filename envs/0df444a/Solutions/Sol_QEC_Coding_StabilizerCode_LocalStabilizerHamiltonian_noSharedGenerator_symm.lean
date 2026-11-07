-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.noSharedGenerator_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:33:25.833546+00:00
-- url     : https://prove2.me/submissions/098393e9-3ee2-4b8e-81ec-7a020cb882d6

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance

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
    {R T : Finset ι} (h : H.NoSharedGenerator R T) :
    H.NoSharedGenerator T R := by
  intro j hboth
  exact h j ⟨hboth.2, hboth.1⟩
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
