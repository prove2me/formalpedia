-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.secondParity_cons_eq_firstParity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:34:22.881865+00:00
-- url     : https://prove2.me/submissions/dbfe3af3-7172-4ae1-852e-6474c0d53fd1

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
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry
theorem _root_.solution {α : Type*} :
    ∀ (A : α) (regions : List α),
      secondParity (A :: regions) = firstParity regions
  | _, [] => rfl
  | _, [_] => rfl
  | _, B :: C :: regions =>
      congrArg (B :: ·)
        (solution C regions)
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry
