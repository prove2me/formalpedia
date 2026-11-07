-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_sublist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:32:12.445081+00:00
-- url     : https://prove2.me/submissions/38bd8413-919b-417f-9465-f64c31dae829

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
    ∀ regions : List α, List.Sublist (firstParity regions) regions
  | [] => .slnil
  | [A] => .cons_cons A .slnil
  | A :: B :: regions =>
      .cons_cons A (.cons B (solution regions))
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry
