-- Prove2me | solution 1 for QEC.Locality.symplecticForm_add_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:11:36.027179+00:00
-- url     : https://prove2.me/submissions/a7d2fe2d-e4a3-4579-b08f-6040eed83d43

import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open PauliSymplectic
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution (a b c : SymplecticVector (ZMod 2) ι) :
    symplecticForm a (b + c) = symplecticForm a b + symplecticForm a c := by
  change FiniteSymplectic.form a (b + c) =
    FiniteSymplectic.form a b + FiniteSymplectic.form a c
  exact map_add (FiniteSymplectic.form a) b c
end QEC.Locality
