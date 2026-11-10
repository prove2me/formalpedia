-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.triangleInputList_toFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:52:12.220911+00:00
-- url     : https://prove2.me/submissions/69d75ddf-aa65-4162-b5de-fac550ab6db5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) :
    (triangleInputList P).toFinset = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro t
  apply List.mem_toFinset.mpr
  apply List.mem_ofFn.mpr
  exact ⟨Fintype.equivFin (Triangle P) t,(Fintype.equivFin (Triangle P)).symm_apply_apply t⟩
end QEC.Coding.BDL26RandomPerturbation
