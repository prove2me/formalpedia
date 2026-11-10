-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.triangleKey_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:51:07.552815+00:00
-- url     : https://prove2.me/submissions/cfb11ea0-d363-45dc-a9e2-86f7e781151c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Coloring

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence
noncomputable section
variable (P : TannerSquarePresentation)
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution : Function.Injective (triangleKey P) := by
  intro a b h
  apply (Fintype.equivFin (Triangle P)).injective
  exact Fin.ext h
end QEC.Coding.BDL26RandomPerturbation
