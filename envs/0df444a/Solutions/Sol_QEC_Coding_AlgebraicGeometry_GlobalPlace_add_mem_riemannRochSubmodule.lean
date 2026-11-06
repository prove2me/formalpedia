-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.add_mem_riemannRochSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:27:33.6982+00:00
-- url     : https://prove2.me/submissions/7389e877-944e-4f07-b5c9-edb9bde22ca6

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_ValuationBound
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Space

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution {G : Divisor (GlobalPlace k F)} {f g : F}
    (hf : f ∈ riemannRochSubmodule G) (hg : g ∈ riemannRochSubmodule G) :
    f + g ∈ riemannRochSubmodule G :=
  (riemannRochSubmodule G).add_mem hf hg
end QEC.Coding.AlgebraicGeometry.GlobalPlace
