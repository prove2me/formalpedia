-- Prove2me | solution 1 for PalomarSpectralStone.StrongContUnitary.generates_toRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:13:29.003621+00:00
-- url     : https://prove2.me/submissions/6e44da97-6151-42e7-bca2-48c9b14405ca

import Definitions.Def_Spectral_Spectral_Intrinsic
import Definitions.Def_Spectral_Stone_Intrinsic
import Definitions.Def_SpectralStoneSolution

set_option autoImplicit false
open Function MeasureTheory
open PalomarSpectralStone
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PalomarSpectralStone
namespace StrongContUnitary
theorem _root_.solution
    {u : StrongContUnitary E} {A : E →ₗ.[ℂ] E} :
    (StrongContUnitary.toRoot u).Generates A ↔ u.Generates A := Iff.rfl
end StrongContUnitary
end PalomarSpectralStone
