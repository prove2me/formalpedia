-- Prove2me | solution 1 for PalomarSpectralStone.StrongContUnitary.generates_ofRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:13:50.41541+00:00
-- url     : https://prove2.me/submissions/744a1401-c856-48e8-8571-89febd376c2e

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
    {u : _root_.StrongContUnitary E} {A : E →ₗ.[ℂ] E} :
    (StrongContUnitary.ofRoot u).Generates A ↔ u.Generates A := Iff.rfl
end StrongContUnitary
end PalomarSpectralStone
