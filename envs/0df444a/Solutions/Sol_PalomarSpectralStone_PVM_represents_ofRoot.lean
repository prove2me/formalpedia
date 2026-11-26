-- Prove2me | solution 1 for PalomarSpectralStone.PVM.represents_ofRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:13:28.07005+00:00
-- url     : https://prove2.me/submissions/359e3b54-7647-4bf8-b318-29f77be067e9

import Definitions.Def_Spectral_Spectral_Intrinsic
import Definitions.Def_Spectral_Stone_Intrinsic
import Definitions.Def_SpectralStoneSolution

set_option autoImplicit false
open Function MeasureTheory
open PalomarSpectralStone
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PalomarSpectralStone
namespace PVM
theorem _root_.solution {p : _root_.PVM E} {A : E →ₗ.[ℂ] E} :
    (PVM.ofRoot p).Represents A ↔ p.Represents A := Iff.rfl
end PVM
end PalomarSpectralStone
