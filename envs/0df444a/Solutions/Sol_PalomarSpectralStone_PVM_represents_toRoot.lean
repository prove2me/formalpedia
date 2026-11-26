-- Prove2me | solution 1 for PalomarSpectralStone.PVM.represents_toRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:14:25.987628+00:00
-- url     : https://prove2.me/submissions/c02598e3-878d-420e-9adb-04ec9d743178

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
theorem _root_.solution {p : PVM E} {A : E →ₗ.[ℂ] E} :
    (PVM.toRoot p).Represents A ↔ p.Represents A := Iff.rfl
end PVM
end PalomarSpectralStone
