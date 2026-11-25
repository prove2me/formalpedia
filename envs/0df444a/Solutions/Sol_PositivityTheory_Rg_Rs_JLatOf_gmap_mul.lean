-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.JLatOf.gmap_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:42:06.122138+00:00
-- url     : https://prove2.me/submissions/bb67cdde-a15c-48d9-94da-466220bf9f18

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_LatticeReduction_LatticeHeightZeroEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.JLatOf
open PositivityTheory.Rg.Rs
variable {k : Type} [Field k] {N : ℕ}
namespace PositivityTheory.Rg.Rs.JLatOf
theorem _root_.solution (g h : GL (Fin N) k) (M : Submodule k (Fin N → k)) : gmap (g * h) M = gmap g (gmap h M) := by
  delta gmap
  simp only [Units.val_mul, Matrix.toLin'_mul, Submodule.map_comp]
end PositivityTheory.Rg.Rs.JLatOf
