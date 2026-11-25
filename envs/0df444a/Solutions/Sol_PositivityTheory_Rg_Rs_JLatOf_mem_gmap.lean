-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.JLatOf.mem_gmap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:38:46.968452+00:00
-- url     : https://prove2.me/submissions/e3340c30-2633-4b9b-8df8-da9aa0a181b3

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
theorem _root_.solution {g : GL (Fin N) k} {M : Submodule k (Fin N → k)} {y : Fin N → k} :
    y ∈ gmap g M ↔ ∃ x ∈ M, (g : Matrix (Fin N) (Fin N) k) *ᵥ x = y := by
  delta gmap
  simp only [Submodule.mem_map, Matrix.toLin'_apply]
end PositivityTheory.Rg.Rs.JLatOf
