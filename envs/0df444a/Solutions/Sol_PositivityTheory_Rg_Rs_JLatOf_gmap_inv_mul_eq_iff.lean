-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.JLatOf.gmap_inv_mul_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:21:00.792453+00:00
-- url     : https://prove2.me/submissions/4afa8f60-43f1-42f4-b3ed-b5112ea52f64

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_LatticeReduction_LatticeHeightZeroEq
import Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_gmap_mul
import Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_gmap_one

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
theorem _root_.solution (g h : GL (Fin N) k) (M : Submodule k (Fin N → k)) :
    gmap (g⁻¹ * h) M = M ↔ gmap h M = gmap g M := by
  constructor
  · intro h1
    conv_rhs => rw [← h1]
    rw [← gmap_mul, mul_inv_cancel_left]
  · intro h1
    rw [gmap_mul, h1, ← gmap_mul, inv_mul_cancel, gmap_one]
end PositivityTheory.Rg.Rs.JLatOf
