-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.JLatOf.finrank_Mj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:55:27.294427+00:00
-- url     : https://prove2.me/submissions/f0319754-3d4f-4ec4-9d99-9c80d83f3f9b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_LatticeReduction_LatticeHeightZeroEq
import Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_linInd_ej
import Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_Mj_eq_span

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
theorem _root_.solution (N j : ℕ) (h : j ≤ N) : finrank k (Mj k N j) = N - j := by
  rw [Mj_eq_span N j (N - j) (by omega), finrank_span_eq_card (linInd_ej N j (N - j) (by omega))]
  simp
end PositivityTheory.Rg.Rs.JLatOf
