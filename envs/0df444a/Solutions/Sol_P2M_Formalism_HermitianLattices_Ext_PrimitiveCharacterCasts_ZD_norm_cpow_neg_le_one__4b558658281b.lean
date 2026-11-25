-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_norm_cpow_neg_le_one__4b558658281b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:45:15.085863+00:00
-- url     : https://prove2.me/submissions/d87caf11-fa54-4a6d-8033-2eb3a4a2d080

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) {w : ℂ} (hw : 0 ≤ w.re) : ‖(n : ℂ) ^ (-w)‖ ≤ 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn)
  simp only [Complex.neg_re]
  linarith
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
