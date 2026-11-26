-- Prove2me | solution 1 for Sendov.continuous_rpow_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:53:55.157843+00:00
-- url     : https://prove2.me/submissions/4159c445-570c-49bf-82b3-fc72ba4ac296

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_Common_Rpow

set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution {e : ℝ} (he : 0 ≤ e) : Continuous fun x : ℝ => x ^ e :=
  continuous_iff_continuousAt.2 fun x => Real.continuousAt_rpow_const x e (Or.inr he)
end Sendov
