-- Prove2me | solution 1 for PositivityTheory.CW.CharpolyPowerTraces.coeff_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:25:13.83981+00:00
-- url     : https://prove2.me/submissions/499edc02-f46a-46ca-8a9f-51263add1ec5

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_NilpotentOfPowerTraces
import Theorems.Thm_GroundTheory_Global_coe_derivative_charpolyRev


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.CharpolyPowerTraces
open Polynomial
namespace PositivityTheory.CW.CharpolyPowerTraces
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} (N : Matrix (Fin n) (Fin n) R)
    (h : ∀ k, (N ^ (k + 1)).trace = 0) (m : ℕ) :
    ((m : R) + 1) * N.charpolyRev.coeff (m + 1) = 0 := by
  have hps : (PowerSeries.mk fun k => (N ^ (k + 1)).trace) = 0 := by
    ext k
    simp [h]
  have hd : derivative N.charpolyRev = 0 := by
    have hc := GroundTheory.Global.coe_derivative_charpolyRev N
    rw [hps, mul_zero] at hc
    exact Polynomial.coe_eq_zero_iff.mp hc
  have hm := congrArg (fun p => Polynomial.coeff p m) hd
  simp only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hm
  rw [mul_comm]
  exact hm
end PositivityTheory.CW.CharpolyPowerTraces
