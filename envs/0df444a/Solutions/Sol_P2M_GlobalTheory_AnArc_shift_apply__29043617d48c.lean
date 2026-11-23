-- Prove2me | solution 1 for P2M_GlobalTheory_AnArc_shift_apply__29043617d48c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:15:48.321179+00:00
-- url     : https://prove2.me/submissions/f4f6437d-a70e-405f-8d65-002a5e4e413d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
variable (k : ℕ) [NeZero k]
namespace GlobalTheory.AnArc
theorem _root_.solution (la : A.La) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (z : Fin A.gB → ℂ) :
    A.shift k la α th z = eTwoPi ((A.P0 la).1 α / k) * Complex.exp (-(Real.pi * A.H z la.l)) *
      th (z + (k : ℂ)⁻¹ • (A.P0 la).2) := rfl
end GlobalTheory.AnArc
