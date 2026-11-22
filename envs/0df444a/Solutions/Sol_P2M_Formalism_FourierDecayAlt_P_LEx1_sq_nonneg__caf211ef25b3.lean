-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_LEx1_sq_nonneg__caf211ef25b3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:54:26.832137+00:00
-- url     : https://prove2.me/submissions/e1c9517f-2786-4d15-8e34-7358122bfeb2

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution (B : Base) {A' : Type} [Fintype A'] (wt : B.Ω → A' → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a) (v : Fn B A') (ω) :
    0 ≤ LE.sq B wt v ω := Finset.sum_nonneg fun a _ => mul_nonneg (hpos ω a) (by positivity)
end Formalism.FourierDecayAlt.P.LEx1
