-- Prove2me | solution 1 for P2M_GlobalTheory_SingleBlock_measurable_toRows__1516c29dbd57
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:51:37.334884+00:00
-- url     : https://prove2.me/submissions/34c16949-47cd-4671-9468-bba1323ffc42

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {r t : ℕ}
  {O : Subring F} {ϖ : F} {P : Subgroup (GL (Fin r) F)}
variable [MeasurableSpace F] [BorelSpace F]
omit [TopologicalSpace F] [IsTopologicalRing F] [BorelSpace F] [Field F]
namespace GlobalTheory.SingleBlock
theorem _root_.solution :
    Measurable (fun x : Matrix (Fin r ⊕ Fin t) (Fin r) F => toRows₁ x) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (Sum.inl i)
end GlobalTheory.SingleBlock
