-- Prove2me | solution 1 for ZetaZeros.D.EllReg.Dec.prod_neg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:53:07.063863+00:00
-- url     : https://prove2.me/submissions/37c96af5-ad8a-447f-960b-e8c627628976

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegStep
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_Decompose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
open ZetaZeros.D.EllReg.Dec
variable {d : ℕ}
namespace ZetaZeros.D.EllReg.Dec
theorem _root_.solution (n : ℕ) (w : Fin n → Fin d) (ξ : E d) :
    ((List.ofFn w).map fun j => -(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ))).prod = (-1 : ℂ) ^ n * mono w ξ := by
  rw [List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_def]
  rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin]
  rfl
end ZetaZeros.D.EllReg.Dec
