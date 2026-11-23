-- Prove2me | solution 1 for P2M_GlobalTheory_HilbertSamuelPS_lexOrder_monomial_one__d29802e760af
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:13.865857+00:00
-- url     : https://prove2.me/submissions/cf69dd63-5f41-405f-b0f5-9dd674a3333d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
open GlobalTheory.HilbertSamuelPS
open MvPowerSeries
variable {D : ℕ}
namespace GlobalTheory.HilbertSamuelPS
theorem _root_.solution (a : Fin D →₀ ℕ) :
    lexOrder (monomial a (1 : ℂ)) = ((toLex a : Lex (Fin D →₀ ℕ)) : WithTop (Lex (Fin D →₀ ℕ))) := by
  apply le_antisymm
  · apply lexOrder_le_of_coeff_ne_zero; simp
  · rw [le_lexOrder_iff]
    intro d hd
    rw [coeff_monomial, if_neg]
    rintro rfl
    exact lt_irrefl _ (WithTop.coe_lt_coe.mp hd)
end GlobalTheory.HilbertSamuelPS
