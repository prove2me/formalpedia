-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.Mi.detE_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:54.225432+00:00
-- url     : https://prove2.me/submissions/cd410c41-f22d-4518-97f6-6ef800048c07

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCore
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorIter
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_foldr_C_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP PositivityTheory.Rg.Sw.SP.Mi
variable {R : Type} [CommRing R] {ρ : ℕ}
namespace PositivityTheory.Rg.Sw.SP.Mi
theorem _root_.solution (α : R) (r : R) (g : Pm R ρ) : detE α (C r * g) = C r * detE α g := by
  simp only [detE, LinearMap.sum_apply, LinearMap.smul_apply, foldr_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_smul_comm]
end PositivityTheory.Rg.Sw.SP.Mi
