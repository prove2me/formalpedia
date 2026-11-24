-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.CycF.th_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:38:31.006357+00:00
-- url     : https://prove2.me/submissions/98c26ada-d712-49cb-815c-428a0a1d3102

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTC
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_th_embT
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_th_embF

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.CycF
variable {m n : ℕ} (ε : Fin m → Bool)
variable {ε}
namespace PositivityTheory.Rg.Sw.FFTSteps.CycF
theorem _root_.solution (c : PV (Rw ε true) (Fin n) (Fin n)) (μ : VV (Rw ε false) n →₀ ℕ) :
    Th ε (emb ε true c * emb ε false (monomial μ 1)) = monomial μ c := by
  rw [map_mul, th_embT, th_embF, map_monomial, map_one, C_mul_monomial, mul_one]
end PositivityTheory.Rg.Sw.FFTSteps.CycF
