-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.mom_ellpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:52:30.664444+00:00
-- url     : https://prove2.me/submissions/90745d62-3974-4f44-8a22-80e429f0ca28

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_NullTop
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_evX_ell

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.FFTSteps
theorem _root_.solution (ε : Fin m → Bool) (c : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) (P : PX m n) :
    mom c ((∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) ^ k * P) =
      ∫ x : Fin m → Fin n → ℂ, evX P x * gs c x * ((b * gramX ε x).trace) ^ k := by
  unfold mom
  congr 1
  ext x
  have e : evX ((∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) ^ k * P) x =
      (evX (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) x) ^ k * evX P x := by
    simp only [evX, map_mul, map_pow]
  rw [e, evX_ell]
  ring
end PositivityTheory.Rg.Sw.FFTSteps
