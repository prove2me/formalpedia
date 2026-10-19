-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_setup_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T13:22:18.999006+00:00
-- url     : https://prove2.me/submissions/94153513-4139-4b89-a279-e912e9ddcddc

import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic
import Definitions.Def_TaoFivePrimes_RHFastWindow256Setup
import Definitions.Def_TaoFivePrimes_RHBatch01New256Common
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
open RHFastBallArithmetic

theorem solution :
 RHBatch01New256Common.inputs=RHFastWindow256Setup.inputs 3289999808 ∧
 RHBatch01New256Common.qs=RHFastWindow256Setup.coefficients 3289999808 ∧
 RHBatch01New256Common.pi=RHFastWindow256Setup.lift RHFastBallSeedPrograms.pi ∧
 RHBatch01New256Common.root=RHFastWindow256Setup.lift RHFastBallSeedPrograms.root ∧
 RHBatch01New256Common.omega=RHFastWindow256Setup.lift (RHFastBallSeedPrograms.omega 3289999808) ∧
 RHBatch01New256Common.factors=RHFastWindow256Setup.factors RHBatch01New256Common.pi ∧
 RHBatch01New256Common.anchor=RHFastWindow256Setup.lift (RHFastBallSeedPrograms.anchor
  (RHFastKernelGammaArithmetic.compute 3289999808 8192).cos
  (RHFastKernelGammaArithmetic.compute 3289999808 8192).sin
  (RHFastKernelGammaArithmetic.compute 3289999808 8192).amplitude
  (RHFastKernelGammaArithmetic.compute 3289999808 8192).negative) := by decide +kernel
#print axioms solution
