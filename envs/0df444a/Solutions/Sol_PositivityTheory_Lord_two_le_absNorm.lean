-- Prove2me | solution 1 for PositivityTheory.Lord.two_le_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:48:39.04885+00:00
-- url     : https://prove2.me/submissions/2faf4460-32a5-4bca-bfae-097703ff559b

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_MeromorphicAtProd
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_FactorDifferentiable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Complex NumberField IsDedekindDomain
open PositivityTheory PositivityTheory.Lord
theorem _root_.solution (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    2 ≤ Ideal.absNorm P.asIdeal := by
  first
    | (have h0 : Ideal.absNorm P.asIdeal ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
       have h1 : Ideal.absNorm P.asIdeal ≠ 1 := fun h => P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
       omega)

