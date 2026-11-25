-- Prove2me | solution 1 for PI.Dv.ProjAW.lenAt_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:36:13.177153+00:00
-- url     : https://prove2.me/submissions/c0d1cc96-552b-4a49-b099-7015ea81c91b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_LenAtEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V W : Type} [AddCommGroup V] [Module (𝓞 K) V] [AddCommGroup W] [Module (𝓞 K) W]
namespace PI.Dv.ProjAW
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V) (M' N' : Submodule (𝓞 K) W)
    (φ : (↥M ⧸ N.comap M.subtype) ≃ₗ[𝓞 K] (↥M' ⧸ N'.comap M'.subtype)) :
    lenAt w M N = lenAt w M' N' := by
  unfold lenAt
  let _ : w.asIdeal.IsPrime := w.isPrime
  exact (IsLocalizedModule.mapEquiv w.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap w.asIdeal.primeCompl _)
    (LocalizedModule.mkLinearMap w.asIdeal.primeCompl _)
    (Localization.AtPrime w.asIdeal) φ).length_eq
end PI.Dv.ProjAW
