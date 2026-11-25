-- Prove2me | solution 1 for PI.IsoDetW.Loc.relativeLength_localized_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:43:12.214107+00:00
-- url     : https://prove2.me/submissions/a919998f-f856-4185-a795-2e08e42b64f5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm
import Theorems.Thm_PI_IsoDetW_Loc_rlen_map
import Theorems.Thm_P2M_PI_IsoDetW_Loc_localization_map__da8ebf0c7662

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoDetW PI.IsoDetW.Loc
open PI.IsoDetDefs
variable {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W] [Module R W]
variable (p : Ideal R) [p.IsPrime]
namespace PI.IsoDetW.Loc
theorem _root_.solution {W' : Type*} [AddCommGroup W'] [Module R W'] (f : W →ₗ[R] W')
    (hf : Function.Injective f)
    (hsat : ∀ (s : R) (y : W'), s ∈ p.primeCompl → s • y ∈ LinearMap.range f → y ∈ LinearMap.range f)
    (A B : Submodule R W) :
    relative₂ (localization₂ p (A.map f)) (localization₂ p (B.map f)) = relative₂ (localization₂ p A) (localization₂ p B) := by
  rw [localization_map₂ p f hf hsat, localization_map₂ p f hf hsat, rlen_map f hf]
end PI.IsoDetW.Loc
