-- Prove2me | solution 1 for PI.CompAtExist.muV_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:53:14.453831+00:00
-- url     : https://prove2.me/submissions/71a524c8-e9d5-4143-b61b-7a9c39538ee5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_UniROfUniRT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionExistence_LeOneIffOfMulEqOne
import Theorems.Thm_PI_CompAtExist_val_eq_of_le_one_iff
import Theorems.Thm_PI_CompAtExist_muV_apply
import Theorems.Thm_PI_CompAtExist_muV_le_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CompAtExist
open NumberField IsDedekindDomain ReciprocityTheory.Aut
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
namespace PI.CompAtExist
theorem _root_.solution (s : SplitPlace L) (x : L) : muV s x = s.w.valuation L x := by
  obtain ⟨ϖ, hϖ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer L s.w
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer s.v
  refine val_eq_of_le_one_iff (muV s) (s.w.valuation L) (muV_le_one_iff s) hϖ
    (π := ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a : 𝓞 L) : L)) ?_ x
  rw [muV_apply, s.split_val_alg, RingOfIntegers.coe_eq_algebraMap, s.v.valuation_of_algebraMap, ha]
end PI.CompAtExist
