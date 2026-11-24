-- Prove2me | solution 1 for PI.WAU.ohat_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:24:17.047274+00:00
-- url     : https://prove2.me/submissions/25d7e8e7-742f-4a70-9100-8a080781e61e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CoordTmulOneMul
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_SmulEqAlgebraMapMul
import Theorems.Thm_PI_WAU_ohat_neg
import Theorems.Thm_PI_WAU_ohat_nsmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F]
namespace PI.WAU
theorem _root_.solution {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (m : ℤ) : m • a ∈ Ohat F := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [natCast_zsmul]; exact ohat_nsmul ha n
  · rw [neg_zsmul, natCast_zsmul]; exact ohat_neg (ohat_nsmul ha n)
end PI.WAU
