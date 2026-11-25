-- Prove2me | solution 1 for PI.WAU.intC_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:05:22.149091+00:00
-- url     : https://prove2.me/submissions/ee43f308-a85c-40ff-a8e4-b7c566098d0b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CoordTmulOneMul
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_SmulEqAlgebraMapMul
import Theorems.Thm_PI_WAU_ohat_add

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
variable {E : Type} [Field E] [NumberField E] [Algebra F E]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
local notation "Af" => FiniteAdeleRing (𝓞 F) F
variable {b}
namespace PI.WAU
theorem _root_.solution {x y : E ⊗[F] Af} (hx : IntC b x) (hy : IntC b y) : IntC b (x + y) := by
  intro k
  rw [map_add]
  exact ohat_add (hx k) (hy k)
end PI.WAU
