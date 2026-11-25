-- Prove2me | solution 1 for PI.WAU.one_tmul_mem_intAf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:16.551402+00:00
-- url     : https://prove2.me/submissions/6c8b84e8-cc25-4cbf-946f-bc090463ce57

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_SmulEqAlgebraMapMul
import Definitions.Def_Lemmata_GeneralBFactThirdMore_Key
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatSmulMem

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
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Formalism.MainNotions.S
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}
local notation "Af" => FiniteAdeleRing (𝓞 F) F
namespace PI.WAU
theorem _root_.solution {c : Af} (hc : c ∈ Ohat F) : ((1 : E) ⊗ₜ[F] c) ∈ IntAf F E :=
  Subring.subset_closure (Or.inr ⟨⟨c, hc⟩, rfl⟩)
end PI.WAU
