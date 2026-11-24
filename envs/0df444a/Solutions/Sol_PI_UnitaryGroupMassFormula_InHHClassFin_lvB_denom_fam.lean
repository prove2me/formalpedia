-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.lvB_denom_fam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:19:40.388071+00:00
-- url     : https://prove2.me/submissions/56b58817-c279-4ab4-8e55-fa439956451d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_LevelA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Lemmata_IntegerMulIntegral_IntMulIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_LevelB
import Theorems.Thm_Formalism_UG_P_levelafC_mem
import Theorems.Thm_Formalism_UG_P_levelafC_mul
import Theorems.Thm_Formalism_UG_P_levelaf_denom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain Formalism.UG Formalism.UG.P PI.InHHClassFin
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.InHHClassFin
theorem _root_.solution {ι : Type} [Fintype ι] (f : ι → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ i, levelafC E d * f i ∈
      tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := by
  classical
  choose d hd0 hd using fun i => levelaf_denom (E := E) (f i)
  refine ⟨∏ k, d k, Finset.prod_ne_zero_iff.2 fun i _ => hd0 i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), levelafC_mul,
    mul_comm (levelafC E (d i)), mul_assoc]
  exact mul_mem (levelafC_mem _) (hd i)
end PI.UnitaryGroupMassFormula.InHHClassFin
