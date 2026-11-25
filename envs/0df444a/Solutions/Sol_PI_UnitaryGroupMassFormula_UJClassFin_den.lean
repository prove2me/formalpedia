-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:58:47.728438+00:00
-- url     : https://prove2.me/submissions/15aae563-e3ac-4e09-a771-4ba932f0bf4f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_tmul_mem_Oh
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_isIntegral_of_intOE
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UJClassFin_nsmul_tmul__c42d1c934366
import Theorems.Thm_PIW_AdelClassFin_DictRing_af_denom
import Theorems.Thm_PIW_AdelClassFin_DictRing_e_denom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution (r : Af F ⊗[F] E) : ∃ m : ℕ, 0 < m ∧ m • r ∈ Oh F E := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _⟩
  | tmul a e =>
    obtain ⟨m1, hm1, h1⟩ := PIW.AdelClassFin.DictRing.af_denom a
    obtain ⟨m2, hm2, h2⟩ := PIW.AdelClassFin.DictRing.e_denom e
    refine ⟨m1 * m2, Nat.mul_pos hm1 hm2, ?_⟩
    rw [nsmul_tmul']
    exact tmul_mem_Oh h1 (isIntegral_of_intOE h2)
  | add x y hx hy =>
    obtain ⟨m1, hm1, h1⟩ := hx
    obtain ⟨m2, hm2, h2⟩ := hy
    refine ⟨m1 * m2, Nat.mul_pos hm1 hm2, ?_⟩
    rw [smul_add, mul_comm m1 m2, mul_smul, mul_comm m2 m1, mul_smul]
    exact add_mem (AddSubgroup.nsmul_mem _ h1 _) (AddSubgroup.nsmul_mem _ h2 _)
end PI.UnitaryGroupMassFormula.UJClassFin
