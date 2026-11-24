-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.Oh_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:27:44.014828+00:00
-- url     : https://prove2.me/submissions/cb5a0bc3-45a1-4a5e-8bbf-b3c306c50af8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_intAf_mul

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
theorem _root_.solution {x y : Af F ⊗[F] E} (hx : x ∈ Oh F E) (hy : y ∈ Oh F E) : x * y ∈ Oh F E := by
  unfold Oh at hx hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem y hy' =>
    induction hx using AddSubgroup.closure_induction with
    | mem x hx' =>
      obtain ⟨a, ha, e, he, rfl⟩ := hx'
      obtain ⟨b, hb, f, hf, rfl⟩ := hy'
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact AddSubgroup.subset_closure ⟨a * b, intAf_mul ha hb, e * f, he.mul hf, rfl⟩
    | zero =>
      rw [zero_mul]
      exact zero_mem _
    | add x x' _ _ h1 h2 =>
      rw [add_mul]
      exact add_mem h1 h2
    | neg x _ h1 =>
      rw [neg_mul]
      exact neg_mem h1
  | zero =>
    rw [mul_zero]
    exact zero_mem _
  | add y y' _ _ h1 h2 =>
    rw [mul_add]
    exact add_mem h1 h2
  | neg y _ h1 =>
    rw [mul_neg]
    exact neg_mem h1
end PI.UnitaryGroupMassFormula.UJClassFin
