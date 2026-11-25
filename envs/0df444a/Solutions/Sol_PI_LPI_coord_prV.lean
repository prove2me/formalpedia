-- Prove2me | solution 1 for PI.LPI.coord_prV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:57:07.929269+00:00
-- url     : https://prove2.me/submissions/c0041f32-b415-49c0-b939-6aaeb6e6ddc8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_PrVTmulEqTmulApply
import Theorems.Thm_PI_LPI_prV_tmul_eq_tmul_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct
noncomputable section
open PI PI.LPI
namespace PI.LPI
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {ι : Type}
    [DecidableEq ι] (b : Module.Basis ι F E) (v : HeightOneSpectrum (𝓞 F)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (prV (E := E) v z) i =
      (TensorProduct.equivFinsuppOfBasisLeft b z i) v := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]; try rfl
  | tmul e a =>
    rw [prV_tmul_eq_tmul_apply, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
      TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    simp only [Algebra.smul_def]
    rfl
  | add x y hx hy =>
    simp only [map_add, Finsupp.coe_add, Pi.add_apply, hx, hy]
    try rfl
end PI.LPI
