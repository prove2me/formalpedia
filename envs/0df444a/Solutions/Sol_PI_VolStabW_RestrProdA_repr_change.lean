-- Prove2me | solution 1 for PI.VolStabW.RestrProdA.repr_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:04:29.399161+00:00
-- url     : https://prove2.me/submissions/9af0d415-d560-40da-9c95-56117ca33134

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.RestrProdA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
namespace PI.VolStabW.RestrProdA
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] {d d' : ℕ}
    (R : Type) [CommRing R] [Algebra F R] (b : Module.Basis (Fin d) F E)
    (b' : Module.Basis (Fin d') F E) (y : R ⊗[F] E) (k' : Fin d') :
    (Algebra.TensorProduct.basis R b').repr y k' =
      ∑ k, (Algebra.TensorProduct.basis R b).repr y k * algebraMap F R (b'.repr (b k) k') := by
  have hE : ∀ e : E, b'.repr e k' = ∑ k, b.repr e k * b'.repr (b k) k' := fun e => by
    conv_lhs => rw [← b.sum_repr e]
    simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, hE,
      map_sum, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul, map_mul, mul_assoc]
  | add x y hx hy =>
    rw [map_add, Finsupp.add_apply, hx, hy, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add, Finsupp.add_apply, add_mul]
end PI.VolStabW.RestrProdA
