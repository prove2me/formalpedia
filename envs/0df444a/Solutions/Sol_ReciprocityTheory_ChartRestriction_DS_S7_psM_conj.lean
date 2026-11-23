-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.psM_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:17:14.382824+00:00
-- url     : https://prove2.me/submissions/486aafab-a1d1-401f-801b-214a57e78996

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousConjProjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
private lemma toMatrix_mul_alt (a b : KG ε) : toMK (a * b) = toMK a * toMK b := rfl
private lemma toMatrix_one_alt : toMK (1 : KG ε) = 1 := rfl
private lemma toMatrix_inv_mul (a : KG ε) : toMK a⁻¹ * toMK a = 1 := by
  rw [← toMatrix_mul_alt, inv_mul_cancel, toMatrix_one_alt]
private lemma conjAction_apply (T : KType ε Λ) (k : KG ε) (A : T.V →L[ℂ] T.V) :
    ps2C T k A = T.op k * A * T.op k⁻¹ := by
  ext v
  rfl
private lemma integral_conj_equivariant (T : KType ε Λ) (μ : Fin n → ℤ) (k : KG ε) (x : Matrix (Fin n) (Fin n) ℂ) :
    ∫ k', PhiM μ (toMK k'⁻¹ * (toMK k * x * toMK k⁻¹) * toMK k') • (T.op k' * projW T * T.op k'⁻¹) ∂(muK ε) =
      ps2C T k (∫ k', PhiM μ (toMK k'⁻¹ * x * toMK k') • (T.op k' * projW T * T.op k'⁻¹) ∂(muK ε)) := by
  haveI : (muK ε).IsMulLeftInvariant := by
    unfold muK
    infer_instance
  rw [← ContinuousLinearEquiv.integral_comp_comm (ps2C T k)]
  calc _ = ∫ k', PhiM μ (toMK (k * k')⁻¹ * (toMK k * x * toMK k⁻¹) * toMK (k * k')) •
        (T.op (k * k') * projW T * T.op (k * k')⁻¹) ∂(muK ε) :=
        (MeasureTheory.integral_mul_left_eq_self (fun k' => PhiM μ (toMK k'⁻¹ * (toMK k * x * toMK k⁻¹) *
          toMK k') • (T.op k' * projW T * T.op k'⁻¹)) k).symm
    _ = _ := by
        congr 1
        funext k'
        rw [map_smul, conjAction_apply]
        congr 1
        · congr 1
          rw [_root_.mul_inv_rev, toMatrix_mul_alt, toMatrix_mul_alt]
          calc _ = toMK k'⁻¹ * (toMK k⁻¹ * toMK k) * x * (toMK k⁻¹ * toMK k) * toMK k' := by
                simp only [Matrix.mul_assoc]
            _ = _ := by rw [toMatrix_inv_mul, Matrix.mul_one, Matrix.mul_one]
        · rw [_root_.mul_inv_rev, kType_op_mul, kType_op_mul]
          simp only [mul_assoc]
end ReciprocityTheory.ChartRestriction.DS.S7
end
end

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) (k : KG ε) (x : Matrix (Fin n) (Fin n) ℂ) :
    psM T μ (toMK k * x * toMK k⁻¹) = T.op k * psM T μ x * T.op k⁻¹ := by
  simp only [psM]
  rw [integral_conj_equivariant, conjAction_apply, mul_smul_comm, smul_mul_assoc]
end ReciprocityTheory.ChartRestriction.DS.S7
