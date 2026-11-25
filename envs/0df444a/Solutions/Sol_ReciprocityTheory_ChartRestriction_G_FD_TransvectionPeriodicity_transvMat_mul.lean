-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity.transvMat_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:39.023187+00:00
-- url     : https://prove2.me/submissions/65011cad-163e-4bfc-aa02-b48048a05651

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_AdmissibleHermitianColumns
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TransvectionPeriodicity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
theorem _root_.solution (G : Matrix (Fin r) (Fin r) E) {ξ : Fin r → E} (hξ : herm G ξ ξ = 0)
    (α β : E) : transvMat G ξ α * transvMat G ξ β = transvMat G ξ (α + β) := by
  set w : Fin r → E := fun b => ∑ k, G b k * cc (ξ k) with hw
  have hA : ∀ γ, transvMat G ξ γ = 1 + γ • Matrix.vecMulVec ξ w := by
    intro γ
    ext a b
    simp only [transvMat, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, hw]
    ring
  have h0 : ∑ j, w j * ξ j = 0 := by
    rw [← hξ]
    unfold herm
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hw, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

  have hAA : Matrix.vecMulVec ξ w * Matrix.vecMulVec ξ w = 0 := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
    calc ∑ j, ξ a * w j * (ξ j * w b) = ξ a * w b * ∑ j, w j * ξ j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [h0, mul_zero]
  rw [hA, hA, hA, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, smul_mul_smul_comm, hAA,
    smul_zero, add_zero, add_smul]
  abel
end ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
