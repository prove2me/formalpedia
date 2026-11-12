-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P10.renyi_order_complement
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T02:35:42.064208+00:00
-- url     : https://prove2.me/submissions/c77780af-c381-4b25-9b98-89824397545b

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P10

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal Topology

open Filter Set MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)

open QAlgorithms.Papers.Independent.Dependency50.P18 (logBits)

open QAlgorithms.Papers.Independent.Advance50.P10 in
theorem solution {I : Type} [Fintype I] [DecidableEq I]
    (A B : Operator I) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (a : ℝ) (ha : 0 < a) (ha_one : a < 1) :
    petzRelativeBits (1 - a) A B = (((1 - a) / a : ℝ) : EReal) * petzRelativeBits a B A := by
  have h1 : (1 - a) ≠ 1 := by intro h; linarith
  have h2 : ¬ (1 < 1 - a ∧ ¬ SupportIncluded A B) := fun h => by linarith [h.1]
  have h3 : a ≠ 1 := by intro h; linarith
  have h4 : ¬ (1 < a ∧ ¬ SupportIncluded B A) := fun h => by linarith [h.1]
  unfold petzRelativeBits
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  have hT : petzTrace (1 - a) A B = petzTrace a B A := by
    unfold petzTrace
    rw [sub_sub_cancel, Matrix.trace_mul_comm]
  have hr : ((1 - a - 1)⁻¹ : ℝ) = (1 - a) / a * (a - 1)⁻¹ := by
    rw [show (1 - a - 1 : ℝ) = -a by ring]
    have ha0 : a ≠ 0 := ha.ne'
    have ha1 : a - 1 ≠ 0 := by intro h; linarith
    field_simp <;> ring
  rw [hT, hr, EReal.coe_mul, mul_assoc]

end
