-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P67.klm_threefoldPorts
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:40:54.38869+00:00
-- url     : https://prove2.me/submissions/14f2a30b-15ca-4e00-9521-cd7926f0812d

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P67

noncomputable section

open scoped Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)
open QAlgorithms.Papers.Independent.Advance50.P49 (spinMultiplicity)

open QAlgorithms.Papers.Independent.Intake100.P67 in
theorem solution (N m : ℕ) (hN : 1 ≤ N) (hm : 1 ≤ m) :
    probabilisticOptimumSuccess N = klmCurve m ↔ N = 3 * m := by
  unfold probabilisticOptimumSuccess klmCurve
  have h1 : (0 : ℝ) < (N : ℝ) + 3 := by positivity
  have h2 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have key : (N : ℝ) / (N + 3) = 1 - 1 / ((m : ℝ) + 1) ↔ (N : ℝ) * ((m : ℝ) + 1) = (m : ℝ) * ((N : ℝ) + 3) := by
    rw [div_eq_iff h1.ne', one_sub_div h2.ne', div_mul_eq_mul_div, eq_div_iff h2.ne']
    constructor <;> intro h <;> linarith
  rw [key]
  constructor
  · intro h
    have h' : (N : ℝ) = 3 * m := by linarith
    exact_mod_cast h'
  · intro h
    subst h
    push_cast
    ring
