-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P12.identical_unitary_switch
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T06:23:37.074206+00:00
-- url     : https://prove2.me/submissions/c49dc95b-de8e-47dc-a569-8fe1d459abdb

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P12

noncomputable section

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace Aux_P12_identical_switch

theorem foldl_rep {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) :
    ∀ (n : ℕ) (V : Matrix (Fin d) (Fin d) ℂ),
      (List.replicate n U).foldl (fun V W => W * V) V = U ^ n * V := by
  intro n
  induction n with
  | zero => intro V; simp
  | succ n ih =>
    intro V
    rw [List.replicate_succ, List.foldl_cons, ih, pow_succ, Matrix.mul_assoc]

end Aux_P12_identical_switch

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Intake100.P12
  QAlgorithms.Papers.Independent.Information100.P21 in
theorem solution {d k : ℕ} (hd : 0 < d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    switchMatrix (k := k) (fun _ => (U : Op (Fin d))) =
      (1 : Op (Equiv.Perm (Fin k))) ⊗ₖ ((U : Op (Fin d))^k) := by
  ext a b
  simp only [switchMatrix, List.map_const', List.length_finRange]
  rw [Aux_P12_identical_switch.foldl_rep, Matrix.mul_one, Matrix.kronecker_apply,
    Matrix.one_apply]
  split_ifs <;> simp
