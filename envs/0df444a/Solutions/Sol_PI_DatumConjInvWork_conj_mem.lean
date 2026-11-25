-- Prove2me | solution 1 for PI.DatumConjInvWork.conj_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:27:20.473591+00:00
-- url     : https://prove2.me/submissions/7ed6aa09-db0b-4916-b41f-11830502e8fd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DatumConjInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugationInvariance_SecondRowsBlockDiagMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
namespace PI.DatumConjInvWork
variable {F : Type} [Field F] {a t : ℕ}
private theorem int_mul_lemma {O : Subring F} {n : ℕ} {A B : Matrix (Fin n) (Fin n) F}
    (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) : ∀ i j, (A * B) i j ∈ O := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem O fun k _ => O.mul_mem (hA i k) (hB k j)
end PI.DatumConjInvWork
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.DatumConjInvWork
variable {F : Type} [Field F] {a t : ℕ}
namespace PI.DatumConjInvWork
theorem _root_.solution (O : Subring F) (ϖ : F) (h : GL (Fin a) F) (hh : h ∈ Formalism.DoubleCosetMeasures.GLint O a)
    (g : GL (Fin a) F) (hg : g ∈ Formalism.DoubleCosetMeasures.congSub O ϖ a) :
    h⁻¹ * g * h ∈ Formalism.DoubleCosetMeasures.congSub O ϖ a := by
  have hh' : (∀ i j, (h : Matrix (Fin a) (Fin a) F) i j ∈ O) ∧
      (∀ i j, ((h⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) i j ∈ O) := hh
  have hg' : g ∈ Formalism.DoubleCosetMeasures.GLint O a ∧
      ∀ i j, (ϖ⁻¹ • ((g : Matrix (Fin a) (Fin a) F) - 1)) i j ∈ O := hg
  have hmem : h⁻¹ * g * h ∈ Formalism.DoubleCosetMeasures.GLint O a :=
    (Formalism.DoubleCosetMeasures.GLint O a).mul_mem ((Formalism.DoubleCosetMeasures.GLint O a).mul_mem ((Formalism.DoubleCosetMeasures.GLint O a).inv_mem hh) hg'.1) hh
  have key : ϖ⁻¹ • (((h⁻¹ * g * h : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) - 1) =
      ((h⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) * (ϖ⁻¹ • ((g : Matrix (Fin a) (Fin a) F) - 1)) *
        (h : Matrix (Fin a) (Fin a) F) := by
    simp only [Units.val_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul]
  show h⁻¹ * g * h ∈ Formalism.DoubleCosetMeasures.GLint O a ∧
    ∀ i j, (ϖ⁻¹ • (((h⁻¹ * g * h : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) - 1)) i j ∈ O
  refine ⟨hmem, ?_⟩
  rw [key]
  exact int_mul_lemma (int_mul_lemma hh'.2 hg'.2) hh'.1
end PI.DatumConjInvWork
