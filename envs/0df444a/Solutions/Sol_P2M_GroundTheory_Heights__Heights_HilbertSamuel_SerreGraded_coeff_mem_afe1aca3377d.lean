-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_coeff_mem_afe1aca3377d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:05:03.619953+00:00
-- url     : https://prove2.me/submissions/41c8a29e-fdd3-47fc-b872-ea87743a36a8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSerreGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSerreGraded
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_smul_coeff_mem_5255ac3f8e81
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_gradedSpan_gen_mem_90c514e33d20


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
open Polynomial
variable {Ω : Type} [Field Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω)
variable [Algebra (MvPolynomial (Fin q) ℤ) (Polynomial Ω)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
theorem _root_.solution (hA : algebraMap (MvPolynomial (Fin q) ℤ) (Polynomial Ω) = act w) {m : (Polynomial Ω)}
    (hm : m ∈ gradedModule q d t) (n : ℕ) : m.coeff n ∈ gradedSpan w d t n := by
  let P : Submodule (MvPolynomial (Fin q) ℤ) (Polynomial Ω) :=
    { carrier := {p | ∀ n, p.coeff n ∈ gradedSpan w d t n}
      add_mem' := fun ha hb n => by rw [coeff_add]; exact add_mem (ha n) (hb n)
      zero_mem' := fun n => by simp
      smul_mem' := fun c _ hp => smul_coeff_mem w d t hA c hp }
  have hle : gradedModule q d t ≤ P := by
    rw [gradedModule, Submodule.span_le]
    rintro _ ⟨l, rfl⟩ n
    rw [coeff_C_mul_X_pow]
    split_ifs with h
    · subst h
      simpa using gradedSpan_gen_mem w d t l 0
    · exact zero_mem _
  exact hle hm n
end GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
