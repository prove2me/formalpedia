-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FlagGramNonneg.gamma_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:22.633564+00:00
-- url     : https://prove2.me/submissions/c9a74234-ac44-4c31-9a54-dfa9c78259a0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_BinaryFormMulEqNormSqAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix ComplexConjugate
namespace PI.UnitaryGroupMassFormula.FlagGramNonneg
private theorem re_star_mul' (z w : ℂ) : (star z * w).re = z.re * w.re + z.im * w.im := by
  change ((starRingEnd ℂ) z * w).re = _
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring
end PI.UnitaryGroupMassFormula.FlagGramNonneg
end
end

set_option autoImplicit false
noncomputable section
open Matrix ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FlagGramNonneg
namespace PI.UnitaryGroupMassFormula.FlagGramNonneg
theorem _root_.solution (r : ℕ) (T T' : ℝ) (s : ℂ) (c : Fin r ⊕ Fin 2 → ℂ) :
    (star c ⬝ᵥ (gamma r T T' s *ᵥ c)).re =
      -2 * ∑ a, Complex.normSq (c (Sum.inl a)) -
        (T * Complex.normSq (c (Sum.inr 0)) + T' * Complex.normSq (c (Sum.inr 1)) -
          2 * (conj (c (Sum.inr 0)) * s * c (Sum.inr 1)).re) := by
  have hinl : ∀ a, (gamma r T T' s *ᵥ c) (Sum.inl a) =
      -(c (Sum.inl a) + c (Sum.inl a)) := by
    intro a
    first
    | (rw [gamma, Matrix.fromBlocks_mulVec]
       simp [Matrix.smul_mulVec_assoc, Matrix.one_mulVec] <;> ring1)
    | (rw [gamma, Matrix.fromBlocks_mulVec]
       simp [Matrix.smul_mulVec, Matrix.one_mulVec] <;> ring1)
    | (simp [gamma, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply,
        mul_ite, ite_mul, Finset.sum_ite_eq] <;> ring1)
    | (simp [gamma, Matrix.mulVec, Matrix.dotProduct, Fintype.sum_sum_type,
        Matrix.one_apply, mul_ite, ite_mul, Finset.sum_ite_eq] <;> ring1)
  have hinr0 : (gamma r T T' s *ᵥ c) (Sum.inr 0) =
      -(T : ℂ) * c (Sum.inr 0) + s * c (Sum.inr 1) := by
    rw [gamma, Matrix.fromBlocks_mulVec]
    simp [dotProduct, Fin.sum_univ_two]
  have hinr1 : (gamma r T T' s *ᵥ c) (Sum.inr 1) =
      conj s * c (Sum.inr 0) + -(T' : ℂ) * c (Sum.inr 1) := by
    rw [gamma, Matrix.fromBlocks_mulVec]
    simp [dotProduct, Fin.sum_univ_two]
  have hsplit : star c ⬝ᵥ (gamma r T T' s *ᵥ c) =
      ∑ a, star (c (Sum.inl a)) * (gamma r T T' s *ᵥ c) (Sum.inl a) +
        (star (c (Sum.inr 0)) * (gamma r T T' s *ᵥ c) (Sum.inr 0) +
          star (c (Sum.inr 1)) * (gamma r T T' s *ᵥ c) (Sum.inr 1)) := by
    simp only [dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, Pi.star_apply]
  have hsum : (∑ a, star (c (Sum.inl a)) * -(c (Sum.inl a) + c (Sum.inl a))).re =
      -2 * ∑ a, Complex.normSq (c (Sum.inl a)) := by
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [re_star_mul', Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
      Complex.normSq_apply]
    ring
  rw [hsplit]
  simp only [hinl, hinr0, hinr1]
  simp only [Complex.add_re, hsum, re_star_mul']
  simp only [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  ring
end PI.UnitaryGroupMassFormula.FlagGramNonneg
