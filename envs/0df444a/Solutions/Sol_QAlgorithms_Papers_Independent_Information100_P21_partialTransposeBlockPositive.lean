-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P21.partialTransposeBlockPositive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T05:58:40.814893+00:00
-- url     : https://prove2.me/submissions/96952cbe-039f-44f7-a837-5289726254ac

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P21 in
theorem solution (rho : Op QQ) (h : rho.PosSemidef) (e f : Vec (Fin 2)) :
  quad (pt rho) (tensor e f) = quad rho (tensor e (conjugate f)) ∧
    0 ≤ quad (pt rho) (tensor e f) := by
  have key : quad (pt rho) (tensor e f) = quad rho (tensor e (conjugate f)) := by
    have h1 : ∀ p q : Fin 2 × Fin 2, (pt rho : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) p q
        = rho (p.1, q.2) (q.1, p.2) := fun _ _ => rfl
    have h2 : ∀ p : Fin 2 × Fin 2, (tensor e f) p = e p.1 * f p.2 := fun _ => rfl
    have h3 : ∀ p : Fin 2 × Fin 2, (tensor e (conjugate f)) p = e p.1 * conj (f p.2) :=
      fun _ => rfl
    unfold quad
    simp only [h1, h2, h3, map_mul, Complex.conj_conj, Fintype.sum_prod_type]
    congr 1
    simp only [Fin.sum_univ_two]
    ring
  refine ⟨key, ?_⟩
  rw [key]
  have hv := h.dotProduct_mulVec_nonneg (fun p => (tensor e (conjugate f)) p)
  have : (star (fun p => (tensor e (conjugate f)) p) ⬝ᵥ
      (rho *ᵥ fun p => (tensor e (conjugate f)) p)) =
      ∑ i, ∑ j, conj ((tensor e (conjugate f)) i) * rho i j * (tensor e (conjugate f)) j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def,
      mul_assoc]
  unfold quad
  rw [this] at hv
  exact (Complex.nonneg_iff.mp hv).1
