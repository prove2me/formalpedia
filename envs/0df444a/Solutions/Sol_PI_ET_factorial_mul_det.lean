-- Prove2me | solution 1 for PI.ET.factorial_mul_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:43:10.49202+00:00
-- url     : https://prove2.me/submissions/0fc83dbf-3b56-4148-b8bd-f29c21290006

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_ProdLeOfInjective
import Theorems.Thm_PI_ET_det_mul_rect
import Theorems.Thm_PI_ET_sum_comp_perm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.ET
namespace PI.ET
theorem _root_.solution (k n : ℕ) (q : Fin n → ℂ) (V : Matrix (Fin n) (Fin k) ℂ) :
    (k.factorial : ℂ) * (Vᴴ * diagonal q * V).det =
      ∑ f : Fin k → Fin n, (∏ i, q (f i)) *
        ((V.submatrix f id).det * star (V.submatrix f id).det) := by
  have h2 : ∀ f : Fin k → Fin n, ((Vᴴ * diagonal q).submatrix id f).det =
      (∏ i, q (f i)) * star (V.submatrix f id).det := by
    intro f
    have he : (Vᴴ * diagonal q).submatrix id f = (V.submatrix f id)ᴴ * diagonal (fun i => q (f i)) := by
      ext a b
      simp [conjTranspose_apply, mul_diagonal, submatrix_apply]
    rw [he, det_mul, det_diagonal, det_conjTranspose, mul_comm]
  have h3 : ∀ (f : Fin k → Fin n) (τ : Equiv.Perm (Fin k)),
      (V.submatrix (fun i => f (τ i)) id).det = Equiv.Perm.sign τ * (V.submatrix f id).det := by
    intro f τ
    exact det_permute τ (V.submatrix f id)
  have hperm : ∀ τ : Equiv.Perm (Fin k),
      ∑ f : Fin k → Fin n, (∏ i, V (f i) i) * ((∏ i, q (f i)) * star (V.submatrix f id).det) =
        ∑ f : Fin k → Fin n, ((Equiv.Perm.sign τ : ℂ) * ∏ i, V (f (τ i)) i) *
          ((∏ i, q (f i)) * star (V.submatrix f id).det) := by
    intro τ
    rw [← sum_comp_perm (fun f : Fin k → Fin n =>
      (∏ i, V (f i) i) * ((∏ i, q (f i)) * star (V.submatrix f id).det)) τ]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only
    rw [h3 f τ, Equiv.prod_comp τ (fun i => q (f i)), star_mul', star_intCast]
    ring
  rw [det_mul_rect]
  simp_rw [h2]
  rw [show (k.factorial : ℂ) * ∑ f : Fin k → Fin n,
      (∏ i, V (f i) i) * ((∏ i, q (f i)) * star (V.submatrix f id).det) =
      ∑ τ : Equiv.Perm (Fin k), ∑ f : Fin k → Fin n,
      (∏ i, V (f i) i) * ((∏ i, q (f i)) * star (V.submatrix f id).det) by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]]
  rw [Finset.sum_congr rfl fun τ _ => hperm τ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hd : (V.submatrix f id).det = ∑ τ : Equiv.Perm (Fin k), (Equiv.Perm.sign τ : ℂ) * ∏ i, V (f (τ i)) i := by
    rw [det_apply']
    rfl
  rw [← Finset.sum_mul, ← hd]
  ring
end PI.ET
