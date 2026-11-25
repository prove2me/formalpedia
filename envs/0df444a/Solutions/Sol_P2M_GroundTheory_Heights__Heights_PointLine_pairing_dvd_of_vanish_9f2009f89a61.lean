-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointLine_pairing_dvd_of_vanish_9f2009f89a61
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:33.248907+00:00
-- url     : https://prove2.me/submissions/f07d6388-c98d-4473-932f-339d6209551a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_eval_pairing_f70de561052b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_exists_ne_zero_98697fadef41

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.PointLine
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.PointLine
theorem _root_.solution {y : Fin n → ℂ} (hy : y ≠ 0) (f : MvPolynomial (Fin 1 × Fin n) ℂ)
    (hf : ∀ u, eval u (pairing y) = 0 → eval u f = 0) : pairing y ∣ f := by
  obtain ⟨a, ha⟩ := exists_ne_zero hy
  set ℓ := pairing y with hℓ
  let c : Fin 1 × Fin n → ℂ := Pi.single ((0 : Fin 1), a) (y a)⁻¹
  let s : Fin 1 × Fin n → MvPolynomial (Fin 1 × Fin n) ℂ := fun ij => X ij - C (c ij) * ℓ
  have hsum : ∀ L : ℂ, ∑ j, y j * c (0, j) * L = L := by
    intro L
    rw [← Finset.sum_mul]
    have : ∑ j, y j * c (0, j) = y a * (y a)⁻¹ := by
      rw [Finset.sum_eq_single a]
      · simp [c]
      · intro j _ hj
        simp [c, hj]
      · simp
    rw [this, mul_inv_cancel₀ ha, one_mul]
  have hs0 : bind₁ s f = 0 := by
    apply MvPolynomial.funext
    intro u
    rw [map_zero]
    have he : eval u (bind₁ s f) = eval (fun ij => eval u (s ij)) f := by
      simp only [eval, eval₂Hom_bind₁]
    rw [he]
    apply hf
    rw [eval_pairing]
    simp only [s, map_sub, map_mul, eval_X, eval_C, mul_sub, Finset.sum_sub_distrib]
    have h2 : ∀ j, y j * (c (0, j) * eval u ℓ) = y j * c (0, j) * eval u ℓ := fun j => by ring
    simp only [h2, hsum]
    rw [hℓ, eval_pairing, sub_self]
  have hmem : f - bind₁ s f ∈ Ideal.span {ℓ} := by
    have hcomp : (Ideal.Quotient.mkₐ ℂ (Ideal.span {ℓ})).comp (bind₁ s) =
        Ideal.Quotient.mkₐ ℂ (Ideal.span {ℓ}) := by
      apply MvPolynomial.algHom_ext
      intro ij
      simp only [AlgHom.comp_apply, bind₁_X_right, s, Ideal.Quotient.mkₐ_eq_mk, map_sub, map_mul,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ℓ), mul_zero, sub_zero]
    have h := DFunLike.congr_fun hcomp f
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h
    exact Ideal.Quotient.eq.mp h.symm
  rw [hs0, sub_zero, Ideal.mem_span_singleton] at hmem
  exact hmem
end GroundTheory.Heights₂.Heights.PointLine
