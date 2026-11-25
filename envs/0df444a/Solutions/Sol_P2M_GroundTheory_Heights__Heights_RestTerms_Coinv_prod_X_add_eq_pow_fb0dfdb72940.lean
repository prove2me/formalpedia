-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_prod_X_add_eq_pow_fb0dfdb72940
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:22:54.672284+00:00
-- url     : https://prove2.me/submissions/34204015-d7fa-4e9b-9194-c1b37ca2406b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoinvReduction
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_rename_esymm_mem_1c581a89718a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Coinv
open MvPolynomial Finset
noncomputable section
variable (K : Type*) [Field K] (f n : ℕ)
variable {K f n}
variable [CharZero K]
namespace GroundTheory.Heights₂.Heights.RestTerms.Coinv
theorem _root_.solution (b : Fin f) :
    (∏ i : Fin n, (Polynomial.X + Polynomial.C
      (Ideal.Quotient.mk (psumIdeal K f n) (X (b, i))))) = Polynomial.X ^ n := by
  set φ : MvPolynomial (Fin n) K →+* MvPolynomial (Fin f × Fin n) K ⧸ psumIdeal K f n :=
    (Ideal.Quotient.mk (psumIdeal K f n)).comp (rename (fun i : Fin n => (b, i))).toRingHom
  have hV := congrArg (Polynomial.map φ) (MvPolynomial.prod_C_add_X_eq_sum_esymm K (Fin n))
  simp only [Polynomial.map_prod, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, Fintype.card_fin] at hV
  have hφX : ∀ i : Fin n, φ (X i) = Ideal.Quotient.mk (psumIdeal K f n) (X (b, i)) := by
    intro i; simp [φ]
  simp only [hφX] at hV
  rw [hV, Finset.sum_range_succ']
  have hz : ∀ j ∈ range n, Polynomial.C (φ (esymm (Fin n) K (j + 1))) *
      (Polynomial.X : Polynomial (MvPolynomial (Fin f × Fin n) K ⧸ psumIdeal K f n)) ^ (n - (j + 1)) = 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    have : φ (esymm (Fin n) K (j + 1)) = 0 := by
      simp only [φ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (rename_esymm_mem b (by omega) (by omega))
    rw [this, map_zero, zero_mul]
  rw [Finset.sum_eq_zero hz, zero_add]
  simp [esymm_zero]
end GroundTheory.Heights₂.Heights.RestTerms.Coinv
