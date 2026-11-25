-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_exp_quadratic_tau_shifted_d0d1d6cc101f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:10.606261+00:00
-- url     : https://prove2.me/submissions/69f3853b-6308-49ec-952e-ff276853cd90

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_expCover_castLE_2782f8a785fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_quadratic_tau_shifted_3046c5c219fb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.PeriodPolydisc
variable {n a g : ℕ} (P : PeriodPolydisc n a g)
namespace GroundTheory.Heights₂.Heights.Regular.PeriodPolydisc
theorem _root_.solution (v : Fin g → ℤ) (hnn : ∀ i, 0 ≤ intQuad (P.B i) v) (h : (Fin n → ℂ) → ℂ)
    (w : Fin n → ℂ)
    (hw : Complex.exp (2 * Real.pi * Complex.I *
        ((fun k => (v k : ℂ)) ⬝ᵥ P.τ w *ᵥ fun k => (v k : ℂ))) =
      (∏ i : Fin a, expCover a w (Fin.castLE P.a_le i) ^ (intQuad (P.B i) v).toNat) *
        h (expCover a w)) :
    Complex.exp (2 * Real.pi * Complex.I *
        ((fun k => (v k : ℂ)) ⬝ᵥ P.tau0 w *ᵥ fun k => (v k : ℂ))) = h (expCover a w) := by
  have hk : ∀ i, ((intQuad (P.B i) v : ℤ) : ℂ) = (((intQuad (P.B i) v).toNat : ℕ) : ℂ) := fun i => by
    exact_mod_cast (Int.toNat_of_nonneg (hnn i)).symm
  have hprod : ∏ i : Fin a, expCover a w (Fin.castLE P.a_le i) ^ (intQuad (P.B i) v).toNat ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => by
      rw [expCover_castLE]
      exact pow_ne_zero _ (Complex.exp_ne_zero _)
  have hsum : Complex.exp (2 * Real.pi * Complex.I * ∑ i : Fin a,
      w (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I) * ((intQuad (P.B i) v : ℤ) : ℂ)) =
      ∏ i : Fin a, expCover a w (Fin.castLE P.a_le i) ^ (intQuad (P.B i) v).toNat := by
    rw [Finset.mul_sum, Complex.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [expCover_castLE, ← Complex.exp_nat_mul, hk i]
    congr 1
    field_simp [two_pi_I_ne_zero]
  rw [quadratic_tau_shifted, mul_sub, Complex.exp_sub, hw, hsum]
  field_simp
end GroundTheory.Heights₂.Heights.Regular.PeriodPolydisc
