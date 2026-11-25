-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_fibreComponent_dim_succ_le_b9f9102418e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:26:21.5072+00:00
-- url     : https://prove2.me/submissions/ebdfd273-1b62-4029-859b-5d9792d184d3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsFibreCompDimZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_OfChartPointSecPointSpecChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureCharZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PFibreCompDimZ

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
open MvPolynomial IsDedekindDomain
variable {σ : Type} [Fintype σ] {P : Ideal (MvPolynomial σ ℤ)}
omit [Fintype σ]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (hP : P.IsPrime) (hPC : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥)
    {p : ℕ} (hp : p.Prime) {W : Ideal (MvPolynomial σ ℤ)}
    (hW : W ∈ (P ⊔ Ideal.span {(C (p : ℤ) : MvPolynomial σ ℤ)}).minimalPrimes) :
    ringKrullDim (MvPolynomial σ ℤ ⧸ W) + 1 ≤ ringKrullDim (MvPolynomial σ ℤ ⧸ P) := by
  have hCp : (C (p : ℤ) : MvPolynomial σ ℤ) ∉ P := fun h => by
    have : (p : ℤ) ∈ P.comap (C : ℤ →+* MvPolynomial σ ℤ) := h
    rw [hPC, Ideal.mem_bot] at this
    exact hp.ne_zero (by exact_mod_cast this)
  exact ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor (le_sup_left.trans hW.1.2))
    (Ideal.Quotient.factor_surjective _) (r := Ideal.Quotient.mk P (C (p : ℤ)))
    (mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]))
    (by
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hW.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl)))
end GroundTheory.Heights₂.Heights
