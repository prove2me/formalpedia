-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_H_lineCoeff__fb5a11f6bb6a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:42:46.556883+00:00
-- url     : https://prove2.me/submissions/bd5bc5bb-5141-43dc-9c0c-049a2b54d292

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_IteratedDerivLine
import Theorems.Thm_Formalism_L2_Th1_H_lineRestr_hasSubst
import Theorems.Thm_Formalism_L2_Th1_H_lineRestr_monomial
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution : LineCoeff := by
  intro K _ n _ _ v T k
  unfold lineRestr
  rw [PowerSeries.coeff, MvPowerSeries.coeff_subst (lineRestr_hasSubst v)]
  have key : ∀ d : n →₀ ℕ, MvPowerSeries.coeff d T •
      MvPowerSeries.coeff (Finsupp.single () k)
        (d.prod fun s e => (PowerSeries.C (v s) * PowerSeries.X : PowerSeries K) ^ e)
      = if k = ∑ i, d i then MvPowerSeries.coeff d T * ∏ i, v i ^ d i else 0 := by
    intro d
    rw [lineRestr_monomial]
    have : MvPowerSeries.coeff (Finsupp.single () k)
        (PowerSeries.C (∏ i, v i ^ d i) * PowerSeries.X ^ (∑ i, d i) : PowerSeries K)
        = PowerSeries.coeff k (PowerSeries.C (∏ i, v i ^ d i) * PowerSeries.X ^ (∑ i, d i) : PowerSeries K) := rfl
    rw [this, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    split_ifs <;> simp
  rw [finsum_congr key]
  rw [finsum_eq_sum_of_support_subset (s := Finset.finsuppAntidiag Finset.univ k)]
  · refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_finsuppAntidiag] at hd
    rw [if_pos hd.1.symm]
  · intro d hd
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hd
    obtain ⟨h, -⟩ := hd
    simp [Finset.mem_finsuppAntidiag, h]
end Formalism.L2.Th1.H
