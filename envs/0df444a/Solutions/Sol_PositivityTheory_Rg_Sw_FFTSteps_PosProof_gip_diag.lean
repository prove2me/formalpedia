-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PosProof.gip_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:31:13.632697+00:00
-- url     : https://prove2.me/submissions/048bf4b9-6af8-4cb8-bfeb-7e5994e0cff4

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousPhi
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralMonSelf
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_integrable_mon
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_integral_mon_ne
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_integral_mon_self
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_Phi_diag
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_eval_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.PosProof
variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof
theorem _root_.solution (d : ι → ℝ) (g : PV ι A B) :
    gip (sub 1 (Matrix.diagonal fun i => (d i : ℂ)) g) g =
      ((∑ m ∈ g.support, Complex.normSq (g.coeff m) * lam d m * ∏ s, jr (m s) : ℝ) : ℂ) := by
  unfold gip
  have hpt : ∀ z : Sg ι A B → ℂ,
      eval z (sub 1 (Matrix.diagonal fun i => (d i : ℂ)) g) * star (eval z g) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) =
        ∑ m ∈ g.support, ∑ m' ∈ g.support, (g.coeff m * (lam d m : ℂ) * star (g.coeff m')) *
          (mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ))) := by
    intro z
    rw [eval_sub, Phi_diag, MvPolynomial.eval_eq', MvPolynomial.eval_eq']
    have hl : ∀ m : Sg ι A B →₀ ℕ, ∏ s, ((kap d s : ℂ) * z s) ^ m s = (lam d m : ℂ) * mon m z := by
      intro m
      simp only [mul_pow, Finset.prod_mul_distrib, lam, mon]
      push_cast
      rfl
    simp_rw [hl]
    rw [star_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m' _ => ?_
    have hmon : (∏ i, z i ^ m' i) = mon m' z := rfl
    try simp only [star_mul']
    try rw [hmon]
    ring
  simp_rw [hpt]
  have hint : ∀ m m' : Sg ι A B →₀ ℕ, Integrable fun z : Sg ι A B → ℂ => mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) :=
    integrable_mon
  rw [integral_finset_sum _ fun m _ => integrable_finset_sum _ fun m' _ => (hint m m').const_mul _]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [integral_finset_sum _ fun m' _ => (hint m m').const_mul _]
  simp_rw [integral_const_mul]
  rw [Finset.sum_eq_single_of_mem m hm fun m' _ hne => by rw [integral_mon_ne m m' hne.symm, mul_zero]]
  rw [integral_mon_self]
  have hc : ((Complex.normSq (g.coeff m) : ℝ) : ℂ) = g.coeff m * star (g.coeff m) := by
    rw [Complex.star_def, Complex.mul_conj]
  rw [Complex.ofReal_mul, Complex.ofReal_mul, hc]
  ring
end PositivityTheory.Rg.Sw.FFTSteps.PosProof
