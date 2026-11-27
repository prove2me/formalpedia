-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:21:57.998424+00:00
-- url     : https://prove2.me/submissions/01cae0e4-519e-46c6-abbf-12b070840c62

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralMonSelf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_Imports
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_Phi_diag
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_Phi_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_Phi_one
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_eval_sub
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_gip_diag
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_hk_diag
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_integral_Phi
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_integral_mon_self
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_jr_pos
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_mon_prod
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_norm_Phi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate ComplexOrder
namespace PositivityTheory.Rg.Sw.FFTSteps
open PosProof
private theorem gip_monomial_self_eq_prod_jr {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
    (m : Sg ι A B →₀ ℕ) :
    gip (monomial m (1 : ℂ)) (monomial m (1 : ℂ)) = ((∏ s : Sg ι A B, jr (m s) : ℝ) : ℂ) := by
  rw [← integral_mon_self m]
  unfold gip
  congr 1
  funext z
  rw [mon_prod]
  have h1 : (eval z) (monomial m (1 : ℂ)) = ∏ s : Sg ι A B, z s ^ m s := by
    rw [eval_monomial, one_mul, Finsupp.prod_fintype]
    intro i
    simp
  rw [h1, star_prod, ← Finset.prod_mul_distrib, Complex.ofReal_sum, ← Finset.sum_neg_distrib,
    Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [hk_diag, star_pow, ← mul_pow]
  have h2 : z s * star (z s) = ((‖z s‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h2]
  push_cast
  ring_nf
private theorem pos_lemma {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
    (d : ι → ℝ) (m : Sg ι A B →₀ ℕ) :
    sub 1 (Matrix.diagonal fun i => (d i : ℂ)) (monomial m (1 : ℂ)) =
      C ((∏ s : Sg ι A B, kap d s ^ m s : ℝ) : ℂ) * monomial m (1 : ℂ) := by
  apply MvPolynomial.funext
  intro z
  rw [PosProof.eval_sub, Phi_diag, eval_mul, eval_C, eval_monomial, eval_monomial, one_mul, one_mul,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  push_cast
  simp only [mul_pow, Finset.prod_mul_distrib]
private theorem lam_eq_prod_kap_pow {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
    (d : ι → ℝ) (m : Sg ι A B →₀ ℕ) :
    lam d m = ∏ s : Sg ι A B, kap d s ^ m s := by
  classical
  have hP : (0 : ℝ) < ∏ s : Sg ι A B, jr (m s) := Finset.prod_pos fun s _ => jr_pos _
  have h := gip_diag (A := A) (B := B) d (monomial m (1 : ℂ))
  rw [pos_lemma, support_monomial, if_neg one_ne_zero, Finset.sum_singleton, coeff_monomial, if_pos rfl,
    Complex.normSq_one, one_mul] at h
  have h3 : gip (C ((∏ s : Sg ι A B, kap d s ^ m s : ℝ) : ℂ) * monomial m (1 : ℂ)) (monomial m (1 : ℂ)) =
      ((∏ s : Sg ι A B, kap d s ^ m s : ℝ) : ℂ) * ((∏ s : Sg ι A B, jr (m s) : ℝ) : ℂ) := by
    rw [← gip_monomial_self_eq_prod_jr]
    unfold gip
    rw [← integral_const_mul]
    congr 1
    funext z
    rw [eval_mul, eval_C]
    ring
  rw [h3] at h
  have h4 : (∏ s : Sg ι A B, kap d s ^ m s) * (∏ s : Sg ι A B, jr (m s)) =
      lam d m * ∏ s : Sg ι A B, jr (m s) := by
    exact_mod_cast h
  exact (mul_right_cancel₀ hP.ne' h4).symm
private theorem gip_sub_eq_of_unitary_conj_diag {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
    (M U D : Matrix ι ι ℂ) (hU1 : star U * U = 1) (hU2 : U * star U = 1) (hMU : M * U = U * D)
    (f : PV ι A B) :
    gip (sub 1 M f) f = gip (sub 1 D (sub 1 U f)) (sub 1 U f) := by
  have hcont : Continuous fun z : Sg ι A B → ℂ =>
      (eval z) (sub 1 M f) * star ((eval z) f) * Complex.exp (-↑(∑ s : Sg ι A B, ‖z s‖ ^ 2)) :=
    ((continuous_eval _).mul (continuous_star.comp (continuous_eval _))).mul
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp
        (continuous_finset_sum _ fun s _ => (continuous_norm.comp (continuous_apply s)).pow 2)).neg)
  unfold gip
  rw [integral_Phi U hU1 hU2 _ hcont]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [PosProof.eval_sub]
  rw [← Phi_mul, ← Phi_mul, hMU, norm_Phi U hU1]
end PositivityTheory.Rg.Sw.FFTSteps
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
open PosProof
namespace PositivityTheory.Rg.Sw.FFTSteps
theorem _root_.solution : Pos := by
  intro ι A B _ _ _ _ M hM f
  have hH := hM.isHermitian
  have hMe : M = (hH.eigenvectorUnitary : Matrix ι ι ℂ) *
      Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) * star (hH.eigenvectorUnitary : Matrix ι ι ℂ) := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  have hU1 : star (hH.eigenvectorUnitary : Matrix ι ι ℂ) * (hH.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  have hU2 : (hH.eigenvectorUnitary : Matrix ι ι ℂ) * star (hH.eigenvectorUnitary : Matrix ι ι ℂ) = 1 := by
    simpa [Unitary.coe_star] using Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hMU : M * (hH.eigenvectorUnitary : Matrix ι ι ℂ) =
      (hH.eigenvectorUnitary : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) := by
    have h := congrArg (· * (hH.eigenvectorUnitary : Matrix ι ι ℂ)) hMe
    rw [h, Matrix.mul_assoc (_ * _), hU1, Matrix.mul_one]
  have hkap : ∀ s : Sg ι A B, 0 ≤ kap hH.eigenvalues s := by
    intro s
    rcases s with s | s
    · simp [kap]
    · simp only [kap, Sum.elim_inr]
      exact hM.eigenvalues_nonneg _
  rw [gip_sub_eq_of_unitary_conj_diag M _ _ hU1 hU2 hMU f, gip_diag]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, trivial, ?_⟩
  · refine Finset.sum_nonneg fun m _ => mul_nonneg (mul_nonneg (Complex.normSq_nonneg _) ?_)
      (Finset.prod_nonneg fun s _ => (jr_pos _).le)
    rw [lam_eq_prod_kap_pow]
    exact Finset.prod_nonneg fun s _ => pow_nonneg (hkap s) _
  · intro hPD hf
    have hkap' : ∀ s : Sg ι A B, 0 < kap hH.eigenvalues s := by
      intro s
      rcases s with s | s
      · simp [kap]
      · simp only [kap, Sum.elim_inr]
        exact hPD.eigenvalues_pos _
    have hinv : sub 1 (star (hH.eigenvectorUnitary : Matrix ι ι ℂ))
        (sub 1 (hH.eigenvectorUnitary : Matrix ι ι ℂ) f) = f := by
      apply MvPolynomial.funext
      intro z
      rw [PosProof.eval_sub, PosProof.eval_sub, ← Phi_mul, hU2, Phi_one]
    have hg : sub 1 (hH.eigenvectorUnitary : Matrix ι ι ℂ) f ≠ 0 := by
      intro hg
      apply hf
      rw [← hinv, hg, map_zero]
    refine Finset.sum_pos (fun m hm => mul_pos (mul_pos (Complex.normSq_pos.2 (mem_support_iff.1 hm)) ?_)
      (Finset.prod_pos fun s _ => jr_pos _)) ?_
    · rw [lam_eq_prod_kap_pow]
      exact Finset.prod_pos fun s _ => pow_pos (hkap' s) _
    · exact Finset.nonempty_iff_ne_empty.2 (by rwa [Ne, MvPolynomial.support_eq_empty])
end PositivityTheory.Rg.Sw.FFTSteps
