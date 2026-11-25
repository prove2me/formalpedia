-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PowSpanB.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:17:36.176188+00:00
-- url     : https://prove2.me/submissions/580ecba8-714b-437b-a156-4ece0ae901b7

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_PowSpan
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PowSpanB_pow_mem
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PowSpanB_natCast_smul_add_mem_W
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MvPolynomial
namespace PositivityTheory.Rg.Sw.FFTSteps
namespace PowSpanB
variable {m n : ℕ} (ε : Fin m → Bool)
private theorem coeff_mem_of_forall_natCast_poly_sum_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Submodule ℂ M) (N : ℕ)
    (c : ℕ → M) (h : ∀ t : ℕ, ∑ j ∈ Finset.range (N + 1), ((t : ℂ) ^ j) • c j ∈ T)
    (k : ℕ) (hk : k < N + 1) : c k ∈ T := by
  let V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := Matrix.vandermonde (fun t : Fin (N + 1) => ((t : ℕ) : ℂ))
  have hV : IsUnit V.det := by
    refine isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr ?_)
    intro a b hab
    exact Fin.ext (Nat.cast_injective hab)
  have key : ∑ t : Fin (N + 1), (V⁻¹ ⟨k, hk⟩ t) • (∑ j ∈ Finset.range (N + 1), (((t : ℕ) : ℂ) ^ j) • c j) = c k := by
    have e : ∀ t : Fin (N + 1), (∑ j ∈ Finset.range (N + 1), (((t : ℕ) : ℂ) ^ j) • c j)
        = ∑ j : Fin (N + 1), V t j • c j := by
      intro t
      rw [← Fin.sum_univ_eq_sum_range (fun j => (((t : ℕ) : ℂ) ^ j) • c j)]
      simp [V, Matrix.vandermonde_apply]
    simp_rw [e, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have hm : ∀ j : Fin (N + 1), ∑ t : Fin (N + 1), V⁻¹ ⟨k, hk⟩ t * V t j = (V⁻¹ * V) ⟨k, hk⟩ j := by
      intro j
      rw [Matrix.mul_apply]
    simp_rw [hm, Matrix.nonsing_inv_mul _ hV, Matrix.one_apply, ite_smul, one_smul, zero_smul]
    simp
  rw [← key]
  exact Submodule.sum_mem _ (fun t _ => T.smul_mem _ (h t))
end PowSpanB
end PositivityTheory.Rg.Sw.FFTSteps
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
open PositivityTheory.Rg.Sw.FFTSteps.PowSpanB
variable {m n : ℕ} (ε : Fin m → Bool)
namespace PositivityTheory.Rg.Sw.FFTSteps.PowSpanB
theorem _root_.solution : ∀ l : List (PX m n), (∀ v ∈ l, v ∈ W ε) → ∀ w ∈ W ε, ∀ r : ℕ, l.prod * w ^ r ∈ S ε := by
  intro l
  induction l with
  | nil =>
    intro _ w hw r
    simpa using pow_mem ε hw r
  | cons v l ih =>
    intro hl w hw r
    have hv : v ∈ W ε := hl v (by simp)
    have ih' := ih (fun u hu => hl u (by simp [hu]))
    have h1 : ∀ t : ℕ, ∑ j ∈ Finset.range (r + 1 + 1), ((t : ℂ) ^ j) •
        (l.prod * (v ^ j * w ^ (r + 1 - j) * (((r + 1).choose j : ℕ) : PX m n))) ∈ S ε := by
      intro t
      have := ih' _ (natCast_smul_add_mem_W ε hw hv t) (r + 1)
      convert this using 1
      rw [add_pow, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [smul_pow, smul_mul_assoc, smul_mul_assoc, mul_smul_comm]
    have h2 := coeff_mem_of_forall_natCast_poly_sum_mem (S ε) (r + 1) _ h1 1 (by omega)
    have e : (v :: l).prod * w ^ r = ((r + 1 : ℕ) : ℂ)⁻¹ •
        (l.prod * (v ^ 1 * w ^ (r + 1 - 1) * (((r + 1).choose 1 : ℕ) : PX m n))) := by
      rw [Nat.choose_one_right, pow_one, Nat.add_sub_cancel, List.prod_cons]
      rw [show (((r + 1 : ℕ)) : PX m n) = ((r + 1 : ℕ) : ℂ) • (1 : PX m n) by
        rw [Nat.cast_smul_eq_nsmul, nsmul_one]]
      rw [mul_smul_comm, mul_smul_comm, smul_smul,
        inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero r)), one_smul]
      ring
    rw [e]
    exact (S ε).smul_mem _ h2
end PositivityTheory.Rg.Sw.FFTSteps.PowSpanB
