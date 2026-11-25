-- Prove2me | solution 1 for PI.OddDualWeyl.evalDuality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:05:09.803897+00:00
-- url     : https://prove2.me/submissions/de75a432-09cb-4bf7-bbad-df120b8a4cab

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_EvalDuality
import Theorems.Thm_PI_OddDualWeyl_EvA_det_revCol
import Theorems.Thm_PI_OddDualWeyl_EvA_sgn_sq
import Theorems.Thm_PI_OddDualWeyl_EvA_arith

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open Red EvA
namespace PI.OddDualWeyl
theorem _root_.solution : EV := by
  intro K hK m e e' D M F F' h hrel hF' z hz
  have hdz : z.det ≠ 0 := hz.ne_zero
  set ρ : Fin (m + 1) × Fin (m + 1) → K := fun x => z x.1 x.2 with hρ
  have hrel0 : dualSub K (m + 1) F' = (genM K (m + 1)).det ^ M * F := hrel
  have hmap : (MvPolynomial.eval ρ).mapMatrix (genM K (m + 1)) = z := by
    ext i j
    simp [genM, hρ]
  have hgen : MvPolynomial.eval ρ (genM K (m + 1)).det = z.det := by
    rw [RingHom.map_det, hmap]
  have hadj : z.adjugate = z.det • z⁻¹ := by
    calc z.adjugate = z.adjugate * (z * z⁻¹) := by rw [Matrix.mul_nonsing_inv z hz, Matrix.mul_one]
      _ = (z.adjugate * z) * z⁻¹ := by rw [Matrix.mul_assoc]
      _ = z.det • z⁻¹ := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have hdinv : (z⁻¹).det = z.det⁻¹ := by
    have h1 : z.det * (z⁻¹).det = 1 := by
      rw [← Matrix.det_mul, Matrix.mul_nonsing_inv z hz, Matrix.det_one]
    exact eq_inv_of_mul_eq_one_right h1
  have hdetW : (revCol (z⁻¹)ᵀ).det = z.det⁻¹ * sgnK K m := by
    rw [PI.OddDualWeyl.EvA.det_revCol, Matrix.det_transpose, hdinv]
  have hentry : ∀ i j : Fin (m + 1),
      MvPolynomial.eval ρ (dualM K (m + 1) i j) = z.det * revCol (z⁻¹)ᵀ i j := by
    intro i j
    have h1 : MvPolynomial.eval ρ ((genM K (m + 1)).adjugate (Fin.rev j) i) =
        ((MvPolynomial.eval ρ).mapMatrix (genM K (m + 1))).adjugate (Fin.rev j) i := by
      rw [← RingHom.map_adjugate]
      first
      | rfl
      | simp [RingHom.mapMatrix_apply]
    simp only [dualM, Matrix.of_apply]
    rw [h1, hmap, hadj]
    simp [revCol]
  have hcomp : ∀ (g : Fin (m + 1) × Fin (m + 1) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)
      (p : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K),
      MvPolynomial.eval ρ (aeval g p) = MvPolynomial.eval (fun v => MvPolynomial.eval ρ (g v)) p := by
    intro g p
    first
    | (have hh : (MvPolynomial.eval ρ).comp (aeval g).toRingHom =
          MvPolynomial.eval (fun v => MvPolynomial.eval ρ (g v)) := by
         ext <;> simp [MvPolynomial.algebraMap_eq]
       exact RingHom.congr_fun hh p)
    | (induction p using MvPolynomial.induction_on <;> simp_all [MvPolynomial.algebraMap_eq])
  have hscale : ∀ (b : Fin (m + 1) × Fin (m + 1) → K) (c : K),
      MvPolynomial.eval (fun v => c * b v) F' = c ^ D * MvPolynomial.eval b F' := by
    intro b c
    rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdeg : ∑ i, d i = D := by
      have h1 := hF' (MvPolynomial.mem_support_iff.mp hd)
      first
      | (rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h1; simpa using h1)
      | simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using h1
      | (rw [← h1]; simp [Finsupp.weight_apply, Finsupp.sum_fintype])
    have hdeg' : ∑ i ∈ d.support, d i = D := by
      rw [← hdeg]
      exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)
    have hprod : ∏ i ∈ d.support, (c * b i) ^ d i = c ^ D * ∏ i ∈ d.support, b i ^ d i := by
      rw [← hdeg', ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => _root_.mul_pow _ _ _
    show MvPolynomial.coeff d F' * ∏ i ∈ d.support, (c * b i) ^ d i =
      c ^ D * (MvPolynomial.coeff d F' * ∏ i ∈ d.support, b i ^ d i)
    rw [hprod]
    ring
  have heval : MvPolynomial.eval ρ (dualSub K (m + 1) F') =
      z.det ^ D * MvPolynomial.eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) F' := by
    rw [show dualSub K (m + 1) F' =
        aeval (fun v : Fin (m + 1) × Fin (m + 1) => dualM K (m + 1) v.1 v.2) F' from rfl, hcomp]
    rw [show (fun v : Fin (m + 1) × Fin (m + 1) => MvPolynomial.eval ρ (dualM K (m + 1) v.1 v.2)) =
        fun v => z.det * revCol (z⁻¹)ᵀ v.1 v.2 from funext fun v => hentry v.1 v.2]
    exact hscale (fun x => revCol (z⁻¹)ᵀ x.1 x.2) z.det
  have hrel' : z.det ^ D * MvPolynomial.eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) F' =
      z.det ^ M * MvPolynomial.eval ρ F := by
    have h1 := congrArg (MvPolynomial.eval ρ) hrel0
    rw [heval, map_mul, map_pow, hgen] at h1
    exact h1
  rw [PI.OddDualWeyl.EvA.arith _ _ hdz (PI.OddDualWeyl.EvA.sgn_sq m) e e' D M h, ← hrel', hdetW,
    MvPolynomial.eval_mul, MvPolynomial.eval_C]
  have h4 : z.det⁻¹ ^ D * (z.det ^ D * MvPolynomial.eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) F') =
      MvPolynomial.eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) F' := by
    rw [← _root_.mul_assoc, ← _root_.mul_pow, inv_mul_cancel₀ hdz, _root_.one_pow, _root_.one_mul]
  rw [h4]
end PI.OddDualWeyl
