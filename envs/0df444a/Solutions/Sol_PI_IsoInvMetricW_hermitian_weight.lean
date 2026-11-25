-- Prove2me | solution 1 for PI.IsoInvMetricW.hermitian_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:12:28.654716+00:00
-- url     : https://prove2.me/submissions/4c9f23d3-1d84-4836-852b-201c9911cd0c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_PolyEqZeroOfCircle
import Theorems.Thm_PI_IsoInvMetricW_poly_eq_zero_of_circle
import Theorems.Thm_PI_IsoInvMetricW_star_mul_self_of_norm
import Theorems.Thm_PI_IsoInvMetricW_wt_lt
import Theorems.Thm_PI_IsoInvMetricW_vnuMap_torus
import Theorems.Thm_PI_IsoInvMetricW_torus_unitary
import Theorems.Thm_PI_IsoInvMetricW_unitVector_val_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical Finset PI.IsoInvMetric Polynomial
open PI PI.IsoInvMetricW
namespace PI.IsoInvMetricW
theorem _root_.solution : HW := by
  intro Lt _ _ N nu ip hip ψ hψ
  by_cases hle : ∀ z, (nu z).colLen 0 ≤ N
  · set J0' := J0 nu hle with hJ0'
    set m0 := wt J0' with hm0
    have hu0 : u0 N nu = fun J => if J = J0' then 1 else 0 := by
      funext J; exact unitVector_val_eq nu hle J
    have hu0V : u0 N nu ∈ Vnu N nu := Submodule.subset_span ⟨_, rfl⟩

    set a : ColChoice N nu → ℂ := fun J => ip (u0 N nu) (fun j => if J = j then 1 else 0) with ha
    have hexp : ∀ φ : LaC N nu, ip (u0 N nu) φ = ∑ J, φ J * a J := by
      intro φ
      rw [LinearMap.pi_apply_eq_sum_univ (ip (u0 N nu)) φ]
      rfl
    have hnorm : ip (u0 N nu) (u0 N nu) = 1 := (hip (fun _ => 1) (fun _ => one_mem _)).2
    have haJ0 : a J0' = 1 := by
      have e : (fun j => if J0' = j then (1:ℂ) else 0) = u0 N nu := by
        rw [hu0]; funext j; simp only [eq_comm]
      show ip (u0 N nu) (fun j => if J0' = j then 1 else 0) = 1
      rw [e, hnorm]

    have htor : ∀ z : ℂ, ‖z‖ = 1 →
        ∑ J, z ^ wt J * (ψ J * a J) = z ^ m0 * ∑ J, ψ J * a J := by
      intro z hz
      have hk := (hip (fun s => Matrix.diagonal (dz z s)) (fun s => torus_unitary hz s)).1
        (u0 N nu) hu0V ψ hψ
      have hρu0 : VnuMap nu (fun s => Matrix.diagonal (dz z s)) (u0 N nu) = z ^ m0 • u0 N nu := by
        funext I
        rw [vnuMap_torus, hu0]
        by_cases hI : I = J0'
        · subst hI; simp [hm0]
        · simp [hI]
      rw [hρu0, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hexp, hexp] at hk
      have hzz : z ^ m0 * starRingEnd ℂ (z ^ m0) = 1 := by
        rw [mul_comm]; exact star_mul_self_of_norm (by rw [norm_pow, hz, one_pow])
      calc ∑ J, z ^ wt J * (ψ J * a J)
          = z ^ m0 * (starRingEnd ℂ (z ^ m0) • ∑ J, VnuMap nu (fun s => Matrix.diagonal (dz z s)) ψ J * a J) := by
            rw [smul_eq_mul, ← mul_assoc, hzz, one_mul]
            refine Finset.sum_congr rfl fun J _ => ?_
            rw [vnuMap_torus]; ring
        _ = z ^ m0 * ∑ J, ψ J * a J := by rw [hk]

    set S := ∑ J, ψ J * a J with hS
    set P : ℂ[X] := (∑ J, C (ψ J * a J) * X ^ wt J) - C S * X ^ m0 with hP
    have hP0 : P = 0 := by
      apply poly_eq_zero_of_circle
      intro z hz
      rw [hP, eval_sub, eval_finsetSum]
      simp only [eval_mul, eval_C, eval_pow, eval_X]
      rw [sub_eq_zero, mul_comm S, ← htor z hz]
      exact Finset.sum_congr rfl fun J _ => by ring
    have hc := congrArg (fun Q : ℂ[X] => Q.coeff m0) hP0
    simp only [hP, coeff_sub, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero, if_true] at hc
    rw [Finset.sum_eq_single J0' (fun J _ hJ => by
        have := wt_lt hle J hJ
        rw [if_neg (by rw [← hm0] at this; omega)]) (fun h => absurd (Finset.mem_univ _) h)] at hc
    rw [if_pos rfl, haJ0, mul_one, sub_eq_zero] at hc
    rw [hexp, ← hS, ← hc]
    simp only [ipl, hu0]
    rw [Finset.sum_eq_single J0' (fun J _ hJ => by simp [hJ]) (fun h => absurd (Finset.mem_univ _) h)]
    simp
  · push Not at hle
    obtain ⟨z, hz⟩ := hle
    have hrow : 0 < (nu z).rowLen 0 := by
      have hmem : ((0 : ℕ), (0 : ℕ)) ∈ nu z := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
      exact YoungDiagram.mem_iff_lt_rowLen.mp hmem
    have : IsEmpty (ColChoice N nu) := ⟨fun J => by
      have e := J z ⟨0, hrow⟩
      have := Fintype.card_le_of_injective e e.injective
      simp only [Fintype.card_fin] at this
      omega⟩
    have hz0 : u0 N nu = 0 := funext fun J => isEmptyElim J
    rw [hz0]
    simp [ipl]
end PI.IsoInvMetricW
