-- Prove2me | solution 1 for PartialDeriv.contDiff_succ_and_norm_iteratedFDeriv_le_of_hasDerivAt_single
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e4076368-9fe3-5444-8b3d-3ee4e9b9a99d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PartialDeriv_contDiff_succ_and_norm_iteratedFDeriv_le_of_hasDerivAt_single

set_option autoImplicit false
set_option linter.unusedVariables false

open Filter Topology Asymptotics

noncomputable section

namespace KcPartialDeriv

abbrev ev {n : ℕ} (j : Fin n) : Fin n → ℝ := Pi.single j 1

def trunc {n : ℕ} (h : Fin n → ℝ) (k : ℕ) : Fin n → ℝ := fun i => if (i : ℕ) < k then h i else 0

theorem trunc_zero {n : ℕ} (h : Fin n → ℝ) : trunc h 0 = 0 := by
  funext i
  simp [trunc]

theorem trunc_self {n : ℕ} (h : Fin n → ℝ) : trunc h n = h := by
  funext i
  simp [trunc, i.isLt]

theorem trunc_succ {n : ℕ} (h : Fin n → ℝ) (j : Fin n) : trunc h ((j : ℕ) + 1) = trunc h j + h j • ev j := by
  funext i
  simp only [trunc, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    simp
  · have hne : (i : ℕ) ≠ (j : ℕ) := fun h' => hij (Fin.ext h')
    by_cases hlt : (i : ℕ) < (j : ℕ)
    · rw [if_pos (by omega), if_pos hlt, if_neg hij, mul_zero, add_zero]
    · rw [if_neg (by omega), if_neg hlt, if_neg hij, mul_zero, add_zero]

theorem norm_trunc_add_smul_le {n : ℕ} (h : Fin n → ℝ) (j : Fin n) (s : ℝ) (hs : |s| ≤ |h j|) :
    ‖trunc h j + s • ev j‖ ≤ ‖h‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg h)]
  intro i
  simp only [trunc, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, Real.norm_eq_abs]
  have hi : |h i| ≤ ‖h‖ := by
    have := norm_le_pi_norm h i
    rwa [Real.norm_eq_abs] at this
  have hj : |h j| ≤ ‖h‖ := by
    have := norm_le_pi_norm h j
    rwa [Real.norm_eq_abs] at this
  by_cases hij : i = j
  · subst hij
    simp only [lt_self_iff_false, if_false, if_true, zero_add, mul_one]
    exact hs.trans hj
  · rw [if_neg hij, mul_zero, add_zero]
    split_ifs
    · exact hi
    · rw [abs_zero]; exact norm_nonneg h

section Line

variable {n : ℕ} {f : (Fin n → ℝ) → ℂ} {g : Fin n → (Fin n → ℝ) → ℂ}

theorem hasDerivAt_line
    (hfg : ∀ (t : Fin n → ℝ) (j : Fin n),
      HasDerivAt (fun s : ℝ => f (t + s • (Pi.single j (1 : ℝ) : Fin n → ℝ))) (g j t) 0)
    (p : Fin n → ℝ) (j : Fin n) (s : ℝ) :
    HasDerivAt (fun s' : ℝ => f (p + s' • ev j)) (g j (p + s • ev j)) s := by
  have h0 : HasDerivAt (fun τ : ℝ => f (p + s • ev j + τ • ev j)) (g j (p + s • ev j)) 0 := hfg (p + s • ev j) j
  have hfun : (fun s' : ℝ => f (p + s' • ev j)) = fun s' => f (p + s • ev j + (s' - s) • ev j) := by
    funext s'
    congr 1
    rw [add_assoc, ← add_smul, add_sub_cancel]
  rw [hfun]
  have h0' : HasDerivAt (fun τ : ℝ => f (p + s • ev j + τ • ev j)) (g j (p + s • ev j)) (s - s) := by
    rw [sub_self]; exact h0
  exact h0'.comp_sub_const s s

theorem norm_sub_sub_smul_le
    (hfg : ∀ (t : Fin n → ℝ) (j : Fin n),
      HasDerivAt (fun s : ℝ => f (t + s • (Pi.single j (1 : ℝ) : Fin n → ℝ))) (g j t) 0)
    (t h : Fin n → ℝ) (j : Fin n) {C : ℝ}
    (hC : ∀ s ∈ Set.uIcc (0 : ℝ) (h j), ‖g j (t + trunc h j + s • ev j) - g j t‖ ≤ C) :
    ‖f (t + trunc h ((j : ℕ) + 1)) - f (t + trunc h j) - h j • g j t‖ ≤ C * |h j| := by
  set φ : ℝ → ℂ := fun s => f (t + trunc h j + s • ev j) - s • g j t with hφ
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) (h j),
      HasDerivWithinAt φ (g j (t + trunc h j + s • ev j) - g j t) (Set.uIcc (0 : ℝ) (h j)) s := by
    intro s _
    have h1 := hasDerivAt_line hfg (t + trunc h j) j s
    have h2 : HasDerivAt (fun s : ℝ => s • g j t) (g j t) s := by
      simpa using (hasDerivAt_id s).smul_const (g j t)
    exact (h1.sub h2).hasDerivWithinAt
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hC (convex_uIcc (0 : ℝ) (h j))
    Set.left_mem_uIcc Set.right_mem_uIcc
  have hφeq : φ (h j) - φ 0 = f (t + trunc h ((j : ℕ) + 1)) - f (t + trunc h j) - h j • g j t := by
    simp only [hφ, zero_smul, add_zero, sub_zero, trunc_succ, add_assoc]
    abel
  rw [← hφeq]
  simpa [Real.norm_eq_abs] using hmv

theorem hasFDerivAt_of_partials (hgc : ∀ j, Continuous (g j))
    (hfg : ∀ (t : Fin n → ℝ) (j : Fin n),
      HasDerivAt (fun s : ℝ => f (t + s • (Pi.single j (1 : ℝ) : Fin n → ℝ))) (g j t) 0)
    (t : Fin n → ℝ) :
    HasFDerivAt f (∑ j, (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (g j t)) t := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc

  have hG : Continuous (fun p : Fin n → ℝ => fun j : Fin n => g j p) := continuous_pi fun j => hgc j
  have hc' : 0 < c / ((n : ℝ) + 1) := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuous_iff.mp hG t (c / ((n : ℝ) + 1)) hc'
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun h hh => ?_⟩
  rw [dist_zero_right] at hh

  have hnear : ∀ (j : Fin n) (s : ℝ), s ∈ Set.uIcc (0 : ℝ) (h j) →
      ‖g j (t + trunc h j + s • ev j) - g j t‖ ≤ c / ((n : ℝ) + 1) := by
    intro j s hs
    have hs' : |s| ≤ |h j| := by simpa using Set.abs_sub_left_of_mem_uIcc hs
    have hd : dist (t + trunc h j + s • ev j) t < δ := by
      rw [dist_eq_norm, add_assoc, add_sub_cancel_left]
      exact (norm_trunc_add_smul_le h j s hs').trans_lt hh
    have hlt := hδ' _ hd
    rw [dist_eq_norm] at hlt
    have hcomp := norm_le_pi_norm ((fun j' : Fin n => g j' (t + trunc h j + s • ev j)) - fun j' => g j' t) j
    simp only [Pi.sub_apply] at hcomp
    exact hcomp.trans hlt.le

  have htel : f (t + h) - f t = ∑ j : Fin n, (f (t + trunc h ((j : ℕ) + 1)) - f (t + trunc h j)) := by
    rw [Fin.sum_univ_eq_sum_range (fun k => f (t + trunc h (k + 1)) - f (t + trunc h k)) n,
      Finset.sum_range_sub (fun k => f (t + trunc h k)) n, trunc_self, trunc_zero, add_zero]
  have hL : (∑ j, (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (g j t)) h =
      ∑ j, h j • g j t := by
    simp [ContinuousLinearMap.smulRight_apply]
  rw [hL, htel, ← Finset.sum_sub_distrib]
  have hn : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  calc ‖∑ j : Fin n, (f (t + trunc h ((j : ℕ) + 1)) - f (t + trunc h j) - h j • g j t)‖
      ≤ ∑ j : Fin n, ‖f (t + trunc h ((j : ℕ) + 1)) - f (t + trunc h j) - h j • g j t‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin n, c / ((n : ℝ) + 1) * |h j| :=
        Finset.sum_le_sum fun j _ => norm_sub_sub_smul_le hfg t h j (hnear j)
    _ ≤ ∑ j : Fin n, c / ((n : ℝ) + 1) * ‖h‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hj : |h j| ≤ ‖h‖ := by
          have := norm_le_pi_norm h j
          rwa [Real.norm_eq_abs] at this
        exact mul_le_mul_of_nonneg_left hj hc'.le
    _ = c * ((n : ℝ) / ((n : ℝ) + 1)) * ‖h‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ c * 1 * ‖h‖ := by gcongr
    _ = c * ‖h‖ := by ring

end Line

section ClassOfDerivative

variable {n : ℕ}

def A (j : Fin n) : ℂ →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℂ) :=
  ContinuousLinearMap.smulRightL ℝ (Fin n → ℝ) ℂ (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)

theorem A_apply (j : Fin n) (c : ℂ) :
    A j c = (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight c :=
  rfl

theorem norm_A_le (j : Fin n) : ‖A j‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun c => ?_
  rw [one_mul, A_apply]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c) fun v => ?_
  rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg c)

variable {g : Fin n → (Fin n → ℝ) → ℂ}

theorem sum_smulRight_eq (t : Fin n → ℝ) :
    (∑ j, (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (g j t)) = ∑ j, A j (g j t) :=
  rfl

theorem contDiff_sum_A {m : ℕ} (hg : ∀ j, ContDiff ℝ m (g j)) :
    ContDiff ℝ m (fun t => ∑ j, (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (g j t)) := by
  simp only [sum_smulRight_eq]
  exact ContDiff.sum fun j _ => (A j).contDiff.comp (hg j)

theorem norm_iteratedFDeriv_sum_A_le {m : ℕ} (hg : ∀ j, ContDiff ℝ m (g j)) {k : ℕ} (hk : k ≤ m)
    (t : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ k (fun t => ∑ j, A j (g j t)) t‖ ≤ ∑ j, ‖iteratedFDeriv ℝ k (g j) t‖ := by
  have hk' : (k : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by exact_mod_cast hk
  have hsum : iteratedFDeriv ℝ k (fun t => ∑ j, A j (g j t)) t = ∑ j, iteratedFDeriv ℝ k (fun t => A j (g j t)) t := by
    have := iteratedFDeriv_sum (𝕜 := ℝ) (u := (Finset.univ : Finset (Fin n))) (i := k)
      (f := fun j t => A j (g j t)) (fun j _ => ((A j).contDiff.comp (hg j)).of_le hk')
    rw [this]
    exact Finset.sum_apply (M := fun _ : Fin n → ℝ =>
      ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin n → ℝ) ((Fin n → ℝ) →L[ℝ] ℂ)) t Finset.univ
      (fun j => iteratedFDeriv ℝ k (fun t => A j (g j t)))
  rw [hsum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hcomp : iteratedFDeriv ℝ k (fun t => A j (g j t)) t =
      (A j).compContinuousMultilinearMap (iteratedFDeriv ℝ k (g j) t) :=
    (A j).iteratedFDeriv_comp_left (hg j).contDiffAt hk'
  rw [hcomp]
  refine ((A j).norm_compContinuousMultilinearMap_le _).trans ?_
  have := norm_A_le j
  have h0 := norm_nonneg (iteratedFDeriv ℝ k (g j) t)
  nlinarith

end ClassOfDerivative

end KcPartialDeriv

end

open KcPartialDeriv in
theorem solution
    (n m : ℕ) (f : (Fin n → ℝ) → ℂ) (g : Fin n → (Fin n → ℝ) → ℂ)
    (hg : ∀ j, ContDiff ℝ m (g j))
    (hfg : ∀ (t : Fin n → ℝ) (j : Fin n),
      HasDerivAt (fun s : ℝ => f (t + s • (Pi.single j (1 : ℝ) : Fin n → ℝ))) (g j t) 0) :
    ContDiff ℝ (m + 1) f ∧
      (∀ t, HasFDerivAt f (∑ j, (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (g j t)) t) ∧
      ∀ k, k ≤ m → ∀ t, ‖iteratedFDeriv ℝ (k + 1) f t‖ ≤ ∑ j, ‖iteratedFDeriv ℝ k (g j) t‖ := by
  have hderiv : ∀ t, HasFDerivAt f
      (∑ j, (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (g j t)) t :=
    hasFDerivAt_of_partials (fun j => (hg j).continuous) hfg
  refine ⟨contDiff_succ_iff_hasFDerivAt.mpr ⟨_, contDiff_sum_A hg, hderiv⟩, hderiv, ?_⟩
  intro k hk t
  have hfd : fderiv ℝ f = fun t => ∑ j, A j (g j t) :=
    funext fun t => (hderiv t).fderiv
  rw [← norm_iteratedFDeriv_fderiv, hfd]
  exact norm_iteratedFDeriv_sum_A_le hg hk t

end S_PartialDeriv_contDiff_succ_and_norm_iteratedFDeriv_le_of_hasDerivAt_single
end P2MW
export P2MW.S_PartialDeriv_contDiff_succ_and_norm_iteratedFDeriv_le_of_hasDerivAt_single (solution)
