-- Prove2me | solution 1 for Real.exists_forall_norm_pow_mul_norm_iteratedFDeriv_mul_log_quadratic_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/71e0856d-d9b0-5488-b969-e4e739b08625

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Real_exists_forall_norm_pow_mul_norm_iteratedFDeriv_mul_log_quadratic_le

set_option autoImplicit false

namespace K2LogGerm

variable (α β : ℝ)

noncomputable def sq (p : ℝ × ℝ) : ℝ := α * p.1 ^ 2 + β * p.2 ^ 2

noncomputable def L (p : ℝ × ℝ) : ℝ := sq α β p * Real.log (sq α β p)

variable {α β}

lemma contDiff_sq : ContDiff ℝ (⊤ : ℕ∞) (sq α β) := by
  unfold sq; fun_prop

lemma sq_smul (t : ℝ) (p : ℝ × ℝ) : sq α β (t • p) = t ^ 2 * sq α β p := by
  simp only [sq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

lemma sq_pos (hα : 0 < α) (hβ : 0 < β) (p : ℝ × ℝ) (hp : p ≠ 0) : 0 < sq α β p := by
  unfold sq
  have h1 : 0 ≤ α * p.1 ^ 2 := by positivity
  have h2 : 0 ≤ β * p.2 ^ 2 := by positivity
  rcases lt_or_eq_of_le h1 with h1 | h1
  · linarith
  · rcases lt_or_eq_of_le h2 with h2 | h2
    · linarith
    · exfalso
      apply hp
      have hx : p.1 = 0 := by
        have : α * p.1 ^ 2 = 0 := h1.symm
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hα.ne'
        · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      have hy : p.2 = 0 := by
        have : β * p.2 ^ 2 = 0 := h2.symm
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hβ.ne'
        · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      exact Prod.ext hx hy

lemma isOpen_ne' : IsOpen {p : ℝ × ℝ | p ≠ 0} := isOpen_ne

lemma contDiffOn_L (hα : 0 < α) (hβ : 0 < β) :
    ContDiffOn ℝ (⊤ : ℕ∞) (L α β) {p : ℝ × ℝ | p ≠ 0} := by
  unfold L
  apply contDiff_sq.contDiffOn.mul
  apply contDiff_sq.contDiffOn.log
  intro p hp
  exact (sq_pos hα hβ p hp).ne'

lemma contDiffAt_L (hα : 0 < α) (hβ : 0 < β) {n : ℕ} (p : ℝ × ℝ) (hp : p ≠ 0) :
    ContDiffAt ℝ n (L α β) p :=
  ((contDiffOn_L hα hβ).of_le (by exact_mod_cast le_top)).contDiffAt (isOpen_ne'.mem_nhds hp)

lemma L_smul (hα : 0 < α) (hβ : 0 < β) (t : ℝ) (ht : 0 < t) (p : ℝ × ℝ) :
    L α β (t • p) = t ^ 2 * L α β p + (t ^ 2 * Real.log (t ^ 2)) * sq α β p := by
  unfold L
  rw [sq_smul]
  by_cases hp : p = 0
  · subst hp
    simp [sq]
  · have hs : sq α β p ≠ 0 := (sq_pos hα hβ p hp).ne'
    have ht2 : t ^ 2 ≠ 0 := by positivity
    rw [Real.log_mul ht2 hs]
    ring

noncomputable def scale (t : ℝ) (ht : t ≠ 0) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearEquiv.equivOfInverse (t • ContinuousLinearMap.id ℝ (ℝ × ℝ))
    (t⁻¹ • ContinuousLinearMap.id ℝ (ℝ × ℝ))
    (fun p => by
      simp only [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_id', Pi.smul_apply, id_eq,
        smul_smul, inv_mul_cancel₀ ht, one_smul])
    (fun p => by
      simp only [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_id', Pi.smul_apply, id_eq,
        smul_smul, mul_inv_cancel₀ ht, one_smul])

@[scoped simp] lemma scale_apply (t : ℝ) (ht : t ≠ 0) (p : ℝ × ℝ) : scale t ht p = t • p := rfl

lemma compContinuousLinearMap_scale {n : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × ℝ) ℝ)
    (t : ℝ) (ht : t ≠ 0) :
    M.compContinuousLinearMap (fun _ => ((scale t ht : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)))
      = (t ^ n) • M := by
  ext v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearEquiv.coe_coe,
    scale_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp

lemma iteratedFDeriv_L_smul (hα : 0 < α) (hβ : 0 < β) (n : ℕ) (t : ℝ) (ht : 0 < t) (ω : ℝ × ℝ)
    (hω : ω ≠ 0) :
    (t ^ n) • iteratedFDeriv ℝ n (L α β) (t • ω) =
      (t ^ 2) • iteratedFDeriv ℝ n (L α β) ω +
        (t ^ 2 * Real.log (t ^ 2)) • iteratedFDeriv ℝ n (sq α β) ω := by
  have ht0 : t ≠ 0 := ht.ne'

  have hcomp := (scale t ht0).iteratedFDerivWithin_comp_right (L α β) uniqueDiffOn_univ
    (x := ω) (Set.mem_univ _) n
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at hcomp
  rw [compContinuousLinearMap_scale] at hcomp

  have hfun : (L α β ∘ (scale t ht0)) =
      (t ^ 2) • L α β + (t ^ 2 * Real.log (t ^ 2)) • sq α β := by
    funext p
    simp only [Function.comp_apply, scale_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact L_smul hα hβ t ht p
  rw [hfun] at hcomp
  have hL : ContDiffAt ℝ n (L α β) ω := contDiffAt_L hα hβ ω hω
  have hs : ContDiffAt ℝ n (sq α β) ω := contDiff_sq.contDiffAt.of_le (by exact_mod_cast le_top)
  have hadd : iteratedFDeriv ℝ n ((t ^ 2) • L α β + (t ^ 2 * Real.log (t ^ 2)) • sq α β) ω =
      (t ^ 2) • iteratedFDeriv ℝ n (L α β) ω +
        (t ^ 2 * Real.log (t ^ 2)) • iteratedFDeriv ℝ n (sq α β) ω := by
    have hL' : ContDiffAt ℝ n ((t ^ 2) • L α β) ω := hL.const_smul (t ^ 2)
    have hs' : ContDiffAt ℝ n ((t ^ 2 * Real.log (t ^ 2)) • sq α β) ω :=
      hs.const_smul (t ^ 2 * Real.log (t ^ 2))
    rw [iteratedFDeriv_add_apply hL' hs', iteratedFDeriv_const_smul_apply hL,
      iteratedFDeriv_const_smul_apply hs]
  rw [hadd, scale_apply] at hcomp
  exact hcomp.symm

lemma exists_bound_sphere {F : Type*} [NormedAddCommGroup F] (f : ℝ × ℝ → F)
    (hf : ContinuousOn f {p : ℝ × ℝ | p ≠ 0}) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ω : ℝ × ℝ, ‖ω‖ = 1 → ‖f ω‖ ≤ C := by
  have hK : IsCompact (Metric.sphere (0 : ℝ × ℝ) 1) := isCompact_sphere _ _
  have hsub : Metric.sphere (0 : ℝ × ℝ) 1 ⊆ {p : ℝ × ℝ | p ≠ 0} := by
    intro ω hω
    simp only [Metric.mem_sphere, dist_zero_right] at hω
    intro h
    rw [h, norm_zero] at hω
    exact zero_ne_one hω
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hf.mono hsub)
  refine ⟨max C 0, le_max_right _ _, fun ω hω => ?_⟩
  have : ω ∈ Metric.sphere (0 : ℝ × ℝ) 1 := by simp [hω]
  exact (hC ω this).trans (le_max_left _ _)

lemma continuousOn_iteratedFDeriv_L (hα : 0 < α) (hβ : 0 < β) (n : ℕ) :
    ContinuousOn (iteratedFDeriv ℝ n (L α β)) {p : ℝ × ℝ | p ≠ 0} := by
  have h := (contDiffOn_L hα hβ).continuousOn_iteratedFDerivWithin (m := n)
    (by exact_mod_cast le_top) isOpen_ne'.uniqueDiffOn
  refine h.congr ?_
  intro p hp
  exact (iteratedFDerivWithin_of_isOpen n isOpen_ne' hp).symm

lemma continuousOn_iteratedFDeriv_sq (n : ℕ) :
    ContinuousOn (iteratedFDeriv ℝ n (sq α β)) {p : ℝ × ℝ | p ≠ 0} :=
  (contDiff_sq.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).continuousOn

theorem main (hα : 0 < α) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, p ≠ 0 →
      ‖p‖ ^ n * ‖iteratedFDeriv ℝ n (L α β) p‖ ≤ C * ‖p‖ ^ 2 * (1 + |Real.log ‖p‖|) := by

  have hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ω : ℝ × ℝ, ‖ω‖ = 1 →
      ‖iteratedFDeriv ℝ n (L α β) ω‖ + 2 * ‖iteratedFDeriv ℝ n (sq α β) ω‖ ≤ C := by
    intro n
    obtain ⟨C₁, hC₁, h₁⟩ := exists_bound_sphere _ (continuousOn_iteratedFDeriv_L hα hβ n)
    obtain ⟨C₂, hC₂, h₂⟩ := exists_bound_sphere _ (continuousOn_iteratedFDeriv_sq (α := α) (β := β) n)
    refine ⟨C₁ + 2 * C₂, by positivity, fun ω hω => ?_⟩
    have := h₁ ω hω
    have := h₂ ω hω
    linarith
  choose Cn hCn0 hCn using hb
  refine ⟨∑ n ∈ Finset.range 5, Cn n, Finset.sum_nonneg (fun n _ => hCn0 n), ?_⟩
  intro n hn p hp
  have hle : Cn n ≤ ∑ k ∈ Finset.range 5, Cn k :=
    Finset.single_le_sum (fun k _ => hCn0 k) (Finset.mem_range.2 (by omega))
  set t : ℝ := ‖p‖ with ht_def
  have ht : 0 < t := norm_pos_iff.2 hp
  set ω : ℝ × ℝ := t⁻¹ • p with hω_def
  have hω1 : ‖ω‖ = 1 := by
    rw [hω_def, norm_smul, norm_inv, norm_norm, ← ht_def, inv_mul_cancel₀ ht.ne']
  have hω0 : ω ≠ 0 := by
    intro h; rw [h, norm_zero] at hω1; exact zero_ne_one hω1
  have hp_eq : t • ω = p := by
    rw [hω_def, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have key := iteratedFDeriv_L_smul hα hβ n t ht ω hω0
  rw [hp_eq] at key
  have hnorm : t ^ n * ‖iteratedFDeriv ℝ n (L α β) p‖ =
      ‖(t ^ 2) • iteratedFDeriv ℝ n (L α β) ω +
        (t ^ 2 * Real.log (t ^ 2)) • iteratedFDeriv ℝ n (sq α β) ω‖ := by
    rw [← key, norm_smul, Real.norm_of_nonneg (pow_nonneg ht.le n)]
  rw [hnorm]
  have hlog2 : Real.log (t ^ 2) = 2 * Real.log t := by
    rw [Real.log_pow]; norm_num
  calc ‖(t ^ 2) • iteratedFDeriv ℝ n (L α β) ω +
        (t ^ 2 * Real.log (t ^ 2)) • iteratedFDeriv ℝ n (sq α β) ω‖
      ≤ ‖(t ^ 2) • iteratedFDeriv ℝ n (L α β) ω‖ +
          ‖(t ^ 2 * Real.log (t ^ 2)) • iteratedFDeriv ℝ n (sq α β) ω‖ := norm_add_le _ _
    _ = t ^ 2 * ‖iteratedFDeriv ℝ n (L α β) ω‖ +
          t ^ 2 * |Real.log t| * (2 * ‖iteratedFDeriv ℝ n (sq α β) ω‖) := by
        rw [norm_smul, norm_smul, hlog2, Real.norm_of_nonneg (pow_nonneg ht.le 2), norm_mul,
          Real.norm_of_nonneg (pow_nonneg ht.le 2), norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_two]
        ring
    _ ≤ t ^ 2 * (1 + |Real.log t|) * ‖iteratedFDeriv ℝ n (L α β) ω‖ +
          t ^ 2 * (1 + |Real.log t|) * (2 * ‖iteratedFDeriv ℝ n (sq α β) ω‖) := by
        have h1 : 0 ≤ ‖iteratedFDeriv ℝ n (L α β) ω‖ := norm_nonneg _
        have h2 : 0 ≤ 2 * ‖iteratedFDeriv ℝ n (sq α β) ω‖ := by positivity
        have h3 : 0 ≤ |Real.log t| := abs_nonneg _
        have h4 : 0 ≤ t ^ 2 := pow_nonneg ht.le 2
        gcongr
        · nlinarith
        · nlinarith
    _ = t ^ 2 * (1 + |Real.log t|) *
          (‖iteratedFDeriv ℝ n (L α β) ω‖ + 2 * ‖iteratedFDeriv ℝ n (sq α β) ω‖) := by ring
    _ ≤ t ^ 2 * (1 + |Real.log t|) * Cn n := by
        have h4 : 0 ≤ t ^ 2 * (1 + |Real.log t|) := by positivity
        exact mul_le_mul_of_nonneg_left (hCn n ω hω1) h4
    _ ≤ t ^ 2 * (1 + |Real.log t|) * ∑ k ∈ Finset.range 5, Cn k := by
        have h4 : 0 ≤ t ^ 2 * (1 + |Real.log t|) := by positivity
        exact mul_le_mul_of_nonneg_left hle h4
    _ = (∑ k ∈ Finset.range 5, Cn k) * t ^ 2 * (1 + |Real.log t|) := by ring

end K2LogGerm
p2m_reactivate "P2MW.S_Real_exists_forall_norm_pow_mul_norm_iteratedFDeriv_mul_log_quadratic_le.K2LogGerm"

open K2LogGerm in
theorem solution
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × ℝ => (α * p.1 ^ 2 + β * p.2 ^ 2) * Real.log (α * p.1 ^ 2 + β * p.2 ^ 2))
        {p : ℝ × ℝ | p ≠ 0} ∧
      ∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, p ≠ 0 →
        ‖p‖ ^ n *
            ‖iteratedFDeriv ℝ n
                (fun p : ℝ × ℝ => (α * p.1 ^ 2 + β * p.2 ^ 2) * Real.log (α * p.1 ^ 2 + β * p.2 ^ 2))
                p‖ ≤
          C * ‖p‖ ^ 2 * (1 + |Real.log ‖p‖|) := by
  obtain ⟨C, hC0, hC⟩ := main hα hβ
  have hL : (fun p : ℝ × ℝ => (α * p.1 ^ 2 + β * p.2 ^ 2) * Real.log (α * p.1 ^ 2 + β * p.2 ^ 2)) =
      L α β := by
    funext p; rfl
  refine ⟨C, hC0, ?_, ?_⟩
  · rw [hL]; exact contDiffOn_L hα hβ
  · rw [hL]; exact hC

end S_Real_exists_forall_norm_pow_mul_norm_iteratedFDeriv_mul_log_quadratic_le
end P2MW
export P2MW.S_Real_exists_forall_norm_pow_mul_norm_iteratedFDeriv_mul_log_quadratic_le (solution)
