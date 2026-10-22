-- Prove2me | solution 1 for RegLearnGames.TotalRegret.lemma_20
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T08:48:22.198985+00:00
-- url     : https://prove2.me/submissions/2fc922b2-38cc-4d64-b6b0-a6a5b9b08719

import Definitions.Def_RegLearnGames_TotalRegret_Setting

set_option autoImplicit false
open Filter Topology
open RegLearnGames.TotalRegret

private lemma l1_nonnegative {d : ℕ} (x : Fin d → ℝ) : 0 ≤ l1 x :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

private lemma l1_sub_symm {d : ℕ} (x y : Fin d → ℝ) : l1 (x-y) = l1 (y-x) := by
  simp only [l1, Pi.sub_apply, abs_sub_comm]

private lemma l1_midpoint {d : ℕ} (x y : Fin d → ℝ) :
    l1 (x-(1/2:ℝ) • (x+y)) = (1/2:ℝ)*l1 (x-y) := by
  simp only [l1, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show x i - 1/2*(x i+y i) = 1/2*(x i-y i) by ring, abs_mul]
  norm_num

private lemma strong_min_gap {d : ℕ} (R : (Fin d → ℝ) → ℝ)
    (hR : IsOneStronglyConvexL1 R) (η : ℝ) (a y : Fin d → ℝ)
    (hy : y ∈ stdSimplex ℝ (Fin d))
    (hm : ∀ v ∈ stdSimplex ℝ (Fin d), R y - η*(y ⬝ᵥ a) ≤ R v - η*(v ⬝ᵥ a))
    (u : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d)) :
    l1 (y-u)^2/2 ≤ R u-η*(u ⬝ᵥ a) - (R y-η*(y ⬝ᵥ a)) := by
  let F : (Fin d → ℝ) → ℝ := fun v => R v-η*(v ⬝ᵥ a)
  have hd : ∀ n : ℕ, ∀ v ∈ stdSimplex ℝ (Fin d),
      (1-(1/2:ℝ)^n)/2*l1 (y-v)^2 ≤ F v-F y := by
    intro n
    induction n with
    | zero =>
      intro v hv
      simpa only [pow_zero, sub_self, zero_div, zero_mul] using sub_nonneg.mpr (hm v hv)
    | succ n ih =>
      intro v hv
      let m := (1/2:ℝ) • (y+v)
      have hmem : m ∈ stdSimplex ℝ (Fin d) := by
        simpa [m, midpoint_eq_smul_add, invOf_eq_inv, one_div] using (convex_stdSimplex ℝ (Fin d)).midpoint_mem hy hv
      have hc : F m ≤ (F y+F v)/2 - l1 (y-v)^2/8 := by
        have hs := hR.2 y hy v hv
        dsimp [F,m]
        simp only [smul_dotProduct, add_dotProduct, smul_eq_mul]
        linarith
      have hmid := ih m hmem
      have hscale : l1 (y-m) = (1/2:ℝ)*l1 (y-v) := l1_midpoint y v
      rw [hscale] at hmid
      rw [pow_succ]
      nlinarith
  have hp : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hl : Tendsto (fun n : ℕ => (1-(1/2:ℝ)^n)/2*l1 (y-u)^2) atTop
      (𝓝 (l1 (y-u)^2/2)) := by
    convert ((tendsto_const_nhds.sub hp).div_const 2).mul_const (l1 (y-u)^2) using 1 <;>
      first | rfl | (congr 1; ring)
  exact le_of_tendsto hl (Filter.Eventually.of_forall (fun n => hd n u hu))

private lemma dot_le_l1_norm {d : ℕ} (x y : Fin d → ℝ) :
    x ⬝ᵥ y ≤ l1 x*‖y‖ := by
  simp only [dotProduct, l1, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  calc
    x i*y i ≤ |x i*y i| := le_abs_self _
    _ = |x i| * |y i| := abs_mul _ _
    _ ≤ |x i| * ‖y‖ := mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y i) (abs_nonneg _)

private lemma stable_min {d : ℕ} (R : (Fin d → ℝ) → ℝ)
    (hR : IsOneStronglyConvexL1 R) (η : ℝ) (hη : 0 ≤ η)
    (a b y z : Fin d → ℝ) (hy : y ∈ stdSimplex ℝ (Fin d)) (hz : z ∈ stdSimplex ℝ (Fin d))
    (hmy : ∀ v ∈ stdSimplex ℝ (Fin d), R y-η*(y ⬝ᵥ a) ≤ R v-η*(v ⬝ᵥ a))
    (hmz : ∀ v ∈ stdSimplex ℝ (Fin d), R z-η*(z ⬝ᵥ b) ≤ R v-η*(v ⬝ᵥ b)) :
    l1 (y-z) ≤ η*‖a-b‖ := by
  have h1 := strong_min_gap R hR η a y hy hmy z hz
  have h2 := strong_min_gap R hR η b z hz hmz y hy
  rw [l1_sub_symm z y] at h2
  have hs : l1 (y-z)^2 ≤ η*((y-z) ⬝ᵥ (a-b)) := by
    simp only [sub_dotProduct, dotProduct_sub]
    linarith
  have hd := mul_le_mul_of_nonneg_left (dot_le_l1_norm (y-z) (a-b)) hη
  have hn := l1_nonnegative (y-z)
  by_cases he : l1 (y-z) = 0
  · rw [he]
    exact mul_nonneg hη (norm_nonneg _)
  · have hp : 0 < l1 (y-z) := lt_of_le_of_ne hn (Ne.symm he)
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith

private lemma max_to_min {d : ℕ} (R : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
    (a y : Fin d → ℝ)
    (hm : ∀ v ∈ stdSimplex ℝ (Fin d), v ⬝ᵥ a - R v/η ≤ y ⬝ᵥ a - R y/η) :
    ∀ v ∈ stdSimplex ℝ (Fin d), R y-η*(y ⬝ᵥ a) ≤ R v-η*(v ⬝ᵥ a) := by
  intro v hv
  have hs := mul_le_mul_of_nonneg_right (hm v hv) hη.le
  have he : ∀ r : ℝ, r/η*η = r := fun r => div_mul_cancel₀ r (ne_of_gt hη)
  simp only [sub_mul, he] at hs
  nlinarith

theorem solution {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
    (h𝓡 : IsOneStronglyConvexL1 𝓡)
    (M u w g : ℕ → Fin d → ℝ) (hw : IsOFTRL 𝓡 η M u w) (hg : IsLeader 𝓡 η u g) :
    ∀ t : ℕ, l1 (w t-g t) ≤ η*‖M t-u t‖ ∧ l1 (g t-w (t+1)) ≤ η*‖M (t+1)‖ := by
  intro t
  have hleader := max_to_min 𝓡 η hη _ _ (hg t).2
  have hwNext := hw.2 (t+1) (by omega)
  have hnext := max_to_min 𝓡 η hη _ _ hwNext.2
  have hsumNext : (∑ s ∈ Finset.Ico 1 (t+1), u s) = ∑ s ∈ Finset.Icc 1 t, u s := by
    rw [Finset.Ico_add_one_right_eq_Icc]
  have hsecond := stable_min 𝓡 h𝓡 η hη.le _ _ (g t) (w (t+1)) (hg t).1 hwNext.1 hleader hnext
  rw [hsumNext] at hsecond
  have hsimp : (∑ s ∈ Finset.Icc 1 t, u s) - ((∑ s ∈ Finset.Icc 1 t, u s)+M (t+1)) = -M (t+1) := by abel
  rw [hsimp, norm_neg] at hsecond
  refine ⟨?_, hsecond⟩
  by_cases ht : t=0
  · subst t
    have hm0 : ∀ v ∈ stdSimplex ℝ (Fin d), 𝓡 (w 0)-η*(w 0 ⬝ᵥ 0) ≤ 𝓡 v-η*(v ⬝ᵥ 0) := by
      simpa using hw.1.2
    have hg0 : ∀ v ∈ stdSimplex ℝ (Fin d), 𝓡 (g 0)-η*(g 0 ⬝ᵥ 0) ≤ 𝓡 v-η*(v ⬝ᵥ 0) := by
      simpa using hleader
    have hb := stable_min 𝓡 h𝓡 η hη.le 0 0 (w 0) (g 0) hw.1.1 (hg 0).1 hm0 hg0
    simp only [sub_self, norm_zero, mul_zero] at hb
    exact hb.trans (mul_nonneg hη.le (norm_nonneg _))
  · have ht1 : 1 ≤ t := by omega
    have hwt := hw.2 t ht1
    have hmin := max_to_min 𝓡 η hη _ _ hwt.2
    have hb := stable_min 𝓡 h𝓡 η hη.le _ _ (w t) (g t) hwt.1 (hg t).1 hmin hleader
    have hsum : (∑ s ∈ Finset.Icc 1 t, u s) = (∑ s ∈ Finset.Ico 1 t, u s)+u t := by
      simpa only [Finset.Ico_add_one_right_eq_Icc] using (Finset.sum_Ico_succ_top ht1 (f := u))
    rw [hsum] at hb
    have he : ((∑ s ∈ Finset.Ico 1 t, u s)+M t)-((∑ s ∈ Finset.Ico 1 t, u s)+u t) = M t-u t := by abel
    rwa [he] at hb

