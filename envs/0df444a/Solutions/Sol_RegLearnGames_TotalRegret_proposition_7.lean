-- Prove2me | solution 1 for RegLearnGames.TotalRegret.proposition_7
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T08:52:01.964181+00:00
-- url     : https://prove2.me/submissions/d3df8f6e-3ec8-4c8e-9f29-c5068c1f0cb6

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


private lemma sum_backward_diff (a : ℕ → ℝ) (T : ℕ) :
    (∑ t ∈ Finset.Icc 1 T, (a t-a (t-1))) = a T-a 0 := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ T+1), ih]
    simp only [Nat.add_sub_cancel]
    ring

private theorem regret_bound {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η R : ℝ) (hη : 0 < η)
    (h𝓡 : IsOneStronglyConvexL1 𝓡)
    (hR : ∀ f ∈ stdSimplex ℝ (Fin d), ∀ g ∈ stdSimplex ℝ (Fin d), 𝓡 f - 𝓡 g ≤ R)
    (M u w g : ℕ → Fin d → ℝ) (hw : IsOFTRL 𝓡 η M u w) (hg : IsLeader 𝓡 η u g)
    (T : ℕ) (wstar : Fin d → ℝ) (hwstar : wstar ∈ stdSimplex ℝ (Fin d)) :
    ∑ t ∈ Finset.Icc 1 T, (wstar - w t) ⬝ᵥ u t ≤
      R / η + ∑ t ∈ Finset.Icc 1 T, ‖u t - M t‖ * l1 (w t - g t)
        - 1 / (2 * η) * ∑ t ∈ Finset.Icc 1 T, (l1 (w t - g t) ^ 2 + l1 (w t - g (t - 1)) ^ 2)  := by
  let U : ℕ → Fin d → ℝ := fun t => ∑ s ∈ Finset.Icc 1 t, u s
  let P : ℕ → ℝ := fun t => 𝓡 (g t)-η*(g t ⬝ᵥ U t)
  let E : ℕ → ℝ := fun t => ‖u t-M t‖*l1 (w t-g t)
  let Q : ℕ → ℝ := fun t => l1 (w t-g t)^2+l1 (w t-g (t-1))^2
  have hlead (t : ℕ) := max_to_min 𝓡 η hη _ _ (hg t).2
  have hpre (t : ℕ) (ht : 1 ≤ t) : (∑ s ∈ Finset.Ico 1 t, u s) = U (t-1) := by
    dsimp [U]
    rw [← Finset.Ico_add_one_right_eq_Icc, Nat.sub_add_cancel ht]
  have hsucc (t : ℕ) (ht : 1 ≤ t) : U t = U (t-1)+u t := by
    rw [← hpre t ht]
    dsimp [U]
    simpa only [Finset.Ico_add_one_right_eq_Icc] using (Finset.sum_Ico_succ_top ht (f := u))
  have hstep (t : ℕ) (ht : 1 ≤ t) :
      η*((wstar-w t) ⬝ᵥ u t) ≤ η*(wstar ⬝ᵥ u t)+(P t-P (t-1))+η*E t-Q t/2 := by
    have hwt := hw.2 t ht
    have hmw := max_to_min 𝓡 η hη _ _ hwt.2
    rw [hpre t ht] at hmw
    have h1 := strong_min_gap 𝓡 h𝓡 η (U (t-1)) (g (t-1)) (hg (t-1)).1
      (hlead (t-1)) (w t) hwt.1
    have h2 := strong_min_gap 𝓡 h𝓡 η (U (t-1)+M t) (w t) hwt.1 hmw (g t) (hg t).1
    rw [l1_sub_symm (g (t-1)) (w t)] at h1
    have he := mul_le_mul_of_nonneg_left (dot_le_l1_norm (g t-w t) (u t-M t)) hη.le
    rw [l1_sub_symm (g t) (w t)] at he
    dsimp [P,E,Q]
    rw [hsucc t ht]
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_add] at h1 h2 he ⊢
    nlinarith
  have hs := Finset.sum_le_sum (fun t (ht : t ∈ Finset.Icc 1 T) => hstep t (Finset.mem_Icc.mp ht).1)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_div] at hs
  have htel : (∑ t ∈ Finset.Icc 1 T, P t)-(∑ t ∈ Finset.Icc 1 T, P (t-1)) = P T-P 0 := by
    rw [← Finset.sum_sub_distrib, sum_backward_diff]
  rw [htel] at hs
  have hdot : (∑ t ∈ Finset.Icc 1 T, wstar ⬝ᵥ u t) = wstar ⬝ᵥ U T := by
    exact (dotProduct_sum wstar (Finset.Icc 1 T) u).symm
  rw [hdot] at hs
  have hpot : η*(wstar ⬝ᵥ U T)+P T-P 0 ≤ R := by
    have hm := hlead T wstar hwstar
    have hr := hR wstar hwstar (g 0) (hg 0).1
    dsimp [P,U]
    simp only [Finset.Icc_eq_empty_of_lt (show (0:ℕ)<1 by omega), Finset.sum_empty,
      dotProduct_zero, mul_zero, sub_zero]
    linarith
  have hbound : η*(∑ t ∈ Finset.Icc 1 T, (wstar-w t) ⬝ᵥ u t) ≤
      R+η*(∑ t ∈ Finset.Icc 1 T, E t)-(∑ t ∈ Finset.Icc 1 T,Q t)/2 := by
    linarith
  change (∑ t ∈ Finset.Icc 1 T, (wstar-w t) ⬝ᵥ u t) ≤
    R/η+(∑ t ∈ Finset.Icc 1 T,E t)-1/(2*η)*(∑ t ∈ Finset.Icc 1 T,Q t)
  apply (mul_le_mul_iff_right₀ hη).mp
  have hη0 : η ≠ 0 := ne_of_gt hη
  field_simp
  nlinarith


private theorem stability_bound {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
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


private lemma l1_triangle_sub {d : ℕ} (x y z : Fin d → ℝ) :
    l1 (x-y) ≤ l1 (x-z)+l1 (y-z) := by
  simp only [l1, Pi.sub_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [abs_sub_comm (y i) (z i)] using abs_sub_le (x i) (z i) (y i)

theorem solution {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η R : ℝ) (hη : 0 < η)
    (h𝓡 : IsOneStronglyConvexL1 𝓡)
    (hR : ∀ f ∈ stdSimplex ℝ (Fin d), ∀ g ∈ stdSimplex ℝ (Fin d), 𝓡 f - 𝓡 g ≤ R)
    (u w : ℕ → Fin d → ℝ) (hw : IsOFTRL 𝓡 η (fun T => u (T - 1)) u w)
    (T : ℕ) (wstar : Fin d → ℝ) (hwstar : wstar ∈ stdSimplex ℝ (Fin d)) :
    ∑ t ∈ Finset.Icc 1 T, (wstar - w t) ⬝ᵥ u t ≤
      R / η + η * ∑ t ∈ Finset.Icc 1 T, ‖u t - u (t - 1)‖ ^ 2
        - 1 / (4 * η) * ∑ t ∈ Finset.Icc 1 T, l1 (w t - w (t - 1)) ^ 2  := by
  classical
  have hex (t : ℕ) : ∃ y ∈ stdSimplex ℝ (Fin d), ∀ v ∈ stdSimplex ℝ (Fin d),
      v ⬝ᵥ (∑ s ∈ Finset.Icc 1 t,u s)-𝓡 v/η ≤ y ⬝ᵥ (∑ s ∈ Finset.Icc 1 t,u s)-𝓡 y/η := by
    have hc : Continuous (fun v : Fin d → ℝ => v ⬝ᵥ (∑ s ∈ Finset.Icc 1 t,u s)) := by
      fun_prop
    exact (isCompact_stdSimplex ℝ (Fin d)).exists_isMaxOn ⟨wstar,hwstar⟩
      (hc.continuousOn.sub (h𝓡.1.div_const η))
  choose a ha using hex
  let g : ℕ → Fin d → ℝ := fun t => if t=0 then w 0 else a t
  have hg0 : g 0 = w 0 := by simp [g]
  have hg : IsLeader 𝓡 η u g := by
    intro t
    by_cases ht : t=0
    · subst t
      rw [hg0]
      refine ⟨hw.1.1, ?_⟩
      intro v hv
      simpa using neg_le_neg (div_le_div_of_nonneg_right (hw.1.2 v hv) hη.le)
    · simpa only [g, if_neg ht] using ha t
  have hreg := regret_bound 𝓡 η R hη h𝓡 hR (fun t => u (t-1)) u w g hw hg T wstar hwstar
  have hstab := stability_bound 𝓡 η hη h𝓡 (fun t => u (t-1)) u w g hw hg
  let A : ℕ → ℝ := fun t => l1 (w t-g t)^2
  let B : ℕ → ℝ := fun t => l1 (w t-g (t-1))^2
  have hA0 : A 0 = 0 := by simp [A,hg0,l1]
  have herror : (∑ t ∈ Finset.Icc 1 T, ‖u t-u (t-1)‖*l1 (w t-g t)) ≤
      η*(∑ t ∈ Finset.Icc 1 T, ‖u t-u (t-1)‖^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    have hb := (hstab t).1
    rw [norm_sub_rev] at hb
    have hm := mul_le_mul_of_nonneg_left hb (norm_nonneg (u t-u (t-1)))
    nlinarith
  have hprevious : (∑ t ∈ Finset.Icc 1 T,A (t-1)) ≤ ∑ t ∈ Finset.Icc 1 T,A t := by
    have he := sum_backward_diff A T
    rw [Finset.sum_sub_distrib,hA0,sub_zero] at he
    have hn : 0 ≤ A T := sq_nonneg _
    linarith
  have hmove (t : ℕ) : l1 (w t-w (t-1))^2 ≤ 2*(B t+A (t-1)) := by
    have ht := l1_triangle_sub (w t) (w (t-1)) (g (t-1))
    have hsq := mul_self_le_mul_self (l1_nonnegative (w t-w (t-1))) ht
    dsimp [A,B]
    nlinarith [sq_nonneg (l1 (w t-g (t-1))-l1 (w (t-1)-g (t-1)))]
  have hsumMove := Finset.sum_le_sum (fun t (_ : t ∈ Finset.Icc 1 T) => hmove t)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsumMove
  have hmovement : (∑ t ∈ Finset.Icc 1 T,l1 (w t-w (t-1))^2) ≤
      2*(∑ t ∈ Finset.Icc 1 T,(A t+B t)) := by
    rw [Finset.sum_add_distrib]
    linarith
  have hcoeff : 0 < 1/(4*η) := by positivity
  have hm := mul_le_mul_of_nonneg_left hmovement hcoeff.le
  have heq : (1/(4*η))*(2*(∑ t ∈ Finset.Icc 1 T,(A t+B t))) =
      (1/(2*η))*(∑ t ∈ Finset.Icc 1 T,(A t+B t)) := by ring
  rw [heq] at hm
  change (∑ t ∈ Finset.Icc 1 T,(wstar-w t) ⬝ᵥ u t) ≤ R/η+
    (∑ t ∈ Finset.Icc 1 T,‖u t-u (t-1)‖*l1 (w t-g t))-
    (1/(2*η))*(∑ t ∈ Finset.Icc 1 T,(A t+B t)) at hreg
  linarith


