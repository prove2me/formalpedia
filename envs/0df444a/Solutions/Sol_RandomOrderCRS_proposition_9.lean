-- Prove2me | solution 1 for RandomOrderCRS.proposition_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:41:34.469689+00:00
-- url     : https://prove2.me/submissions/52d5d9d6-7209-4b9d-bff0-34049f3d975f

import Mathlib
import Definitions.Def_RandomOrderCRS_Attenuation

open Real

namespace Aux_RandomOrderCRS_proposition_9

open Set

noncomputable def Q (c t : ℝ) : ℝ := 6 - 2 * c - 2 * t - 4 * c * t + 2 * c * (t * t)
noncomputable def S (c t : ℝ) : ℝ := 4 - 6 * c - 2 * t + 2 * c * (t * t)
noncomputable def R (c t : ℝ) : ℝ := 2 - 6 * c + (4 * c - 2) * t + 2 * c * (t * t)
noncomputable def F (c t : ℝ) : ℝ := 2 + (2 - 4 * c) * t - exp (t - 1) * Q c t
noncomputable def F' (c t : ℝ) : ℝ := (2 - 4 * c) - exp (t - 1) * S c t

lemma hasDerivE (t : ℝ) : HasDerivAt (fun x => exp (x - 1)) (exp (t - 1) * 1) t :=
  ((hasDerivAt_id' t).sub_const 1).exp

lemma hasDerivQ (c t : ℝ) : HasDerivAt (Q c) (-2 - 4 * c + 4 * c * t) t := by
  have h := (((hasDerivAt_const t (6 - 2 * c)).sub ((hasDerivAt_id' t).const_mul 2)).sub
    ((hasDerivAt_id' t).const_mul (4 * c))).add
    (((hasDerivAt_id' t).mul (hasDerivAt_id' t)).const_mul (2 * c))
  show HasDerivAt (fun t => 6 - 2 * c - 2 * t - 4 * c * t + 2 * c * (t * t)) _ t
  exact h.congr_deriv (by ring)

lemma hasDerivS (c t : ℝ) : HasDerivAt (S c) (-2 + 4 * c * t) t := by
  have h := ((hasDerivAt_const t (4 - 6 * c)).sub ((hasDerivAt_id' t).const_mul 2)).add
    (((hasDerivAt_id' t).mul (hasDerivAt_id' t)).const_mul (2 * c))
  show HasDerivAt (fun t => 4 - 6 * c - 2 * t + 2 * c * (t * t)) _ t
  exact h.congr_deriv (by ring)

lemma hasDerivF (c t : ℝ) : HasDerivAt (F c) (F' c t) t := by
  have h := ((hasDerivAt_const t 2).add ((hasDerivAt_id' t).const_mul (2 - 4 * c))).sub
    ((hasDerivE t).mul (hasDerivQ c t))
  show HasDerivAt (fun t => 2 + (2 - 4 * c) * t - exp (t - 1) * Q c t) _ t
  refine h.congr_deriv ?_
  simp only [F', S, Q]
  ring

lemma hasDerivF' (c t : ℝ) : HasDerivAt (F' c) (-(exp (t - 1) * R c t)) t := by
  have h := (hasDerivAt_const t (2 - 4 * c)).sub ((hasDerivE t).mul (hasDerivS c t))
  show HasDerivAt (fun t => (2 - 4 * c) - exp (t - 1) * S c t) _ t
  refine h.congr_deriv ?_
  simp only [R, S]
  ring

lemma R_eq (c x : ℝ) : R c x = 2 * (x - 1) * (c * x + 3 * c - 1) := by
  unfold R; ring

lemma F_nonneg (c : ℝ) (hc : c = 3 - exp 1) : ∀ t ∈ Icc (0:ℝ) 1, 0 ≤ F c t := by
  have e1 := Real.exp_one_gt_d9
  have e2 := Real.exp_one_lt_d9
  have hc0 : 0 < c := by rw [hc]; linarith
  have hc1 : 1 - 3 * c > 0 := by rw [hc]; linarith
  have hc2 : 1 - 3 * c < c := by rw [hc]; linarith
  set t0 : ℝ := (1 - 3 * c) / c with ht0
  have hct0 : c * t0 = 1 - 3 * c := by rw [ht0, mul_comm c]; exact div_mul_cancel₀ _ hc0.ne'
  have ht0pos : 0 < t0 := div_pos hc1 hc0
  have ht0lt : t0 < 1 := by rw [ht0, div_lt_one hc0]; exact hc2
  have hcontF : ContinuousOn (F c) univ := fun x _ => (hasDerivF c x).continuousAt.continuousWithinAt
  have hcontF' : ContinuousOn (F' c) univ :=
    fun x _ => (hasDerivF' c x).continuousAt.continuousWithinAt
  have hdiffF : DifferentiableOn ℝ (F c) univ :=
    fun x _ => (hasDerivF c x).differentiableAt.differentiableWithinAt
  have hdiffF' : DifferentiableOn ℝ (F' c) univ :=
    fun x _ => (hasDerivF' c x).differentiableAt.differentiableWithinAt
  have hF1 : F c 1 = 0 := by
    unfold F Q; rw [sub_self, exp_zero]; ring
  have hF'1 : F' c 1 = 0 := by
    unfold F' S; rw [sub_self, exp_zero]; ring
  have hF0 : F c 0 = 0 := by
    have : exp (0 - 1) * exp 1 = 1 := by rw [← exp_add]; norm_num
    unfold F Q; rw [hc]; linear_combination (-2) * this
  -- Step 1: on [t0, 1]
  have hmono : MonotoneOn (F' c) (Icc t0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (hcontF'.mono (subset_univ _))
      (hdiffF'.mono (subset_univ _))
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivF' c x).deriv, R_eq]
    have h1 : x - 1 ≤ 0 := by linarith [hx.2]
    have h2 : 0 ≤ c * x + 3 * c - 1 := by
      have : c * t0 ≤ c * x := mul_le_mul_of_nonneg_left hx.1.le hc0.le
      linarith
    have he := exp_pos (x - 1)
    have h3 : 0 ≤ -(x - 1) * (c * x + 3 * c - 1) := mul_nonneg (by linarith) h2
    nlinarith [mul_nonneg he.le h3]
  have hF'neg : ∀ x ∈ Icc t0 1, F' c x ≤ 0 := by
    intro x hx
    rw [← hF'1]
    exact hmono hx ⟨ht0lt.le, le_refl _⟩ hx.2
  have hanti : AntitoneOn (F c) (Icc t0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (hcontF.mono (subset_univ _))
      (hdiffF.mono (subset_univ _))
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivF c x).deriv]
    exact hF'neg x ⟨hx.1.le, hx.2.le⟩
  have hright : ∀ x ∈ Icc t0 1, 0 ≤ F c x := by
    intro x hx
    rw [← hF1]
    exact hanti hx ⟨ht0lt.le, le_refl _⟩ hx.2
  -- Step 2: on [0, t0]
  have hanti' : AntitoneOn (F' c) (Icc 0 t0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (hcontF'.mono (subset_univ _))
      (hdiffF'.mono (subset_univ _))
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivF' c x).deriv, R_eq]
    have h1 : x - 1 ≤ 0 := by linarith [hx.2]
    have h2 : c * x + 3 * c - 1 ≤ 0 := by
      have : c * x ≤ c * t0 := mul_le_mul_of_nonneg_left hx.2.le hc0.le
      linarith
    have he := exp_pos (x - 1)
    have h3 : 0 ≤ (x - 1) * (c * x + 3 * c - 1) := mul_nonneg_of_nonpos_of_nonpos h1 h2
    nlinarith [mul_nonneg he.le h3]
  have hderivF : deriv (F c) = F' c := funext fun x => (hasDerivF c x).deriv
  have hconc : ConcaveOn ℝ (Icc 0 t0) (F c) := by
    apply AntitoneOn.concaveOn_of_deriv (convex_Icc _ _) (hcontF.mono (subset_univ _))
      (hdiffF.mono (subset_univ _))
    rw [hderivF]
    exact hanti'.mono interior_subset
  have hleft : ∀ x ∈ Icc 0 t0, 0 ≤ F c x := by
    intro x hx
    have hseg : x ∈ segment ℝ (0:ℝ) t0 := by rw [segment_eq_Icc ht0pos.le]; exact hx
    have := hconc.ge_on_segment (left_mem_Icc.mpr ht0pos.le) (right_mem_Icc.mpr ht0pos.le) hseg
    have hFt0 : 0 ≤ F c t0 := hright t0 ⟨le_refl _, ht0lt.le⟩
    rw [hF0] at this
    exact le_trans (le_min (le_refl 0) hFt0) this
  intro t ht
  rcases le_total t t0 with h | h
  · exact hleft t ⟨ht.1, h⟩
  · exact hright t ⟨h, ht.2⟩

end Aux_RandomOrderCRS_proposition_9

open RandomOrderCRS Aux_RandomOrderCRS_proposition_9 in
theorem solution :
    ∀ t ∈ Set.Ico (0 : ℝ) 1,
      deriv a₁ t / a₁ t + 4 / (1 - t) - 2 * (1 - exp (t - 1)) / (exp (t - 1) - t) ≤ 0 := by
  intro t ht
  obtain ⟨c, hc⟩ : ∃ c, c = 3 - exp 1 := ⟨_, rfl⟩
  have e1 := Real.exp_one_gt_d9
  have e2 := Real.exp_one_lt_d9
  have hc0 : 0 < c := by rw [hc]; linarith
  have hc1 : c < 1 := by rw [hc]; linarith
  have ha1 : ∀ x, a₁ x = (1 - c * x) * (1 - c * x) := fun x => by
    unfold RandomOrderCRS.a₁; rw [hc]; ring
  have ha : HasDerivAt a₁ (-2 * c * (1 - c * t)) t := by
    have hl : HasDerivAt (fun x => 1 - c * x) (0 - c * 1) t :=
      (hasDerivAt_const t 1).sub ((hasDerivAt_id' t).const_mul c)
    have h2 := hl.mul hl
    have heq : a₁ = fun x => (1 - c * x) * (1 - c * x) := funext ha1
    rw [heq]
    exact h2.congr_deriv (by ring)
  have hA : 0 < 1 - c * t := by
    have : c * t ≤ c * 1 := mul_le_mul_of_nonneg_left ht.2.le hc0.le
    linarith
  have hB : 0 < 1 - t := by linarith [ht.2]
  have hD : 0 < exp (t - 1) - t := by
    have := Real.add_one_lt_exp (x := t - 1) (by linarith [ht.2])
    linarith
  have hF := F_nonneg c hc t ⟨ht.1, ht.2.le⟩
  rw [ha.deriv, ha1 t]
  have e3 : -2 * c * (1 - c * t) / ((1 - c * t) * (1 - c * t)) = -2 * c / (1 - c * t) := by
    rw [div_eq_div_iff (mul_pos hA hA).ne' hA.ne']; ring
  rw [e3, div_add_div _ _ hA.ne' hB.ne', div_sub_div _ _ (mul_ne_zero hA.ne' hB.ne') hD.ne']
  refine div_nonpos_of_nonpos_of_nonneg ?_ (mul_pos (mul_pos hA hB) hD).le
  have : (-2 * c * (1 - t) + (1 - c * t) * 4) * (exp (t - 1) - t)
      - (1 - c * t) * (1 - t) * (2 * (1 - exp (t - 1))) = -F c t := by
    unfold F Q; ring
  linarith
