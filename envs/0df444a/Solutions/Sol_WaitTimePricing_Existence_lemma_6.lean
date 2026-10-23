-- Prove2me | solution 1 for WaitTimePricing.Existence.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T10:18:10.364277+00:00
-- url     : https://prove2.me/submissions/6d36ccc5-4d1c-495c-a345-d3ca4c8c36d0

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting
import Definitions.Def_WaitTimePricing_Existence_Algorithm1
import Theorems.Thm_WaitTimePricing_Existence_proposition_4
import Theorems.Thm_WaitTimePricing_Existence_proposition_5
import Theorems.Thm_WaitTimePricing_Existence_lemma_3

open Set WaitTimePricing.Existence

namespace WTPAux

lemma dU_contDiff {M : Model} (hM : M.Standing) : ContDiff ℝ 2 (deriv M.U) := by
  have h' : ContDiff ℝ (2 + 1) M.U := by
    rw [show ((2 : WithTop ℕ∞) + 1) = 3 by norm_num]; exact hM.U_contDiff
  exact (contDiff_succ_iff_deriv.mp h').2.2

lemma dc_contDiff {M : Model} (hM : M.Standing) : ContDiff ℝ 1 (deriv M.c) := by
  have h' : ContDiff ℝ (1 + 1) M.c := by
    rw [show ((1 : WithTop ℕ∞) + 1) = 2 by norm_num]; exact hM.c_contDiff
  exact (contDiff_succ_iff_deriv.mp h').2.2

lemma U_diff {M : Model} (hM : M.Standing) : Differentiable ℝ M.U :=
  hM.U_contDiff.differentiable (by norm_num)

lemma dU_diff {M : Model} (hM : M.Standing) : Differentiable ℝ (deriv M.U) :=
  (dU_contDiff hM).differentiable (by norm_num)

lemma c_diff {M : Model} (hM : M.Standing) : Differentiable ℝ M.c :=
  hM.c_contDiff.differentiable (by norm_num)

lemma dc_diff {M : Model} (hM : M.Standing) : Differentiable ℝ (deriv M.c) :=
  (dc_contDiff hM).differentiable (by norm_num)

lemma dU_strictAnti {M : Model} (hM : M.Standing) : StrictAntiOn (deriv M.U) (Icc 0 M.C) :=
  strictAntiOn_of_deriv_neg (convex_Icc _ _) (dU_diff hM).continuous.continuousOn
    (fun x hx => hM.deriv2_U_neg x (interior_subset hx))

lemma c_strictMono {M : Model} (hM : M.Standing) : StrictMonoOn M.c (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici _) (c_diff hM).continuous.continuousOn
    (fun x hx => hM.deriv_c_pos x (interior_subset hx))

lemma dc_mono {M : Model} (hM : M.Standing) : MonotoneOn (deriv M.c) (Ici 0) :=
  monotoneOn_of_deriv_nonneg (convex_Ici _) (dc_diff hM).continuous.continuousOn
    (dc_diff hM).differentiableOn (fun x hx => hM.deriv2_c_nonneg x (interior_subset hx))

/-- `c(w) ≥ c'(0) w` for `w ≥ 0`. -/
lemma c_lower {M : Model} (hM : M.Standing) (w : ℝ) (hw : 0 ≤ w) :
    deriv M.c 0 * w ≤ M.c w := by
  have h := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Ici (0:ℝ))
    (c_diff hM).continuous.continuousOn (c_diff hM).differentiableOn
    (C := deriv M.c 0) (fun x hx => by
      rw [interior_Ici] at hx
      exact dc_mono hM (mem_Ici.2 (le_refl (0:ℝ))) (mem_Ici.2 (mem_Ioi.1 hx).le) (mem_Ioi.1 hx).le) 0 (mem_Ici.2 le_rfl) w (mem_Ici.2 hw) hw
  rw [hM.c_zero, sub_zero, sub_zero] at h; exact h

/-- For `A > 0` there is a unique `w ≥ 0` with `c(w) = A`, and it is positive. -/
lemma c_root {M : Model} (hM : M.Standing) (A : ℝ) (hA : 0 < A) :
    ∃ w0, 0 < w0 ∧ M.c w0 = A ∧ ∀ w, 0 ≤ w → M.c w = A → w = w0 := by
  have hc0 := hM.deriv_c_pos 0 le_rfl
  set W := A / deriv M.c 0 with hW
  have hW0 : 0 ≤ W := div_nonneg hA.le hc0.le
  have hcW : A ≤ M.c W := by
    have := c_lower hM W hW0
    rw [hW, mul_div_cancel₀ _ hc0.ne'] at this; exact this
  obtain ⟨w0, hw0, hcw0⟩ := intermediate_value_Icc hW0 (c_diff hM).continuous.continuousOn
    ⟨by rw [hM.c_zero]; exact hA.le, hcW⟩
  have hpos : 0 < w0 := by
    rcases eq_or_lt_of_le hw0.1 with h | h
    · rw [← h, hM.c_zero] at hcw0; linarith
    · exact h
  refine ⟨w0, hpos, hcw0, fun w hw hcw => ?_⟩
  exact (c_strictMono hM).injOn hw (show w0 ∈ Ici (0:ℝ) from hw0.1) (hcw.trans hcw0.symm)

lemma U_C_pos {M : Model} (hM : M.Standing) : 0 < M.U M.C := by
  have hC := hM.C_pos
  -- U' (t) > U'(C) ≥ 0 on [0, C)
  have h := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc (0:ℝ) (M.C / 2))
    (U_diff hM).continuous.continuousOn (U_diff hM).differentiableOn
    (C := deriv M.U (M.C / 2)) (fun x hx => by
      rw [interior_Icc] at hx
      exact (dU_strictAnti hM).antitoneOn ⟨hx.1.le, by linarith [hx.2]⟩
        ⟨by linarith, by linarith⟩ hx.2.le) 0 ⟨le_rfl, by linarith⟩ (M.C / 2) ⟨by linarith, le_rfl⟩
        (by linarith)
  have h2 : 0 < deriv M.U (M.C / 2) := lt_of_le_of_lt (hM.deriv_U_nonneg M.C ⟨hC.le, le_rfl⟩)
    ((dU_strictAnti hM) ⟨by linarith, by linarith⟩ ⟨hC.le, le_rfl⟩ (by linarith))
  have h3 : M.U (M.C / 2) ≤ M.U M.C := by
    have := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc (0:ℝ) M.C)
      (U_diff hM).continuous.continuousOn (U_diff hM).differentiableOn
      (C := 0) (fun x hx => hM.deriv_U_nonneg x (interior_subset hx)) (M.C / 2)
      ⟨by linarith, by linarith⟩ M.C ⟨hC.le, le_rfl⟩ (by linarith)
    linarith
  rw [hM.U_zero, sub_zero] at h
  nlinarith

/-- `r(t) = U(t) − U′(t) t` is strictly increasing on `[0, C]`. -/
lemma r_strictMono {M : Model} (hM : M.Standing) :
    StrictMonoOn (fun t => M.U t - deriv M.U t * t) (Icc 0 M.C) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact ((U_diff hM).continuous.sub ((dU_diff hM).continuous.mul continuous_id)).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hd : HasDerivAt (fun t => M.U t - deriv M.U t * t)
        (deriv M.U x - (deriv (deriv M.U) x * x + deriv M.U x * 1)) x :=
      ((U_diff hM) x).hasDerivAt.sub (((dU_diff hM) x).hasDerivAt.mul (hasDerivAt_id x))
    rw [hd.deriv]
    have := hM.deriv2_U_neg x ⟨hx.1.le, hx.2.le⟩
    nlinarith [hx.1]

lemma wbar_spec {M : Model} (hM : M.Standing) :
    0 < wbar M ∧ M.U M.C = M.c (wbar M) ∧ ∀ w : ℝ, 0 < w → M.U M.C = M.c w → w = wbar M := by
  obtain ⟨w0, hw0, hcw0, huniq⟩ := c_root hM _ (U_C_pos hM)
  have hset : {w ∈ Ioi (0 : ℝ) | M.U M.C = M.c w} = {w0} := by
    ext w; simp only [mem_setOf_eq, mem_Ioi, mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact huniq w h1.le h2.symm
    · rintro rfl; exact ⟨hw0, hcw0.symm⟩
  have hwb : wbar M = w0 := by unfold wbar; rw [hset, csSup_singleton]
  rw [hwb]
  exact ⟨hw0, hcw0.symm, fun w hw h => huniq w hw.le h.symm⟩

lemma tOf_nonneg (M : Model) (p : ℝ) : 0 ≤ tOf M p := Real.sSup_nonneg (fun x hx => hx.1.1)

lemma tOf_le_C {M : Model} (hM : M.Standing) (p : ℝ) : tOf M p ≤ M.C :=
  Real.sSup_le (fun x hx => hx.1.2) hM.C_pos.le

lemma tOf_bdd (M : Model) (p : ℝ) : BddAbove {t ∈ Icc 0 M.C | p ≤ deriv M.U t} :=
  ⟨M.C, fun x hx => hx.1.2⟩

lemma tOf_mem {M : Model} (hM : M.Standing) (p : ℝ) (hp : p ≤ deriv M.U 0) :
    tOf M p ∈ {t ∈ Icc 0 M.C | p ≤ deriv M.U t} := by
  have hne : ({t ∈ Icc 0 M.C | p ≤ deriv M.U t} : Set ℝ).Nonempty :=
    ⟨0, ⟨le_rfl, hM.C_pos.le⟩, hp⟩
  have hcl : IsClosed ({t ∈ Icc 0 M.C | p ≤ deriv M.U t} : Set ℝ) :=
    (dU_diff hM).continuous.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  exact hcl.csSup_mem hne (tOf_bdd M p)

lemma tOf_gt {M : Model} (p s : ℝ) (hs : s ∈ Icc 0 M.C) (hlt : tOf M p < s) :
    deriv M.U s < p := by
  by_contra h
  exact absurd (le_csSup (tOf_bdd M p) ⟨hs, not_lt.1 h⟩) (not_le.2 hlt)

/-- `t(p)` maximizes `U(t) − p t` over `[0, C]`. -/
lemma H_ge {M : Model} (hM : M.Standing) (p : ℝ) (hp : p ≤ deriv M.U 0) (t : ℝ)
    (ht : t ∈ Icc 0 M.C) : M.U t - p * t ≤ M.U (tOf M p) - p * tOf M p := by
  have hm := tOf_mem hM p hp
  set τ := tOf M p
  rcases le_total t τ with h | h
  · have := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc t τ)
      (U_diff hM).continuous.continuousOn (U_diff hM).differentiableOn (C := p)
      (fun x hx => by
        rw [interior_Icc] at hx
        exact le_trans hm.2 ((dU_strictAnti hM).antitoneOn
          ⟨by linarith [ht.1, hx.1], by linarith [hm.1.2, hx.2]⟩ hm.1 hx.2.le))
      t ⟨le_rfl, h⟩ τ ⟨h, le_rfl⟩ h
    linarith
  · have := Convex.image_sub_le_mul_sub_of_deriv_le (convex_Icc τ t)
      (U_diff hM).continuous.continuousOn (U_diff hM).differentiableOn (C := p)
      (fun x hx => by
        rw [interior_Icc] at hx
        exact (tOf_gt p x ⟨by linarith [hm.1.1, hx.1], by linarith [ht.2, hx.2]⟩ hx.1).le)
      τ ⟨le_rfl, h⟩ t ⟨h, le_rfl⟩ h
    linarith

lemma tOf_zero {M : Model} (hM : M.Standing) : tOf M 0 = M.C := by
  have : {t ∈ Icc 0 M.C | (0:ℝ) ≤ deriv M.U t} = Icc 0 M.C := by
    ext t; exact ⟨fun h => h.1, fun h => ⟨h, hM.deriv_U_nonneg t h⟩⟩
  unfold tOf; rw [this, csSup_Icc hM.C_pos.le]

lemma tOf_top {M : Model} (hM : M.Standing) : tOf M (deriv M.U 0) = 0 := by
  have : {t ∈ Icc 0 M.C | deriv M.U 0 ≤ deriv M.U t} = {0} := by
    ext t; simp only [mem_singleton_iff]
    constructor
    · rintro ⟨ht, h⟩
      by_contra hne
      have hpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hne)
      exact absurd h (not_le.2 ((dU_strictAnti hM) ⟨le_rfl, hM.C_pos.le⟩ ht hpos))
    · rintro rfl; exact ⟨⟨le_rfl, hM.C_pos.le⟩, le_rfl⟩
  unfold tOf; rw [this, csSup_singleton]

/-- The consumer surplus `H(p) = U(t(p)) − p t(p)`. -/
noncomputable def H (M : Model) (p : ℝ) : ℝ := M.U (tOf M p) - p * tOf M p

lemma H_anti {M : Model} (hM : M.Standing) (p q : ℝ) (hpq : p ≤ q) (hq : q ≤ deriv M.U 0) :
    H M q ≤ H M p := by
  unfold H
  have h1 := H_ge hM p (le_trans hpq hq) (tOf M q) ⟨tOf_nonneg M q, tOf_le_C hM q⟩
  have h2 := tOf_nonneg M q
  nlinarith

lemma H_lip {M : Model} (hM : M.Standing) (p q : ℝ) (hpq : p ≤ q) (hq : q ≤ deriv M.U 0) :
    H M p ≤ H M q + (q - p) * M.C := by
  unfold H
  have h1 := H_ge hM q hq (tOf M p) ⟨tOf_nonneg M p, tOf_le_C hM p⟩
  have h2 := tOf_le_C hM p
  have h3 := tOf_nonneg M p
  nlinarith

lemma H_cont {M : Model} (hM : M.Standing) : ContinuousOn (H M) (Icc 0 (deriv M.U 0)) := by
  apply (LipschitzOnWith.continuousOn (K := M.C.toNNReal))
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hM.C_pos.le]
  rcases le_total x y with h | h
  · have a := H_lip hM x y h hy.2; have b := H_anti hM x y h hy.2
    rw [abs_of_nonpos (by linarith : x - y ≤ 0), abs_le]; constructor <;> nlinarith [hM.C_pos]
  · have a := H_lip hM y x h hx.2; have b := H_anti hM y x h hx.2
    rw [abs_of_nonneg (by linarith : 0 ≤ x - y), abs_le]; constructor <;> nlinarith [hM.C_pos]

lemma H_zero {M : Model} (hM : M.Standing) : H M 0 = M.U M.C := by
  unfold H; rw [tOf_zero hM]; ring

lemma U_le_lin {M : Model} (hM : M.Standing) (t : ℝ) (ht : t ∈ Icc 0 M.C) :
    M.U t ≤ deriv M.U 0 * t := by
  have := Convex.image_sub_le_mul_sub_of_deriv_le (convex_Icc (0:ℝ) M.C)
    (U_diff hM).continuous.continuousOn (U_diff hM).differentiableOn (C := deriv M.U 0)
    (fun x hx => hM.deriv_U_le x (interior_subset hx)) 0 ⟨le_rfl, hM.C_pos.le⟩ t ht ht.1
  rw [hM.U_zero, sub_zero, sub_zero] at this; exact this

/-- the joining set of prices at wait time `w` -/
lemma Gamma_spec {M : Model} (hM : M.Standing) (w : ℝ) (hw : w ∈ Icc 0 (wbar M)) :
    Gamma M w ∈ {p ∈ Icc 0 (deriv M.U 0) | 0 ≤ M.U (tOf M p) - p * tOf M p - M.c w} ∧
    ∀ p ∈ {p ∈ Icc 0 (deriv M.U 0) | 0 ≤ M.U (tOf M p) - p * tOf M p - M.c w}, p ≤ Gamma M w := by
  have hU0 : 0 ≤ deriv M.U 0 := hM.deriv_U_nonneg 0 ⟨le_rfl, hM.C_pos.le⟩
  obtain ⟨hwb, hUc, -⟩ := wbar_spec hM
  have hcw : M.c w ≤ M.c (wbar M) :=
    (c_strictMono hM).monotoneOn (mem_Ici.2 hw.1) (mem_Ici.2 hwb.le) hw.2
  have hbdd : BddAbove {p ∈ Icc 0 (deriv M.U 0) | 0 ≤ M.U (tOf M p) - p * tOf M p - M.c w} :=
    ⟨deriv M.U 0, fun x hx => hx.1.2⟩
  have hne : (0:ℝ) ∈ {p ∈ Icc 0 (deriv M.U 0) | 0 ≤ M.U (tOf M p) - p * tOf M p - M.c w} := by
    refine ⟨⟨le_rfl, hU0⟩, ?_⟩
    have := H_zero hM; unfold H at this; rw [this]; linarith
  refine ⟨?_, fun p hp => le_csSup hbdd hp⟩
  apply IsClosed.csSup_mem _ ⟨0, hne⟩ hbdd
  have hc : ContinuousOn (fun p => M.U (tOf M p) - p * tOf M p - M.c w) (Icc 0 (deriv M.U 0)) :=
    (H_cont hM).sub continuousOn_const
  exact hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici

lemma v_le {M : Model} (hM : M.Standing) (obj : Objective) (p : ℝ) (hp : p ∈ Icc 0 (deriv M.U 0)) :
    v M obj p ≤ deriv M.U 0 * tOf M p := by
  cases obj with
  | revenue =>
    show p * tOf M p ≤ _
    exact mul_le_mul_of_nonneg_right hp.2 (tOf_nonneg M p)
  | welfare =>
    exact U_le_lin hM _ ⟨tOf_nonneg M p, tOf_le_C hM p⟩

lemma c_nonneg {M : Model} (hM : M.Standing) (w : ℝ) (hw : 0 ≤ w) : 0 ≤ M.c w :=
  le_trans (mul_nonneg (hM.deriv_c_pos 0 le_rfl).le hw) (c_lower hM w hw)

lemma alpha_nonneg (obj : Objective) : 0 ≤ alpha obj := by
  cases obj <;> simp [alpha]

lemma Gamma_nonneg (M : Model) (w : ℝ) : 0 ≤ Gamma M w := Real.sSup_nonneg (fun x hx => hx.1.1)

lemma Gamma_le {M : Model} (hM : M.Standing) (w : ℝ) : Gamma M w ≤ deriv M.U 0 :=
  Real.sSup_le (fun x hx => hx.1.2) (hM.deriv_U_nonneg 0 ⟨le_rfl, hM.C_pos.le⟩)

lemma wbar_nonneg (M : Model) : 0 ≤ wbar M := Real.sSup_nonneg (fun x hx => le_of_lt hx.1)

lemma grid_nonneg (M : Model) (N i : ℕ) : 0 ≤ grid M N i :=
  mul_nonneg (Nat.cast_nonneg _) (div_nonneg (wbar_nonneg M) (Nat.cast_nonneg _))

lemma grid_mono (M : Model) (N : ℕ) {i j : ℕ} (h : i ≤ j) : grid M N i ≤ grid M N j :=
  mul_le_mul_of_nonneg_right (by exact_mod_cast h) (div_nonneg (wbar_nonneg M) (Nat.cast_nonneg _))


lemma concave_glue {f : ℝ → ℝ} {a b c s : ℝ}
    (hlin : ∀ x ∈ Icc a b, f x = f b + s * (x - b)) (hconc : ConcaveOn ℝ (Icc b c) f)
    (hdom : ∀ y ∈ Icc b c, f y ≤ f b + s * (y - b)) : ConcaveOn ℝ (Icc a c) f := by
  rw [concaveOn_iff_slope_anti_adjacent]
  refine ⟨convex_Icc _ _, fun x y z hx hz hxy hyz => ?_⟩
  have hy : y ∈ Icc a c := ⟨by linarith [hx.1], by linarith [hz.2]⟩
  have hyx : 0 < y - x := by linarith
  have hzy : 0 < z - y := by linarith
  rcases le_or_gt b x with hbx | hxb
  · exact hconc.slope_anti_adjacent ⟨hbx, hx.2⟩ ⟨by linarith, hz.2⟩ hxy hyz
  rcases le_or_gt z b with hzb | hbz
  · rw [hlin x ⟨hx.1, hxb.le⟩, hlin y ⟨hy.1, by linarith⟩, hlin z ⟨hz.1, hzb⟩]
    rw [div_le_div_iff₀ hzy hyx]; ring_nf; rfl
  rcases le_or_gt y b with hyb | hby
  · have h1 := hdom z ⟨hbz.le, hz.2⟩
    rw [hlin x ⟨hx.1, hxb.le⟩, hlin y ⟨hy.1, hyb⟩]
    rw [div_le_div_iff₀ hzy hyx]
    have : (f b + s * (y - b) - (f b + s * (x - b))) = s * (y - x) := by ring
    rw [this]
    nlinarith
  · have h1 := hconc.slope_anti_adjacent (x := b) ⟨le_rfl, by linarith [hz.2]⟩ ⟨hbz.le, hz.2⟩ hby hyz
    have h2 := hdom y ⟨hby.le, by linarith [hz.2]⟩
    rw [hlin x ⟨hx.1, hxb.le⟩]
    refine le_trans h1 ?_
    rw [div_le_div_iff₀ (by linarith) hyx]
    nlinarith

lemma concave_incr {f : ℝ → ℝ} {a c p q h : ℝ} (hconc : ConcaveOn ℝ (Icc a c) f)
    (hp : a ≤ p) (hpq : p ≤ q) (hh : 0 ≤ h) (hq : q + h ≤ c) :
    f (q + h) - f q ≤ f (p + h) - f p := by
  rcases eq_or_lt_of_le hh with h0 | h0
  · subst h0; simp
  rcases eq_or_lt_of_le hpq with e | hlt
  · subst e; exact le_rfl
  have hd : 0 < q + h - p := by linarith
  set μ := h / (q + h - p) with hμ
  have hμ0 : 0 ≤ μ := div_nonneg hh hd.le
  have hμ1 : μ ≤ 1 := by rw [div_le_one hd]; linarith
  have hP : p ∈ Icc a c := ⟨hp, by linarith⟩
  have hQ : q + h ∈ Icc a c := ⟨by linarith, hq⟩
  have e1 : μ • p + (1 - μ) • (q + h) = q := by
    simp only [smul_eq_mul]; rw [hμ]; field_simp; ring
  have e2 : (1 - μ) • p + μ • (q + h) = p + h := by
    simp only [smul_eq_mul]; rw [hμ]; field_simp; ring
  have c1 := hconc.2 hP hQ (show 0 ≤ μ from hμ0) (show 0 ≤ 1 - μ by linarith) (by ring)
  have c2 := hconc.2 hP hQ (show 0 ≤ 1 - μ by linarith) (show 0 ≤ μ from hμ0) (by ring)
  rw [e1] at c1; rw [e2] at c2
  simp only [smul_eq_mul] at c1 c2
  linarith

lemma sSup_image_mono {S S' : Set ℝ} (f f' : ℝ → ℝ) (hS : S.Nonempty) (hsub : S ⊆ S')
    (hle : ∀ x ∈ S, f x ≤ f' x) (hb : BddAbove (f' '' S')) :
    sSup (f '' S) ≤ sSup (f' '' S') := by
  apply csSup_le (hS.image _)
  rintro _ ⟨x, hx, rfl⟩
  exact le_trans (hle x hx) (le_csSup hb ⟨x, hsub hx, rfl⟩)

lemma grid_N (M : Model) (N : ℕ) (hN : 1 ≤ N) : grid M N N = wbar M := by
  unfold grid; have : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  field_simp

lemma grid_succ (M : Model) (N i : ℕ) : grid M N (i + 1) = grid M N i + wbar M / N := by
  unfold grid; push_cast; ring

lemma VStep_frozen (M : Model) (obj : Objective) (g : ℝ) (N k m : ℕ) (hkm : k ≤ m) (w : ℝ)
    (hw : grid M N (N - k) ≤ w) : VStep M obj g N m w = VStep M obj g N k w := by
  induction m, hkm using Nat.le_induction with
  | base => rfl
  | succ m hkm ih =>
    show (if grid M N (N - (m + 1)) ≤ w ∧ w < grid M N (N - m) then _ else _) = _
    rw [if_neg (fun h => absurd (lt_of_lt_of_le h.2 (grid_mono M N (Nat.sub_le_sub_left hkm N)))
      (not_lt.2 hw)), ih]

lemma KStep_frozen (M : Model) (obj : Objective) (g : ℝ) (N k m : ℕ) (hkm : k ≤ m) (w : ℝ)
    (hw : grid M N (N - k) < w) : KStep M obj g N m w = KStep M obj g N k w := by
  induction m, hkm using Nat.le_induction with
  | base => rfl
  | succ m hkm ih =>
    show (if grid M N (N - (m + 1)) < w ∧ w ≤ grid M N (N - m) then _ else _) = _
    rw [if_neg (fun h => absurd (lt_of_le_of_lt (grid_mono M N (Nat.sub_le_sub_left hkm N)) hw)
      (not_lt.2 h.2)), ih]

lemma innerMax_congr (M : Model) (obj : Objective) (V1 V2 : ℝ → ℝ) (x : ℝ)
    (h : ∀ y, x ≤ y → V1 y = V2 y) : innerMax M obj V1 x = innerMax M obj V2 x := by
  unfold innerMax
  congr 1
  apply Set.image_congr
  intro p _
  rw [h x le_rfl, h (x + tOf M p) (by linarith [tOf_nonneg M p])]

lemma slopeAdj_congr (M : Model) (obj : Objective) (V1 V2 : ℝ → ℝ) (x : ℝ)
    (h : ∀ y, x ≤ y → V1 y = V2 y) : slopeAdj M obj V1 x = slopeAdj M obj V2 x := by
  unfold slopeAdj; rw [innerMax_congr M obj V1 V2 x h]

/-- On `[x_{i−1}, x_i)`, `V^g_N` is the line through `(x_i, V(x_i))` with slope
`−g + slopeAdj V x_i`. -/
lemma VgN_piece (M : Model) (obj : Objective) (g : ℝ) (N i : ℕ) (hi1 : 1 ≤ i) (hiN : i ≤ N)
    (w : ℝ) (hw : w ∈ Ico (grid M N (i - 1)) (grid M N i)) :
    VgN M obj g N w = VgN M obj g N (grid M N i) +
      (-g + slopeAdj M obj (VgN M obj g N) (grid M N i)) * (w - grid M N i) := by
  have e1 : N - (N - i) = i := by omega
  have e2 : N - (N - i + 1) = i - 1 := by omega
  have hfz : ∀ y, grid M N i ≤ y → VgN M obj g N y = VStep M obj g N (N - i) y := by
    intro y hy
    exact VStep_frozen M obj g N (N - i) N (by omega) y (by rw [e1]; exact hy)
  have h1 : VgN M obj g N w = VStep M obj g N (N - i + 1) w :=
    VStep_frozen M obj g N (N - i + 1) N (by omega) w (by rw [e2]; exact hw.1)
  rw [h1]
  show (if grid M N (N - (N - i + 1)) ≤ w ∧ w < grid M N (N - (N - i)) then _ else _) = _
  rw [e1, e2, if_pos (show grid M N (i - 1) ≤ w ∧ w < grid M N i from hw), hfz _ le_rfl,
    slopeAdj_congr M obj (VgN M obj g N) (VStep M obj g N (N - i)) _ hfz]

lemma VgN_right (M : Model) (obj : Objective) (g : ℝ) (N : ℕ) (w : ℝ) (hw : grid M N N ≤ w) :
    VgN M obj g N w = -(w - wbar M) * g := by
  have := VStep_frozen M obj g N 0 N (Nat.zero_le _) w (by simpa using hw)
  rw [VgN, this]; rfl

lemma KgN_piece (M : Model) (obj : Objective) (g : ℝ) (N i : ℕ) (hi1 : 1 ≤ i) (hiN : i ≤ N)
    (w : ℝ) (hw : w ∈ Ioc (grid M N (i - 1)) (grid M N i)) :
    KgN M obj g N w = slopeAdj M obj (VgN M obj g N) (grid M N i) := by
  have e1 : N - (N - i) = i := by omega
  have e2 : N - (N - i + 1) = i - 1 := by omega
  have hw0 : w ≠ 0 := ne_of_gt (lt_of_le_of_lt (grid_nonneg M N _) hw.1)
  have hfz : ∀ y, grid M N i ≤ y → VgN M obj g N y = VStep M obj g N (N - i) y := by
    intro y hy
    exact VStep_frozen M obj g N (N - i) N (by omega) y (by rw [e1]; exact hy)
  unfold KgN
  rw [if_neg hw0, KStep_frozen M obj g N (N - i + 1) N (by omega) w (by rw [e2]; exact hw.1)]
  show (if grid M N (N - (N - i + 1)) < w ∧ w ≤ grid M N (N - (N - i)) then _ else _) = _
  rw [e1, e2, if_pos (show grid M N (i - 1) < w ∧ w ≤ grid M N i from hw), slopeAdj_congr M obj (VgN M obj g N) (VStep M obj g N (N - i)) _ hfz]

lemma KgN_right (M : Model) (obj : Objective) (g : ℝ) (N : ℕ) (w : ℝ) (hw : grid M N N < w) :
    KgN M obj g N w = 0 := by
  have hw0 : w ≠ 0 := ne_of_gt (lt_of_le_of_lt (grid_nonneg M N _) hw)
  unfold KgN
  rw [if_neg hw0, KStep_frozen M obj g N 0 N (Nat.zero_le _) w (by simpa using hw)]
  rfl


lemma Gamma_anti {M : Model} (hM : M.Standing) : AntitoneOn (Gamma M) (Icc 0 (wbar M)) := by
  intro a ha b hb hab
  obtain ⟨hmb, -⟩ := Gamma_spec hM b hb
  obtain ⟨-, hla⟩ := Gamma_spec hM a ha
  apply hla
  refine ⟨hmb.1, ?_⟩
  have := (c_strictMono hM).monotoneOn (mem_Ici.2 ha.1) (mem_Ici.2 hb.1) hab
  linarith [hmb.2]

lemma slopeAdj_nonneg {M : Model} (hM : M.Standing) (obj : Objective) (V : ℝ → ℝ) (x : ℝ) :
    0 ≤ slopeAdj M obj V x := mul_nonneg hM.lam_pos.le (le_max_right _ _)

lemma grid_zero (M : Model) (N : ℕ) : grid M N 0 = 0 := by simp [grid]

lemma grid_le_wbar (M : Model) (N i : ℕ) (hN : 1 ≤ N) (hi : i ≤ N) : grid M N i ≤ wbar M := by
  rw [← grid_N M N hN]; exact grid_mono M N hi

/-- Backward induction of Proposition 4 (Lin–Shang–Sun, Appendix B). -/
lemma P_all {M : Model} (hM : M.Standing) (obj : Objective) (g : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∀ i ≤ N,
      ConcaveOn ℝ (Icc (grid M N i) (wbar M + M.C)) (VgN M obj g N) ∧
      (∀ y ∈ Icc (grid M N i) (wbar M + M.C), VgN M obj g N y ≤ VgN M obj g N (grid M N i) +
        (-g + (if i < N then slopeAdj M obj (VgN M obj g N) (grid M N (i + 1)) else 0)) *
          (y - grid M N i)) ∧
      (if i < N then slopeAdj M obj (VgN M obj g N) (grid M N (i + 1)) else 0) ≤
        slopeAdj M obj (VgN M obj g N) (grid M N i) := by
  set V := VgN M obj g N with hV
  set κ : ℕ → ℝ := fun i => slopeAdj M obj V (grid M N i) with hκ
  have hC := hM.C_pos
  have hw0 := wbar_nonneg M
  have hU0 : 0 ≤ deriv M.U 0 := hM.deriv_U_nonneg 0 ⟨le_rfl, hC.le⟩
  suffices H : ∀ d, d ≤ N →
      ConcaveOn ℝ (Icc (grid M N (N - d)) (wbar M + M.C)) V ∧
      (∀ y ∈ Icc (grid M N (N - d)) (wbar M + M.C), V y ≤ V (grid M N (N - d)) +
        (-g + (if N - d < N then κ (N - d + 1) else 0)) * (y - grid M N (N - d))) ∧
      (if N - d < N then κ (N - d + 1) else 0) ≤ κ (N - d) by
    intro i hi
    have := H (N - i) (Nat.sub_le _ _)
    rwa [Nat.sub_sub_self hi] at this
  intro d
  induction d with
  | zero =>
    intro _
    simp only [Nat.sub_zero, lt_irrefl, if_false, add_zero]
    rw [grid_N M N hN]
    have hR : ∀ y, wbar M ≤ y → V y = -(y - wbar M) * g := fun y hy =>
      VgN_right M obj g N y (by rw [grid_N M N hN]; exact hy)
    refine ⟨⟨convex_Icc _ _, fun x hx y hy a b ha hb hab => ?_⟩, fun y hy => ?_, ?_⟩
    · have hz : wbar M ≤ a • x + b • y := by
        have := (convex_Icc (wbar M) (wbar M + M.C)) hx hy ha hb hab; exact this.1
      rw [hR x hx.1, hR y hy.1, hR _ hz]
      simp only [smul_eq_mul]
      apply le_of_eq
      have : b = 1 - a := by linarith
      subst this; ring
    · rw [hR y hy.1, hR _ le_rfl]; ring_nf; rfl
    · exact slopeAdj_nonneg hM obj V _
  | succ d ih =>
    intro hd
    obtain ⟨hconc, hdom, hκle⟩ := ih (by omega)
    set i := N - (d + 1) with hi
    have hi1 : N - d = i + 1 := by omega
    rw [hi1] at hconc hdom hκle
    have hiN : i < N := by omega
    simp only [hiN, if_true]
    set a := grid M N i with ha
    set b := grid M N (i + 1) with hb
    set s := -g + κ (i + 1) with hs
    have hab : a ≤ b := grid_mono M N (Nat.le_succ i)
    have hbw : b ≤ wbar M := grid_le_wbar M N (i + 1) hN (by omega)
    have ha0 : 0 ≤ a := grid_nonneg M N i
    have hlin : ∀ x ∈ Icc a b, V x = V b + s * (x - b) := by
      intro x hx
      rcases eq_or_lt_of_le hx.2 with e | hlt
      · rw [e]; ring
      · have := VgN_piece M obj g N (i + 1) (by omega) (by omega) x
          ⟨by simpa using hx.1, hlt⟩
        simpa using this
    have hsig : (-g + (if i + 1 < N then κ (i + 1 + 1) else 0)) ≤ s := by
      rw [hs]; linarith
    have hdom' : ∀ y ∈ Icc b (wbar M + M.C), V y ≤ V b + s * (y - b) := by
      intro y hy
      have := hdom y hy
      have : (-g + (if i + 1 < N then κ (i + 1 + 1) else 0)) * (y - b) ≤ s * (y - b) :=
        mul_le_mul_of_nonneg_right hsig (by linarith [hy.1])
      linarith
    have hconc' : ConcaveOn ℝ (Icc a (wbar M + M.C)) V := concave_glue hlin hconc hdom'
    have hVa : V a = V b + s * (a - b) := hlin a ⟨le_rfl, hab⟩
    have hdomA : ∀ y ∈ Icc a (wbar M + M.C), V y ≤ V a + s * (y - a) := by
      intro y hy
      rcases le_or_gt y b with hyb | hyb
      · rw [hlin y ⟨hy.1, hyb⟩, hVa]; ring_nf; rfl
      · have := hdom' y ⟨hyb.le, hy.2⟩
        rw [hVa]; linarith
    refine ⟨hconc', hdomA, ?_⟩
    -- κ(i+1) ≤ κ(i): comparison of the inner maxima
    show slopeAdj M obj V b ≤ slopeAdj M obj V a
    unfold slopeAdj
    apply mul_le_mul_of_nonneg_left _ hM.lam_pos.le
    apply max_le_max _ le_rfl
    unfold innerMax
    have hGab : Gamma M b ≤ Gamma M a :=
      Gamma_anti hM ⟨ha0, le_trans hab hbw⟩ ⟨le_trans ha0 hab, hbw⟩ hab
    apply sSup_image_mono _ _ (nonempty_Icc.2 (Gamma_nonneg M b)) (Icc_subset_Icc le_rfl hGab)
    · intro p hp
      have ht0 := tOf_nonneg M p
      have htC := tOf_le_C hM p
      have hca : M.c a ≤ M.c b :=
        (c_strictMono hM).monotoneOn (mem_Ici.2 ha0) (mem_Ici.2 (le_trans ha0 hab)) hab
      have hinc := concave_incr hconc' le_rfl hab ht0 (by linarith)
      have := mul_le_mul_of_nonneg_left hca (alpha_nonneg obj)
      linarith
    · refine ⟨deriv M.U 0 * M.C + |s| * M.C, ?_⟩
      rintro _ ⟨p, hp, rfl⟩
      have ht0 := tOf_nonneg M p
      have htC := tOf_le_C hM p
      have hv := v_le hM obj p ⟨hp.1, le_trans hp.2 (Gamma_le hM a)⟩
      have hd := hdomA (a + tOf M p) ⟨by linarith, by linarith⟩
      have hca := mul_nonneg (alpha_nonneg obj) (c_nonneg hM a ha0)
      have h1 : deriv M.U 0 * tOf M p ≤ deriv M.U 0 * M.C := mul_le_mul_of_nonneg_left htC hU0
      have h2 : s * tOf M p ≤ |s| * M.C :=
        le_trans (mul_le_mul_of_nonneg_right (le_abs_self s) ht0)
          (mul_le_mul_of_nonneg_left htC (abs_nonneg s))
      simp only
      nlinarith

lemma KgN_eq_kappa {M : Model} (hM : M.Standing) (obj : Objective) (g : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (w : ℝ) (hw : w ∈ Icc 0 (wbar M)) :
    KgN M obj g N w = slopeAdj M obj (VgN M obj g N) (grid M N ⌈w / (wbar M / N)⌉₊) := by
  have hwb := (wbar_spec hM).1
  have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hε : 0 < wbar M / N := div_pos hwb hNpos
  rcases eq_or_lt_of_le hw.1 with h0 | hpos
  · subst h0; simp [KgN, grid_zero]
  set i := ⌈w / (wbar M / N)⌉₊ with hi
  have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 (div_pos hpos hε)))
  have hiN : i ≤ N := by
    apply Nat.ceil_le.2
    rw [div_le_iff₀ hε]; field_simp; exact hw.2
  apply KgN_piece M obj g N i hi1 hiN w
  have hc1 := Nat.le_ceil (w / (wbar M / N))
  have hc2 := Nat.ceil_lt_add_one (div_pos hpos hε).le
  rw [← hi] at hc1 hc2
  have hcast : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by rw [Nat.cast_sub hi1]; simp
  constructor
  · show ((i - 1 : ℕ) : ℝ) * (wbar M / N) < w
    rw [hcast]
    have : (i:ℝ) - 1 < w / (wbar M / N) := by linarith
    rwa [lt_div_iff₀ hε] at this
  · show w ≤ (i : ℝ) * (wbar M / N)
    rwa [div_le_iff₀ hε] at hc1

lemma kappa_anti {M : Model} (hM : M.Standing) (obj : Objective) (g : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∀ i j, i ≤ j → j ≤ N → slopeAdj M obj (VgN M obj g N) (grid M N j) ≤
      slopeAdj M obj (VgN M obj g N) (grid M N i) := by
  intro i j hij hjN
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    have := (P_all hM obj g N hN j (by omega)).2.2
    rw [if_pos (by omega)] at this
    exact le_trans this (ih (by omega))

lemma KgN_nonneg {M : Model} (hM : M.Standing) (obj : Objective) (g : ℝ) (N : ℕ) (w : ℝ) :
    0 ≤ KgN M obj g N w := by
  unfold KgN
  split_ifs
  · exact slopeAdj_nonneg hM obj _ _
  · induction N generalizing w with
    | zero => exact le_rfl
    | succ n _ =>
      -- generic: every `KStep` value is a slope adjustment or `0`
      have : ∀ k, ∀ w, 0 ≤ KStep M obj g (n + 1) k w := by
        intro k
        induction k with
        | zero => intro w; exact le_rfl
        | succ k ihk =>
          intro w
          show 0 ≤ (if grid M (n + 1) (n + 1 - (k + 1)) < w ∧ w ≤ grid M (n + 1) (n + 1 - k) then
            slopeAdj M obj (VStep M obj g (n + 1) k) (grid M (n + 1) (n + 1 - k))
            else KStep M obj g (n + 1) k w)
          split_ifs
          · exact slopeAdj_nonneg hM obj _ _
          · exact ihk w
      exact this _ _

lemma VgN_piece' (M : Model) (obj : Objective) (g : ℝ) (N i : ℕ) (hi1 : 1 ≤ i) (hiN : i ≤ N)
    (w : ℝ) (hw : w ∈ Icc (grid M N (i - 1)) (grid M N i)) :
    VgN M obj g N w = VgN M obj g N (grid M N i) +
      (-g + slopeAdj M obj (VgN M obj g N) (grid M N i)) * (w - grid M N i) := by
  rcases eq_or_lt_of_le hw.2 with e | hlt
  · rw [e]; ring
  · exact VgN_piece M obj g N i hi1 hiN w ⟨hw.1, hlt⟩

lemma monotoneOn_glue {D : ℝ → ℝ} {a b s : ℝ} (hab : a ≤ b)
    (h1 : ∀ x ∈ Icc a b, D x = D b + s * (x - b)) (hs : 0 ≤ s) (h2 : MonotoneOn D (Ici b)) :
    MonotoneOn D (Ici a) := by
  intro x hx y hy hxy
  rcases le_or_gt y b with hyb | hyb
  · rw [h1 x ⟨hx, le_trans hxy hyb⟩, h1 y ⟨le_trans (mem_Ici.1 hx) hxy, hyb⟩]
    nlinarith
  rcases le_or_gt x b with hxb | hxb
  · have : D x ≤ D b := by rw [h1 x ⟨hx, hxb⟩]; nlinarith
    exact le_trans this (h2 (mem_Ici.2 le_rfl) (mem_Ici.2 hyb.le) hyb.le)
  · exact h2 (mem_Ici.2 hxb.le) (mem_Ici.2 hyb.le) hxy

/-- Comparison of slope adjustments: if `W − V` is nondecreasing to the right of `x`, then the
slope adjustment of `V` at `x` is at most that of `W`. -/
lemma slopeAdj_mono_of_incr {M : Model} (hM : M.Standing) (obj : Objective) (V W : ℝ → ℝ)
    (x : ℝ) (hx : 0 ≤ x) (hD : ∀ y, x ≤ y → y ≤ x + M.C → V y - V x ≤ W y - W x)
    (hB : ∃ B, ∀ y, x ≤ y → y ≤ x + M.C → W y - W x ≤ B) :
    slopeAdj M obj V x ≤ slopeAdj M obj W x := by
  obtain ⟨B, hB⟩ := hB
  have hU0 : 0 ≤ deriv M.U 0 := hM.deriv_U_nonneg 0 ⟨le_rfl, hM.C_pos.le⟩
  unfold slopeAdj
  apply mul_le_mul_of_nonneg_left _ hM.lam_pos.le
  apply max_le_max _ le_rfl
  unfold innerMax
  apply sSup_image_mono _ _ (nonempty_Icc.2 (Gamma_nonneg M x)) subset_rfl
  · intro p _
    have := hD (x + tOf M p) (by linarith [tOf_nonneg M p]) (by linarith [tOf_le_C hM p])
    linarith
  · refine ⟨deriv M.U 0 * M.C + B, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    have ht0 := tOf_nonneg M p
    have htC := tOf_le_C hM p
    have hv := v_le hM obj p ⟨hp.1, le_trans hp.2 (Gamma_le hM x)⟩
    have hd := hB (x + tOf M p) (by linarith) (by linarith)
    have hca := mul_nonneg (alpha_nonneg obj) (c_nonneg hM x hx)
    have h1 : deriv M.U 0 * tOf M p ≤ deriv M.U 0 * M.C := mul_le_mul_of_nonneg_left htC hU0
    simp only
    linarith

/-- Upper bound for increments of `V^g_N` to the right of a grid point. -/
lemma VgN_incr_bdd {M : Model} (hM : M.Standing) (obj : Objective) (g : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (i : ℕ) (hi : i ≤ N) : ∃ B, ∀ y, grid M N i ≤ y → y ≤ grid M N i + M.C →
      VgN M obj g N y - VgN M obj g N (grid M N i) ≤ B := by
  obtain ⟨-, hdom, -⟩ := P_all hM obj g N hN i hi
  set σ := (-g + (if i < N then slopeAdj M obj (VgN M obj g N) (grid M N (i + 1)) else 0))
  refine ⟨|σ| * M.C, fun y hy1 hy2 => ?_⟩
  have hgw := grid_le_wbar M N i hN hi
  have := hdom y ⟨hy1, by linarith⟩
  have h2 : σ * (y - grid M N i) ≤ |σ| * M.C :=
    le_trans (mul_le_mul_of_nonneg_right (le_abs_self σ) (by linarith))
      (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg σ))
  linarith

lemma grid_double (M : Model) (j i : ℕ) (hj : 1 ≤ j) : grid M (2 * j) (2 * i) = grid M j i := by
  unfold grid
  have : (j:ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  push_cast; field_simp

lemma sSup_image_close {S : Set ℝ} (f h : ℝ → ℝ) (δ : ℝ) (hS : S.Nonempty)
    (hfh : ∀ x ∈ S, |f x - h x| ≤ δ) (hf : BddAbove (f '' S)) :
    |sSup (f '' S) - sSup (h '' S)| ≤ δ := by
  obtain ⟨B, hB⟩ := hf
  have hh : BddAbove (h '' S) := ⟨B + δ, by
    rintro _ ⟨x, hx, rfl⟩
    have := hB ⟨x, hx, rfl⟩; have := (abs_le.1 (hfh x hx)); linarith⟩
  have hfb : BddAbove (f '' S) := ⟨B, hB⟩
  rw [abs_le]; constructor
  · have : sSup (h '' S) ≤ sSup (f '' S) + δ := by
      apply csSup_le (hS.image _)
      rintro _ ⟨x, hx, rfl⟩
      have h1 := le_csSup hfb ⟨x, hx, rfl⟩
      have := (abs_le.1 (hfh x hx)); linarith
    linarith
  · have : sSup (f '' S) ≤ sSup (h '' S) + δ := by
      apply csSup_le (hS.image _)
      rintro _ ⟨x, hx, rfl⟩
      have h1 := le_csSup hh ⟨x, hx, rfl⟩
      have := (abs_le.1 (hfh x hx)); linarith
    linarith

lemma innerMax_bdd {M : Model} (hM : M.Standing) (obj : Objective) (V : ℝ → ℝ) (x : ℝ)
    (hx : 0 ≤ x) (B : ℝ) (hB : ∀ y, x ≤ y → y ≤ x + M.C → V y - V x ≤ B) :
    BddAbove ((fun p => v M obj p - alpha obj * M.c x + V (x + tOf M p) - V x) ''
      Icc 0 (Gamma M x)) := by
  have hU0 : 0 ≤ deriv M.U 0 := hM.deriv_U_nonneg 0 ⟨le_rfl, hM.C_pos.le⟩
  refine ⟨deriv M.U 0 * M.C + B, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have ht0 := tOf_nonneg M p
  have htC := tOf_le_C hM p
  have hv := v_le hM obj p ⟨hp.1, le_trans hp.2 (Gamma_le hM x)⟩
  have hd := hB (x + tOf M p) (by linarith) (by linarith)
  have hca := mul_nonneg (alpha_nonneg obj) (c_nonneg hM x hx)
  have h1 : deriv M.U 0 * tOf M p ≤ deriv M.U 0 * M.C := mul_le_mul_of_nonneg_left htC hU0
  simp only
  linarith

lemma innerMax_close {M : Model} (hM : M.Standing) (obj : Objective) (V W : ℝ → ℝ) (x : ℝ)
    (hx : 0 ≤ x) (e : ℝ) (hVW : ∀ y, x ≤ y → y ≤ x + M.C → |V y - W y| ≤ e)
    (hB : ∃ B, ∀ y, x ≤ y → y ≤ x + M.C → V y - V x ≤ B) :
    |innerMax M obj V x - innerMax M obj W x| ≤ 2 * e := by
  obtain ⟨B, hB⟩ := hB
  unfold innerMax
  apply sSup_image_close _ _ _ (nonempty_Icc.2 (Gamma_nonneg M x)) _
    (innerMax_bdd hM obj V x hx B hB)
  intro p _
  have h1 := hVW (x + tOf M p) (by linarith [tOf_nonneg M p]) (by linarith [tOf_le_C hM p])
  have h2 := hVW x le_rfl (by linarith [hM.C_pos])
  rw [abs_le] at h1 h2 ⊢; constructor <;> linarith

lemma slopeAdj_close {M : Model} (hM : M.Standing) (obj : Objective) (V W : ℝ → ℝ) (x : ℝ)
    (hx : 0 ≤ x) (e : ℝ) (hVW : ∀ y, x ≤ y → y ≤ x + M.C → |V y - W y| ≤ e)
    (hB : ∃ B, ∀ y, x ≤ y → y ≤ x + M.C → V y - V x ≤ B) :
    |slopeAdj M obj V x - slopeAdj M obj W x| ≤ M.lam * (2 * e) := by
  unfold slopeAdj
  rw [← mul_sub, abs_mul, abs_of_pos hM.lam_pos]
  apply mul_le_mul_of_nonneg_left _ hM.lam_pos.le
  exact le_trans (abs_max_sub_max_le_abs _ _ _) (innerMax_close hM obj V W x hx e hVW hB)

/-- Lipschitz dependence of `V^g_N` on `g`, with a constant uniform in `N`. -/
lemma VgN_lip_g {M : Model} (hM : M.Standing) (obj : Objective) (N : ℕ) (hN : 1 ≤ N)
    (g g' : ℝ) : ∀ i ≤ N, ∀ y ∈ Icc (grid M N i) (wbar M + M.C),
      |VgN M obj g N y - VgN M obj g' N y| ≤
        (M.C + ((N - i : ℕ) : ℝ) * (wbar M / N)) *
          (1 + 2 * M.lam * (wbar M / N)) ^ (N - i) * |g - g'| := by
  have hC := hM.C_pos
  have hl := hM.lam_pos
  have hε : 0 ≤ wbar M / N := div_nonneg (wbar_nonneg M) (Nat.cast_nonneg _)
  set ε := wbar M / N with hεdef
  set q := 1 + 2 * M.lam * ε with hq
  have hq1 : 1 ≤ q := by rw [hq]; nlinarith
  set δ := |g - g'| with hδ
  have hδ0 : 0 ≤ δ := abs_nonneg _
  suffices H : ∀ d ≤ N, ∀ y ∈ Icc (grid M N (N - d)) (wbar M + M.C),
      |VgN M obj g N y - VgN M obj g' N y| ≤ (M.C + (d : ℝ) * ε) * q ^ d * δ by
    intro i hi y hy
    exact H (N - i) (Nat.sub_le _ _) y (by rwa [Nat.sub_sub_self hi])
  intro d
  induction d with
  | zero =>
    intro _ y hy
    simp only [Nat.sub_zero, Nat.cast_zero, zero_mul, add_zero, pow_zero, mul_one] at hy ⊢
    rw [grid_N M N hN] at hy
    rw [VgN_right M obj g N y (by rw [grid_N M N hN]; exact hy.1),
      VgN_right M obj g' N y (by rw [grid_N M N hN]; exact hy.1)]
    rw [show -(y - wbar M) * g - -(y - wbar M) * g' = -(y - wbar M) * (g - g') by ring,
      abs_mul, abs_neg, abs_of_nonneg (by linarith [hy.1] : 0 ≤ y - wbar M)]
    exact mul_le_mul_of_nonneg_right (by linarith [hy.2]) hδ0
  | succ d ih =>
    intro hd y hy
    have e : N - d = (N - (d + 1)) + 1 := by omega
    set i := N - (d + 1) with hi
    have ih' := ih (by omega)
    rw [e] at ih'
    have hEle : (M.C + (d : ℝ) * ε) * q ^ d * δ ≤ (M.C + ((d + 1 : ℕ) : ℝ) * ε) * q ^ (d + 1) * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ0
      push_cast
      have h1 : q ^ d ≤ q ^ (d + 1) := pow_le_pow_right₀ hq1 (Nat.le_succ d)
      have h2 : 0 ≤ q ^ d := pow_nonneg (by linarith) d
      have h3 : M.C + (d : ℝ) * ε ≤ M.C + ((d : ℝ) + 1) * ε := by nlinarith
      exact mul_le_mul h3 h1 h2 (by positivity)
    rcases le_or_gt (grid M N (i + 1)) y with hy1 | hy1
    · exact le_trans (ih' y ⟨hy1, hy.2⟩) hEle
    · -- `y` lies in the cell `[x_i, x_{i+1})`
      have hx0 := grid_nonneg M N (i + 1)
      have hxw := grid_le_wbar M N (i + 1) hN (by omega)
      have hk := slopeAdj_close hM obj (VgN M obj g N) (VgN M obj g' N) (grid M N (i + 1)) hx0
        ((M.C + (d : ℝ) * ε) * q ^ d * δ)
        (fun z hz1 hz2 => ih' z ⟨hz1, by linarith⟩)
        (VgN_incr_bdd hM obj g N hN (i + 1) (by omega))
      have a1 := VgN_piece' M obj g N (i + 1) (by omega) (by omega) y
        ⟨by simpa using hy.1, hy1.le⟩
      have a2 := VgN_piece' M obj g' N (i + 1) (by omega) (by omega) y
        ⟨by simpa using hy.1, hy1.le⟩
      have hb := ih' (grid M N (i + 1)) ⟨le_rfl, by linarith⟩
      rw [a1, a2]
      have hlen : 0 ≤ grid M N (i + 1) - y ∧ grid M N (i + 1) - y ≤ ε := by
        constructor
        · linarith
        · have := grid_succ M N i
          have := hy.1
          simp only [Nat.cast_add, Nat.cast_one] at *
          linarith
      set E := (M.C + (d : ℝ) * ε) * q ^ d * δ with hE
      have hE0 : 0 ≤ E := by rw [hE]; have := pow_nonneg (by linarith : (0:ℝ) ≤ q) d; positivity
      set k1 := slopeAdj M obj (VgN M obj g N) (grid M N (i + 1))
      set k2 := slopeAdj M obj (VgN M obj g' N) (grid M N (i + 1))
      set L := grid M N (i + 1) - y
      have key : |VgN M obj g N (grid M N (i + 1)) + (-g + k1) * (y - grid M N (i + 1)) -
          (VgN M obj g' N (grid M N (i + 1)) + (-g' + k2) * (y - grid M N (i + 1)))| ≤
          E + (δ + M.lam * (2 * E)) * ε := by
        have : VgN M obj g N (grid M N (i + 1)) + (-g + k1) * (y - grid M N (i + 1)) -
          (VgN M obj g' N (grid M N (i + 1)) + (-g' + k2) * (y - grid M N (i + 1))) =
          (VgN M obj g N (grid M N (i + 1)) - VgN M obj g' N (grid M N (i + 1))) +
            ((g - g') - (k1 - k2)) * L := by rw [show L = grid M N (i + 1) - y from rfl]; ring
        rw [this]
        refine le_trans (abs_add_le _ _) (add_le_add hb ?_)
        rw [abs_mul, abs_of_nonneg hlen.1]
        have : |(g - g') - (k1 - k2)| ≤ δ + M.lam * (2 * E) :=
          le_trans (abs_sub _ _) (add_le_add le_rfl hk)
        exact mul_le_mul this hlen.2 hlen.1 (by positivity)
      refine le_trans key ?_
      -- `E + (δ + 2λE) ε ≤ (C + (d+1) ε) q^(d+1) δ`
      rw [hE]
      push_cast
      have hqd : 1 ≤ q ^ d := one_le_pow₀ hq1
      have : (M.C + ↑d * ε) * q ^ d * δ + (δ + M.lam * (2 * ((M.C + ↑d * ε) * q ^ d * δ))) * ε =
          (M.C + ↑d * ε) * q ^ d * δ * q + δ * ε := by rw [hq]; ring
      rw [this, pow_succ]
      have h5 : δ * ε ≤ ε * q ^ d * q * δ := by
        have h7 : 1 ≤ q ^ d * q := one_le_mul_of_one_le_of_one_le hqd hq1
        have h6 : 0 ≤ ε * δ := mul_nonneg hε hδ0
        have := mul_le_mul_of_nonneg_left h7 h6
        linarith [show ε * δ * (q ^ d * q) = ε * q ^ d * q * δ by ring]
      have h8 : (M.C + (↑d + 1) * ε) * (q ^ d * q) * δ =
          (M.C + ↑d * ε) * q ^ d * δ * q + ε * q ^ d * q * δ := by ring
      linarith

lemma K0_lip {M : Model} (hM : M.Standing) (obj : Objective) (N : ℕ) (hN : 1 ≤ N) (g g' : ℝ) :
    |KgN M obj g N 0 - KgN M obj g' N 0| ≤
      M.lam * (2 * ((M.C + wbar M) * Real.exp (2 * M.lam * wbar M))) * |g - g'| := by
  have hC := hM.C_pos
  have hl := hM.lam_pos
  have hw := wbar_nonneg M
  have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hε : 0 ≤ wbar M / N := div_nonneg hw hNpos.le
  -- the bound at `i = 0`
  have hb : ∀ y ∈ Icc (0:ℝ) (wbar M + M.C), |VgN M obj g N y - VgN M obj g' N y| ≤
      (M.C + wbar M) * Real.exp (2 * M.lam * wbar M) * |g - g'| := by
    intro y hy
    have h := VgN_lip_g hM obj N hN g g' 0 (Nat.zero_le _) y (by rw [grid_zero]; exact hy)
    refine le_trans h (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
    simp only [Nat.sub_zero]
    have e1 : (N : ℝ) * (wbar M / N) = wbar M := by field_simp
    rw [e1]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    have h1 : 1 + 2 * M.lam * (wbar M / N) ≤ Real.exp (2 * M.lam * (wbar M / N)) := by
      have := Real.add_one_le_exp (2 * M.lam * (wbar M / N)); linarith
    calc (1 + 2 * M.lam * (wbar M / N)) ^ N ≤ Real.exp (2 * M.lam * (wbar M / N)) ^ N :=
          pow_le_pow_left₀ (by positivity) h1 N
      _ = Real.exp (2 * M.lam * wbar M) := by
          rw [← Real.exp_nat_mul]; congr 1; field_simp
  unfold KgN
  simp only [if_true]
  have := slopeAdj_close hM obj (VgN M obj g N) (VgN M obj g' N) 0 le_rfl
    ((M.C + wbar M) * Real.exp (2 * M.lam * wbar M) * |g - g'|)
    (fun y hy1 hy2 => hb y ⟨hy1, by linarith⟩)
    (by have := VgN_incr_bdd hM obj g N hN 0 (Nat.zero_le _); rwa [grid_zero] at this)
  calc _ ≤ _ := this
    _ = _ := by ring

lemma K_top_zero {M : Model} (hM : M.Standing) (obj : Objective) :
    ∀ N : ℕ, 1 ≤ N → ∀ w ∈ Icc 0 (wbar M + M.C), KgN M obj (deriv M.U 0) N w = 0 := by
  intro N _ w _
  set g := deriv M.U 0 with hg
  have hl := hM.lam_pos
  -- the slope adjustment of the line `−(w − w̄) g` vanishes at every `x ≥ 0`
  have hslope : ∀ x : ℝ, 0 ≤ x → slopeAdj M obj (fun w => -(w - wbar M) * g) x = 0 := by
    intro x hx
    have hle : innerMax M obj (fun w => -(w - wbar M) * g) x ≤ 0 := by
      apply csSup_le ((nonempty_Icc.2 (Gamma_nonneg M x)).image _)
      rintro _ ⟨p, hp, rfl⟩
      have h1 := v_le hM obj p ⟨hp.1, le_trans hp.2 (Gamma_le hM x)⟩
      have h2 := mul_nonneg (alpha_nonneg obj) (c_nonneg hM x hx)
      show v M obj p - alpha obj * M.c x + -(x + tOf M p - wbar M) * g - -(x - wbar M) * g ≤ 0
      nlinarith
    unfold slopeAdj; rw [max_eq_right hle, mul_zero]
  have hV : ∀ k, VStep M obj g N k = fun w => -(w - wbar M) * g := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      funext w
      show (if grid M N (N - (k + 1)) ≤ w ∧ w < grid M N (N - k) then
          VStep M obj g N k (grid M N (N - k)) +
            (-g + slopeAdj M obj (VStep M obj g N k) (grid M N (N - k))) * (w - grid M N (N - k))
        else VStep M obj g N k w) = _
      rw [ih, hslope _ (grid_nonneg M N _)]
      split_ifs <;> ring
  have hK : ∀ k, KStep M obj g N k = fun _ => 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      funext w
      show (if grid M N (N - (k + 1)) < w ∧ w ≤ grid M N (N - k) then
          slopeAdj M obj (VStep M obj g N k) (grid M N (N - k)) else KStep M obj g N k w) = 0
      rw [ih, hV k, hslope _ (grid_nonneg M N _)]
      split_ifs <;> rfl
  unfold KgN
  split_ifs
  · rw [VgN, hV N]; exact hslope 0 le_rfl
  · rw [hK N]

lemma gN_spec {M : Model} (hM : M.Standing) (obj : Objective) (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ gN M obj N ∧ KgN M obj (gN M obj N) N 0 = gN M obj N := by
  have hC := hM.C_pos
  have hU0 : 0 ≤ deriv M.U 0 := hM.deriv_U_nonneg 0 ⟨le_rfl, hC.le⟩
  set Λ := M.lam * (2 * ((M.C + wbar M) * Real.exp (2 * M.lam * wbar M))) with hΛ
  have hΛ0 : 0 ≤ Λ := by
    have := wbar_nonneg M; have := hM.lam_pos; rw [hΛ]; positivity
  have hcont : Continuous (fun g => KgN M obj g N 0) := by
    apply (LipschitzWith.continuous (K := Λ.toNNReal))
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hΛ0]
    exact K0_lip hM obj N hN x y
  set S := {g : ℝ | 0 ≤ g ∧ KgN M obj g N 0 ≤ g} with hS
  have hbdd : BddBelow S := ⟨0, fun x hx => hx.1⟩
  have hmemU : deriv M.U 0 ∈ S := by
    refine ⟨hU0, ?_⟩
    rw [K_top_zero hM obj N hN 0 ⟨le_rfl, by linarith [wbar_nonneg M]⟩]; exact hU0
  have hcl : IsClosed S :=
    (isClosed_le continuous_const continuous_id).inter (isClosed_le hcont continuous_id)
  have hmem : gN M obj N ∈ S := hcl.csInf_mem ⟨_, hmemU⟩ hbdd
  refine ⟨hmem.1, le_antisymm hmem.2 ?_⟩
  by_contra hlt
  push Not at hlt
  set g0 := gN M obj N
  set k0 := KgN M obj g0 N 0
  have hk0 : 0 ≤ k0 := KgN_nonneg hM obj g0 N 0
  have hg0 : 0 < g0 := lt_of_le_of_lt hk0 hlt
  set η := min g0 ((g0 - k0) / (2 * (1 + Λ))) with hη
  have hη0 : 0 < η := lt_min hg0 (div_pos (by linarith) (by linarith))
  have hη1 : η ≤ g0 := min_le_left _ _
  have hη2 : η ≤ (g0 - k0) / (2 * (1 + Λ)) := min_le_right _ _
  have hη3 : η * (1 + Λ) < g0 - k0 := by
    have := (le_div_iff₀ (by linarith : (0:ℝ) < 2 * (1 + Λ))).1 hη2
    nlinarith
  have hin : g0 - η ∈ S := by
    refine ⟨by linarith, ?_⟩
    have h := K0_lip hM obj N hN (g0 - η) g0
    rw [show g0 - η - g0 = -η by ring, abs_neg, abs_of_pos hη0] at h
    have := (abs_le.1 h).2
    nlinarith
  have := csInf_le hbdd hin
  have hg0eq : sInf S = g0 := rfl
  linarith

/-- If every slope of `a·V + b·id` is nonnegative, it is monotone on `[0, ∞)`. -/
lemma lin_mono {M : Model} (obj : Objective) (g : ℝ) (N : ℕ) (hN : 1 ≤ N) (a b : ℝ)
    (hcell : ∀ i, 1 ≤ i → i ≤ N → 0 ≤ a * (-g + slopeAdj M obj (VgN M obj g N) (grid M N i)) + b)
    (hbase : 0 ≤ a * (-g) + b) :
    MonotoneOn (fun y => a * VgN M obj g N y + b * y) (Ici 0) := by
  suffices H : ∀ d ≤ N, MonotoneOn (fun y => a * VgN M obj g N y + b * y) (Ici (grid M N (N - d))) by
    have := H N le_rfl; rwa [Nat.sub_self, grid_zero] at this
  intro d
  induction d with
  | zero =>
    intro _ x hx y hy hxy
    have hx' : grid M N N ≤ x := by simpa using hx
    have hy' : grid M N N ≤ y := by simpa using hy
    simp only
    rw [VgN_right M obj g N x hx', VgN_right M obj g N y hy']
    nlinarith
  | succ d ih =>
    intro hd
    have h1 := ih (by omega)
    have e : N - d = (N - (d + 1)) + 1 := by omega
    rw [e] at h1
    set i := N - (d + 1)
    apply monotoneOn_glue (grid_mono M N (Nat.le_succ i))
      (s := a * (-g + slopeAdj M obj (VgN M obj g N) (grid M N (i + 1))) + b) _
      (hcell (i + 1) (by omega) (by omega)) h1
    intro x hx
    have a1 := VgN_piece' M obj g N (i + 1) (by omega) (by omega) x (by simpa using hx)
    rw [a1]; ring

end WTPAux

theorem aux_bounds (M : Model) (hM : M.Standing) (obj : Objective) (j : ℕ) (hj : 1 ≤ j) :
    0 ≤ gbar M obj ∧ gN M obj (2 ^ j) ≤ gbar M obj ∧
    KgN M obj (gbar M obj) (2 ^ j) 0 ≤ gN M obj (2 ^ j) ∧
    gN M obj (2 ^ j) - M.lam * (2 * ((M.C + wbar M) * Real.exp (2 * M.lam * wbar M))) *
      (gbar M obj - gN M obj (2 ^ j)) ≤ KgN M obj (gbar M obj) (2 ^ j) 0 := by
  obtain ⟨h5a, h5b, -, h5d⟩ := proposition_5 M hM obj
  have hN : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have hle : gN M obj (2 ^ j) ≤ gbar M obj := by
    apply ge_of_tendsto h5d
    rw [Filter.eventually_atTop]
    refine ⟨j, fun k hk => ?_⟩
    induction k, hk using Nat.le_induction with
    | base => exact le_rfl
    | succ k hk ih => exact le_trans ih (h5b k (by omega))
  have hg0 : 0 ≤ gN M obj (2 ^ j) := h5a j hj
  obtain ⟨-, hbind⟩ := WTPAux.gN_spec hM obj (2 ^ j) hN
  have h0I : (0:ℝ) ∈ Icc 0 (wbar M + M.C) := ⟨le_rfl, by linarith [WTPAux.wbar_nonneg M, hM.C_pos]⟩
  have hup : KgN M obj (gbar M obj) (2 ^ j) 0 ≤ gN M obj (2 ^ j) := by
    rcases eq_or_lt_of_le hle with e | hlt
    · rw [← e, hbind]
    · have := lemma_3 M hM obj (2 ^ j) hN _ _ hg0 hlt 0 h0I
      rw [hbind] at this; exact this
  refine ⟨le_trans hg0 hle, hle, hup, ?_⟩
  have h := WTPAux.K0_lip hM obj (2 ^ j) hN (gN M obj (2 ^ j)) (gbar M obj)
  rw [hbind, abs_sub_comm (gN M obj (2 ^ j)) (gbar M obj),
    abs_of_nonneg (show 0 ≤ gbar M obj - gN M obj (2 ^ j) by linarith)] at h
  have := (abs_le.1 h).2
  linarith

theorem solution (M : Model) (hM : M.Standing) (obj : Objective) :
    ∀ j : ℕ, 1 ≤ j →
      AntitoneOn (VgN M obj (gbar M obj) (2 ^ j)) (Icc 0 (wbar M + M.C)) ∧
      ConcaveOn ℝ (Icc 0 (wbar M + M.C)) (VgN M obj (gbar M obj) (2 ^ j)) ∧
      ∀ x ∈ Icc 0 (wbar M + M.C), ∀ y ∈ Icc 0 (wbar M + M.C),
        |VgN M obj (gbar M obj) (2 ^ j) x - VgN M obj (gbar M obj) (2 ^ j) y|
          ≤ gbar M obj * |x - y| := by
  intro j hj
  have hN : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  obtain ⟨hgb0, hle, hup, -⟩ := aux_bounds M hM obj j hj
  set gb := gbar M obj
  set N := 2 ^ j
  -- all slope adjustments lie in `[0, ḡ]`
  have hK0 : slopeAdj M obj (VgN M obj gb N) (grid M N 0) ≤ gb := by
    have : KgN M obj gb N 0 = slopeAdj M obj (VgN M obj gb N) (grid M N 0) := by
      simp [KgN, WTPAux.grid_zero]
    linarith
  have hκ : ∀ i, 1 ≤ i → i ≤ N → slopeAdj M obj (VgN M obj gb N) (grid M N i) ≤ gb := fun i _ hi =>
    le_trans (WTPAux.kappa_anti hM obj gb N hN 0 i (Nat.zero_le _) hi) hK0
  have hanti := WTPAux.lin_mono obj gb N hN (-1) 0
    (fun i hi1 hiN => by have := hκ i hi1 hiN; linarith) (by linarith)
  have hlip := WTPAux.lin_mono obj gb N hN 1 gb
    (fun i _ _ => by have := WTPAux.slopeAdj_nonneg hM obj (VgN M obj gb N) (grid M N i); linarith)
    (by linarith)
  have hA : AntitoneOn (VgN M obj gb N) (Icc 0 (wbar M + M.C)) := by
    intro x hx y hy hxy
    have := hanti (mem_Ici.2 hx.1) (mem_Ici.2 hy.1) hxy
    simp only at this; linarith
  refine ⟨hA, (proposition_4 M hM obj gb hgb0 N hN).1, fun x hx y hy => ?_⟩
  rcases le_total x y with hxy | hxy
  · have h1 := hA hx hy hxy
    have h2 := hlip (mem_Ici.2 hx.1) (mem_Ici.2 hy.1) hxy
    simp only at h2
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have h1 := hA hy hx hxy
    have h2 := hlip (mem_Ici.2 hy.1) (mem_Ici.2 hx.1) hxy
    simp only at h2
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linarith
