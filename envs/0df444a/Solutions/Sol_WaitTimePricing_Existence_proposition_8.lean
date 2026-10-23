-- Prove2me | solution 1 for WaitTimePricing.Existence.proposition_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T10:33:09.181326+00:00
-- url     : https://prove2.me/submissions/becf2cdb-e388-43d0-b821-5d57e64e8e35

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting
import Definitions.Def_WaitTimePricing_Existence_Algorithm1
import Theorems.Thm_WaitTimePricing_Existence_proposition_6

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


lemma tOf_cont {M : Model} (hM : M.Standing) : ContinuousOn (tOf M) (Icc 0 (deriv M.U 0)) := by
  have hC := hM.C_pos
  rw [Metric.continuousOn_iff]
  intro p0 hp0 ε hε
  have hm := tOf_mem hM p0 hp0.2
  set τ0 := tOf M p0 with hτ0
  -- lower side
  obtain ⟨δ1, hδ1, hlow⟩ : ∃ δ1 > 0, ∀ p, p ≤ deriv M.U 0 → p < p0 + δ1 → τ0 - ε < tOf M p := by
    by_cases h : τ0 - ε / 2 ≤ 0
    · exact ⟨1, one_pos, fun p _ _ => by linarith [tOf_nonneg M p]⟩
    · push Not at h
      have hs : τ0 - ε / 2 ∈ Icc 0 M.C := ⟨h.le, by linarith [hm.1.2]⟩
      have hlt : deriv M.U τ0 < deriv M.U (τ0 - ε / 2) :=
        (dU_strictAnti hM) hs hm.1 (by linarith)
      refine ⟨deriv M.U (τ0 - ε / 2) - p0, by linarith [hm.2], fun p _ hp => ?_⟩
      have : τ0 - ε / 2 ≤ tOf M p := le_csSup (tOf_bdd M p) ⟨hs, by linarith⟩
      linarith
  -- upper side
  obtain ⟨δ2, hδ2, hup⟩ : ∃ δ2 > 0, ∀ p, 0 ≤ p → p ≤ deriv M.U 0 → p0 - δ2 < p →
      tOf M p < τ0 + ε := by
    by_cases h : M.C ≤ τ0 + ε / 2
    · exact ⟨1, one_pos, fun p _ _ _ => by linarith [tOf_le_C hM p]⟩
    · push Not at h
      have hs : τ0 + ε / 2 ∈ Icc 0 M.C := ⟨by linarith [hm.1.1], h.le⟩
      have hlt : deriv M.U (τ0 + ε / 2) < p0 := tOf_gt p0 _ hs (by linarith)
      refine ⟨p0 - deriv M.U (τ0 + ε / 2), by linarith, fun p hp0' hpU hp => ?_⟩
      have : tOf M p ≤ τ0 + ε / 2 := by
        unfold tOf
        apply csSup_le (show ({t ∈ Icc 0 M.C | p ≤ deriv M.U t} : Set ℝ).Nonempty from
          ⟨0, ⟨le_rfl, hC.le⟩, hpU⟩)
        rintro t ⟨ht, hpt⟩
        by_contra hgt; push Not at hgt
        have := (dU_strictAnti hM) hs ht hgt
        linarith
      linarith
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun p hp hd => ?_⟩
  rw [Real.dist_eq] at hd ⊢
  have hd1 := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 := lt_of_lt_of_le hd (min_le_right _ _)
  rw [abs_lt] at hd1 hd2 ⊢
  exact ⟨by linarith [hlow p hp.2 (by linarith)], by linarith [hup p hp.1 hp.2 (by linarith)]⟩

lemma H_pos {M : Model} (hM : M.Standing) (p : ℝ) (hp : p < deriv M.U 0) : 0 < H M p := by
  have hC := hM.C_pos
  have hcont : ContinuousAt (deriv M.U) 0 := (dU_diff hM).continuous.continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hδ'⟩ := hcont (deriv M.U 0 - p) (by linarith)
  set s := min (δ / 2) M.C with hs
  have hs0 : 0 < s := lt_min (by linarith) hC
  have hsC : s ≤ M.C := min_le_right _ _
  have hsd : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hUs : p < deriv M.U s := by
    have := hδ' (show dist s 0 < δ by rw [Real.dist_eq, sub_zero, abs_of_pos hs0]; exact hsd)
    rw [Real.dist_eq, abs_lt] at this; linarith
  have hmv := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc (0:ℝ) s)
    (U_diff hM).continuous.continuousOn (U_diff hM).differentiableOn (C := deriv M.U s)
    (fun x hx => by
      rw [interior_Icc] at hx
      exact (dU_strictAnti hM).antitoneOn ⟨hx.1.le, by linarith [hx.2]⟩ ⟨hs0.le, hsC⟩ hx.2.le)
    0 ⟨le_rfl, hs0.le⟩ s ⟨hs0.le, le_rfl⟩ hs0.le
  rw [hM.U_zero, sub_zero, sub_zero] at hmv
  have := H_ge hM p hp.le s ⟨hs0.le, hsC⟩
  unfold H
  nlinarith

lemma H_strictAnti {M : Model} (hM : M.Standing) (p q : ℝ) (hpq : p < q)
    (hq : q ≤ deriv M.U 0) : H M q < H M p := by
  rcases eq_or_lt_of_le (tOf_nonneg M q) with h0 | hpos
  · have : H M q = 0 := by unfold H; rw [← h0, hM.U_zero]; ring
    rw [this]; exact H_pos hM p (by linarith)
  · have h1 := H_ge hM p (by linarith) (tOf M q) ⟨tOf_nonneg M q, tOf_le_C hM q⟩
    unfold H at *
    nlinarith

lemma Gamma_cont {M : Model} (hM : M.Standing) : ContinuousOn (Gamma M) (Icc 0 (wbar M)) := by
  rw [Metric.continuousOn_iff]
  intro x0 hx0 ε hε
  obtain ⟨hmem, hle⟩ := Gamma_spec hM x0 hx0
  set γ0 := Gamma M x0
  have hcc : ContinuousAt M.c x0 := (c_diff hM).continuous.continuousAt
  rw [Metric.continuousAt_iff] at hcc
  -- lower side
  obtain ⟨δ1, hδ1, hlow⟩ : ∃ δ1 > 0, ∀ x ∈ Icc 0 (wbar M), dist x x0 < δ1 → γ0 - ε < Gamma M x := by
    by_cases h : γ0 - ε / 2 ≤ 0
    · exact ⟨1, one_pos, fun x _ _ => by linarith [Gamma_nonneg M x]⟩
    · push Not at h
      have hHq : H M γ0 < H M (γ0 - ε / 2) := H_strictAnti hM _ _ (by linarith) hmem.1.2
      have h2 : M.c x0 ≤ H M γ0 := by unfold H; linarith [hmem.2]
      obtain ⟨δ, hδ, hδ'⟩ := hcc (H M (γ0 - ε / 2) - M.c x0) (by linarith)
      refine ⟨δ, hδ, fun x hx hd => ?_⟩
      have := hδ' hd
      rw [Real.dist_eq, abs_lt] at this
      have hin := (Gamma_spec hM x hx).2 (γ0 - ε / 2) ⟨⟨h.le, by linarith [hmem.1.2]⟩, by
        have e1 := hHq; have e2 := h2; have e3 := this.2; unfold H at e1 e2 e3; linarith⟩
      linarith
  -- upper side
  obtain ⟨δ2, hδ2, hup⟩ : ∃ δ2 > 0, ∀ x ∈ Icc 0 (wbar M), dist x x0 < δ2 → Gamma M x < γ0 + ε := by
    by_cases h : deriv M.U 0 ≤ γ0 + ε / 2
    · exact ⟨1, one_pos, fun x _ _ => by linarith [Gamma_le hM x]⟩
    · push Not at h
      have hq : ¬ (0 ≤ M.U (tOf M (γ0 + ε / 2)) - (γ0 + ε / 2) * tOf M (γ0 + ε / 2) - M.c x0) := by
        intro hh
        have := hle (γ0 + ε / 2) ⟨⟨by linarith [hmem.1.1], h.le⟩, hh⟩
        linarith
      push Not at hq
      obtain ⟨δ, hδ, hδ'⟩ := hcc (M.c x0 - H M (γ0 + ε / 2)) (by unfold H; linarith)
      refine ⟨δ, hδ, fun x hx hd => ?_⟩
      have := hδ' hd
      rw [Real.dist_eq, abs_lt] at this
      have : Gamma M x ≤ γ0 + ε / 2 := by
        obtain ⟨hmx, -⟩ := Gamma_spec hM x hx
        by_contra hgt; push Not at hgt
        have := H_anti hM (γ0 + ε / 2) (Gamma M x) hgt.le hmx.1.2
        have := hmx.2
        unfold H at *
        linarith
      linarith
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun x hx hd => ?_⟩
  have a := hlow x hx (lt_of_lt_of_le hd (min_le_left _ _))
  have b := hup x hx (lt_of_lt_of_le hd (min_le_right _ _))
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith

lemma Gamma_wbar {M : Model} (hM : M.Standing) : Gamma M (wbar M) = 0 := by
  obtain ⟨hwb, hUc, -⟩ := wbar_spec hM
  obtain ⟨hmem, -⟩ := Gamma_spec hM (wbar M) ⟨hwb.le, le_rfl⟩
  apply le_antisymm _ (Gamma_nonneg M _)
  by_contra hpos; push Not at hpos
  have := H_strictAnti hM 0 (Gamma M (wbar M)) hpos hmem.1.2
  rw [H_zero hM] at this
  have := hmem.2
  unfold H at *
  linarith

lemma v_cont {M : Model} (hM : M.Standing) (obj : Objective) :
    ContinuousOn (v M obj) (Icc 0 (deriv M.U 0)) := by
  cases obj with
  | revenue => exact continuousOn_id.mul (tOf_cont hM)
  | welfare => exact (U_diff hM).continuous.comp_continuousOn (tOf_cont hM)


lemma alpha_le_one (obj : Objective) : alpha obj ≤ 1 := by
  cases obj <;> simp [alpha]

/-- Joint continuity of the inner maximum in the value function (uniform metric on
`[0, w̄ + C]`) and the state `x ∈ [0, w̄]`, at a Lipschitz value function `V`. -/
lemma innerMax_joint {M : Model} (hM : M.Standing) (obj : Objective) (V : ℝ → ℝ) (L : ℝ)
    (hL0 : 0 ≤ L)
    (hVL : ∀ x ∈ Icc 0 (wbar M + M.C), ∀ y ∈ Icc 0 (wbar M + M.C), |V x - V y| ≤ L * |x - y|)
    (x0 : ℝ) (hx0 : x0 ∈ Icc 0 (wbar M)) :
    ∀ ε > 0, ∃ δ > 0, ∀ W : ℝ → ℝ, (∀ y ∈ Icc 0 (wbar M + M.C), |W y - V y| < δ) →
      ∀ x ∈ Icc 0 (wbar M), |x - x0| < δ →
        |innerMax M obj W x - innerMax M obj V x0| < ε := by
  intro ε hε
  have hC := hM.C_pos
  set P := Icc 0 (deriv M.U 0) with hP
  set I := Icc 0 (wbar M + M.C) with hI
  have htI : ∀ x ∈ Icc 0 (wbar M), ∀ p, x + tOf M p ∈ I := fun x hx p =>
    ⟨by linarith [hx.1, tOf_nonneg M p], by linarith [hx.2, tOf_le_C hM p]⟩
  have hxI : ∀ x ∈ Icc 0 (wbar M), x ∈ I := fun x hx => ⟨hx.1, by linarith [hx.2]⟩
  set F0 : ℝ → ℝ := fun p => v M obj p - alpha obj * M.c x0 + V (x0 + tOf M p) - V x0 with hF0
  have hVc : ContinuousOn V I := by
    rw [Metric.continuousOn_iff]
    intro a ha e he
    refine ⟨e / (L + 1), div_pos he (by linarith), fun b hb hd => ?_⟩
    rw [Real.dist_eq] at hd ⊢
    have := hVL b hb a ha
    have h2 : L * |b - a| ≤ L * (e / (L + 1)) := mul_le_mul_of_nonneg_left hd.le hL0
    have h3 : L * (e / (L + 1)) < e := by
      rw [mul_div_assoc']; rw [div_lt_iff₀ (by linarith)]; nlinarith
    linarith
  have hF0c : ContinuousOn F0 P := by
    have h1 : ContinuousOn (fun p => V (x0 + tOf M p)) P :=
      hVc.comp (continuousOn_const.add (tOf_cont hM)) (fun p _ => htI x0 hx0 p)
    exact (((v_cont hM obj).sub continuousOn_const).add h1).sub continuousOn_const
  have hF0u := isCompact_Icc.uniformContinuousOn_of_continuous hF0c
  rw [Metric.uniformContinuousOn_iff] at hF0u
  obtain ⟨δ1, hδ1, hu⟩ := hF0u (ε / 3) (by linarith)
  obtain ⟨Bf, hBf⟩ := (isCompact_Icc.image_of_continuousOn hF0c).bddAbove
  have hGc := Gamma_cont hM
  rw [Metric.continuousOn_iff] at hGc
  obtain ⟨δ2, hδ2, hG⟩ := hGc x0 hx0 δ1 hδ1
  have hcc : ContinuousAt M.c x0 := (c_diff hM).continuous.continuousAt
  rw [Metric.continuousAt_iff] at hcc
  obtain ⟨δ3, hδ3, hcδ⟩ := hcc (ε / 9) (by linarith)
  set δ := min (min δ2 δ3) (ε / (9 * (L + 1))) with hδ
  have hδ4 : 0 < ε / (9 * (L + 1)) := div_pos hε (by linarith)
  refine ⟨δ, lt_min (lt_min hδ2 hδ3) hδ4, fun W hW x hx hxd => ?_⟩
  have hd2 : |x - x0| < δ2 := lt_of_lt_of_le hxd (le_trans (min_le_left _ _) (min_le_left _ _))
  have hd3 : |x - x0| < δ3 := lt_of_lt_of_le hxd (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδle : δ ≤ ε / (9 * (L + 1)) := min_le_right _ _
  have hδL : δ * (1 + L) ≤ ε / 9 := by
    have : ε / (9 * (L + 1)) * (1 + L) = ε / 9 := by field_simp; ring
    rw [← this]; exact mul_le_mul_of_nonneg_right hδle (by linarith)
  set FW : ℝ → ℝ := fun p => v M obj p - alpha obj * M.c x + W (x + tOf M p) - W x with hFW
  -- uniform closeness of the integrands
  have hclose : ∀ p, |FW p - F0 p| < ε / 3 := by
    intro p
    have hc := hcδ (show dist x x0 < δ3 by rw [Real.dist_eq]; exact hd3)
    rw [Real.dist_eq] at hc
    have h1 : |W (x + tOf M p) - V (x0 + tOf M p)| < ε / 9 := by
      have a1 := hW _ (htI x hx p)
      have a2 := hVL _ (htI x hx p) _ (htI x0 hx0 p)
      rw [show x + tOf M p - (x0 + tOf M p) = x - x0 by ring] at a2
      have a3 : L * |x - x0| ≤ L * δ := mul_le_mul_of_nonneg_left hxd.le hL0
      calc |W (x + tOf M p) - V (x0 + tOf M p)|
          ≤ |W (x + tOf M p) - V (x + tOf M p)| + |V (x + tOf M p) - V (x0 + tOf M p)| :=
            abs_sub_le _ _ _
        _ < δ + L * δ := by linarith
        _ ≤ ε / 9 := by linarith
    have h2 : |W x - V x0| < ε / 9 := by
      have a1 := hW _ (hxI x hx)
      have a2 := hVL _ (hxI x hx) _ (hxI x0 hx0)
      have a3 : L * |x - x0| ≤ L * δ := mul_le_mul_of_nonneg_left hxd.le hL0
      calc |W x - V x0| ≤ |W x - V x| + |V x - V x0| := abs_sub_le _ _ _
        _ < δ + L * δ := by linarith
        _ ≤ ε / 9 := by linarith
    have h3 : |alpha obj * (M.c x - M.c x0)| < ε / 9 := by
      rw [abs_mul, abs_of_nonneg (alpha_nonneg obj)]
      calc alpha obj * |M.c x - M.c x0| ≤ 1 * |M.c x - M.c x0| :=
            mul_le_mul_of_nonneg_right (alpha_le_one obj) (abs_nonneg _)
        _ < ε / 9 := by linarith
    have : FW p - F0 p = -(alpha obj * (M.c x - M.c x0)) + (W (x + tOf M p) - V (x0 + tOf M p))
        - (W x - V x0) := by simp only [hFW, hF0]; ring
    rw [this]
    calc |-(alpha obj * (M.c x - M.c x0)) + (W (x + tOf M p) - V (x0 + tOf M p)) - (W x - V x0)|
        ≤ |-(alpha obj * (M.c x - M.c x0))| + |W (x + tOf M p) - V (x0 + tOf M p)| + |W x - V x0| :=
          le_trans (abs_sub _ _) (add_le_add_left (abs_add_le _ _) _)
      _ < ε / 9 + ε / 9 + ε / 9 := by rw [abs_neg]; linarith
      _ = ε / 3 := by ring
  have hGx := hG x hx (by rw [Real.dist_eq]; exact hd2)
  rw [Real.dist_eq] at hGx
  have hG0 := Gamma_nonneg M x0
  have hGx0 := Gamma_nonneg M x
  have hG0le := Gamma_le hM x0
  have hGxle := Gamma_le hM x
  have hbdd0 : BddAbove (F0 '' Icc 0 (Gamma M x0)) :=
    ⟨Bf, fun _ ⟨p, hp, e⟩ => hBf ⟨p, ⟨hp.1, le_trans hp.2 hG0le⟩, e⟩⟩
  have hbddW : BddAbove (FW '' Icc 0 (Gamma M x)) := by
    refine ⟨Bf + ε / 3, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    have := hBf ⟨p, ⟨hp.1, le_trans hp.2 hGxle⟩, rfl⟩
    have := (abs_lt.1 (hclose p)).2
    linarith
  -- upper estimate
  have hup : sSup (FW '' Icc 0 (Gamma M x)) ≤ sSup (F0 '' Icc 0 (Gamma M x0)) + 2 * ε / 3 := by
    apply csSup_le ((nonempty_Icc.2 hGx0).image _)
    rintro _ ⟨p, hp, rfl⟩
    set p' := min p (Gamma M x0)
    have hp' : p' ∈ Icc 0 (Gamma M x0) := ⟨le_min hp.1 hG0, min_le_right _ _⟩
    have hpp : dist p p' < δ1 := by
      rw [Real.dist_eq]
      rcases le_total p (Gamma M x0) with h | h
      · rw [show p' = p from min_eq_left h, sub_self, abs_zero]; exact hδ1
      · rw [show p' = Gamma M x0 from min_eq_right h, abs_of_nonneg (by linarith)]
        rw [abs_lt] at hGx; linarith [hp.2]
    have h1 := hu p ⟨hp.1, le_trans hp.2 hGxle⟩ p' ⟨hp'.1, le_trans hp'.2 hG0le⟩ hpp
    rw [Real.dist_eq, abs_lt] at h1
    have h2 := le_csSup hbdd0 ⟨p', hp', rfl⟩
    have h3 := (abs_lt.1 (hclose p)).2
    linarith
  have hlow : sSup (F0 '' Icc 0 (Gamma M x0)) ≤ sSup (FW '' Icc 0 (Gamma M x)) + 2 * ε / 3 := by
    apply csSup_le ((nonempty_Icc.2 hG0).image _)
    rintro _ ⟨p, hp, rfl⟩
    set p' := min p (Gamma M x)
    have hp' : p' ∈ Icc 0 (Gamma M x) := ⟨le_min hp.1 hGx0, min_le_right _ _⟩
    have hpp : dist p p' < δ1 := by
      rw [Real.dist_eq]
      rcases le_total p (Gamma M x) with h | h
      · rw [show p' = p from min_eq_left h, sub_self, abs_zero]; exact hδ1
      · rw [show p' = Gamma M x from min_eq_right h, abs_of_nonneg (by linarith)]
        rw [abs_lt] at hGx; linarith [hp.2]
    have h1 := hu p ⟨hp.1, le_trans hp.2 hG0le⟩ p' ⟨hp'.1, le_trans hp'.2 hGxle⟩ hpp
    rw [Real.dist_eq, abs_lt] at h1
    have h2 := le_csSup hbddW ⟨p', hp', rfl⟩
    have h3 := (abs_lt.1 (hclose p')).1
    linarith
  show |sSup (FW '' Icc 0 (Gamma M x)) - sSup (F0 '' Icc 0 (Gamma M x0))| < ε
  rw [abs_lt]; constructor <;> linarith


lemma concave_upper {f : ℝ → ℝ} {l r a e b s : ℝ} (hconc : ConcaveOn ℝ (Icc l r) f)
    (ha : a ∈ Icc l r) (hb : b ∈ Icc l r) (hae : a < e) (heb : e ≤ b)
    (hlin : ∀ y ∈ Icc a e, f y = f a + s * (y - a)) : f b - f a ≤ s * (b - a) := by
  rcases eq_or_lt_of_le heb with h | h
  · rw [← h, hlin e ⟨hae.le, le_rfl⟩]; ring_nf; rfl
  · have h1 := hconc.slope_anti_adjacent ha hb hae h
    rw [hlin e ⟨hae.le, le_rfl⟩] at h1
    rw [show (f a + s * (e - a) - f a) / (e - a) = s by
      rw [show f a + s * (e - a) - f a = s * (e - a) by ring, mul_div_assoc,
        div_self (ne_of_gt (sub_pos.2 hae)), mul_one]] at h1
    rw [div_le_iff₀ (by linarith)] at h1
    have := hlin e ⟨hae.le, le_rfl⟩
    nlinarith

lemma concave_lower {f : ℝ → ℝ} {l r a e b s : ℝ} (hconc : ConcaveOn ℝ (Icc l r) f)
    (ha : a ∈ Icc l r) (hb : b ∈ Icc l r) (hae : a ≤ e) (heb : e < b)
    (hlin : ∀ y ∈ Icc e b, f y = f b + s * (y - b)) : s * (b - a) ≤ f b - f a := by
  rcases eq_or_lt_of_le hae with h | h
  · rw [hlin a ⟨h.ge, by linarith⟩]; ring_nf; rfl
  · have h1 := hconc.slope_anti_adjacent ha hb h heb
    rw [hlin e ⟨le_rfl, heb.le⟩] at h1
    rw [show (f b - (f b + s * (e - b))) / (b - e) = s by
      rw [show f b - (f b + s * (e - b)) = s * (b - e) by ring, mul_div_assoc,
        div_self (ne_of_gt (sub_pos.2 heb)), mul_one]] at h1
    rw [le_div_iff₀ (by linarith)] at h1
    have := hlin e ⟨le_rfl, heb.le⟩
    nlinarith

lemma ceil_cell {M : Model} (hM : M.Standing) (N : ℕ) (hN : 1 ≤ N) (w : ℝ) (hw0 : 0 < w)
    (hw : w ≤ wbar M) :
    1 ≤ ⌈w / (wbar M / N)⌉₊ ∧ ⌈w / (wbar M / N)⌉₊ ≤ N ∧
      w ∈ Ioc (grid M N (⌈w / (wbar M / N)⌉₊ - 1)) (grid M N ⌈w / (wbar M / N)⌉₊) := by
  have hwb := (wbar_spec hM).1
  have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hε : 0 < wbar M / N := div_pos hwb hNpos
  set i := ⌈w / (wbar M / N)⌉₊ with hi
  have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 (div_pos hw0 hε)))
  have hiN : i ≤ N := by
    apply Nat.ceil_le.2
    rw [div_le_iff₀ hε]; field_simp; exact hw
  refine ⟨hi1, hiN, ?_⟩
  have hc1 := Nat.le_ceil (w / (wbar M / N))
  have hc2 := Nat.ceil_lt_add_one (div_pos hw0 hε).le
  rw [← hi] at hc1 hc2
  have hcast : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by rw [Nat.cast_sub hi1]; simp
  constructor
  · show ((i - 1 : ℕ) : ℝ) * (wbar M / N) < w
    rw [hcast]
    have : (i:ℝ) - 1 < w / (wbar M / N) := by linarith
    rwa [lt_div_iff₀ hε] at this
  · show w ≤ (i : ℝ) * (wbar M / N)
    rwa [div_le_iff₀ hε] at hc1

lemma VgN_sandwich {M : Model} (hM : M.Standing) (obj : Objective) (g : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ wbar M + M.C) :
    (-g + KgN M obj g N b) * (b - a) ≤ VgN M obj g N b - VgN M obj g N a ∧
      VgN M obj g N b - VgN M obj g N a ≤ (-g + KgN M obj g N a) * (b - a) := by
  have hC := hM.C_pos
  have hwb := (wbar_spec hM).1
  have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hε : 0 < wbar M / N := div_pos hwb hNpos
  have hwN := grid_N M N hN
  have hconc := (P_all hM obj g N hN 0 (Nat.zero_le _)).1
  rw [grid_zero] at hconc
  have haI : a ∈ Icc 0 (wbar M + M.C) := ⟨ha, by linarith⟩
  have hbI : b ∈ Icc 0 (wbar M + M.C) := ⟨by linarith, hb⟩
  constructor
  · -- lower bound
    rcases le_or_gt b (wbar M) with hbw | hbw
    · obtain ⟨hi1, hiN, hcell⟩ := ceil_cell hM N hN b (by linarith) hbw
      set i := ⌈b / (wbar M / N)⌉₊
      rw [KgN_eq_kappa hM obj g N hN b ⟨by linarith, hbw⟩]
      apply concave_lower hconc haI hbI (le_max_left a (grid M N (i - 1)))
        (max_lt hab hcell.1)
      intro y hy
      rw [VgN_piece' M obj g N i hi1 hiN y ⟨le_trans (le_max_right _ _) hy.1, le_trans hy.2 hcell.2⟩,
        VgN_piece' M obj g N i hi1 hiN b ⟨hcell.1.le, hcell.2⟩]
      ring
    · rw [KgN_right M obj g N b (by rw [hwN]; exact hbw), add_zero]
      rcases le_or_gt (wbar M) a with haw | haw
      · rw [VgN_right M obj g N b (by rw [hwN]; exact hbw.le),
          VgN_right M obj g N a (by rw [hwN]; exact haw)]
        ring_nf; rfl
      · apply concave_lower hconc haI hbI haw.le hbw
        intro y hy
        rw [VgN_right M obj g N y (by rw [hwN]; exact hy.1),
          VgN_right M obj g N b (by rw [hwN]; exact hbw.le)]
        ring
  · -- upper bound
    rcases le_or_gt (wbar M) a with haw | haw
    · rw [VgN_right M obj g N b (by rw [hwN]; linarith),
        VgN_right M obj g N a (by rw [hwN]; exact haw)]
      have := KgN_nonneg hM obj g N a
      nlinarith
    · set i := ⌊a / (wbar M / N)⌋₊ + 1 with hi
      have hfl1 := Nat.floor_le (div_nonneg ha hε.le)
      have hfl2 := Nat.lt_floor_add_one (a / (wbar M / N))
      have hiN : i ≤ N := by
        have : ⌊a / (wbar M / N)⌋₊ < N := by
          apply (Nat.floor_lt (div_nonneg ha hε.le)).2
          rw [div_lt_iff₀ hε]; field_simp; exact haw
        omega
      have hcell1 : grid M N (i - 1) ≤ a := by
        show ((i - 1 : ℕ) : ℝ) * (wbar M / N) ≤ a
        rw [hi, Nat.add_sub_cancel]
        rwa [le_div_iff₀ hε] at hfl1
      have hcell2 : a < grid M N i := by
        show ((i : ℕ) : ℝ) * (wbar M / N) > a
        rw [hi]; push_cast
        rwa [div_lt_iff₀ hε] at hfl2
      have hup := concave_upper hconc haI hbI (lt_min hcell2 hab) (min_le_right _ _)
        (s := -g + slopeAdj M obj (VgN M obj g N) (grid M N i)) (by
          intro y hy
          rw [VgN_piece' M obj g N i (by omega) hiN y ⟨le_trans hcell1 hy.1,
              le_trans hy.2 (min_le_left _ _)⟩,
            VgN_piece' M obj g N i (by omega) hiN a ⟨hcell1, hcell2.le⟩]
          ring)
      refine le_trans hup (mul_le_mul_of_nonneg_right ?_ (by linarith))
      rw [KgN_eq_kappa hM obj g N hN a ⟨ha, haw.le⟩]
      have : ⌈a / (wbar M / N)⌉₊ ≤ i := by rw [hi]; exact Nat.ceil_le_floor_add_one _
      have := kappa_anti hM obj g N hN _ i this hiN
      linarith

end WTPAux

open Filter

theorem aux_slope {A B D h : ℝ} (hh : 0 < h) (h1 : A * h ≤ D) (h2 : D ≤ B * h) :
    A ≤ D / h ∧ D / h ≤ B := by
  have a1 : A ≤ D / h := by rw [le_div_iff₀ hh]; exact h1
  have a2 : D / h ≤ B := by rw [div_le_iff₀ hh]; exact h2
  exact ⟨a1, a2⟩

theorem aux_Vbar_right (M : Model) (hM : M.Standing) (obj : Objective) (y : ℝ) (hy : wbar M ≤ y) :
    Vbar M obj y = -(y - wbar M) * gbar M obj := by
  have : (fun n : ℕ => VgN M obj (gbar M obj) (2 ^ n) y) = fun _ => -(y - wbar M) * gbar M obj := by
    funext n
    exact WTPAux.VgN_right M obj _ _ y (by rw [WTPAux.grid_N M _ Nat.one_le_two_pow]; exact hy)
  unfold Vbar; rw [this]; exact tendsto_const_nhds.limUnder_eq

theorem solution (M : Model) (hM : M.Standing) (obj : Objective) :
    (∀ w ∈ Ioc 0 (wbar M),
      HasDerivAt (Vbar M obj) (M.lam * max (innerMax M obj (Vbar M obj) w) 0 - gbar M obj) w) ∧
    HasDerivWithinAt (Vbar M obj)
      (M.lam * max (innerMax M obj (Vbar M obj) 0) 0 - gbar M obj) (Ici 0) 0 := by
  have hC := hM.C_pos
  have hl := hM.lam_pos
  have hwb := (WTPAux.wbar_spec hM).1
  obtain ⟨hpt, hunif, -, -, hlip⟩ := proposition_6 M hM obj
  set gb := gbar M obj with hgb
  set Vb := Vbar M obj with hVb
  set I := Icc 0 (wbar M + M.C) with hI
  have h0I : (0:ℝ) ∈ I := ⟨le_rfl, by linarith⟩
  have hg0 : 0 ≤ gb := by
    have h := hlip (wbar M + M.C) ⟨by linarith, le_rfl⟩ 0 h0I
    rw [sub_zero, abs_of_pos (by linarith : (0:ℝ) < wbar M + M.C)] at h
    have h' : 0 * (wbar M + M.C) ≤ gb * (wbar M + M.C) := by
      rw [zero_mul]; exact le_trans (abs_nonneg _) h
    exact le_of_mul_le_mul_right h' (by linarith)
  set κt : ℝ → ℝ := fun s => if s ≤ wbar M then slopeAdj M obj Vb s else 0 with hκt
  -- continuity of `s ↦ slopeAdj V^ḡ s` on `[0, w̄]`
  have hC1 : ∀ w0 ∈ Icc 0 (wbar M), ∀ e > 0, ∃ δ > 0, ∀ s ∈ Icc 0 (wbar M), |s - w0| < δ →
      |slopeAdj M obj Vb s - slopeAdj M obj Vb w0| < e := by
    intro w0 hw0 e he
    obtain ⟨δ, hδ, hJ⟩ := WTPAux.innerMax_joint hM obj Vb gb hg0 hlip w0 hw0 (e / (2 * M.lam))
      (div_pos he (by linarith))
    refine ⟨δ, hδ, fun s hs hsd => ?_⟩
    have h := hJ Vb (fun y _ => by rw [sub_self, abs_zero]; exact hδ) s hs hsd
    unfold slopeAdj
    rw [← mul_sub, abs_mul, abs_of_pos hl]
    have := le_trans (abs_max_sub_max_le_abs _ _ (0:ℝ)) h.le
    calc M.lam * |max (innerMax M obj Vb s) 0 - max (innerMax M obj Vb w0) 0|
        ≤ M.lam * (e / (2 * M.lam)) := mul_le_mul_of_nonneg_left this hl.le
      _ = e / 2 := by field_simp
      _ < e := by linarith
  -- the slope adjustment vanishes at `w̄`
  have hκw : slopeAdj M obj Vb (wbar M) = 0 := by
    have hle : innerMax M obj Vb (wbar M) ≤ 0 := by
      unfold innerMax
      have e1 : Vb (wbar M + M.C) = -(wbar M + M.C - wbar M) * gb :=
        aux_Vbar_right M hM obj _ (by linarith)
      have e2 : Vb (wbar M) = -(wbar M - wbar M) * gb := aux_Vbar_right M hM obj _ le_rfl
      rw [WTPAux.Gamma_wbar hM, Icc_self, image_singleton, csSup_singleton,
        WTPAux.tOf_zero hM, e1, e2]
      have hUc := (WTPAux.wbar_spec hM).2.1
      cases obj with
      | revenue => simp [v, alpha, WTPAux.tOf_zero hM]; nlinarith
      | welfare => simp [v, alpha, WTPAux.tOf_zero hM]; rw [← hUc]; nlinarith
    unfold slopeAdj; rw [max_eq_right hle, mul_zero]
  -- continuity of `κt` at points of `[0, w̄]`, within `I`
  have hκc : ∀ w ∈ Icc 0 (wbar M), ∀ e > 0, ∃ δ > 0, ∀ s ∈ I, |s - w| < δ →
      |κt s - κt w| < e := by
    intro w hw e he
    obtain ⟨δ1, hδ1, h1⟩ := hC1 w hw e he
    obtain ⟨δ2, hδ2, h2⟩ := hC1 (wbar M) ⟨hwb.le, le_rfl⟩ e he
    refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun s hs hsd => ?_⟩
    have hκw' : κt w = slopeAdj M obj Vb w := by simp [hκt, hw.2]
    rw [hκw']
    by_cases hsw : s ≤ wbar M
    · have : κt s = slopeAdj M obj Vb s := by simp [hκt, hsw]
      rw [this]; exact h1 s ⟨hs.1, hsw⟩ (lt_of_lt_of_le hsd (min_le_left _ _))
    · have : κt s = 0 := by simp [hκt, hsw]
      rw [this, zero_sub, abs_neg, ← sub_zero (slopeAdj M obj Vb w), ← hκw]
      apply h2 w hw
      push Not at hsw
      rw [abs_lt] at hsd ⊢
      constructor <;> linarith [hw.2, min_le_right δ1 δ2]
  -- convergence of `K^ḡ_{2^n}(s)` to `κt s`
  have hKlim : ∀ s ∈ I, Tendsto (fun n : ℕ => KgN M obj gb (2 ^ n) s) atTop (nhds (κt s)) := by
    intro s hs
    by_cases hsw : s ≤ wbar M
    · have hκs : κt s = slopeAdj M obj Vb s := by simp [hκt, hsw]
      rw [hκs, Metric.tendsto_atTop]
      intro e he
      obtain ⟨δ, hδ, hJ⟩ := WTPAux.innerMax_joint hM obj Vb gb hg0 hlip s ⟨hs.1, hsw⟩
        (e / (2 * M.lam)) (div_pos he (by linarith))
      have hu := hunif
      rw [Metric.tendstoUniformlyOn_iff] at hu
      obtain ⟨n1, hn1⟩ := eventually_atTop.1 (hu δ hδ)
      obtain ⟨n2, hn2⟩ := pow_unbounded_of_one_lt (wbar M / δ) (by norm_num : (1:ℝ) < 2)
      refine ⟨max n1 n2, fun n hn => ?_⟩
      have hN : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have hNpos : (0:ℝ) < (2 ^ n : ℕ) := by exact_mod_cast (show 0 < 2 ^ n by positivity)
      have hpow : (2:ℝ) ^ n2 ≤ (2:ℝ) ^ n := pow_le_pow_right₀ (by norm_num) (le_trans (le_max_right _ _) hn)
      have hεδ : wbar M / ((2 ^ n : ℕ) : ℝ) < δ := by
        push_cast
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hδ] at hn2
        nlinarith
      rw [WTPAux.KgN_eq_kappa hM obj gb (2 ^ n) hN s ⟨hs.1, hsw⟩]
      set x := grid M (2 ^ n) ⌈s / (wbar M / ((2 ^ n : ℕ) : ℝ))⌉₊ with hx
      have hxs : x ∈ Icc 0 (wbar M) ∧ |x - s| < δ := by
        rcases eq_or_lt_of_le hs.1 with h0 | hpos
        · rw [hx, ← h0, zero_div, Nat.ceil_zero, WTPAux.grid_zero]
          exact ⟨⟨le_rfl, hwb.le⟩, by rw [sub_self, abs_zero]; exact hδ⟩
        · obtain ⟨hi1, hiN, hcell⟩ := WTPAux.ceil_cell hM (2 ^ n) hN s hpos hsw
          refine ⟨⟨WTPAux.grid_nonneg M _ _, WTPAux.grid_le_wbar M _ _ hN hiN⟩, ?_⟩
          have hsucc := WTPAux.grid_succ M (2 ^ n) (⌈s / (wbar M / ((2 ^ n : ℕ) : ℝ))⌉₊ - 1)
          rw [Nat.sub_add_cancel hi1] at hsucc
          rw [abs_lt]; constructor
          · linarith [hcell.2]
          · linarith [hcell.1]
      have h := hJ (VgN M obj gb (2 ^ n))
        (fun y hy => by
          have := hn1 n (le_trans (le_max_left _ _) hn) y hy
          rw [Real.dist_eq, abs_sub_comm] at this; exact this) x hxs.1 hxs.2
      rw [Real.dist_eq]
      unfold slopeAdj
      rw [← mul_sub, abs_mul, abs_of_pos hl]
      have := le_trans (abs_max_sub_max_le_abs _ _ (0:ℝ)) h.le
      calc M.lam * |max (innerMax M obj (VgN M obj gb (2 ^ n)) x) 0 - max (innerMax M obj Vb s) 0|
          ≤ M.lam * (e / (2 * M.lam)) := mul_le_mul_of_nonneg_left this hl.le
        _ = e / 2 := by field_simp
        _ < e := by linarith
    · have hκs : κt s = 0 := by simp [hκt, hsw]
      rw [hκs]
      push Not at hsw
      have : (fun n : ℕ => KgN M obj gb (2 ^ n) s) = fun _ => 0 := by
        funext n
        exact WTPAux.KgN_right M obj gb (2 ^ n) s
          (by rw [WTPAux.grid_N M _ Nat.one_le_two_pow]; exact hsw)
      rw [this]; exact tendsto_const_nhds
  -- limiting sandwich
  have hsand : ∀ a b, 0 ≤ a → a < b → b ≤ wbar M + M.C →
      (-gb + κt b) * (b - a) ≤ Vb b - Vb a ∧ Vb b - Vb a ≤ (-gb + κt a) * (b - a) := by
    intro a b ha hab hb
    have haI : a ∈ I := ⟨ha, by linarith⟩
    have hbI : b ∈ I := ⟨by linarith, hb⟩
    have hV : Tendsto (fun n : ℕ => VgN M obj gb (2 ^ n) b - VgN M obj gb (2 ^ n) a) atTop
        (nhds (Vb b - Vb a)) := (hpt b hbI).sub (hpt a haI)
    constructor
    · apply le_of_tendsto_of_tendsto' (((hKlim b hbI).const_add (-gb)).mul_const (b - a)) hV
      intro n
      exact (WTPAux.VgN_sandwich hM obj gb (2 ^ n) Nat.one_le_two_pow a b ha hab hb).1
    · apply le_of_tendsto_of_tendsto' hV (((hKlim a haI).const_add (-gb)).mul_const (b - a))
      intro n
      exact (WTPAux.VgN_sandwich hM obj gb (2 ^ n) Nat.one_le_two_pow a b ha hab hb).2
  have hval : ∀ w ∈ Icc 0 (wbar M),
      M.lam * max (innerMax M obj Vb w) 0 - gb = -gb + κt w := by
    intro w hw
    have : κt w = slopeAdj M obj Vb w := by simp [hκt, hw.2]
    rw [this]; unfold slopeAdj; ring
  constructor
  · intro w hw
    rw [hval w ⟨hw.1.le, hw.2⟩, hasDerivAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
    intro e he
    obtain ⟨δ, hδ, hκ⟩ := hκc w ⟨hw.1.le, hw.2⟩ (e / 2) (by linarith)
    refine ⟨min δ (min w M.C), lt_min hδ (lt_min hw.1 hC), fun y hy hyd => ?_⟩
    rw [Real.dist_eq] at hyd ⊢
    have hyd1 := lt_of_lt_of_le hyd (min_le_left _ _)
    have hyd2 := lt_of_lt_of_le hyd (le_trans (min_le_right _ _) (min_le_left _ _))
    have hyd3 := lt_of_lt_of_le hyd (le_trans (min_le_right _ _) (min_le_right _ _))
    rw [abs_lt] at hyd2 hyd3
    have hyI : y ∈ I := ⟨by linarith, by linarith [hw.2]⟩
    have hk := hκ y hyI hyd1
    rw [slope_def_field]
    rcases lt_or_gt_of_ne (show y ≠ w from hy) with hlt | hgt
    · obtain ⟨s1, s2⟩ := hsand y w hyI.1 hlt (by linarith [hw.2])
      have hq : (Vb y - Vb w) / (y - w) = (Vb w - Vb y) / (w - y) := by
        rw [← neg_sub (Vb w), ← neg_sub w, neg_div_neg_eq]
      rw [hq]
      have := aux_slope (by linarith : (0:ℝ) < w - y) s1 s2
      rw [abs_lt] at hk
      have h3 : |(Vb w - Vb y) / (w - y) - (-gb + κt w)| ≤ κt y - κt w := by
        rw [abs_le]; constructor <;> linarith [this.1, this.2]
      linarith
    · obtain ⟨s1, s2⟩ := hsand w y hw.1.le hgt hyI.2
      have := aux_slope (by linarith : (0:ℝ) < y - w) s1 s2
      rw [abs_lt] at hk
      have h3 : |(Vb y - Vb w) / (y - w) - (-gb + κt w)| ≤ κt w - κt y := by
        rw [abs_le]; constructor <;> linarith [this.1, this.2]
      linarith
  · rw [hval 0 ⟨le_rfl, hwb.le⟩, hasDerivWithinAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
    intro e he
    obtain ⟨δ, hδ, hκ⟩ := hκc 0 ⟨le_rfl, hwb.le⟩ (e / 2) (by linarith)
    refine ⟨min δ M.C, lt_min hδ hC, fun y hy hyd => ?_⟩
    rw [Real.dist_eq] at hyd ⊢
    have hy0 : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hy.2)
    have hyd1 := lt_of_lt_of_le hyd (min_le_left _ _)
    have hyd2 := lt_of_lt_of_le hyd (min_le_right _ _)
    rw [sub_zero, abs_of_pos hy0] at hyd1 hyd2
    have hyI : y ∈ I := ⟨hy0.le, by linarith⟩
    have hk := hκ y hyI (by rw [sub_zero, abs_of_pos hy0]; exact hyd1)
    rw [slope_def_field]
    obtain ⟨s1, s2⟩ := hsand 0 y le_rfl hy0 hyI.2
    have := aux_slope (by linarith : (0:ℝ) < y - 0) s1 s2
    rw [abs_lt] at hk
    have h3 : |(Vb y - Vb 0) / (y - 0) - (-gb + κt 0)| ≤ κt 0 - κt y := by
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    linarith
