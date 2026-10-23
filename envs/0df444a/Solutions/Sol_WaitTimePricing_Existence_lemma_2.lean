-- Prove2me | solution 1 for WaitTimePricing.Existence.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T09:58:38.42572+00:00
-- url     : https://prove2.me/submissions/a7251c15-fe5a-4a31-9802-332540f42bf4

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting
import Definitions.Def_WaitTimePricing_Existence_Algorithm1

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

end WTPAux

theorem solution (M : Model) (hM : M.Standing) (obj : Objective) :
    ∀ g : ℝ, 0 ≤ g → ∀ j : ℕ, 1 ≤ j → ∀ w ∈ Icc 0 (wbar M + M.C),
      VgN M obj g (2 * j) w ≤ VgN M obj g j w ∧ KgN M obj g j w ≤ KgN M obj g (2 * j) w := by
  intro g _ j hj w hw
  have hj2 : 1 ≤ 2 * j := by omega
  have hwN := WTPAux.grid_N M j hj
  have hwN2 := WTPAux.grid_N M (2 * j) hj2
  -- comparison of slope adjustments at a coarse grid point
  have kstep : ∀ i ≤ j,
      MonotoneOn (fun y => VgN M obj g (2 * j) y - VgN M obj g j y) (Ici (grid M j i)) →
      slopeAdj M obj (VgN M obj g j) (grid M j i) ≤
        slopeAdj M obj (VgN M obj g (2 * j)) (grid M j i) := by
    intro i hi hmono
    apply WTPAux.slopeAdj_mono_of_incr hM obj _ _ _ (WTPAux.grid_nonneg M j i)
    · intro y hy _
      have := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hy) hy
      simp only at this; linarith
    · have := WTPAux.VgN_incr_bdd hM obj g (2 * j) hj2 (2 * i) (by omega)
      rwa [WTPAux.grid_double M j i hj] at this
  have R : ∀ i ≤ j,
      MonotoneOn (fun y => VgN M obj g (2 * j) y - VgN M obj g j y) (Ici (grid M j i)) := by
    suffices H : ∀ d ≤ j, MonotoneOn (fun y => VgN M obj g (2 * j) y - VgN M obj g j y)
        (Ici (grid M j (j - d))) by
      intro i hi
      have h := H (j - i) (Nat.sub_le _ _)
      rwa [Nat.sub_sub_self hi] at h
    intro d
    induction d with
    | zero =>
      intro _
      simp only [Nat.sub_zero]
      intro x hx y hy _
      simp only
      rw [WTPAux.VgN_right M obj g j x hx, WTPAux.VgN_right M obj g j y hy,
        WTPAux.VgN_right M obj g (2 * j) x (by rw [hwN2, ← hwN]; exact hx),
        WTPAux.VgN_right M obj g (2 * j) y (by rw [hwN2, ← hwN]; exact hy)]
      simp
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      have e : j - d = (j - (d + 1)) + 1 := by omega
      rw [e] at h1
      set i := j - (d + 1) with hi
      have hk := kstep (i + 1) (by omega) h1
      have g2 : grid M (2 * j) (2 * (i + 1)) = grid M j (i + 1) := WTPAux.grid_double M j (i + 1) hj
      have g0 : grid M (2 * j) (2 * i) = grid M j i := WTPAux.grid_double M j i hj
      have hka := WTPAux.kappa_anti hM obj g (2 * j) hj2 (2 * i + 1) (2 * (i + 1)) (by omega)
        (by omega)
      rw [g2] at hka
      -- the coarse slope of `V^g_j` on `[x_i, x_{i+1}]`
      have hV : ∀ x ∈ Icc (grid M j i) (grid M j (i + 1)), VgN M obj g j x =
          VgN M obj g j (grid M j (i + 1)) +
          (-g + slopeAdj M obj (VgN M obj g j) (grid M j (i + 1))) * (x - grid M j (i + 1)) := by
        intro x hx
        exact WTPAux.VgN_piece' M obj g j (i + 1) (by omega) (by omega) x (by simpa using hx)
      set m := grid M (2 * j) (2 * i + 1) with hm
      have hm1 : grid M j i ≤ m := by
        rw [← g0]; exact WTPAux.grid_mono M _ (by omega)
      have hm2 : m ≤ grid M j (i + 1) := by
        rw [← g2]; exact WTPAux.grid_mono M _ (by omega)
      -- right half `[m, x_{i+1}]`
      have hR : MonotoneOn (fun y => VgN M obj g (2 * j) y - VgN M obj g j y) (Ici m) := by
        apply WTPAux.monotoneOn_glue hm2
          (s := (-g + slopeAdj M obj (VgN M obj g (2 * j)) (grid M j (i + 1))) -
            (-g + slopeAdj M obj (VgN M obj g j) (grid M j (i + 1)))) _ (by linarith) h1
        intro x hx
        have a1 := WTPAux.VgN_piece' M obj g (2 * j) (2 * (i + 1)) (by omega) (by omega) x
          (by rw [g2, show 2 * (i + 1) - 1 = 2 * i + 1 by omega]; exact hx)
        rw [g2] at a1
        rw [a1, hV x ⟨le_trans hm1 hx.1, hx.2⟩]; ring
      -- left half `[x_i, m]`
      apply WTPAux.monotoneOn_glue hm1
        (s := (-g + slopeAdj M obj (VgN M obj g (2 * j)) m) -
          (-g + slopeAdj M obj (VgN M obj g j) (grid M j (i + 1)))) _ (by linarith) hR
      intro x hx
      have a1 := WTPAux.VgN_piece' M obj g (2 * j) (2 * i + 1) (by omega) (by omega) x
        (by rw [show 2 * i + 1 - 1 = 2 * i by omega, g0]; exact hx)
      rw [a1, hV x ⟨hx.1, le_trans hx.2 hm2⟩, hV m ⟨hm1, hm2⟩]; ring
  constructor
  · rcases le_or_gt (wbar M) w with hww | hww
    · rw [WTPAux.VgN_right M obj g j w (by rw [hwN]; exact hww),
        WTPAux.VgN_right M obj g (2 * j) w (by rw [hwN2]; exact hww)]
    · have h := R 0 (Nat.zero_le _)
      rw [WTPAux.grid_zero] at h
      have := h (mem_Ici.2 hw.1) (mem_Ici.2 (WTPAux.wbar_nonneg M)) hww.le
      simp only at this
      rw [WTPAux.VgN_right M obj g j (wbar M) (by rw [hwN]),
        WTPAux.VgN_right M obj g (2 * j) (wbar M) (by rw [hwN2])] at this
      simp at this; linarith
  · rcases le_or_gt w (wbar M) with hww | hww
    · have hwb := (WTPAux.wbar_spec hM).1
      have hjpos : (0:ℝ) < j := by exact_mod_cast (show 0 < j by omega)
      have hε : 0 < wbar M / j := div_pos hwb hjpos
      rw [WTPAux.KgN_eq_kappa hM obj g j hj w ⟨hw.1, hww⟩,
        WTPAux.KgN_eq_kappa hM obj g (2 * j) hj2 w ⟨hw.1, hww⟩]
      set i := ⌈w / (wbar M / j)⌉₊ with hi
      have hiN : i ≤ j := by
        apply Nat.ceil_le.2
        rw [div_le_iff₀ hε]; field_simp; exact hww
      have hm : ⌈w / (wbar M / ((2 * j : ℕ) : ℝ))⌉₊ ≤ 2 * i := by
        apply Nat.ceil_le.2
        have h1 := Nat.le_ceil (w / (wbar M / j))
        rw [← hi] at h1
        have : w / (wbar M / ((2 * j : ℕ) : ℝ)) = 2 * (w / (wbar M / j)) := by
          push_cast; field_simp
        rw [this]; push_cast; linarith
      have h1 := kstep i hiN (R i hiN)
      have h2 := WTPAux.kappa_anti hM obj g (2 * j) hj2 _ (2 * i) hm (by omega)
      rw [WTPAux.grid_double M j i hj] at h2
      linarith
    · rw [WTPAux.KgN_right M obj g j w (by rw [hwN]; exact hww),
        WTPAux.KgN_right M obj g (2 * j) w (by rw [hwN2]; exact hww)]
