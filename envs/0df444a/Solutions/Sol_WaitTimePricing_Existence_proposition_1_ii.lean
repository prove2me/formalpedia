-- Prove2me | solution 1 for WaitTimePricing.Existence.proposition_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T09:45:24.342312+00:00
-- url     : https://prove2.me/submissions/299a46e5-03dc-49ba-86b4-17ecff7ecae8

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting

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

end WTPAux

theorem solution (M : Model) (hM : M.Standing) :
    ∀ w ∈ Icc 0 (what M),
      Lw M w ∈ Icc 0 M.C ∧
      (∀ t ∈ Icc 0 M.C, 0 ≤ M.U t - deriv M.U t * t - M.c w ↔ Lw M w ≤ t) ∧
      (∀ L ∈ Icc 0 M.C,
        (∀ t ∈ Icc 0 M.C, 0 ≤ M.U t - deriv M.U t * t - M.c w ↔ L ≤ t) → L = Lw M w) := by
  intro w hw
  have hC := hM.C_pos
  -- `ŵ` solves (3)
  have hA : 0 < M.U M.C - deriv M.U M.C * M.C := by
    have := WTPAux.r_strictMono hM ⟨le_rfl, hC.le⟩ ⟨hC.le, le_rfl⟩ hC
    simp only [hM.U_zero, mul_zero, sub_zero] at this; exact this
  obtain ⟨w0, hw0, hcw0, huniq⟩ := WTPAux.c_root hM _ hA
  have hset : {w ∈ Ioi (0 : ℝ) | M.U M.C - deriv M.U M.C * M.C - M.c w = 0} = {w0} := by
    ext w; simp only [mem_setOf_eq, mem_Ioi, mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact huniq w h1.le (by linarith)
    · rintro rfl; exact ⟨hw0, by linarith⟩
  have hwh : what M = w0 := by unfold what; rw [hset, csSup_singleton]
  have hcw : M.c w ≤ M.c w0 :=
    (WTPAux.c_strictMono hM).monotoneOn (mem_Ici.2 hw.1) (mem_Ici.2 hw0.le) (hwh ▸ hw.2)
  set S := {t ∈ Icc 0 M.C | 0 ≤ M.U t - deriv M.U t * t - M.c w} with hS
  have hCS : M.C ∈ S := ⟨⟨hC.le, le_rfl⟩, by linarith⟩
  have hbdd : BddBelow S := ⟨0, fun x hx => hx.1.1⟩
  have hmem : Lw M w ∈ S := by
    apply IsClosed.csInf_mem _ ⟨_, hCS⟩ hbdd
    have hc : ContinuousOn (fun t => M.U t - deriv M.U t * t - M.c w) (Icc 0 M.C) :=
      (((WTPAux.U_diff hM).continuous.sub ((WTPAux.dU_diff hM).continuous.mul
        continuous_id)).sub continuous_const).continuousOn
    exact hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hiff : ∀ t ∈ Icc 0 M.C, 0 ≤ M.U t - deriv M.U t * t - M.c w ↔ Lw M w ≤ t := by
    intro t ht
    constructor
    · intro h; exact csInf_le hbdd ⟨ht, h⟩
    · intro h
      have := (WTPAux.r_strictMono hM).monotoneOn hmem.1 ht h
      have := hmem.2
      linarith
  refine ⟨hmem.1, hiff, fun L hL hLp => ?_⟩
  apply le_antisymm
  · exact (hLp _ hmem.1).1 hmem.2
  · exact csInf_le hbdd ⟨hL, (hLp L hL).2 le_rfl⟩
