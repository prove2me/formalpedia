-- Prove2me | solution 1 for TwoSidedMatching.Statics.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T04:31:46.281062+00:00
-- url     : https://prove2.me/submissions/4ed5d159-a8dd-46ed-8a9e-1cc03d286ad8

import Mathlib
import Definitions.Def_TwoSidedMatching_Statics_Fluid

set_option autoImplicit false

open MeasureTheory

namespace P6f51

/-- clamped primitive -/
noncomputable def C (lo hi : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z in lo..max lo (min x hi), f z

/-- generalized inverse -/
noncomputable def Inv (lo hi : ℝ) (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  sInf {x : ℝ | x ∈ Set.Icc lo hi ∧ r ≤ C lo hi f x}

section generic

variable {lo hi : ℝ} {f : ℝ → ℝ}

lemma clamp_mem (hlt : lo < hi) (x : ℝ) : max lo (min x hi) ∈ Set.Icc lo hi :=
  ⟨le_max_left _ _, max_le hlt.le (min_le_right _ _)⟩

lemma clamp_of_mem {x : ℝ} (hx : x ∈ Set.Icc lo hi) : max lo (min x hi) = x := by
  rw [min_eq_left hx.2, max_eq_right hx.1]

lemma C_of_mem {x : ℝ} (hx : x ∈ Set.Icc lo hi) : C lo hi f x = ∫ z in lo..x, f z := by
  unfold C; rw [clamp_of_mem hx]

lemma C_clamp (hlt : lo < hi) (x : ℝ) : C lo hi f (max lo (min x hi)) = C lo hi f x := by
  unfold C; rw [clamp_of_mem (clamp_mem hlt x)]

lemma C_le_lo (hlt : lo < hi) {x : ℝ} (hx : x ≤ lo) : C lo hi f x = 0 := by
  unfold C
  rw [min_eq_left (hx.trans hlt.le), max_eq_left hx, intervalIntegral.integral_same]

lemma C_ge_hi (hlt : lo < hi) (h1 : ∫ z in lo..hi, f z = 1) {x : ℝ} (hx : hi ≤ x) :
    C lo hi f x = 1 := by
  unfold C
  rw [min_eq_right hx, max_eq_right hlt.le, h1]

lemma sub_int (hint : IntervalIntegrable f volume lo hi) {x y : ℝ} (hy : lo ≤ y) (hyx : y ≤ x)
    (hx : x ≤ hi) : C lo hi f x - C lo hi f y = ∫ z in y..x, f z := by
  rw [C_of_mem ⟨hy.trans hyx, hx⟩, C_of_mem ⟨hy, hyx.trans hx⟩]
  have hsub : ∀ u, lo ≤ u → u ≤ hi → IntervalIntegrable f volume lo u := fun u h1 h2 =>
    hint.mono_set (Set.uIcc_subset_uIcc_left (Set.mem_uIcc.2 (Or.inl ⟨h1, h2⟩)))
  exact intervalIntegral.integral_interval_sub_left (hsub x (hy.trans hyx) hx) (hsub y hy (hyx.trans hx))

lemma C_strict (hpos : ∀ x ∈ Set.Icc lo hi, 0 < f x) (hint : IntervalIntegrable f volume lo hi)
    {x y : ℝ} (hy : lo ≤ y) (hyx : y < x) (hx : x ≤ hi) : C lo hi f y < C lo hi f x := by
  have h := sub_int hint hy hyx.le hx
  have hi' : IntervalIntegrable f volume y x :=
    hint.mono_set (Set.uIcc_subset_uIcc (Set.mem_uIcc.2 (Or.inl ⟨hy, hyx.le.trans hx⟩))
      (Set.mem_uIcc.2 (Or.inl ⟨hy.trans hyx.le, hx⟩)))
  have hp : 0 < ∫ z in y..x, f z :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hi'
      (fun z hz => hpos z ⟨hy.trans hz.1.le, hz.2.le.trans hx⟩) hyx
  linarith

lemma C_mem_bounds (hlt : lo < hi) (hpos : ∀ x ∈ Set.Icc lo hi, 0 < f x)
    (hint : IntervalIntegrable f volume lo hi) (h1 : ∫ z in lo..hi, f z = 1) (x : ℝ) :
    0 ≤ C lo hi f x ∧ C lo hi f x ≤ 1 := by
  rw [← C_clamp hlt x]
  obtain ⟨ha, hb⟩ := clamp_mem hlt x
  set u := max lo (min x hi)
  constructor
  · rcases ha.lt_or_eq with h | h
    · have := C_strict (f := f) hpos hint le_rfl h hb
      rw [C_le_lo hlt le_rfl] at this; exact this.le
    · rw [← h, C_le_lo hlt le_rfl]
  · rcases hb.lt_or_eq with h | h
    · have := C_strict (f := f) hpos hint ha h le_rfl
      rw [C_ge_hi hlt h1 le_rfl] at this; exact this.le
    · rw [h, C_ge_hi hlt h1 le_rfl]

lemma C_cont (hlt : lo < hi) (hint : IntervalIntegrable f volume lo hi) :
    Continuous (C lo hi f) := by
  have hI : IntegrableOn f (Set.uIcc lo hi) := by
    rw [Set.uIcc_of_le hlt.le]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le hlt.le).1 hint
  have hP := intervalIntegral.continuousOn_primitive_interval hI
  rw [Set.uIcc_of_le hlt.le] at hP
  have : C lo hi f = (fun u => ∫ z in lo..u, f z) ∘ (fun x => max lo (min x hi)) := rfl
  rw [this]; exact hP.comp_continuous (by fun_prop) (clamp_mem hlt)

end generic

section inv

variable {lo hi : ℝ} {f : ℝ → ℝ} (hlt : lo < hi) (hpos : ∀ x ∈ Set.Icc lo hi, 0 < f x)
  (hint : IntervalIntegrable f volume lo hi) (h1 : ∫ z in lo..hi, f z = 1)
include hlt hpos hint h1

lemma hi_mem_set {r : ℝ} (hr : r ≤ 1) : hi ∈ {x : ℝ | x ∈ Set.Icc lo hi ∧ r ≤ C lo hi f x} :=
  ⟨⟨hlt.le, le_rfl⟩, by rw [C_ge_hi hlt h1 le_rfl]; exact hr⟩

omit hpos hint h1 in
lemma set_bdd (r : ℝ) : BddBelow {x : ℝ | x ∈ Set.Icc lo hi ∧ r ≤ C lo hi f x} :=
  ⟨lo, fun _ hx => hx.1.1⟩

lemma Inv_mem {r : ℝ} (hr : r ≤ 1) : Inv lo hi f r ∈ Set.Icc lo hi :=
  ⟨le_csInf ⟨hi, hi_mem_set hlt hpos hint h1 hr⟩ (fun _ hx => hx.1.1),
    csInf_le (set_bdd hlt r) (hi_mem_set hlt hpos hint h1 hr)⟩

lemma Inv_mono {r r' : ℝ} (h : r ≤ r') (h' : r' ≤ 1) : Inv lo hi f r ≤ Inv lo hi f r' :=
  csInf_le_csInf (set_bdd hlt r) ⟨hi, hi_mem_set hlt hpos hint h1 h'⟩
    (fun _ hx => ⟨hx.1, h.trans hx.2⟩)

lemma le_C_Inv {r : ℝ} (hr : r ≤ 1) : r ≤ C lo hi f (Inv lo hi f r) := by
  have hcl : IsClosed {x : ℝ | x ∈ Set.Icc lo hi ∧ r ≤ C lo hi f x} :=
    isClosed_Icc.inter (isClosed_le continuous_const (C_cont hlt hint))
  exact (hcl.csInf_mem ⟨hi, hi_mem_set hlt hpos hint h1 hr⟩ (set_bdd hlt r)).2

lemma C_Inv {r : ℝ} (h0 : 0 ≤ r) (hr : r ≤ 1) : C lo hi f (Inv lo hi f r) = r := by
  have hm := Inv_mem hlt hpos hint h1 hr
  obtain ⟨c, hc, hcv⟩ := intermediate_value_Icc hm.1 (C_cont hlt hint).continuousOn
    ⟨by rw [C_le_lo hlt le_rfl]; exact h0, le_C_Inv hlt hpos hint h1 hr⟩
  have hmc : Inv lo hi f r ≤ c :=
    csInf_le (set_bdd hlt r) ⟨⟨hc.1, hc.2.trans hm.2⟩, hcv.ge⟩
  have : c = Inv lo hi f r := le_antisymm hc.2 hmc
  rw [← this, hcv]

lemma Inv_le {r x : ℝ} (hx : lo ≤ x) (hr : r ≤ C lo hi f x) (hr1 : r ≤ 1) :
    Inv lo hi f r ≤ x := by
  by_cases hxh : x ≤ hi
  · exact csInf_le (set_bdd hlt r) ⟨⟨hx, hxh⟩, hr⟩
  · exact (Inv_mem hlt hpos hint h1 hr1).2.trans (le_of_lt (not_le.1 hxh))

lemma le_Inv {r x : ℝ} (hx : C lo hi f x ≤ r) (hr1 : r ≤ 1) :
    min x hi ≤ Inv lo hi f r := by
  by_contra h
  push Not at h
  have hm := Inv_mem hlt hpos hint h1 hr1
  have hCy : C lo hi f (min x hi) = C lo hi f x := by
    by_cases hxh : x ≤ hi
    · rw [min_eq_left hxh]
    · rw [min_eq_right (le_of_lt (not_le.1 hxh)), C_ge_hi hlt h1 le_rfl,
        C_ge_hi hlt h1 (le_of_lt (not_le.1 hxh))]
  have h2 := C_strict hpos hint hm.1 h (min_le_right _ _)
  have h3 := le_C_Inv hlt hpos hint h1 hr1
  linarith

lemma Inv_meas : Measurable (fun r => Inv lo hi f (min r 1)) :=
  Monotone.measurable (fun _ _ hab => Inv_mono hlt hpos hint h1 (min_le_min_right 1 hab)
    (min_le_right _ _))

end inv

lemma sSup_mono_sub {S1 S2 : Set ℝ} (hsub : S1 ⊆ S2) (hb : BddAbove S2)
    (h0 : ∀ x ∈ S2, 0 ≤ x) : sSup S1 ≤ sSup S2 :=
  Real.sSup_le (fun _ hx => le_csSup hb (hsub hx)) (Real.sSup_nonneg h0)

lemma sSup_scale {S1 S2 : Set ℝ} {c : ℝ} (hc : 0 < c) (hmap : ∀ x ∈ S2, c * x ∈ S1)
    (hb : BddAbove S1) (h0 : ∀ x ∈ S1, 0 ≤ x) : c * sSup S2 ≤ sSup S1 := by
  have : sSup S2 ≤ sSup S1 / c := Real.sSup_le (fun x hx => by
      rw [le_div_iff₀ hc]; have := le_csSup hb (hmap x hx); linarith)
    (div_nonneg (Real.sSup_nonneg h0) hc.le)
  rw [le_div_iff₀ hc] at this; linarith

end P6f51

namespace P6f51
open TwoSidedMatching.Statics

variable (E : Environment)

lemma Fd_eq (p : ℝ) : Fd E p = C E.loB E.hiB E.fB p := rfl
lemma Fs_eq (w : ℝ) : Fs E w = C E.loS E.hiS E.fS w := rfl
lemma FsInv_eq (q : ℝ) : FsInv E q = Inv E.loS E.hiS E.fS q := rfl
lemma FdBarInv_eq (q : ℝ) : FdBarInv E q = Inv E.loB E.hiB E.fB (1 - q) := by
  unfold FdBarInv Inv FdBar
  congr 1; ext p; simp only [Set.mem_setOf_eq, Fd_eq]
  constructor <;> rintro ⟨ha, hb⟩ <;> exact ⟨ha, by linarith⟩

lemma FdBar_bounds (p : ℝ) : 0 ≤ FdBar E p ∧ FdBar E p ≤ 1 := by
  have := C_mem_bounds E.loB_lt_hiB E.fB_pos E.fB_intervalIntegrable E.fB_integral p
  unfold FdBar; rw [Fd_eq]; constructor <;> linarith

lemma Fs_bounds (w : ℝ) : 0 ≤ Fs E w ∧ Fs E w ≤ 1 :=
  C_mem_bounds E.loS_lt_hiS E.fS_pos E.fS_intervalIntegrable E.fS_integral w

lemma FdBar_cont : Continuous (FdBar E) := by
  show Continuous (fun p => 1 - C E.loB E.hiB E.fB p)
  exact continuous_const.sub (C_cont E.loB_lt_hiB E.fB_intervalIntegrable)

lemma Fs_cont : Continuous (Fs E) :=
  C_cont E.loS_lt_hiS E.fS_intervalIntegrable

lemma FdBar_hi {p : ℝ} (hp : E.hiB ≤ p) : FdBar E p = 0 := by
  unfold FdBar; rw [Fd_eq, C_ge_hi E.loB_lt_hiB E.fB_integral hp]; ring

lemma Fs_lo {w : ℝ} (hw : w ≤ E.loS) : Fs E w = 0 := by
  rw [Fs_eq, C_le_lo E.loS_lt_hiS hw]

lemma FdBarInv_mem {q : ℝ} (hq : 0 ≤ q) : FdBarInv E q ∈ Set.Icc E.loB E.hiB := by
  rw [FdBarInv_eq]
  exact Inv_mem E.loB_lt_hiB E.fB_pos E.fB_intervalIntegrable E.fB_integral (by linarith)

lemma FdBarInv_anti {q q' : ℝ} (h0 : 0 ≤ q) (h : q ≤ q') : FdBarInv E q' ≤ FdBarInv E q := by
  rw [FdBarInv_eq, FdBarInv_eq]
  exact Inv_mono E.loB_lt_hiB E.fB_pos E.fB_intervalIntegrable E.fB_integral (by linarith)
    (by linarith)

lemma FsInv_mem {q : ℝ} (hq : q ≤ 1) : FsInv E q ∈ Set.Icc E.loS E.hiS :=
  Inv_mem E.loS_lt_hiS E.fS_pos E.fS_intervalIntegrable E.fS_integral hq

lemma FsInv_mono {q q' : ℝ} (h : q ≤ q') (h1 : q' ≤ 1) : FsInv E q ≤ FsInv E q' :=
  Inv_mono E.loS_lt_hiS E.fS_pos E.fS_intervalIntegrable E.fS_integral h h1

lemma FdBar_FdBarInv {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : FdBar E (FdBarInv E q) = q := by
  unfold FdBar
  rw [FdBarInv_eq, Fd_eq, C_Inv E.loB_lt_hiB E.fB_pos E.fB_intervalIntegrable E.fB_integral
    (by linarith) (by linarith)]
  ring

lemma Fs_FsInv {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : Fs E (FsInv E q) = q :=
  C_Inv E.loS_lt_hiS E.fS_pos E.fS_intervalIntegrable E.fS_integral h0 h1

lemma B_anti (hreg : E.Regular) {q q' : ℝ} (h0 : 0 ≤ q) (h : q ≤ q') :
    E.psiB (FdBarInv E q') ≤ E.psiB (FdBarInv E q) :=
  hreg.2 (FdBarInv_mem E (h0.trans h)) (FdBarInv_mem E h0) (FdBarInv_anti E h0 h)

lemma S_mono (hreg : E.Regular) {q q' : ℝ} (h : q ≤ q') (h1 : q' ≤ 1) :
    E.psiS (FsInv E q) ≤ E.psiS (FsInv E q') :=
  hreg.1 (FsInv_mem E (h.trans h1)) (FsInv_mem E h1) (FsInv_mono E h h1)

/-- the feasible volume set -/
def Mset (lamD lamS T : ℝ) : Set ℝ :=
  {μ : ℝ | μ ∈ Set.Icc 0 (min (lamD * T) (lamS * T)) ∧ 0 ≤ V E lamD lamS T μ}

lemma muStar_eq (lamD lamS T : ℝ) : muStar E lamD lamS T = sSup (Mset E lamD lamS T) := rfl

lemma Mset_nonneg (lamD lamS T : ℝ) : ∀ x ∈ Mset E lamD lamS T, 0 ≤ x := fun _ hx => hx.1.1

lemma Mset_bdd (lamD lamS T : ℝ) : BddAbove (Mset E lamD lamS T) :=
  ⟨lamS * T, fun _ hx => hx.1.2.trans (min_le_right _ _)⟩

lemma muStar_nonneg (lamD lamS T : ℝ) : 0 ≤ muStar E lamD lamS T :=
  Real.sSup_nonneg (Mset_nonneg E lamD lamS T)

lemma muStar_le_D {lamD lamS T : ℝ} (h : 0 ≤ lamD * T) : muStar E lamD lamS T ≤ lamD * T :=
  Real.sSup_le (fun _ hx => hx.1.2.trans (min_le_left _ _)) h

lemma muStar_le_S {lamD lamS T : ℝ} (h : 0 ≤ lamS * T) : muStar E lamD lamS T ≤ lamS * T :=
  Real.sSup_le (fun _ hx => hx.1.2.trans (min_le_right _ _)) h

lemma mu_demand (hreg : E.Regular) {T lamS lamD₁ lamD₂ : ℝ} (hT : 0 < T) (hS : 0 < lamS)
    (h1 : 0 < lamD₁) (h12 : lamD₁ ≤ lamD₂) :
    muStar E lamD₁ lamS T ≤ muStar E lamD₂ lamS T ∧
    muStar E lamD₂ lamS T / (lamD₂ * T) ≤ muStar E lamD₁ lamS T / (lamD₁ * T) := by
  have h2 : 0 < lamD₂ := h1.trans_le h12
  have hT1 : 0 < lamD₁ * T := mul_pos h1 hT
  have hT2 : 0 < lamD₂ * T := mul_pos h2 hT
  have hTS : 0 < lamS * T := mul_pos hS hT
  constructor
  · rw [muStar_eq, muStar_eq]
    refine sSup_mono_sub ?_ (Mset_bdd E _ _ _) (Mset_nonneg E _ _ _)
    rintro μ ⟨⟨h0, hcap⟩, hV⟩
    refine ⟨⟨h0, le_min ((hcap.trans (min_le_left _ _)).trans (by nlinarith))
      (hcap.trans (min_le_right _ _))⟩, ?_⟩
    unfold V at *
    have := B_anti E hreg (q := μ / (lamD₂ * T)) (q' := μ / (lamD₁ * T))
      (div_nonneg h0 hT2.le) (div_le_div_of_nonneg_left h0 hT1 (by nlinarith))
    linarith
  · set c := lamD₁ / lamD₂ with hc
    have hc0 : 0 < c := div_pos h1 h2
    have hc1 : c ≤ 1 := (div_le_one h2).2 h12
    have key : c * muStar E lamD₂ lamS T ≤ muStar E lamD₁ lamS T := by
      rw [muStar_eq, muStar_eq]
      refine sSup_scale hc0 ?_ (Mset_bdd E _ _ _) (Mset_nonneg E _ _ _)
      rintro μ ⟨⟨h0, hcap⟩, hV⟩
      have hμD : μ ≤ lamD₂ * T := hcap.trans (min_le_left _ _)
      have hμS : μ ≤ lamS * T := hcap.trans (min_le_right _ _)
      have hcμ : c * μ ≤ μ := by nlinarith
      have hq : c * μ / (lamD₁ * T) = μ / (lamD₂ * T) := by
        rw [hc]; field_simp
      refine ⟨⟨mul_nonneg hc0.le h0, le_min ?_ (hcμ.trans hμS)⟩, ?_⟩
      · have : c * (lamD₂ * T) = lamD₁ * T := by rw [hc]; field_simp
        nlinarith
      · unfold V at *
        rw [hq]
        have := S_mono E hreg (q := c * μ / (lamS * T)) (q' := μ / (lamS * T))
          (div_le_div_of_nonneg_right hcμ hTS.le) ((div_le_one hTS).2 hμS)
        linarith
    have : muStar E lamD₂ lamS T / (lamD₂ * T) = c * muStar E lamD₂ lamS T / (lamD₁ * T) := by
      rw [hc]; field_simp
    rw [this]
    exact div_le_div_of_nonneg_right key hT1.le

lemma mu_supply (hreg : E.Regular) {T lamD lamS₁ lamS₂ : ℝ} (hT : 0 < T) (hD : 0 < lamD)
    (h1 : 0 < lamS₁) (h12 : lamS₁ ≤ lamS₂) :
    muStar E lamD lamS₁ T ≤ muStar E lamD lamS₂ T ∧
    muStar E lamD lamS₂ T / (lamS₂ * T) ≤ muStar E lamD lamS₁ T / (lamS₁ * T) := by
  have h2 : 0 < lamS₂ := h1.trans_le h12
  have hT1 : 0 < lamS₁ * T := mul_pos h1 hT
  have hT2 : 0 < lamS₂ * T := mul_pos h2 hT
  have hTD : 0 < lamD * T := mul_pos hD hT
  constructor
  · rw [muStar_eq, muStar_eq]
    refine sSup_mono_sub ?_ (Mset_bdd E _ _ _) (Mset_nonneg E _ _ _)
    rintro μ ⟨⟨h0, hcap⟩, hV⟩
    have hμS : μ ≤ lamS₁ * T := hcap.trans (min_le_right _ _)
    refine ⟨⟨h0, le_min (hcap.trans (min_le_left _ _))
      (hμS.trans (by nlinarith))⟩, ?_⟩
    unfold V at *
    have := S_mono E hreg (q := μ / (lamS₂ * T)) (q' := μ / (lamS₁ * T))
      (div_le_div_of_nonneg_left h0 hT1 (by nlinarith)) ((div_le_one hT1).2 hμS)
    linarith
  · set c := lamS₁ / lamS₂ with hc
    have hc0 : 0 < c := div_pos h1 h2
    have hc1 : c ≤ 1 := (div_le_one h2).2 h12
    have key : c * muStar E lamD lamS₂ T ≤ muStar E lamD lamS₁ T := by
      rw [muStar_eq, muStar_eq]
      refine sSup_scale hc0 ?_ (Mset_bdd E _ _ _) (Mset_nonneg E _ _ _)
      rintro μ ⟨⟨h0, hcap⟩, hV⟩
      have hμD : μ ≤ lamD * T := hcap.trans (min_le_left _ _)
      have hμS : μ ≤ lamS₂ * T := hcap.trans (min_le_right _ _)
      have hcμ : c * μ ≤ μ := by nlinarith
      have hq : c * μ / (lamS₁ * T) = μ / (lamS₂ * T) := by
        rw [hc]; field_simp
      refine ⟨⟨mul_nonneg hc0.le h0, le_min (hcμ.trans hμD) ?_⟩, ?_⟩
      · have : c * (lamS₂ * T) = lamS₁ * T := by rw [hc]; field_simp
        nlinarith
      · unfold V at *
        rw [hq]
        have := B_anti E hreg (q := c * μ / (lamD * T)) (q' := μ / (lamD * T))
          (div_nonneg (mul_nonneg hc0.le h0) hTD.le) (div_le_div_of_nonneg_right hcμ hTD.le)
        linarith
    have : muStar E lamD lamS₂ T / (lamS₂ * T) = c * muStar E lamD lamS₂ T / (lamS₁ * T) := by
      rw [hc]; field_simp
    rw [this]
    exact div_le_div_of_nonneg_right key hT1.le

/-- the feasible value set of (D) -/
def Fset (lamD lamS T : ℝ) : Set ℝ :=
  {v : ℝ | ∃ π : ℝ → ℝ × ℝ,
    IsFeasiblePath E lamD lamS T π ∧ v = fluidObjective E lamD lamS T π}

lemma fv_eq (lamD lamS T : ℝ) : fluidValue E lamD lamS T = sSup (Fset E lamD lamS T) := rfl

lemma pFd_le {p : ℝ} (hp : 0 ≤ p) (hhi : 0 ≤ E.hiB) : p * FdBar E p ≤ E.hiB := by
  by_cases h : p ≤ E.hiB
  · have := FdBar_bounds E p; nlinarith
  · rw [FdBar_hi E (le_of_lt (not_le.1 h)), mul_zero]; exact hhi

lemma Fset_nonempty (hhi : 0 ≤ E.hiB) (hseller : 0 ≤ E.loS) (lamD lamS T : ℝ) :
    (Fset E lamD lamS T).Nonempty :=
  ⟨_, fun _ => (E.hiB, E.loS), ⟨measurable_const, fun _ _ => ⟨hhi, hseller, by
    show lamD * FdBar E E.hiB = lamS * Fs E E.loS
    rw [FdBar_hi E le_rfl, Fs_lo E le_rfl]; ring⟩,
    intervalIntegrable_const, intervalIntegrable_const⟩, rfl⟩

lemma Fset_bdd {lamD lamS T : ℝ} (hD : 0 ≤ lamD) (hS : 0 ≤ lamS) (hT : 0 ≤ T)
    (hhi : 0 ≤ E.hiB) : BddAbove (Fset E lamD lamS T) := by
  refine ⟨lamD * E.hiB * T, ?_⟩
  rintro v ⟨π, ⟨_, hf, hi1, hi2⟩, rfl⟩
  unfold fluidObjective
  have hA : (∫ t in (0:ℝ)..T, lamD * (π t).1 * FdBar E (π t).1) ≤
      ∫ t in (0:ℝ)..T, lamD * E.hiB :=
    intervalIntegral.integral_mono_on hT hi1 intervalIntegrable_const (fun t ht => by
      have h := mul_le_mul_of_nonneg_left (pFd_le E (hf t ht).1 hhi) hD
      calc lamD * (π t).1 * FdBar E (π t).1 = lamD * ((π t).1 * FdBar E (π t).1) := by ring
        _ ≤ lamD * E.hiB := h)
  have hB : 0 ≤ ∫ t in (0:ℝ)..T, lamS * (π t).2 * Fs E (π t).2 :=
    intervalIntegral.integral_nonneg hT (fun t ht =>
      mul_nonneg (mul_nonneg hS (hf t ht).2.1) (Fs_bounds E _).1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hA
  nlinarith

lemma ii_bdd {g : ℝ → ℝ} (hg : Measurable g) (M : ℝ) (hM : ∀ t, |g t| ≤ M) (a b : ℝ) :
    IntervalIntegrable g volume a b :=
  (intervalIntegrable_const (c := M)).mono_fun hg.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => by
      simp only [Real.norm_eq_abs]; exact (hM t).trans (le_abs_self M)))

lemma abs_mem_le {x a b : ℝ} (h : x ∈ Set.Icc a b) : |x| ≤ |a| + |b| := by
  rw [abs_le]; constructor
  · linarith [neg_abs_le a, abs_nonneg b, h.1]
  · linarith [le_abs_self b, abs_nonneg a, h.2]

lemma fv_demand (hhi : 0 ≤ E.hiB) (hseller : 0 ≤ E.loS) {T lamS lamD₁ lamD₂ : ℝ} (hT : 0 < T)
    (hS : 0 < lamS) (h1 : 0 < lamD₁) (h12 : lamD₁ ≤ lamD₂) :
    fluidValue E lamD₁ lamS T ≤ fluidValue E lamD₂ lamS T := by
  have h2 : 0 < lamD₂ := h1.trans_le h12
  have h2' : lamD₂ ≠ 0 := h2.ne'
  rw [fv_eq, fv_eq]
  refine csSup_le (Fset_nonempty E hhi hseller _ _ _) ?_
  rintro v ⟨π, ⟨hm, hf, hi1, hi2⟩, rfl⟩
  set q : ℝ → ℝ := fun t => lamD₁ * FdBar E (π t).1 / lamD₂ with hqdef
  have hlq : ∀ t, lamD₂ * q t = lamD₁ * FdBar E (π t).1 := fun t => by
    simp only [hqdef]; field_simp
  have hq0 : ∀ t, 0 ≤ q t := fun t =>
    div_nonneg (mul_nonneg h1.le (FdBar_bounds E _).1) h2.le
  have hqF : ∀ t, q t ≤ FdBar E (π t).1 := fun t => by
    have hF := (FdBar_bounds E (π t).1).1
    have := hlq t
    by_contra hc
    push Not at hc
    have := mul_lt_mul_of_pos_left hc h2
    nlinarith
  have hq1 : ∀ t, q t ≤ 1 := fun t => (hqF t).trans (FdBar_bounds E _).2
  have hFd : ∀ t, FdBar E (FdBarInv E (q t)) = q t := fun t =>
    FdBar_FdBarInv E (hq0 t) (hq1 t)
  have hmem : ∀ t, FdBarInv E (q t) ∈ Set.Icc E.loB E.hiB := fun t => FdBarInv_mem E (hq0 t)
  have hge : ∀ t, min (π t).1 E.hiB ≤ FdBarInv E (q t) := fun t => by
    rw [FdBarInv_eq]
    refine le_Inv E.loB_lt_hiB E.fB_pos E.fB_intervalIntegrable E.fB_integral ?_
      (by linarith [hq0 t])
    have := hqF t
    unfold FdBar at this; rw [Fd_eq] at this; linarith
  have hqm : Measurable q :=
    (measurable_const.mul ((FdBar_cont E).measurable.comp hm.fst)).div_const _
  have hpm : Measurable (fun t => FdBarInv E (q t)) := by
    have : (fun t => FdBarInv E (q t)) =
        (fun r => Inv E.loB E.hiB E.fB (min r 1)) ∘ (fun t => 1 - q t) := by
      funext t; simp only [Function.comp, FdBarInv_eq]; rw [min_eq_left (by linarith [hq0 t])]
    rw [this]
    exact (Inv_meas E.loB_lt_hiB E.fB_pos E.fB_intervalIntegrable E.fB_integral).comp
      (measurable_const.sub hqm)
  have hi1' : IntervalIntegrable
      (fun t => lamD₂ * FdBarInv E (q t) * FdBar E (FdBarInv E (q t))) volume 0 T := by
    refine ii_bdd (g := fun t => lamD₂ * FdBarInv E (q t) * FdBar E (FdBarInv E (q t)))
      ((measurable_const.mul hpm).mul ((FdBar_cont E).measurable.comp hpm))
      (lamD₂ * (|E.loB| + |E.hiB|)) (fun t => ?_) 0 T
    have hb := FdBar_bounds E (FdBarInv E (q t))
    have hB := abs_mem_le (hmem t)
    rw [abs_mul, abs_mul, abs_of_pos h2, abs_of_nonneg hb.1]
    have : |FdBarInv E (q t)| * FdBar E (FdBarInv E (q t)) ≤ |E.loB| + |E.hiB| := by
      nlinarith [abs_nonneg (FdBarInv E (q t))]
    calc lamD₂ * |FdBarInv E (q t)| * FdBar E (FdBarInv E (q t))
        = lamD₂ * (|FdBarInv E (q t)| * FdBar E (FdBarInv E (q t))) := by ring
      _ ≤ lamD₂ * (|E.loB| + |E.hiB|) := mul_le_mul_of_nonneg_left this h2.le
  have hfeas : IsFeasiblePath E lamD₂ lamS T (fun t => (FdBarInv E (q t), (π t).2)) := by
    refine ⟨hpm.prodMk hm.snd, fun t ht => ⟨?_, (hf t ht).2.1, ?_⟩, hi1', hi2⟩
    · exact le_trans (le_min (hf t ht).1 hhi) (hge t)
    · show lamD₂ * FdBar E (FdBarInv E (q t)) = lamS * Fs E (π t).2
      rw [hFd t, hlq t, (hf t ht).2.2]
  refine le_csSup_of_le (Fset_bdd E h2.le hS.le hT.le hhi) ⟨_, hfeas, rfl⟩ ?_
  unfold fluidObjective
  have hR : (∫ t in (0:ℝ)..T, lamD₁ * (π t).1 * FdBar E (π t).1) ≤
      ∫ t in (0:ℝ)..T, lamD₂ * FdBarInv E (q t) * FdBar E (FdBarInv E (q t)) := by
    refine intervalIntegral.integral_mono_on hT.le hi1 hi1' (fun t ht => ?_)
    rw [hFd t]
    have e : lamD₂ * FdBarInv E (q t) * q t = lamD₁ * FdBar E (π t).1 * FdBarInv E (q t) := by
      calc lamD₂ * FdBarInv E (q t) * q t = (lamD₂ * q t) * FdBarInv E (q t) := by ring
        _ = _ := by rw [hlq t]
    rw [e]
    by_cases hp : (π t).1 ≤ E.hiB
    · have hg := hge t
      rw [min_eq_left hp] at hg
      have : 0 ≤ lamD₁ * FdBar E (π t).1 := mul_nonneg h1.le (FdBar_bounds E (π t).1).1
      nlinarith
    · rw [FdBar_hi E (le_of_lt (not_le.1 hp))]; simp
  exact sub_le_sub_right hR _

lemma fv_supply (hhi : 0 ≤ E.hiB) (hseller : 0 ≤ E.loS) {T lamD lamS₁ lamS₂ : ℝ} (hT : 0 < T)
    (hD : 0 < lamD) (h1 : 0 < lamS₁) (h12 : lamS₁ ≤ lamS₂) :
    fluidValue E lamD lamS₁ T ≤ fluidValue E lamD lamS₂ T := by
  have h2 : 0 < lamS₂ := h1.trans_le h12
  have h2' : lamS₂ ≠ 0 := h2.ne'
  rw [fv_eq, fv_eq]
  refine csSup_le (Fset_nonempty E hhi hseller _ _ _) ?_
  rintro v ⟨π, ⟨hm, hf, hi1, hi2⟩, rfl⟩
  set q : ℝ → ℝ := fun t => lamS₁ * Fs E (π t).2 / lamS₂ with hqdef
  have hlq : ∀ t, lamS₂ * q t = lamS₁ * Fs E (π t).2 := fun t => by
    simp only [hqdef]; field_simp
  have hq0 : ∀ t, 0 ≤ q t := fun t =>
    div_nonneg (mul_nonneg h1.le (Fs_bounds E _).1) h2.le
  have hqF : ∀ t, q t ≤ Fs E (π t).2 := fun t => by
    have hF := (Fs_bounds E (π t).2).1
    have := hlq t
    by_contra hc
    push Not at hc
    have := mul_lt_mul_of_pos_left hc h2
    nlinarith
  have hq1 : ∀ t, q t ≤ 1 := fun t => (hqF t).trans (Fs_bounds E _).2
  have hFs : ∀ t, Fs E (FsInv E (q t)) = q t := fun t => Fs_FsInv E (hq0 t) (hq1 t)
  have hmem : ∀ t, FsInv E (q t) ∈ Set.Icc E.loS E.hiS := fun t => FsInv_mem E (hq1 t)
  have hle : ∀ t, E.loS ≤ (π t).2 → FsInv E (q t) ≤ (π t).2 := fun t hw =>
    Inv_le E.loS_lt_hiS E.fS_pos E.fS_intervalIntegrable E.fS_integral hw (hqF t) (hq1 t)
  have hqm : Measurable q :=
    (measurable_const.mul ((Fs_cont E).measurable.comp hm.snd)).div_const _
  have hwm : Measurable (fun t => FsInv E (q t)) := by
    have : (fun t => FsInv E (q t)) =
        (fun r => Inv E.loS E.hiS E.fS (min r 1)) ∘ q := by
      funext t; simp only [Function.comp, FsInv_eq]; rw [min_eq_left (hq1 t)]
    rw [this]
    exact (Inv_meas E.loS_lt_hiS E.fS_pos E.fS_intervalIntegrable E.fS_integral).comp hqm
  have hi2' : IntervalIntegrable
      (fun t => lamS₂ * FsInv E (q t) * Fs E (FsInv E (q t))) volume 0 T := by
    refine ii_bdd (g := fun t => lamS₂ * FsInv E (q t) * Fs E (FsInv E (q t)))
      ((measurable_const.mul hwm).mul ((Fs_cont E).measurable.comp hwm))
      (lamS₂ * (|E.loS| + |E.hiS|)) (fun t => ?_) 0 T
    have hb := Fs_bounds E (FsInv E (q t))
    have hB := abs_mem_le (hmem t)
    rw [abs_mul, abs_mul, abs_of_pos h2, abs_of_nonneg hb.1]
    have : |FsInv E (q t)| * Fs E (FsInv E (q t)) ≤ |E.loS| + |E.hiS| := by
      nlinarith [abs_nonneg (FsInv E (q t))]
    calc lamS₂ * |FsInv E (q t)| * Fs E (FsInv E (q t))
        = lamS₂ * (|FsInv E (q t)| * Fs E (FsInv E (q t))) := by ring
      _ ≤ lamS₂ * (|E.loS| + |E.hiS|) := mul_le_mul_of_nonneg_left this h2.le
  have hfeas : IsFeasiblePath E lamD lamS₂ T (fun t => ((π t).1, FsInv E (q t))) := by
    refine ⟨hm.fst.prodMk hwm, fun t ht => ⟨(hf t ht).1, ?_, ?_⟩, hi1, hi2'⟩
    · exact hseller.trans (hmem t).1
    · show lamD * FdBar E (π t).1 = lamS₂ * Fs E (FsInv E (q t))
      rw [hFs t, hlq t, (hf t ht).2.2]
  refine le_csSup_of_le (Fset_bdd E hD.le h2.le hT.le hhi) ⟨_, hfeas, rfl⟩ ?_
  unfold fluidObjective
  have hC : (∫ t in (0:ℝ)..T, lamS₂ * FsInv E (q t) * Fs E (FsInv E (q t))) ≤
      ∫ t in (0:ℝ)..T, lamS₁ * (π t).2 * Fs E (π t).2 := by
    refine intervalIntegral.integral_mono_on hT.le hi2' hi2 (fun t ht => ?_)
    rw [hFs t]
    have e : lamS₂ * FsInv E (q t) * q t = lamS₁ * Fs E (π t).2 * FsInv E (q t) := by
      calc lamS₂ * FsInv E (q t) * q t = (lamS₂ * q t) * FsInv E (q t) := by ring
        _ = _ := by rw [hlq t]
    rw [e]
    by_cases hw : E.loS ≤ (π t).2
    · have hg := hle t hw
      have : 0 ≤ lamS₁ * Fs E (π t).2 := mul_nonneg h1.le (Fs_bounds E (π t).2).1
      nlinarith
    · rw [Fs_lo E (le_of_lt (not_le.1 hw))]; simp
  exact sub_le_sub_left hC _

end P6f51

open TwoSidedMatching.Statics in
theorem solution (E : Environment) (T : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hcross : E.loS ≤ E.hiB)
    (hseller : 0 ≤ E.loS) (hT : 0 < T) :
    (∀ lamS lamD₁ lamD₂ : ℝ, 0 < lamS → 0 < lamD₁ → lamD₁ ≤ lamD₂ →
      pStar E lamD₁ lamS T ≤ pStar E lamD₂ lamS T ∧
      wStar E lamD₁ lamS T ≤ wStar E lamD₂ lamS T ∧
      muStar E lamD₁ lamS T ≤ muStar E lamD₂ lamS T ∧
      fluidValue E lamD₁ lamS T ≤ fluidValue E lamD₂ lamS T) ∧
    (∀ lamD lamS₁ lamS₂ : ℝ, 0 < lamD → 0 < lamS₁ → lamS₁ ≤ lamS₂ →
      pStar E lamD lamS₂ T ≤ pStar E lamD lamS₁ T ∧
      wStar E lamD lamS₂ T ≤ wStar E lamD lamS₁ T ∧
      muStar E lamD lamS₁ T ≤ muStar E lamD lamS₂ T ∧
      fluidValue E lamD lamS₁ T ≤ fluidValue E lamD lamS₂ T) := by
  have hhi : 0 ≤ E.hiB := hseller.trans hcross
  refine ⟨fun lamS lamD₁ lamD₂ hS h1 h12 => ?_, fun lamD lamS₁ lamS₂ hD h1 h12 => ?_⟩
  · obtain ⟨hm, hq⟩ := P6f51.mu_demand E hreg hT hS h1 h12
    have h2 : 0 < lamD₂ := h1.trans_le h12
    have hTS : 0 < lamS * T := mul_pos hS hT
    refine ⟨?_, ?_, hm, P6f51.fv_demand E hhi hseller hT hS h1 h12⟩
    · exact P6f51.FdBarInv_anti E
        (div_nonneg (P6f51.muStar_nonneg E _ _ _) (mul_pos h2 hT).le) hq
    · exact P6f51.FsInv_mono E (div_le_div_of_nonneg_right hm hTS.le)
        ((div_le_one hTS).2 (P6f51.muStar_le_S E hTS.le))
  · obtain ⟨hm, hq⟩ := P6f51.mu_supply E hreg hT hD h1 h12
    have hTD : 0 < lamD * T := mul_pos hD hT
    have hT1 : 0 < lamS₁ * T := mul_pos h1 hT
    refine ⟨?_, ?_, hm, P6f51.fv_supply E hhi hseller hT hD h1 h12⟩
    · exact P6f51.FdBarInv_anti E
        (div_nonneg (P6f51.muStar_nonneg E _ _ _) hTD.le) (div_le_div_of_nonneg_right hm hTD.le)
    · exact P6f51.FsInv_mono E hq ((div_le_one hT1).2 (P6f51.muStar_le_S E hT1.le))
