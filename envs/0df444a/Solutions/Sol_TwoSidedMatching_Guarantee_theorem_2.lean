-- Prove2me | solution 1 for TwoSidedMatching.Guarantee.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T07:28:58.152452+00:00
-- url     : https://prove2.me/submissions/935417d8-f7ab-41a7-b11c-c064fa8c6f7e

import Mathlib
import Definitions.Def_TwoSidedMatching_Guarantee_Market

set_option autoImplicit false

open MeasureTheory

namespace TwoSidedMatching.Guarantee


lemma inv_main (F : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hc : ContinuousOn F (Set.Icc a b))
    (hm : StrictMonoOn F (Set.Icc a b)) (h0 : F a = 0) (h1 : F b = 1) :
    (∀ q ∈ Set.Icc (0:ℝ) 1, Function.invFunOn F (Set.Icc a b) q ∈ Set.Icc a b ∧
        F (Function.invFunOn F (Set.Icc a b) q) = q) ∧
    ContinuousOn (Function.invFunOn F (Set.Icc a b)) (Set.Icc 0 1) := by
  have hmaps : ∀ x ∈ Set.Icc a b, F x ∈ Set.Icc (0:ℝ) 1 := by
    intro x hx
    constructor
    · rw [← h0]; exact hm.monotoneOn (Set.left_mem_Icc.2 hab.le) hx hx.1
    · rw [← h1]; exact hm.monotoneOn hx (Set.right_mem_Icc.2 hab.le) hx.2
  have hsurj : ∀ q ∈ Set.Icc (0:ℝ) 1, ∃ x ∈ Set.Icc a b, F x = q := by
    intro q hq
    have := intermediate_value_Icc hab.le hc
    rw [h0, h1] at this
    exact this hq
  have hq : ∀ q ∈ Set.Icc (0:ℝ) 1, Function.invFunOn F (Set.Icc a b) q ∈ Set.Icc a b ∧
      F (Function.invFunOn F (Set.Icc a b) q) = q := by
    intro q hq
    obtain ⟨x, hx, hxq⟩ := hsurj q hq
    exact ⟨Function.invFunOn_mem ⟨x, hx, hxq⟩, Function.invFunOn_eq ⟨x, hx, hxq⟩⟩
  refine ⟨hq, ?_⟩
  let f' : Set.Icc a b → Set.Icc (0:ℝ) 1 := fun x => ⟨F x, hmaps x x.2⟩
  have hf'm : StrictMono f' := fun x y hxy => hm x.2 y.2 hxy
  have hf's : Function.Surjective f' := by
    rintro ⟨q, hq'⟩
    obtain ⟨x, hx, hxq⟩ := hsurj q hq'
    exact ⟨⟨x, hx⟩, Subtype.ext hxq⟩
  let e := StrictMono.orderIsoOfSurjective f' hf'm hf's
  have hec : Continuous e.symm := e.symm.continuous
  rw [continuousOn_iff_continuous_domRestrict]
  have : (Set.Icc (0:ℝ) 1).domRestrict (Function.invFunOn F (Set.Icc a b)) =
      fun x => ((e.symm x : Set.Icc a b) : ℝ) := by
    funext ⟨q, hq'⟩
    have h2 : e (e.symm ⟨q, hq'⟩) = ⟨q, hq'⟩ := e.apply_symm_apply _
    have h3 : F ((e.symm ⟨q, hq'⟩ : Set.Icc a b) : ℝ) = q := by
      have := congrArg Subtype.val h2
      exact this
    exact hm.injOn (hq q hq').1 (e.symm ⟨q, hq'⟩).2 ((hq q hq').2.trans h3.symm)
  rw [this]
  exact continuous_subtype_val.comp hec

lemma prim_facts (lo hi : ℝ) (f : ℝ → ℝ) (hlt : lo < hi)
    (hpos : ∀ x ∈ Set.Icc lo hi, 0 < f x)
    (hint : IntervalIntegrable f volume lo hi) :
    ContinuousOn (fun y => ∫ z in lo..y, f z) (Set.Icc lo hi) ∧
    StrictMonoOn (fun y => ∫ z in lo..y, f z) (Set.Icc lo hi) := by
  constructor
  · have := intervalIntegral.continuousOn_primitive_interval' hint (a := lo)
      (Set.left_mem_uIcc)
    rwa [Set.uIcc_of_le hlt.le] at this
  · intro x hx y hy hxy
    have hxi : IntervalIntegrable f volume lo x :=
      hint.mono_set (by
        rw [Set.uIcc_of_le hx.1, Set.uIcc_of_le hlt.le]
        exact Set.Icc_subset_Icc le_rfl hx.2)
    have hyi : IntervalIntegrable f volume lo y :=
      hint.mono_set (by
        rw [Set.uIcc_of_le hy.1, Set.uIcc_of_le hlt.le]
        exact Set.Icc_subset_Icc le_rfl hy.2)
    have hxyi : IntervalIntegrable f volume x y :=
      hint.mono_set (by
        rw [Set.uIcc_of_le hxy.le, Set.uIcc_of_le hlt.le]
        exact Set.Icc_subset_Icc hx.1 hy.2)
    have h1 := intervalIntegral.integral_interval_sub_left hyi hxi
    have h2 : 0 < ∫ z in x..y, f z :=
      intervalIntegral.intervalIntegral_pos_of_pos_on hxyi
        (fun z hz => hpos z ⟨hx.1.trans hz.1.le, hz.2.le.trans hy.2⟩) hxy
    show (∫ z in lo..x, f z) < ∫ z in lo..y, f z
    linarith

open MechanismDesign.BilateralTrade in
lemma cdfB_props (E : Environment) :
    ContinuousOn E.cdfB (Set.Icc E.loB E.hiB) ∧ StrictMonoOn E.cdfB (Set.Icc E.loB E.hiB) ∧
    E.cdfB E.loB = 0 ∧ E.cdfB E.hiB = 1 := by
  obtain ⟨h1, h2⟩ := prim_facts E.loB E.hiB E.fB E.loB_lt_hiB E.fB_pos E.fB_intervalIntegrable
  refine ⟨h1, h2, ?_, E.fB_integral⟩
  show ∫ z in E.loB..E.loB, E.fB z = 0
  simp

open MechanismDesign.BilateralTrade in
lemma cdfS_props (E : Environment) :
    ContinuousOn E.cdfS (Set.Icc E.loS E.hiS) ∧ StrictMonoOn E.cdfS (Set.Icc E.loS E.hiS) ∧
    E.cdfS E.loS = 0 ∧ E.cdfS E.hiS = 1 := by
  obtain ⟨h1, h2⟩ := prim_facts E.loS E.hiS E.fS E.loS_lt_hiS E.fS_pos E.fS_intervalIntegrable
  refine ⟨h1, h2, ?_, E.fS_integral⟩
  show ∫ z in E.loS..E.loS, E.fS z = 0
  simp

lemma FdBar_eq (E : Environment) {p : ℝ} (hp : p ∈ Set.Icc E.loB E.hiB) :
    FdBar E p = 1 - E.cdfB p := by
  unfold FdBar Fd
  rw [min_eq_left hp.2, max_eq_right hp.1]

lemma Fs_eq (E : Environment) {w : ℝ} (hw : w ∈ Set.Icc E.loS E.hiS) :
    Fs E w = E.cdfS w := by
  unfold Fs
  rw [min_eq_left hw.2, max_eq_right hw.1]

lemma FdBarInv_spec (E : Environment) {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1) :
    FdBarInv E q ∈ Set.Icc E.loB E.hiB ∧ FdBar E (FdBarInv E q) = q ∧
    FdBarInv E q = Function.invFunOn E.cdfB (Set.Icc E.loB E.hiB) (1 - q) := by
  obtain ⟨hc, hm, h0, h1⟩ := cdfB_props E
  obtain ⟨hG, -⟩ := inv_main E.cdfB E.loB E.hiB E.loB_lt_hiB hc hm h0 h1
  have hq' : 1 - q ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hq.2], by linarith [hq.1]⟩
  obtain ⟨hp0, hp1⟩ := hG _ hq'
  have hex : ∃ a ∈ Set.Icc E.loB E.hiB, FdBar E a = q :=
    ⟨_, hp0, by rw [FdBar_eq E hp0, hp1]; ring⟩
  have hmem : FdBarInv E q ∈ Set.Icc E.loB E.hiB := Function.invFunOn_mem hex
  have heq : FdBar E (FdBarInv E q) = q := Function.invFunOn_eq hex
  refine ⟨hmem, heq, ?_⟩
  apply hm.injOn hmem hp0
  rw [FdBar_eq E hmem] at heq
  rw [hp1]; linarith

lemma FsInv_spec (E : Environment) {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1) :
    FsInv E q ∈ Set.Icc E.loS E.hiS ∧ Fs E (FsInv E q) = q ∧
    FsInv E q = Function.invFunOn E.cdfS (Set.Icc E.loS E.hiS) q := by
  obtain ⟨hc, hm, h0, h1⟩ := cdfS_props E
  obtain ⟨hG, -⟩ := inv_main E.cdfS E.loS E.hiS E.loS_lt_hiS hc hm h0 h1
  obtain ⟨hp0, hp1⟩ := hG _ hq
  have hex : ∃ a ∈ Set.Icc E.loS E.hiS, Fs E a = q :=
    ⟨_, hp0, by rw [Fs_eq E hp0, hp1]⟩
  have hmem : FsInv E q ∈ Set.Icc E.loS E.hiS := Function.invFunOn_mem hex
  have heq : Fs E (FsInv E q) = q := Function.invFunOn_eq hex
  refine ⟨hmem, heq, ?_⟩
  apply hm.injOn hmem hp0
  rw [Fs_eq E hmem] at heq
  rw [hp1]; exact heq

lemma FdBarInv_cont (E : Environment) : ContinuousOn (FdBarInv E) (Set.Icc 0 1) := by
  obtain ⟨hc, hm, h0, h1⟩ := cdfB_props E
  obtain ⟨-, hG⟩ := inv_main E.cdfB E.loB E.hiB E.loB_lt_hiB hc hm h0 h1
  have hcomp : ContinuousOn (fun q : ℝ => Function.invFunOn E.cdfB (Set.Icc E.loB E.hiB) (1 - q))
      (Set.Icc 0 1) :=
    hG.comp (continuousOn_const.sub continuousOn_id)
      (fun q hq => ⟨by linarith [hq.2], by linarith [hq.1]⟩)
  exact hcomp.congr (fun q hq => (FdBarInv_spec E hq).2.2)

lemma FsInv_cont (E : Environment) : ContinuousOn (FsInv E) (Set.Icc 0 1) := by
  obtain ⟨hc, hm, h0, h1⟩ := cdfS_props E
  obtain ⟨-, hG⟩ := inv_main E.cdfS E.loS E.hiS E.loS_lt_hiS hc hm h0 h1
  exact hG.congr (fun q hq => (FsInv_spec E hq).2.2)

open MechanismDesign.BilateralTrade in
lemma psiB_cont (E : Environment) (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB)) :
    ContinuousOn E.psiB (Set.Icc E.loB E.hiB) := by
  obtain ⟨hc, -⟩ := cdfB_props E
  unfold Environment.psiB
  exact continuousOn_id.sub
    ((continuousOn_const.sub hc).div hcontB (fun x hx => (E.fB_pos x hx).ne'))

open MechanismDesign.BilateralTrade in
lemma psiS_cont (E : Environment) (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS)) :
    ContinuousOn E.psiS (Set.Icc E.loS E.hiS) := by
  obtain ⟨hc, -⟩ := cdfS_props E
  unfold Environment.psiS
  exact continuousOn_id.add
    (hc.div hcontS (fun x hx => (E.fS_pos x hx).ne'))

lemma FdBarInv_zero (E : Environment) : FdBarInv E 0 = E.hiB := by
  obtain ⟨hc, hm, h0, h1⟩ := cdfB_props E
  obtain ⟨hmem, heq, -⟩ := FdBarInv_spec E (q := 0) ⟨le_rfl, zero_le_one⟩
  rw [FdBar_eq E hmem] at heq
  exact hm.injOn hmem (Set.right_mem_Icc.2 E.loB_lt_hiB.le) (by rw [h1]; linarith)

lemma FsInv_zero (E : Environment) : FsInv E 0 = E.loS := by
  obtain ⟨hc, hm, h0, h1⟩ := cdfS_props E
  obtain ⟨hmem, heq, -⟩ := FsInv_spec E (q := 0) ⟨le_rfl, zero_le_one⟩
  rw [Fs_eq E hmem] at heq
  exact hm.injOn hmem (Set.left_mem_Icc.2 E.loS_lt_hiS.le) (by rw [h0]; exact heq)

open MechanismDesign.BilateralTrade in
lemma V_zero (E : Environment) (lamD lamS T : ℝ) : V E lamD lamS T 0 = E.hiB - E.loS := by
  obtain ⟨-, -, -, h1⟩ := cdfB_props E
  obtain ⟨-, -, h0, -⟩ := cdfS_props E
  unfold V
  rw [zero_div, zero_div, FdBarInv_zero, FsInv_zero]
  unfold Environment.psiB Environment.psiS
  rw [h1, h0]; simp

lemma V_cont (E : Environment) (lamD lamS T : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T) :
    ContinuousOn (V E lamD lamS T) (Set.Icc 0 (min (lamD * T) (lamS * T))) := by
  have hDT : 0 < lamD * T := mul_pos hd hT
  have hST : 0 < lamS * T := mul_pos hs hT
  have hmaps1 : Set.MapsTo (fun μ : ℝ => μ / (lamD * T)) (Set.Icc 0 (min (lamD * T) (lamS * T)))
      (Set.Icc 0 1) := fun μ hμ =>
    ⟨div_nonneg hμ.1 hDT.le, (div_le_one hDT).2 (hμ.2.trans (min_le_left _ _))⟩
  have hmaps2 : Set.MapsTo (fun μ : ℝ => μ / (lamS * T)) (Set.Icc 0 (min (lamD * T) (lamS * T)))
      (Set.Icc 0 1) := fun μ hμ =>
    ⟨div_nonneg hμ.1 hST.le, (div_le_one hST).2 (hμ.2.trans (min_le_right _ _))⟩
  have h1 : ContinuousOn (fun μ : ℝ => E.psiB (FdBarInv E (μ / (lamD * T))))
      (Set.Icc 0 (min (lamD * T) (lamS * T))) :=
    (psiB_cont E hcontB).comp
      ((FdBarInv_cont E).comp (continuousOn_id.div_const _) hmaps1)
      (fun μ hμ => (FdBarInv_spec E (hmaps1 hμ)).1)
  have h2 : ContinuousOn (fun μ : ℝ => E.psiS (FsInv E (μ / (lamS * T))))
      (Set.Icc 0 (min (lamD * T) (lamS * T))) :=
    (psiS_cont E hcontS).comp
      ((FsInv_cont E).comp (continuousOn_id.div_const _) hmaps2)
      (fun μ hμ => (FsInv_spec E (hmaps2 hμ)).1)
  exact h1.sub h2

open MechanismDesign.BilateralTrade in
lemma core (E : Environment) (lamD lamS T : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hgap : E.loS < E.hiB)
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T) :
    0 < muStar E lamD lamS T ∧ muStar E lamD lamS T ∈ admissibleVolume E lamD lamS T ∧
    pStar E lamD lamS T ∈ Set.Icc E.loB E.hiB ∧ wStar E lamD lamS T ∈ Set.Icc E.loS E.hiS ∧
    FdBar E (pStar E lamD lamS T) = muStar E lamD lamS T / (lamD * T) ∧
    Fs E (wStar E lamD lamS T) = muStar E lamD lamS T / (lamS * T) ∧
    (muStar E lamD lamS T / (lamD * T)) / E.fB (pStar E lamD lamS T) +
      (muStar E lamD lamS T / (lamS * T)) / E.fS (wStar E lamD lamS T) ≤
      pStar E lamD lamS T - wStar E lamD lamS T := by
  have hDT : 0 < lamD * T := mul_pos hd hT
  have hST : 0 < lamS * T := mul_pos hs hT
  set m := min (lamD * T) (lamS * T) with hmdef
  have hm0 : 0 < m := lt_min hDT hST
  have hVc := V_cont E lamD lamS T hcontB hcontS hd hs hT
  have hV0 : 0 < V E lamD lamS T 0 := by rw [V_zero]; linarith
  have hclosed : IsClosed (admissibleVolume E lamD lamS T) := by
    have : admissibleVolume E lamD lamS T =
        Set.Icc 0 m ∩ (V E lamD lamS T) ⁻¹' (Set.Ici 0) := by
      ext μ; simp [admissibleVolume, hmdef]
    rw [this]
    exact hVc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hbdd : BddAbove (admissibleVolume E lamD lamS T) := ⟨m, fun x hx => hx.1.2⟩
  have hne : (admissibleVolume E lamD lamS T).Nonempty :=
    ⟨0, ⟨le_rfl, hm0.le⟩, hV0.le⟩
  have hmem : muStar E lamD lamS T ∈ admissibleVolume E lamD lamS T :=
    hclosed.csSup_mem hne hbdd
  have hpos : 0 < muStar E lamD lamS T := by
    have h0mem : (0:ℝ) ∈ Set.Icc 0 m := ⟨le_rfl, hm0.le⟩
    have hcw := hVc 0 h0mem
    rw [Metric.continuousWithinAt_iff] at hcw
    obtain ⟨δ, hδ, hδ'⟩ := hcw _ hV0
    set x := min (δ / 2) m with hx
    have hxpos : 0 < x := lt_min (by linarith) hm0
    have hxm : x ∈ Set.Icc 0 m := ⟨hxpos.le, min_le_right _ _⟩
    have hdist : dist x 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hxpos]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have := hδ' hxm hdist
    rw [Real.dist_eq, abs_lt] at this
    have hxmem : x ∈ admissibleVolume E lamD lamS T := ⟨hxm, by linarith [this.1]⟩
    exact lt_of_lt_of_le hxpos (le_csSup hbdd hxmem)
  have hmem' := hmem
  obtain ⟨⟨hμ0, hμm⟩, hVμ⟩ := hmem'
  set μ := muStar E lamD lamS T with hμ
  have hq1 : μ / (lamD * T) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨div_nonneg hμ0 hDT.le, (div_le_one hDT).2 (hμm.trans (min_le_left _ _))⟩
  have hq2 : μ / (lamS * T) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨div_nonneg hμ0 hST.le, (div_le_one hST).2 (hμm.trans (min_le_right _ _))⟩
  obtain ⟨hp, hFp, -⟩ := FdBarInv_spec E hq1
  obtain ⟨hw, hFw, -⟩ := FsInv_spec E hq2
  have hpdef : pStar E lamD lamS T = FdBarInv E (μ / (lamD * T)) := rfl
  have hwdef : wStar E lamD lamS T = FsInv E (μ / (lamS * T)) := rfl
  rw [← hpdef] at hp hFp
  rw [← hwdef] at hw hFw
  refine ⟨hpos, hmem, hp, hw, hFp, hFw, ?_⟩
  have hVeq : V E lamD lamS T μ = E.psiB (pStar E lamD lamS T) - E.psiS (wStar E lamD lamS T) := rfl
  have hF1 := FdBar_eq E hp
  have hF2 := Fs_eq E hw
  have e1 : E.psiB (pStar E lamD lamS T) =
      pStar E lamD lamS T - (1 - E.cdfB (pStar E lamD lamS T)) / E.fB (pStar E lamD lamS T) := rfl
  have e2 : E.psiS (wStar E lamD lamS T) =
      wStar E lamD lamS T + E.cdfS (wStar E lamD lamS T) / E.fS (wStar E lamD lamS T) := rfl
  have a1 : 1 - E.cdfB (pStar E lamD lamS T) = μ / (lamD * T) := by rw [← hF1, hFp]
  have a2 : E.cdfS (wStar E lamD lamS T) = μ / (lamS * T) := by rw [← hF2, hFw]
  rw [a1] at e1
  rw [a2] at e2
  linarith

lemma FdBarInv_anti (E : Environment) {q1 q2 : ℝ} (h1 : q1 ∈ Set.Icc (0:ℝ) 1)
    (h2 : q2 ∈ Set.Icc (0:ℝ) 1) (h : q1 ≤ q2) : FdBarInv E q2 ≤ FdBarInv E q1 := by
  obtain ⟨hc, hm, -, -⟩ := cdfB_props E
  obtain ⟨m1, f1, -⟩ := FdBarInv_spec E h1
  obtain ⟨m2, f2, -⟩ := FdBarInv_spec E h2
  by_contra hlt
  push_neg at hlt
  have := hm m1 m2 hlt
  rw [FdBar_eq E m1] at f1
  rw [FdBar_eq E m2] at f2
  linarith

lemma FsInv_mono (E : Environment) {q1 q2 : ℝ} (h1 : q1 ∈ Set.Icc (0:ℝ) 1)
    (h2 : q2 ∈ Set.Icc (0:ℝ) 1) (h : q1 ≤ q2) : FsInv E q1 ≤ FsInv E q2 := by
  obtain ⟨hc, hm, -, -⟩ := cdfS_props E
  obtain ⟨m1, f1, -⟩ := FsInv_spec E h1
  obtain ⟨m2, f2, -⟩ := FsInv_spec E h2
  by_contra hlt
  push_neg at hlt
  have := hm m2 m1 hlt
  rw [Fs_eq E m1] at f1
  rw [Fs_eq E m2] at f2
  linarith


open MechanismDesign.BilateralTrade in
lemma cdfB_hasDeriv (E : Environment) (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    {x : ℝ} (hx : x ∈ Set.Ioo E.loB E.hiB) : HasDerivAt E.cdfB (E.fB x) x := by
  have hint : IntervalIntegrable E.fB volume E.loB x :=
    E.fB_intervalIntegrable.mono_set (by
      rw [Set.uIcc_of_le hx.1.le, Set.uIcc_of_le E.loB_lt_hiB.le]
      exact Set.Icc_subset_Icc le_rfl hx.2.le)
  have hmeas : StronglyMeasurableAtFilter E.fB (nhds x) :=
    E.fB_measurable.stronglyMeasurable.stronglyMeasurableAtFilter
  have hca : ContinuousAt E.fB x := hcontB.continuousAt (Icc_mem_nhds hx.1 hx.2)
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hca

open MechanismDesign.BilateralTrade in
lemma cdfS_hasDeriv (E : Environment) (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    {x : ℝ} (hx : x ∈ Set.Ioo E.loS E.hiS) : HasDerivAt E.cdfS (E.fS x) x := by
  have hint : IntervalIntegrable E.fS volume E.loS x :=
    E.fS_intervalIntegrable.mono_set (by
      rw [Set.uIcc_of_le hx.1.le, Set.uIcc_of_le E.loS_lt_hiS.le]
      exact Set.Icc_subset_Icc le_rfl hx.2.le)
  have hmeas : StronglyMeasurableAtFilter E.fS (nhds x) :=
    E.fS_measurable.stronglyMeasurable.stronglyMeasurableAtFilter
  have hca : ContinuousAt E.fS x := hcontS.continuousAt (Icc_mem_nhds hx.1 hx.2)
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hca

open MechanismDesign.BilateralTrade in
lemma fB_int (E : Environment) {p : ℝ} (hp : p ∈ Set.Icc E.loB E.hiB) :
    ∫ y in p..E.hiB, E.fB y = 1 - E.cdfB p := by
  have h1 : IntervalIntegrable E.fB volume E.loB p :=
    E.fB_intervalIntegrable.mono_set (by
      rw [Set.uIcc_of_le hp.1, Set.uIcc_of_le E.loB_lt_hiB.le]
      exact Set.Icc_subset_Icc le_rfl hp.2)
  have := intervalIntegral.integral_interval_sub_left E.fB_intervalIntegrable h1
  have h2 : ∫ x in E.loB..E.hiB, E.fB x = 1 := E.fB_integral
  show _ = 1 - ∫ z in E.loB..p, E.fB z
  linarith

open MechanismDesign.BilateralTrade in
lemma psiB_integral (E : Environment) (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    {p : ℝ} (hp : p ∈ Set.Icc E.loB E.hiB) :
    ∫ y in p..E.hiB, E.psiB y * E.fB y = p * (1 - E.cdfB p) := by
  obtain ⟨hc, hm, h0, h1⟩ := cdfB_props E
  have hsub : Set.Icc p E.hiB ⊆ Set.Icc E.loB E.hiB := Set.Icc_subset_Icc hp.1 le_rfl
  have hpt : p ≤ E.hiB := hp.2
  have hG : ContinuousOn (fun y => y * (1 - E.cdfB y)) (Set.Icc p E.hiB) :=
    (continuousOn_id.mul (continuousOn_const.sub hc)).mono hsub
  have hD : ∀ y ∈ Set.Ioo p E.hiB,
      HasDerivAt (fun y => y * (1 - E.cdfB y)) ((1 - E.cdfB y) - y * E.fB y) y := by
    intro y hy
    have hy' : y ∈ Set.Ioo E.loB E.hiB := ⟨lt_of_le_of_lt hp.1 hy.1, hy.2⟩
    have := (hasDerivAt_id' y).mul ((hasDerivAt_const y (1:ℝ)).sub (cdfB_hasDeriv E hcontB hy'))
    exact this.congr_deriv (by simp only [Pi.sub_apply]; ring)
  have hI : IntervalIntegrable (fun y => (1 - E.cdfB y) - y * E.fB y) volume p E.hiB := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hpt]
    exact ((continuousOn_const.sub hc).sub (continuousOn_id.mul hcontB)).mono hsub
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpt hG hD hI
  have heq : ∫ y in p..E.hiB, E.psiB y * E.fB y =
      ∫ y in p..E.hiB, -((1 - E.cdfB y) - y * E.fB y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hpt] at hy
    have hy' : y ∈ Set.Icc E.loB E.hiB := hsub hy
    have hne : E.fB y ≠ 0 := (E.fB_pos y hy').ne'
    show (y - (1 - E.cdfB y) / E.fB y) * E.fB y = _
    field_simp
    ring
  rw [heq, intervalIntegral.integral_neg, hF, h1]
  simp

open MechanismDesign.BilateralTrade in
lemma psiS_integral (E : Environment) (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    {w : ℝ} (hw : w ∈ Set.Icc E.loS E.hiS) :
    ∫ x in E.loS..w, E.psiS x * E.fS x = w * E.cdfS w := by
  obtain ⟨hc, hm, h0, h1⟩ := cdfS_props E
  have hsub : Set.Icc E.loS w ⊆ Set.Icc E.loS E.hiS := Set.Icc_subset_Icc le_rfl hw.2
  have hpt : E.loS ≤ w := hw.1
  have hG : ContinuousOn (fun y => y * E.cdfS y) (Set.Icc E.loS w) :=
    (continuousOn_id.mul hc).mono hsub
  have hD : ∀ y ∈ Set.Ioo E.loS w,
      HasDerivAt (fun y => y * E.cdfS y) (E.cdfS y + y * E.fS y) y := by
    intro y hy
    have hy' : y ∈ Set.Ioo E.loS E.hiS := ⟨hy.1, lt_of_lt_of_le hy.2 hw.2⟩
    have := (hasDerivAt_id' y).mul (cdfS_hasDeriv E hcontS hy')
    exact this.congr_deriv (by ring)
  have hI : IntervalIntegrable (fun y => E.cdfS y + y * E.fS y) volume E.loS w := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hpt]
    exact (hc.add (continuousOn_id.mul hcontS)).mono hsub
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpt hG hD hI
  have heq : ∫ y in E.loS..w, E.psiS y * E.fS y = ∫ y in E.loS..w, (E.cdfS y + y * E.fS y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hpt] at hy
    have hy' : y ∈ Set.Icc E.loS E.hiS := hsub hy
    have hne : E.fS y ≠ 0 := (E.fS_pos y hy').ne'
    show (y + E.cdfS y / E.fS y) * E.fS y = _
    field_simp
    ring
  rw [heq, hF, h0]
  simp

open MechanismDesign.BilateralTrade in
lemma psiB_tail (E : Environment) (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB)) (η : ℝ)
    {x y : ℝ} (hx : x ∈ Set.Icc E.loB E.hiB) (hy : y ∈ Set.Icc E.loB E.hiB) (hxy : x ≤ y) :
    (x - η) * (1 - E.cdfB x) - (y - η) * (1 - E.cdfB y) =
      ∫ u in x..y, (E.psiB u - η) * E.fB u := by
  obtain ⟨hc, hm, h0, h1⟩ := cdfB_props E
  have hsub : ∀ a b : ℝ, a ∈ Set.Icc E.loB E.hiB → b ∈ Set.Icc E.loB E.hiB →
      Set.uIcc a b ⊆ Set.Icc E.loB E.hiB := fun a b ha hb => Set.uIcc_subset_Icc ha hb
  have hI1 : ∀ a b : ℝ, a ∈ Set.Icc E.loB E.hiB → b ∈ Set.Icc E.loB E.hiB →
      IntervalIntegrable (fun u => E.psiB u * E.fB u) volume a b := fun a b ha hb =>
    ((psiB_cont E hcontB).mul hcontB).mono (hsub a b ha hb) |>.intervalIntegrable
  have hI2 : ∀ a b : ℝ, a ∈ Set.Icc E.loB E.hiB → b ∈ Set.Icc E.loB E.hiB →
      IntervalIntegrable E.fB volume a b := fun a b ha hb =>
    hcontB.mono (hsub a b ha hb) |>.intervalIntegrable
  have hhi : E.hiB ∈ Set.Icc E.loB E.hiB := Set.right_mem_Icc.2 E.loB_lt_hiB.le
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hI1 x y hx hy) (hI1 y E.hiB hy hhi)
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hI2 x y hx hy) (hI2 y E.hiB hy hhi)
  rw [psiB_integral E hcontB hx, psiB_integral E hcontB hy] at e1
  rw [fB_int E hx, fB_int E hy] at e2
  have e3 : ∫ u in x..y, (E.psiB u - η) * E.fB u =
      (∫ u in x..y, E.psiB u * E.fB u) - η * ∫ u in x..y, E.fB u := by
    have : ∀ u, (E.psiB u - η) * E.fB u = E.psiB u * E.fB u - η * E.fB u := fun u => by ring
    simp_rw [this]
    rw [intervalIntegral.integral_sub (hI1 x y hx hy) ((hI2 x y hx hy).const_mul η),
      intervalIntegral.integral_const_mul]
  rw [e3]
  have a1 : (∫ u in x..y, E.fB u) = E.cdfB y - E.cdfB x := by linarith
  have a2 : (∫ u in x..y, E.psiB u * E.fB u) = x * (1 - E.cdfB x) - y * (1 - E.cdfB y) := by
    linarith
  rw [a1, a2]; ring

open MechanismDesign.BilateralTrade in
lemma psiS_tail (E : Environment) (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS)) (η : ℝ)
    {x y : ℝ} (hx : x ∈ Set.Icc E.loS E.hiS) (hy : y ∈ Set.Icc E.loS E.hiS) (hxy : x ≤ y) :
    (η - y) * E.cdfS y - (η - x) * E.cdfS x =
      ∫ u in x..y, (η - E.psiS u) * E.fS u := by
  obtain ⟨hc, hm, h0, h1⟩ := cdfS_props E
  have hsub : ∀ a b : ℝ, a ∈ Set.Icc E.loS E.hiS → b ∈ Set.Icc E.loS E.hiS →
      Set.uIcc a b ⊆ Set.Icc E.loS E.hiS := fun a b ha hb => Set.uIcc_subset_Icc ha hb
  have hI1 : ∀ a b : ℝ, a ∈ Set.Icc E.loS E.hiS → b ∈ Set.Icc E.loS E.hiS →
      IntervalIntegrable (fun u => E.psiS u * E.fS u) volume a b := fun a b ha hb =>
    ((psiS_cont E hcontS).mul hcontS).mono (hsub a b ha hb) |>.intervalIntegrable
  have hI2 : ∀ a b : ℝ, a ∈ Set.Icc E.loS E.hiS → b ∈ Set.Icc E.loS E.hiS →
      IntervalIntegrable E.fS volume a b := fun a b ha hb =>
    hcontS.mono (hsub a b ha hb) |>.intervalIntegrable
  have hlo : E.loS ∈ Set.Icc E.loS E.hiS := Set.left_mem_Icc.2 E.loS_lt_hiS.le
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hI1 E.loS x hlo hx) (hI1 x y hx hy)
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hI2 E.loS x hlo hx) (hI2 x y hx hy)
  rw [psiS_integral E hcontS hx, psiS_integral E hcontS hy] at e1
  have e2' : (∫ u in E.loS..x, E.fS u) = E.cdfS x := rfl
  have e2'' : (∫ u in E.loS..y, E.fS u) = E.cdfS y := rfl
  rw [e2', e2''] at e2
  have e3 : ∫ u in x..y, (η - E.psiS u) * E.fS u =
      η * (∫ u in x..y, E.fS u) - ∫ u in x..y, E.psiS u * E.fS u := by
    have : ∀ u, (η - E.psiS u) * E.fS u = η * E.fS u - E.psiS u * E.fS u := fun u => by ring
    simp_rw [this]
    rw [intervalIntegral.integral_sub ((hI2 x y hx hy).const_mul η) (hI1 x y hx hy),
      intervalIntegral.integral_const_mul]
  rw [e3]
  have a1 : (∫ u in x..y, E.fS u) = E.cdfS y - E.cdfS x := by linarith
  have a2 : (∫ u in x..y, E.psiS u * E.fS u) = y * E.cdfS y - x * E.cdfS x := by linarith
  rw [a1, a2]; ring

open MechanismDesign.BilateralTrade in
lemma V_nonpos_of_lt (E : Environment) (lamD lamS T : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hgap : E.loS < E.hiB) (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T)
    (hlt : muStar E lamD lamS T < min (lamD * T) (lamS * T)) :
    V E lamD lamS T (muStar E lamD lamS T) ≤ 0 := by
  by_contra hV
  have hV' : 0 < V E lamD lamS T (muStar E lamD lamS T) := not_le.mp hV
  obtain ⟨hpos, hmem, -⟩ := core E lamD lamS T hcontB hcontS hgap hd hs hT
  have hVc := V_cont E lamD lamS T hcontB hcontS hd hs hT
  set m := min (lamD * T) (lamS * T) with hmdef
  set μ := muStar E lamD lamS T with hμ
  have hbdd : BddAbove (admissibleVolume E lamD lamS T) := ⟨m, fun x hx => hx.1.2⟩
  have hμmem : μ ∈ Set.Icc 0 m := hmem.1
  have hcw := hVc μ hμmem
  rw [Metric.continuousWithinAt_iff] at hcw
  obtain ⟨δ, hδ, hδ'⟩ := hcw _ hV'
  set x := min (μ + δ / 2) m with hx
  have hxμ : μ < x := lt_min (by linarith) hlt
  have hxm : x ∈ Set.Icc 0 m := ⟨by linarith [hμmem.1], min_le_right _ _⟩
  have hdist : dist x μ < δ := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]
    have := min_le_left (μ + δ / 2) m
    linarith
  have := hδ' hxm hdist
  rw [Real.dist_eq, abs_lt] at this
  have hxa : x ∈ admissibleVolume E lamD lamS T := ⟨hxm, by linarith [this.1]⟩
  exact absurd (le_csSup hbdd hxa) (not_le.mpr hxμ)

open MechanismDesign.BilateralTrade in
lemma eta_exists (E : Environment) (lamD lamS T : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hgap : E.loS < E.hiB) (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T) :
    ∃ η : ℝ, E.psiS (wStar E lamD lamS T) ≤ η ∧ η ≤ E.psiB (pStar E lamD lamS T) ∧
      (E.loB < pStar E lamD lamS T → E.psiB (pStar E lamD lamS T) ≤ η) ∧
      (wStar E lamD lamS T < E.hiS → η ≤ E.psiS (wStar E lamD lamS T)) := by
  obtain ⟨hpos, hmem, hp, hw, hFp, hFw, hsp⟩ := core E lamD lamS T hcontB hcontS hgap hd hs hT
  have hDT : 0 < lamD * T := mul_pos hd hT
  have hST : 0 < lamS * T := mul_pos hs hT
  have hV : 0 ≤ V E lamD lamS T (muStar E lamD lamS T) := hmem.2
  have hVeq : V E lamD lamS T (muStar E lamD lamS T) =
      E.psiB (pStar E lamD lamS T) - E.psiS (wStar E lamD lamS T) := rfl
  by_cases hlo : E.loB < pStar E lamD lamS T
  · refine ⟨E.psiB (pStar E lamD lamS T), by linarith, le_rfl, fun _ => le_rfl, fun hw' => ?_⟩
    obtain ⟨hcB, hmB, h0B, h1B⟩ := cdfB_props E
    obtain ⟨hcS, hmS, h0S, h1S⟩ := cdfS_props E
    have hpl : 0 < E.cdfB (pStar E lamD lamS T) := by
      have := hmB (Set.left_mem_Icc.2 E.loB_lt_hiB.le) hp hlo
      rwa [h0B] at this
    have hwl : E.cdfS (wStar E lamD lamS T) < 1 := by
      have := hmS hw (Set.right_mem_Icc.2 E.loS_lt_hiS.le) hw'
      rwa [h1S] at this
    have hF1 := FdBar_eq E hp
    have hF2 := Fs_eq E hw
    have h1 : muStar E lamD lamS T < lamD * T := by
      have : muStar E lamD lamS T / (lamD * T) < 1 := by rw [← hFp, hF1]; linarith
      exact (div_lt_one hDT).1 this
    have h2 : muStar E lamD lamS T < lamS * T := by
      have : muStar E lamD lamS T / (lamS * T) < 1 := by rw [← hFw, hF2]; exact hwl
      exact (div_lt_one hST).1 this
    have := V_nonpos_of_lt E lamD lamS T hcontB hcontS hgap hd hs hT (lt_min h1 h2)
    linarith
  · exact ⟨E.psiS (wStar E lamD lamS T), le_rfl, by linarith, fun h => absurd h hlo,
      fun _ => le_rfl⟩

open MechanismDesign.BilateralTrade in
lemma supp_ineq (E : Environment) (lamD lamS T : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hgap : E.loS < E.hiB)
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T)
    {pc wc : ℝ} (hpc : pc ∈ Set.Icc E.loB E.hiB) (hwc : wc ∈ Set.Icc E.loS E.hiS)
    (hrate : lamD * (1 - E.cdfB pc) = lamS * E.cdfS wc) :
    lamD * (pc * (1 - E.cdfB pc)) - lamS * (wc * E.cdfS wc) ≤
      muStar E lamD lamS T * (pStar E lamD lamS T - wStar E lamD lamS T) / T := by
  obtain ⟨hpos, hmem, hp, hw, hFp, hFw, hsp⟩ := core E lamD lamS T hcontB hcontS hgap hd hs hT
  obtain ⟨η, ha, hb, hc, hd'⟩ := eta_exists E lamD lamS T hcontB hcontS hgap hd hs hT
  have hDT : 0 < lamD * T := mul_pos hd hT
  have hST : 0 < lamS * T := mul_pos hs hT
  set pS := pStar E lamD lamS T with hpS
  set wS := wStar E lamD lamS T with hwS
  set μ := muStar E lamD lamS T with hμ
  have hψB : ∀ x ∈ Set.Icc E.loB E.hiB,
      (x - η) * (1 - E.cdfB x) ≤ (pS - η) * (1 - E.cdfB pS) := by
    intro x hx
    rcases le_total x pS with h | h
    · have ht := psiB_tail E hcontB η hx hp h
      have hnp : ∫ u in x..pS, (E.psiB u - η) * E.fB u ≤ 0 := by
        rcases eq_or_lt_of_le h with he | hl
        · rw [he]; simp
        · have hlo : E.loB < pS := lt_of_le_of_lt hx.1 hl
          have : 0 ≤ ∫ u in x..pS, -((E.psiB u - η) * E.fB u) := by
            apply intervalIntegral.integral_nonneg h
            intro u hu
            have hu' : u ∈ Set.Icc E.loB E.hiB := ⟨hx.1.trans hu.1, hu.2.trans hp.2⟩
            have h1 : E.psiB u ≤ E.psiB pS := hreg.2 hu' hp hu.2
            have h2 := hc hlo
            have h3 := E.fB_pos u hu'
            nlinarith
          rw [intervalIntegral.integral_neg] at this
          linarith
      linarith
    · have ht := psiB_tail E hcontB η hp hx h
      have hnp : 0 ≤ ∫ u in pS..x, (E.psiB u - η) * E.fB u := by
        apply intervalIntegral.integral_nonneg h
        intro u hu
        have hu' : u ∈ Set.Icc E.loB E.hiB := ⟨hp.1.trans hu.1, hu.2.trans hx.2⟩
        have h1 : E.psiB pS ≤ E.psiB u := hreg.2 hp hu' hu.1
        have h3 := E.fB_pos u hu'
        have : 0 ≤ E.psiB u - η := by linarith
        exact mul_nonneg this h3.le
      linarith
  have hψS : ∀ x ∈ Set.Icc E.loS E.hiS,
      (η - x) * E.cdfS x ≤ (η - wS) * E.cdfS wS := by
    intro x hx
    rcases le_total x wS with h | h
    · have ht := psiS_tail E hcontS η hx hw h
      have hnp : 0 ≤ ∫ u in x..wS, (η - E.psiS u) * E.fS u := by
        apply intervalIntegral.integral_nonneg h
        intro u hu
        have hu' : u ∈ Set.Icc E.loS E.hiS := ⟨hx.1.trans hu.1, hu.2.trans hw.2⟩
        have h1 : E.psiS u ≤ E.psiS wS := hreg.1 hu' hw hu.2
        have h3 := E.fS_pos u hu'
        have : 0 ≤ η - E.psiS u := by linarith
        exact mul_nonneg this h3.le
      linarith
    · have ht := psiS_tail E hcontS η hw hx h
      have hnp : ∫ u in wS..x, (η - E.psiS u) * E.fS u ≤ 0 := by
        rcases eq_or_lt_of_le h with he | hl
        · rw [he]; simp
        · have hlo : wS < E.hiS := lt_of_lt_of_le hl hx.2
          have : 0 ≤ ∫ u in wS..x, -((η - E.psiS u) * E.fS u) := by
            apply intervalIntegral.integral_nonneg h
            intro u hu
            have hu' : u ∈ Set.Icc E.loS E.hiS := ⟨hw.1.trans hu.1, hu.2.trans hx.2⟩
            have h1 : E.psiS wS ≤ E.psiS u := hreg.1 hw hu' hu.1
            have h2 := hd' hlo
            have h3 := E.fS_pos u hu'
            nlinarith
          rw [intervalIntegral.integral_neg] at this
          linarith
      linarith
  have e1 : 1 - E.cdfB pS = μ / (lamD * T) := by rw [← FdBar_eq E hp, hFp]
  have e2 : E.cdfS wS = μ / (lamS * T) := by rw [← Fs_eq E hw, hFw]
  have k1 := mul_le_mul_of_nonneg_left (hψB pc hpc) hd.le
  have k2 := mul_le_mul_of_nonneg_left (hψS wc hwc) hs.le
  have k3 : η * (lamD * (1 - E.cdfB pc)) = η * (lamS * E.cdfS wc) := by rw [hrate]
  have k4 : lamD * ((pS - η) * (1 - E.cdfB pS)) + lamS * ((η - wS) * E.cdfS wS) =
      μ * (pS - wS) / T := by
    rw [e1, e2]; field_simp; ring
  nlinarith [k1, k2, k3, k4]

open MechanismDesign.BilateralTrade in
lemma pointwise_bound (E : Environment) (lamD lamS T : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hgap : E.loS < E.hiB)
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T) (p w : ℝ)
    (hrate : lamD * FdBar E p = lamS * Fs E w) :
    lamD * (p * FdBar E p) - lamS * (w * Fs E w) ≤
      muStar E lamD lamS T * (pStar E lamD lamS T - wStar E lamD lamS T) / T := by
  obtain ⟨hcB, hmB, h0B, h1B⟩ := cdfB_props E
  obtain ⟨hcS, hmS, h0S, h1S⟩ := cdfS_props E
  have hlB := E.loB_lt_hiB
  have hlS := E.loS_lt_hiS
  have hpc : max E.loB (min p E.hiB) ∈ Set.Icc E.loB E.hiB :=
    ⟨le_max_left _ _, max_le hlB.le (min_le_right _ _)⟩
  have hwc : max E.loS (min w E.hiS) ∈ Set.Icc E.loS E.hiS :=
    ⟨le_max_left _ _, max_le hlS.le (min_le_right _ _)⟩
  have hFp : FdBar E p = 1 - E.cdfB (max E.loB (min p E.hiB)) := rfl
  have hFw : Fs E w = E.cdfS (max E.loS (min w E.hiS)) := rfl
  have hrev : p * FdBar E p ≤
      max E.loB (min p E.hiB) * (1 - E.cdfB (max E.loB (min p E.hiB))) := by
    rw [hFp]
    rcases lt_or_ge p E.loB with h1 | h1
    · have : max E.loB (min p E.hiB) = E.loB := by
        rw [min_eq_left (by linarith), max_eq_left h1.le]
      rw [this, h0B]; nlinarith
    · rcases le_or_gt p E.hiB with h2 | h2
      · rw [min_eq_left h2, max_eq_right h1]
      · have : max E.loB (min p E.hiB) = E.hiB := by
          rw [min_eq_right h2.le, max_eq_right hlB.le]
        rw [this, h1B]; simp
  have hcost : max E.loS (min w E.hiS) * E.cdfS (max E.loS (min w E.hiS)) ≤
      w * E.cdfS (max E.loS (min w E.hiS)) := by
    rcases lt_or_ge w E.loS with h1 | h1
    · have : max E.loS (min w E.hiS) = E.loS := by
        rw [min_eq_left (by linarith), max_eq_left h1.le]
      rw [this, h0S]; simp
    · rcases le_or_gt w E.hiS with h2 | h2
      · rw [min_eq_left h2, max_eq_right h1]
      · have : max E.loS (min w E.hiS) = E.hiS := by
          rw [min_eq_right h2.le, max_eq_right hlS.le]
        rw [this, h1S]; linarith
  have key := supp_ineq E lamD lamS T hcontB hcontS hreg hgap hd hs hT hpc hwc
    (by rw [hFp, hFw] at hrate; exact hrate)
  have k1 := mul_le_mul_of_nonneg_left hrev hd.le
  have k2 := mul_le_mul_of_nonneg_left hcost hs.le
  rw [hFw]
  linarith

open MechanismDesign.BilateralTrade in
/-- C2. The fluid optimum is attained by the constant path `(p*, w*)`. -/
theorem fluid_value (E : Environment) (lamD lamS T : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hgap : E.loS < E.hiB)
    (hloB : 0 ≤ E.loB) (hloS : 0 ≤ E.loS)
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T) :
    fluidValue E lamD lamS T =
      muStar E lamD lamS T * (pStar E lamD lamS T - wStar E lamD lamS T) := by
  obtain ⟨hpos, hmem, hp, hw, hFp, hFw, hsp⟩ := core E lamD lamS T hcontB hcontS hgap hd hs hT
  have hDT : 0 < lamD * T := mul_pos hd hT
  have hST : 0 < lamS * T := mul_pos hs hT
  have hrate : lamD * FdBar E (pStar E lamD lamS T) = lamS * Fs E (wStar E lamD lamS T) := by
    rw [hFp, hFw]; field_simp
  unfold fluidValue
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨fun _ => (pStar E lamD lamS T, wStar E lamD lamS T),
      ⟨measurable_const, ?_, intervalIntegrable_const, intervalIntegrable_const⟩, ?_⟩
    · intro t _
      exact ⟨hloB.trans hp.1, hloS.trans hw.1, hrate⟩
    · unfold fluidObjective
      simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      rw [hFp, hFw]
      field_simp
  · rintro z ⟨π, ⟨hmeas, hfeas, hi1, hi2⟩, rfl⟩
    unfold fluidObjective
    rw [← intervalIntegral.integral_sub hi1 hi2]
    calc ∫ t in (0:ℝ)..T, (lamD * (π t).1 * FdBar E (π t).1 - lamS * (π t).2 * Fs E (π t).2)
        ≤ ∫ t in (0:ℝ)..T, (muStar E lamD lamS T * (pStar E lamD lamS T - wStar E lamD lamS T) / T) :=
          intervalIntegral.integral_mono_on hT.le (hi1.sub hi2) intervalIntegrable_const
            (fun t ht => by
              obtain ⟨-, -, hr⟩ := hfeas t ht
              have := pointwise_bound E lamD lamS T hcontB hcontS hreg hgap hd hs hT
                (π t).1 (π t).2 hr
              rw [mul_assoc, mul_assoc]
              exact this)
      _ = muStar E lamD lamS T * (pStar E lamD lamS T - wStar E lamD lamS T) := by
          simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
          field_simp

open MechanismDesign.BilateralTrade in
/-- C1. Fluid primitives: the optimal fluid volume is positive, the spread is positive,
and both sides request at the common rate `μ*/T`. -/
theorem fluid_primitives (E : Environment) (lamD lamS T : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hgap : E.loS < E.hiB)
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T) :
    0 < muStar E lamD lamS T ∧ wStar E lamD lamS T < pStar E lamD lamS T ∧
    lamD * T * FdBar E (pStar E lamD lamS T) = muStar E lamD lamS T ∧
    lamS * T * Fs E (wStar E lamD lamS T) = muStar E lamD lamS T := by
  have hDT : 0 < lamD * T := mul_pos hd hT
  have hST : 0 < lamS * T := mul_pos hs hT
  obtain ⟨hpos, -, hp, hw, hFp, hFw, hsp⟩ := core E lamD lamS T hcontB hcontS hgap hd hs hT
  refine ⟨hpos, ?_, ?_, ?_⟩
  · have h1 : 0 < (muStar E lamD lamS T / (lamD * T)) / E.fB (pStar E lamD lamS T) :=
      div_pos (div_pos hpos hDT) (E.fB_pos _ hp)
    have h2 : 0 ≤ (muStar E lamD lamS T / (lamS * T)) / E.fS (wStar E lamD lamS T) :=
      div_nonneg (div_pos hpos hST).le (E.fS_pos _ hw).le
    linarith
  · rw [hFp]; field_simp
  · rw [hFw]; field_simp

lemma V_scale (E : Environment) (hreg : E.Regular) (lamD lamS T lamD' lamS' k μ0 : ℝ)
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T) (hk : 0 < k)
    (hd' : k * lamD ≤ lamD') (hs' : k * lamS ≤ lamS')
    (hμ0 : μ0 ∈ Set.Icc 0 (min (lamD * T) (lamS * T))) :
    V E lamD lamS T μ0 ≤ V E lamD' lamS' T (k * μ0) := by
  have hDT : 0 < lamD * T := mul_pos hd hT
  have hST : 0 < lamS * T := mul_pos hs hT
  have hDT' : 0 < lamD' * T := mul_pos (lt_of_lt_of_le (mul_pos hk hd) hd') hT
  have hST' : 0 < lamS' * T := mul_pos (lt_of_lt_of_le (mul_pos hk hs) hs') hT
  have hq1 : μ0 / (lamD * T) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨div_nonneg hμ0.1 hDT.le, (div_le_one hDT).2 (hμ0.2.trans (min_le_left _ _))⟩
  have hq2 : μ0 / (lamS * T) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨div_nonneg hμ0.1 hST.le, (div_le_one hST).2 (hμ0.2.trans (min_le_right _ _))⟩
  have hl1 : k * μ0 / (lamD' * T) ≤ μ0 / (lamD * T) := by
    rw [div_le_div_iff₀ hDT' hDT]
    have : k * lamD * T ≤ lamD' * T := mul_le_mul_of_nonneg_right hd' hT.le
    nlinarith [hμ0.1]
  have hl2 : k * μ0 / (lamS' * T) ≤ μ0 / (lamS * T) := by
    rw [div_le_div_iff₀ hST' hST]
    have : k * lamS * T ≤ lamS' * T := mul_le_mul_of_nonneg_right hs' hT.le
    nlinarith [hμ0.1]
  have hq1' : k * μ0 / (lamD' * T) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨div_nonneg (mul_nonneg hk.le hμ0.1) hDT'.le, hl1.trans hq1.2⟩
  have hq2' : k * μ0 / (lamS' * T) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨div_nonneg (mul_nonneg hk.le hμ0.1) hST'.le, hl2.trans hq2.2⟩
  unfold V
  have a1 := hreg.2 (FdBarInv_spec E hq1).1 (FdBarInv_spec E hq1').1
    (FdBarInv_anti E hq1' hq1 hl1)
  have a2 := hreg.1 (FsInv_spec E hq2').1 (FsInv_spec E hq2).1
    (FsInv_mono E hq2' hq2 hl2)
  linarith

lemma aux_side (μ0 μn k L L' T M f : ℝ) (hk : 0 < k) (hL : 0 < L) (hL' : L' = k * L)
    (hT : 0 < T) (hM : 0 < M) (hf : 0 < f) (hfM : f ≤ M) (hμ : k * μ0 ≤ μn) (hμ0 : 0 ≤ μ0) :
    μ0 / (L * T * M) ≤ (μn / (L' * T)) / f := by
  have h1 : μ0 / (L * T) ≤ μn / (L' * T) := by
    rw [div_le_div_iff₀ (mul_pos hL hT) (mul_pos (by rw [hL']; exact mul_pos hk hL) hT)]
    rw [hL']
    nlinarith [mul_pos hL hT]
  have hμn : 0 ≤ μn / (L' * T) := le_trans (div_nonneg hμ0 (mul_pos hL hT).le) h1
  calc μ0 / (L * T * M) = (μ0 / (L * T)) / M := by rw [div_div]
    _ ≤ (μn / (L' * T)) / M := div_le_div_of_nonneg_right h1 hM.le
    _ ≤ (μn / (L' * T)) / f := div_le_div_of_nonneg_left hμn hf hfM

open MechanismDesign.BilateralTrade in
/-- C5. Scaling: the fluid volume grows like `n^{min αd αs}` and the spread stays
bounded away from zero. -/
theorem scaling_uniform (E : Environment) (lamD lamS T : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hgap : E.loS < E.hiB)
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T)
    (αd αs : ℝ) (had : 0 < αd) (has : 0 < αs) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ n : ℕ, 1 ≤ n →
      c * (n : ℝ) ^ min αd αs ≤
        muStar E ((n : ℝ) ^ αd * lamD) ((n : ℝ) ^ αs * lamS) T ∧
      δ ≤ pStar E ((n : ℝ) ^ αd * lamD) ((n : ℝ) ^ αs * lamS) T -
        wStar E ((n : ℝ) ^ αd * lamD) ((n : ℝ) ^ αs * lamS) T := by
  obtain ⟨hμ0pos, hμ0mem, -, -, -, -, -⟩ := core E lamD lamS T hcontB hcontS hgap hd hs hT
  have hDT : 0 < lamD * T := mul_pos hd hT
  have hST : 0 < lamS * T := mul_pos hs hT
  set μ0 := muStar E lamD lamS T with hμ0def
  obtain ⟨MB, hMB⟩ := isCompact_Icc.bddAbove_image hcontB
  obtain ⟨MS, hMS⟩ := isCompact_Icc.bddAbove_image hcontS
  have hMBp : 0 < max MB 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hMSp : 0 < max MS 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨μ0, min (μ0 / (lamD * T * max MB 1)) (μ0 / (lamS * T * max MS 1)),
    hμ0pos, lt_min (div_pos hμ0pos (mul_pos hDT hMBp)) (div_pos hμ0pos (mul_pos hST hMSp)), ?_⟩
  intro n hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hk1 : 1 ≤ (n:ℝ) ^ min αd αs := Real.one_le_rpow hn1 (le_min had.le has.le)
  have hk0 : 0 < (n:ℝ) ^ min αd αs := by linarith
  have hkd : (n:ℝ) ^ min αd αs ≤ (n:ℝ) ^ αd :=
    Real.rpow_le_rpow_of_exponent_le hn1 (min_le_left _ _)
  have hks : (n:ℝ) ^ min αd αs ≤ (n:ℝ) ^ αs :=
    Real.rpow_le_rpow_of_exponent_le hn1 (min_le_right _ _)
  set k := (n:ℝ) ^ min αd αs with hkdef
  have hlD : 0 < (n:ℝ) ^ αd * lamD := mul_pos (Real.rpow_pos_of_pos hn0 _) hd
  have hlS : 0 < (n:ℝ) ^ αs * lamS := mul_pos (Real.rpow_pos_of_pos hn0 _) hs
  have hkD : k * lamD ≤ (n:ℝ) ^ αd * lamD := mul_le_mul_of_nonneg_right hkd hd.le
  have hkS : k * lamS ≤ (n:ℝ) ^ αs * lamS := mul_le_mul_of_nonneg_right hks hs.le
  obtain ⟨hμnpos, hμnmem, hpn, hwn, hFpn, hFwn, hspn⟩ :=
    core E ((n:ℝ) ^ αd * lamD) ((n:ℝ) ^ αs * lamS) T hcontB hcontS hgap hlD hlS hT
  have hbdd : BddAbove (admissibleVolume E ((n:ℝ) ^ αd * lamD) ((n:ℝ) ^ αs * lamS) T) :=
    ⟨min (((n:ℝ) ^ αd * lamD) * T) (((n:ℝ) ^ αs * lamS) * T), fun x hx => hx.1.2⟩
  have part1 : k * μ0 ≤ muStar E ((n:ℝ) ^ αd * lamD) ((n:ℝ) ^ αs * lamS) T := by
    have hm0 : (μ0 ∈ Set.Icc 0 (min (lamD * T) (lamS * T))) := hμ0mem.1
    have hmem : k * μ0 ∈ admissibleVolume E ((n:ℝ) ^ αd * lamD) ((n:ℝ) ^ αs * lamS) T := by
      refine ⟨⟨mul_nonneg hk0.le hμ0pos.le, le_min ?_ ?_⟩, ?_⟩
      · calc k * μ0 ≤ k * (lamD * T) := mul_le_mul_of_nonneg_left (hm0.2.trans (min_le_left _ _)) hk0.le
          _ = (k * lamD) * T := by ring
          _ ≤ ((n:ℝ) ^ αd * lamD) * T := mul_le_mul_of_nonneg_right hkD hT.le
      · calc k * μ0 ≤ k * (lamS * T) := mul_le_mul_of_nonneg_left (hm0.2.trans (min_le_right _ _)) hk0.le
          _ = (k * lamS) * T := by ring
          _ ≤ ((n:ℝ) ^ αs * lamS) * T := mul_le_mul_of_nonneg_right hkS hT.le
      · exact hμ0mem.2.trans (V_scale E hreg lamD lamS T _ _ k μ0 hd hs hT hk0 hkD hkS hm0)
    exact le_csSup hbdd hmem
  refine ⟨by rw [mul_comm]; exact part1, ?_⟩
  set μn := muStar E ((n:ℝ) ^ αd * lamD) ((n:ℝ) ^ αs * lamS) T with hμn
  set pn := pStar E ((n:ℝ) ^ αd * lamD) ((n:ℝ) ^ αs * lamS) T with hpndef
  set wn := wStar E ((n:ℝ) ^ αd * lamD) ((n:ℝ) ^ αs * lamS) T with hwndef
  have hfB : E.fB pn ≤ max MB 1 := le_trans (hMB ⟨pn, hpn, rfl⟩) (le_max_left _ _)
  have hfS : E.fS wn ≤ max MS 1 := le_trans (hMS ⟨wn, hwn, rfl⟩) (le_max_left _ _)
  have hAnn : 0 ≤ (μn / (((n:ℝ) ^ αd * lamD) * T)) / E.fB pn :=
    div_nonneg (div_pos hμnpos (mul_pos hlD hT)).le (E.fB_pos _ hpn).le
  have hBnn : 0 ≤ (μn / (((n:ℝ) ^ αs * lamS) * T)) / E.fS wn :=
    div_nonneg (div_pos hμnpos (mul_pos hlS hT)).le (E.fS_pos _ hwn).le
  rcases min_choice αd αs with h | h
  · have hkeq : k = (n:ℝ) ^ αd := by rw [hkdef, h]
    have := aux_side μ0 μn k lamD ((n:ℝ) ^ αd * lamD) T (max MB 1) (E.fB pn) hk0 hd
      (by rw [hkeq]) hT hMBp (E.fB_pos _ hpn) hfB part1 hμ0pos.le
    exact (min_le_left _ _).trans (this.trans (by linarith))
  · have hkeq : k = (n:ℝ) ^ αs := by rw [hkdef, h]
    have := aux_side μ0 μn k lamS ((n:ℝ) ^ αs * lamS) T (max MS 1) (E.fS wn) hk0 hs
      (by rw [hkeq]) hT hMSp (E.fS_pos _ hwn) hfS part1 hμ0pos.le
    exact (min_le_right _ _).trans (this.trans (by linarith))



lemma worth_le_sum {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ) (u : M → ℝ) (v : N → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j) (huv : ∀ i j, a i j ≤ u i + v j) :
    AssignmentGame.CoreLP.worth a Finset.univ Finset.univ ≤ ∑ i, u i + ∑ j, v j := by
  classical
  unfold AssignmentGame.CoreLP.worth
  apply Finset.sup'_le
  intro P hP
  unfold AssignmentGame.CoreLP.matchings at hP
  rw [Finset.mem_filter] at hP
  obtain ⟨-, -, h1, h2⟩ := hP
  have e1 : ∑ p ∈ P, u p.1 = ∑ i ∈ P.image Prod.fst, u i := by
    rw [Finset.sum_image]
    intro p hp q hq hpq
    exact h1 p hp q hq hpq
  have e2 : ∑ p ∈ P, v p.2 = ∑ j ∈ P.image Prod.snd, v j := by
    rw [Finset.sum_image]
    intro p hp q hq hpq
    exact h2 p hp q hq hpq
  calc ∑ p ∈ P, a p.1 p.2 ≤ ∑ p ∈ P, (u p.1 + v p.2) :=
        Finset.sum_le_sum (fun p _ => huv p.1 p.2)
    _ = ∑ p ∈ P, u p.1 + ∑ p ∈ P, v p.2 := Finset.sum_add_distrib
    _ ≤ ∑ i, u i + ∑ j, v j := by
        rw [e1, e2]
        exact add_le_add
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hu i))
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hv i))

lemma worth_nonneg {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ) :
    0 ≤ AssignmentGame.CoreLP.worth a Finset.univ Finset.univ := by
  classical
  unfold AssignmentGame.CoreLP.worth
  have := Finset.le_sup' (fun P => ∑ p ∈ P, a p.1 p.2)
    (AssignmentGame.CoreLP.empty_mem_matchings (M := M) (N := N) Finset.univ Finset.univ)
  simpa using this

lemma Jbar_le (E : Environment) (b h η : ℝ) (hb : 0 ≤ b) (hh : 0 ≤ h) (ω : Ω) :
    Jbar E b h ω ≤ (∑ i : Fin ω.1.1, max (E.psiB (buyerValue ω i) - η) 0) +
      (∑ j : Fin ω.2.1, max (η - E.psiS (sellerCost ω j)) 0) := by
  unfold Jbar
  have := worth_le_sum (assignmentWeight E b h ω)
    (fun j => max (η - E.psiS (sellerCost ω j)) 0) (fun i => max (E.psiB (buyerValue ω i) - η) 0)
    (fun j => le_max_right _ _) (fun i => le_max_right _ _) (by
      intro j i
      unfold assignmentWeight
      have h1 : 0 ≤ b * max (sellerTime ω j - buyerTime ω i) 0 :=
        mul_nonneg hb (le_max_right _ _)
      have h2 : 0 ≤ h * max (buyerTime ω i - sellerTime ω j) 0 :=
        mul_nonneg hh (le_max_right _ _)
      have h3 := le_max_left (E.psiB (buyerValue ω i) - η) 0
      have h4 := le_max_left (η - E.psiS (sellerCost ω j)) 0
      linarith)
  linarith

lemma Jbar_nonneg (E : Environment) (b h : ℝ) (ω : Ω) : 0 ≤ Jbar E b h ω :=
  worth_nonneg _


section PoissonPart
open ProbabilityTheory
open scoped NNReal Nat


lemma poisson_hasSum_mean (r : ℝ≥0) :
    HasSum (fun n : ℕ => (Real.exp (-r) * (r:ℝ) ^ n / (n)!) * (n:ℝ)) (r:ℝ) := by
  have h1 : HasSum (fun n : ℕ => (r:ℝ) ^ n / (n)!) (Real.exp r) := by
    simpa [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (r : ℝ)
  have h2 := h1.mul_left (Real.exp (-r) * (r:ℝ))
  have hv : Real.exp (-r) * (r:ℝ) * Real.exp r = r := by
    rw [mul_right_comm, ← Real.exp_add]; simp
  rw [hv] at h2
  have e : (fun n : ℕ => (Real.exp (-r) * (r:ℝ) ^ (n+1) / ((n+1)!:ℕ)) * ((n+1:ℕ):ℝ)) =
      fun i : ℕ => Real.exp (-r) * (r:ℝ) * ((r:ℝ) ^ i / (i)!) := by
    funext n
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  have key : HasSum (fun n : ℕ => (Real.exp (-r) * (r:ℝ) ^ (n+1) / ((n+1)!:ℕ)) * ((n+1:ℕ):ℝ)) (r:ℝ) := by
    rw [e]; exact h2
  refine (hasSum_nat_add_iff' 1).1 ?_
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, sub_zero]
  exact key

lemma poisson_hasSum_fact2 (r : ℝ≥0) :
    HasSum (fun n : ℕ => (Real.exp (-r) * (r:ℝ) ^ n / (n)!) * ((n:ℝ) * ((n:ℝ) - 1))) ((r:ℝ)^2) := by
  have h1 : HasSum (fun n : ℕ => (r:ℝ) ^ n / (n)!) (Real.exp r) := by
    simpa [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (r : ℝ)
  have h2 := h1.mul_left (Real.exp (-r) * (r:ℝ)^2)
  have hv : Real.exp (-r) * (r:ℝ)^2 * Real.exp r = (r:ℝ)^2 := by
    rw [mul_right_comm, ← Real.exp_add]; simp
  rw [hv] at h2
  have e : (fun n : ℕ => (Real.exp (-r) * (r:ℝ) ^ (n+2) / ((n+2)!:ℕ)) *
        (((n+2:ℕ):ℝ) * (((n+2:ℕ):ℝ) - 1))) =
      fun i : ℕ => Real.exp (-r) * (r:ℝ)^2 * ((r:ℝ) ^ i / (i)!) := by
    funext n
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  have key : HasSum (fun n : ℕ => (Real.exp (-r) * (r:ℝ) ^ (n+2) / ((n+2)!:ℕ)) *
        (((n+2:ℕ):ℝ) * (((n+2:ℕ):ℝ) - 1))) ((r:ℝ)^2) := by
    rw [e]; exact h2
  refine (hasSum_nat_add_iff' 2).1 ?_
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.cast_zero,
    Nat.cast_one, sub_self, zero_mul, mul_zero, sub_zero, zero_add, zero_sub, mul_neg, mul_one, neg_zero, add_zero]
  exact key

lemma poisson_integrable_id (ρ : ℝ≥0) : Integrable (fun n : ℕ => (n:ℝ)) Po(ρ) := by
  rw [integrable_poissonMeasure_iff]
  refine (poisson_hasSum_mean ρ).summable.congr (fun n => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg n)]

lemma poisson_integral_id (ρ : ℝ≥0) : ∫ n : ℕ, (n:ℝ) ∂Po(ρ) = ρ := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  exact (poisson_hasSum_mean ρ).tsum_eq

lemma sideLaw_eq (r T : ℝ) (Q : Measure (ℝ × ℝ)) :
    sideLaw r T Q = (Po(⟨max (r * T) 0, le_max_right _ _⟩)).prod
      (Measure.infinitePi (fun _ : ℕ => Q)) := rfl

lemma wald (r T : ℝ) (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q]
    (g : ℝ × ℝ → ℝ) (hg : Measurable g) (hint : Integrable g Q) :
    Integrable (fun x : ℕ × (ℕ → ℝ × ℝ) => ∑ i ∈ Finset.range x.1, g (x.2 i)) (sideLaw r T Q) ∧
    ∫ x : ℕ × (ℕ → ℝ × ℝ), ∑ i ∈ Finset.range x.1, g (x.2 i) ∂(sideLaw r T Q) =
      max (r * T) 0 * ∫ z, g z ∂Q := by
  set ρ : ℝ≥0 := ⟨max (r * T) 0, le_max_right _ _⟩ with hρ
  rw [sideLaw_eq]
  have hev : ∀ i : ℕ, MeasureTheory.MeasurePreserving (fun x : ℕ → ℝ × ℝ => x i)
      (Measure.infinitePi (fun _ : ℕ => Q)) Q := fun i => measurePreserving_eval_infinitePi _ i
  have hxint : ∀ i : ℕ, Integrable (fun x : ℕ → ℝ × ℝ => g (x i))
      (Measure.infinitePi (fun _ : ℕ => Q)) := fun i =>
    (hev i).integrable_comp_of_integrable hint
  have hxint' : ∀ i : ℕ, ∫ x : ℕ → ℝ × ℝ, g (x i) ∂(Measure.infinitePi (fun _ : ℕ => Q)) =
      ∫ z, g z ∂Q := by
    intro i
    have := integral_map (μ := Measure.infinitePi (fun _ : ℕ => Q))
      (hev i).measurable.aemeasurable (f := g) hg.aestronglyMeasurable
    rw [(hev i).map_eq] at this
    exact this.symm
  have hxint'abs : ∀ i : ℕ, ∫ x : ℕ → ℝ × ℝ, ‖g (x i)‖ ∂(Measure.infinitePi (fun _ : ℕ => Q)) =
      ∫ z, ‖g z‖ ∂Q := by
    intro i
    have := integral_map (μ := Measure.infinitePi (fun _ : ℕ => Q))
      (hev i).measurable.aemeasurable (f := fun z => ‖g z‖) hg.norm.aestronglyMeasurable
    rw [(hev i).map_eq] at this
    exact this.symm
  have hmeas : Measurable (fun x : ℕ × (ℕ → ℝ × ℝ) => ∑ i ∈ Finset.range x.1, g (x.2 i)) := by
    apply measurable_from_prod_countable_right
    intro n
    show Measurable fun y : ℕ → ℝ × ℝ => ∑ i ∈ Finset.range n, g (y i)
    exact Finset.measurable_sum (Finset.range n) (fun i _ => hg.comp (measurable_pi_apply i))
  -- fiber facts
  have hfib : ∀ n : ℕ, Integrable (fun x : ℕ → ℝ × ℝ => ∑ i ∈ Finset.range n, g (x i))
      (Measure.infinitePi (fun _ : ℕ => Q)) := fun n => integrable_finsetSum _ (fun i _ => hxint i)
  have hfibv : ∀ n : ℕ, ∫ x : ℕ → ℝ × ℝ, ∑ i ∈ Finset.range n, g (x i)
      ∂(Measure.infinitePi (fun _ : ℕ => Q)) = n * ∫ z, g z ∂Q := by
    intro n
    rw [integral_finsetSum _ (fun i _ => hxint i)]
    simp [hxint']
  have hbound : ∀ n : ℕ, ∫ x : ℕ → ℝ × ℝ, ‖∑ i ∈ Finset.range n, g (x i)‖
      ∂(Measure.infinitePi (fun _ : ℕ => Q)) ≤ n * ∫ z, ‖g z‖ ∂Q := by
    intro n
    calc ∫ x : ℕ → ℝ × ℝ, ‖∑ i ∈ Finset.range n, g (x i)‖ ∂(Measure.infinitePi (fun _ : ℕ => Q))
        ≤ ∫ x : ℕ → ℝ × ℝ, ∑ i ∈ Finset.range n, ‖g (x i)‖ ∂(Measure.infinitePi (fun _ : ℕ => Q)) :=
          integral_mono (hfib n).norm (integrable_finsetSum _ (fun i _ => (hxint i).norm))
            (fun x => norm_sum_le _ _)
      _ = n * ∫ z, ‖g z‖ ∂Q := by
          rw [integral_finsetSum _ (fun i _ => (hxint i).norm)]
          simp only [hxint'abs, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hI : Integrable (fun x : ℕ × (ℕ → ℝ × ℝ) => ∑ i ∈ Finset.range x.1, g (x.2 i))
      (Po(ρ).prod (Measure.infinitePi (fun _ : ℕ => Q))) := by
    refine (integrable_prod_iff hmeas.aestronglyMeasurable).2 ⟨Filter.Eventually.of_forall (fun n => hfib n), ?_⟩
    refine Integrable.mono' ((poisson_integrable_id ρ).mul_const (∫ z, ‖g z‖ ∂Q)) ?_ ?_
    · exact (hmeas.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun n => by
        rw [Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
        exact hbound n)
  refine ⟨hI, ?_⟩
  rw [integral_prod _ hI]
  simp_rw [hfibv]
  rw [integral_mul_const, poisson_integral_id]
  rfl


end PoissonPart


lemma measurable_primitive (lo : ℝ) (f : ℝ → ℝ) (hf : Measurable f) :
    Measurable (fun y => ∫ z in lo..y, f z) := by
  have key1 : Measurable (fun y : ℝ => ∫ z in Set.Ioc lo y, f z) := by
    have hF : Measurable (fun p : ℝ × ℝ => Set.indicator {q : ℝ × ℝ | lo < q.2 ∧ q.2 ≤ q.1}
        (fun q => f q.2) p) := by
      apply Measurable.indicator
      · exact hf.comp measurable_snd
      · exact (measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd measurable_fst)
    have hm : Measurable (fun y : ℝ => ∫ z, Set.indicator {q : ℝ × ℝ | lo < q.2 ∧ q.2 ≤ q.1}
        (fun q => f q.2) (y, z) ∂volume) :=
      (hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
    convert hm using 1
    funext y
    symm
    have : (fun z : ℝ => Set.indicator {q : ℝ × ℝ | lo < q.2 ∧ q.2 ≤ q.1}
        (fun q => f q.2) (y, z)) = Set.indicator (Set.Ioc lo y) f := by
      funext z
      by_cases h : lo < z ∧ z ≤ y
      · simp [Set.indicator, h]
      · simp [Set.indicator, h]
    show (∫ z, Set.indicator {q : ℝ × ℝ | lo < q.2 ∧ q.2 ≤ q.1} (fun q => f q.2) (y, z)) = _
    rw [this, integral_indicator measurableSet_Ioc]
  have key2 : Measurable (fun y : ℝ => ∫ z in Set.Ioc y lo, f z) := by
    have hF : Measurable (fun p : ℝ × ℝ => Set.indicator {q : ℝ × ℝ | q.1 < q.2 ∧ q.2 ≤ lo}
        (fun q => f q.2) p) := by
      apply Measurable.indicator
      · exact hf.comp measurable_snd
      · exact (measurableSet_lt measurable_fst measurable_snd).inter
          (measurableSet_le measurable_snd measurable_const)
    have hm : Measurable (fun y : ℝ => ∫ z, Set.indicator {q : ℝ × ℝ | q.1 < q.2 ∧ q.2 ≤ lo}
        (fun q => f q.2) (y, z) ∂volume) :=
      (hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
    convert hm using 1
    funext y
    symm
    have : (fun z : ℝ => Set.indicator {q : ℝ × ℝ | q.1 < q.2 ∧ q.2 ≤ lo}
        (fun q => f q.2) (y, z)) = Set.indicator (Set.Ioc y lo) f := by
      funext z
      by_cases h : y < z ∧ z ≤ lo
      · simp [Set.indicator, h]
      · simp [Set.indicator, h]
    show (∫ z, Set.indicator {q : ℝ × ℝ | q.1 < q.2 ∧ q.2 ≤ lo} (fun q => f q.2) (y, z)) = _
    rw [this, integral_indicator measurableSet_Ioc]
  exact key1.sub key2

open MechanismDesign.BilateralTrade in
lemma measurable_psiB (E : Environment) : Measurable E.psiB := by
  have h1 : Measurable E.cdfB := measurable_primitive E.loB E.fB E.fB_measurable
  exact measurable_id.sub ((measurable_const.sub h1).div E.fB_measurable)

open MechanismDesign.BilateralTrade in
lemma measurable_psiS (E : Environment) : Measurable E.psiS := by
  have h1 : Measurable E.cdfS := measurable_primitive E.loS E.fS E.fS_measurable
  exact measurable_id.add (h1.div E.fS_measurable)

lemma measurable_worth {δ : Type*} [MeasurableSpace δ] {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → δ → ℝ) (ha : ∀ i j, Measurable (a i j)) :
    Measurable (fun x => AssignmentGame.CoreLP.worth (fun i j => a i j x) Finset.univ Finset.univ) := by
  classical
  unfold AssignmentGame.CoreLP.worth
  have hne : (AssignmentGame.CoreLP.matchings (M := M) (N := N) Finset.univ Finset.univ).Nonempty :=
    ⟨∅, AssignmentGame.CoreLP.empty_mem_matchings _ _⟩
  have key : (fun x => (AssignmentGame.CoreLP.matchings (M := M) (N := N) Finset.univ Finset.univ).sup'
      ⟨∅, AssignmentGame.CoreLP.empty_mem_matchings _ _⟩
      (fun P => ∑ p ∈ P, a p.1 p.2 x)) =
      (AssignmentGame.CoreLP.matchings (M := M) (N := N) Finset.univ Finset.univ).sup' hne
        (fun P x => ∑ p ∈ P, a p.1 p.2 x) := by
    funext x
    rw [Finset.sup'_apply]
  rw [key]
  apply Finset.measurable_sup'
  intro P _
  exact Finset.measurable_sum _ (fun p _ => ha p.1 p.2)

lemma weight_meas (E : Environment) (b h : ℝ) (n m : ℕ) (j : Fin m) (i : Fin n) :
    Measurable (fun xy : (ℕ → ℝ × ℝ) × (ℕ → ℝ × ℝ) =>
      E.psiB (xy.1 i).2 - E.psiS (xy.2 j).2 -
        b * max ((xy.2 j).1 - (xy.1 i).1) 0 - h * max ((xy.1 i).1 - (xy.2 j).1) 0) := by
  have hψB := measurable_psiB E
  have hψS := measurable_psiS E
  fun_prop

noncomputable def Gfun (E : Environment) (b h : ℝ) (n m : ℕ)
    (xy : (ℕ → ℝ × ℝ) × (ℕ → ℝ × ℝ)) : ℝ :=
  AssignmentGame.CoreLP.worth (M := Fin m) (N := Fin n)
      (fun j i => E.psiB (xy.1 i).2 - E.psiS (xy.2 j).2 -
        b * max ((xy.2 j).1 - (xy.1 i).1) 0 - h * max ((xy.1 i).1 - (xy.2 j).1) 0)
      Finset.univ Finset.univ

lemma G_meas (E : Environment) (b h : ℝ) (n m : ℕ) : Measurable (Gfun E b h n m) :=
  measurable_worth (fun (j : Fin m) (i : Fin n) (xy : (ℕ → ℝ × ℝ) × (ℕ → ℝ × ℝ)) =>
      E.psiB (xy.1 i).2 - E.psiS (xy.2 j).2 -
        b * max ((xy.2 j).1 - (xy.1 i).1) 0 - h * max ((xy.1 i).1 - (xy.2 j).1) 0)
      (fun j i => weight_meas E b h n m j i)

lemma Jbar_eq (E : Environment) (b h : ℝ) (ω : Ω) :
    Jbar E b h ω = Gfun E b h ω.1.1 ω.2.1 (ω.1.2, ω.2.2) := rfl

lemma hG_meas (E : Environment) (b h : ℝ) :
    Measurable (fun p : (ℕ × ℕ) × ((ℕ → ℝ × ℝ) × (ℕ → ℝ × ℝ)) => Gfun E b h p.1.1 p.1.2 p.2) :=
  measurable_from_prod_countable_right (fun nm => G_meas E b h nm.1 nm.2)

lemma Jbar_measurable (E : Environment) (b h : ℝ) : Measurable (Jbar E b h) := by
  have hpre : Measurable (fun ω : Ω => ((ω.1.1, ω.2.1), (ω.1.2, ω.2.2))) := by
    fun_prop
  have e : Jbar E b h = (fun p : (ℕ × ℕ) × ((ℕ → ℝ × ℝ) × (ℕ → ℝ × ℝ)) =>
      Gfun E b h p.1.1 p.1.2 p.2) ∘ (fun ω : Ω => ((ω.1.1, ω.2.1), (ω.1.2, ω.2.2))) := by
    funext ω
    exact Jbar_eq E b h ω
  rw [e]
  exact (hG_meas E b h).comp hpre


lemma timeLaw_prob (T : ℝ) (hT : 0 < T) : IsProbabilityMeasure (timeLaw T) := by
  refine ⟨?_⟩
  unfold timeLaw
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Icc, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity)]
  have : 1 / T * (T - 0) = 1 := by rw [sub_zero]; field_simp
  rw [this]; simp

open MechanismDesign.BilateralTrade in
lemma valLaw_prob (E : Environment) : IsProbabilityMeasure (valLaw E) := by
  refine ⟨?_⟩
  unfold valLaw
  have hI : IntegrableOn E.fB (Set.Icc E.loB E.hiB) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le E.loB_lt_hiB.le).1 E.fB_intervalIntegrable
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc E.loB E.hiB)] E.fB :=
    (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall (fun x hx => (E.fB_pos x hx).le))
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI hnn]
  have : ∫ x in Set.Icc E.loB E.hiB, E.fB x = 1 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le E.loB_lt_hiB.le]
    exact E.fB_integral
  rw [this]; simp

open MechanismDesign.BilateralTrade in
lemma costLaw_prob (E : Environment) : IsProbabilityMeasure (costLaw E) := by
  refine ⟨?_⟩
  unfold costLaw
  have hI : IntegrableOn E.fS (Set.Icc E.loS E.hiS) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le E.loS_lt_hiS.le).1 E.fS_intervalIntegrable
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc E.loS E.hiS)] E.fS :=
    (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall (fun x hx => (E.fS_pos x hx).le))
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI hnn]
  have : ∫ x in Set.Icc E.loS E.hiS, E.fS x = 1 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le E.loS_lt_hiS.le]
    exact E.fS_integral
  rw [this]; simp

open MechanismDesign.BilateralTrade in
lemma valLaw_integral (E : Environment) (g : ℝ → ℝ) :
    ∫ x, g x ∂valLaw E = ∫ x in Set.Icc E.loB E.hiB, E.fB x * g x := by
  unfold valLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    (E.fB_measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)) g]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  simp [ENNReal.toReal_ofReal (E.fB_pos x hx).le]

open MechanismDesign.BilateralTrade in
lemma costLaw_integral (E : Environment) (g : ℝ → ℝ) :
    ∫ x, g x ∂costLaw E = ∫ x in Set.Icc E.loS E.hiS, E.fS x * g x := by
  unfold costLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    (E.fS_measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)) g]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  simp [ENNReal.toReal_ofReal (E.fS_pos x hx).le]

open MechanismDesign.BilateralTrade in
lemma valLaw_integrable (E : Environment) (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc E.loB E.hiB)) : Integrable g (valLaw E) := by
  unfold valLaw
  rw [integrable_withDensity_iff_integrable_smul' (E.fB_measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  have : IntegrableOn (fun x => E.fB x * g x) (Set.Icc E.loB E.hiB) :=
    (hcontB.mul hg).integrableOn_Icc
  refine this.congr_fun (fun x hx => ?_) measurableSet_Icc
  simp [ENNReal.toReal_ofReal (E.fB_pos x hx).le]

open MechanismDesign.BilateralTrade in
lemma costLaw_integrable (E : Environment) (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc E.loS E.hiS)) : Integrable g (costLaw E) := by
  unfold costLaw
  rw [integrable_withDensity_iff_integrable_smul' (E.fS_measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  have : IntegrableOn (fun x => E.fS x * g x) (Set.Icc E.loS E.hiS) :=
    (hcontS.mul hg).integrableOn_Icc
  refine this.congr_fun (fun x hx => ?_) measurableSet_Icc
  simp [ENNReal.toReal_ofReal (E.fS_pos x hx).le]

lemma snd_marks (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (g : ℝ → ℝ) (hg : Measurable g) (hint : Integrable g ν) :
    Integrable (fun z : ℝ × ℝ => g z.2) (μ.prod ν) ∧
    ∫ z : ℝ × ℝ, g z.2 ∂(μ.prod ν) = ∫ x, g x ∂ν := by
  have mp : MeasurePreserving Prod.snd (μ.prod ν) ν := measurePreserving_snd
  refine ⟨mp.integrable_comp_of_integrable hint, ?_⟩
  have := integral_map (μ := μ.prod ν) mp.measurable.aemeasurable (f := g) hg.aestronglyMeasurable
  rw [mp.map_eq] at this
  exact this.symm

lemma sideLaw_prob (r T : ℝ) (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (sideLaw r T Q) := by
  unfold sideLaw
  have h1 : IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => Q)) := inferInstance
  have h2' : ∀ ρ : NNReal, IsProbabilityMeasure (ProbabilityTheory.poissonMeasure ρ) :=
    fun ρ => inferInstance
  have h2 := h2' ⟨max (r * T) 0, le_max_right _ _⟩
  infer_instance

open MechanismDesign.BilateralTrade in
lemma Seta_facts (E : Environment) (lamD lamS T η : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T) :
    Integrable (fun ω : Ω => (∑ i : Fin ω.1.1, max (E.psiB (buyerValue ω i) - η) 0) +
        (∑ j : Fin ω.2.1, max (η - E.psiS (sellerCost ω j)) 0)) (P E lamD lamS T) ∧
    ∫ ω : Ω, ((∑ i : Fin ω.1.1, max (E.psiB (buyerValue ω i) - η) 0) +
        (∑ j : Fin ω.2.1, max (η - E.psiS (sellerCost ω j)) 0)) ∂(P E lamD lamS T) =
      lamD * T * (∫ x in Set.Icc E.loB E.hiB, E.fB x * max (E.psiB x - η) 0) +
      lamS * T * (∫ x in Set.Icc E.loS E.hiS, E.fS x * max (η - E.psiS x) 0) := by
  have := timeLaw_prob T hT
  have := valLaw_prob E
  have := costLaw_prob E
  have hbm : IsProbabilityMeasure (buyerMark E T) := by unfold buyerMark; infer_instance
  have hsm : IsProbabilityMeasure (sellerMark E T) := by unfold sellerMark; infer_instance
  have hA : IsProbabilityMeasure (sideLaw lamD T (buyerMark E T)) := sideLaw_prob _ _ _
  have hB : IsProbabilityMeasure (sideLaw lamS T (sellerMark E T)) := sideLaw_prob _ _ _
  have gBm : Measurable (fun x => max (E.psiB x - η) 0) :=
    ((measurable_psiB E).sub measurable_const).max measurable_const
  have gSm : Measurable (fun x => max (η - E.psiS x) 0) :=
    (measurable_const.sub (measurable_psiS E)).max measurable_const
  have gBc : ContinuousOn (fun x => max (E.psiB x - η) 0) (Set.Icc E.loB E.hiB) :=
    (continuous_id.max continuous_const).comp_continuousOn
      ((psiB_cont E hcontB).sub continuousOn_const)
  have gSc : ContinuousOn (fun x => max (η - E.psiS x) 0) (Set.Icc E.loS E.hiS) :=
    (continuous_id.max continuous_const).comp_continuousOn
      (continuousOn_const.sub (psiS_cont E hcontS))
  obtain ⟨hBi, hBv⟩ := snd_marks (timeLaw T) (valLaw E) _ gBm (valLaw_integrable E hcontB _ gBc)
  obtain ⟨hSi, hSv⟩ := snd_marks (timeLaw T) (costLaw E) _ gSm (costLaw_integrable E hcontS _ gSc)
  obtain ⟨hWB1, hWB2⟩ := wald lamD T (buyerMark E T) (fun z => max (E.psiB z.2 - η) 0)
    (gBm.comp measurable_snd) hBi
  obtain ⟨hWS1, hWS2⟩ := wald lamS T (sellerMark E T) (fun z => max (η - E.psiS z.2) 0)
    (gSm.comp measurable_snd) hSi
  have eB : ∀ ω : Ω, ∑ i : Fin ω.1.1, max (E.psiB (buyerValue ω i) - η) 0 =
      ∑ i ∈ Finset.range ω.1.1, max (E.psiB (ω.1.2 i).2 - η) 0 := fun ω =>
    Fin.sum_univ_eq_sum_range (fun i => max (E.psiB (ω.1.2 i).2 - η) 0) ω.1.1
  have eS : ∀ ω : Ω, ∑ j : Fin ω.2.1, max (η - E.psiS (sellerCost ω j)) 0 =
      ∑ j ∈ Finset.range ω.2.1, max (η - E.psiS (ω.2.2 j).2) 0 := fun ω =>
    Fin.sum_univ_eq_sum_range (fun j => max (η - E.psiS (ω.2.2 j).2) 0) ω.2.1
  simp_rw [eB, eS]
  have mpf : MeasurePreserving Prod.fst ((sideLaw lamD T (buyerMark E T)).prod
      (sideLaw lamS T (sellerMark E T))) (sideLaw lamD T (buyerMark E T)) := measurePreserving_fst
  have mps : MeasurePreserving Prod.snd ((sideLaw lamD T (buyerMark E T)).prod
      (sideLaw lamS T (sellerMark E T))) (sideLaw lamS T (sellerMark E T)) := measurePreserving_snd
  have i1 := mpf.integrable_comp_of_integrable hWB1
  have i2 := mps.integrable_comp_of_integrable hWS1
  have hPeq : P E lamD lamS T = (sideLaw lamD T (buyerMark E T)).prod
      (sideLaw lamS T (sellerMark E T)) := rfl
  rw [hPeq]
  refine ⟨i1.add i2, ?_⟩
  have j1 := integral_map (μ := (sideLaw lamD T (buyerMark E T)).prod (sideLaw lamS T (sellerMark E T)))
    mpf.measurable.aemeasurable
    (f := fun x : ℕ × (ℕ → ℝ × ℝ) => ∑ i ∈ Finset.range x.1, max (E.psiB (x.2 i).2 - η) 0)
    (by
      apply Measurable.aestronglyMeasurable
      apply measurable_from_prod_countable_right
      intro n
      show Measurable fun y : ℕ → ℝ × ℝ => ∑ i ∈ Finset.range n, max (E.psiB (y i).2 - η) 0
      exact Finset.measurable_sum (Finset.range n) (fun i _ =>
        gBm.comp (measurable_snd.comp (measurable_pi_apply i))))
  have j2 := integral_map (μ := (sideLaw lamD T (buyerMark E T)).prod (sideLaw lamS T (sellerMark E T)))
    mps.measurable.aemeasurable
    (f := fun x : ℕ × (ℕ → ℝ × ℝ) => ∑ i ∈ Finset.range x.1, max (η - E.psiS (x.2 i).2) 0)
    (by
      apply Measurable.aestronglyMeasurable
      apply measurable_from_prod_countable_right
      intro n
      show Measurable fun y : ℕ → ℝ × ℝ => ∑ i ∈ Finset.range n, max (η - E.psiS (y i).2) 0
      exact Finset.measurable_sum (Finset.range n) (fun i _ =>
        gSm.comp (measurable_snd.comp (measurable_pi_apply i))))
  rw [mpf.map_eq] at j1
  rw [mps.map_eq] at j2
  refine Eq.trans (integral_add i1 i2) ?_
  have k1 : ∫ ω : (ℕ × (ℕ → ℝ × ℝ)) × (ℕ × (ℕ → ℝ × ℝ)),
      ∑ i ∈ Finset.range ω.1.1, max (E.psiB (ω.1.2 i).2 - η) 0
        ∂((sideLaw lamD T (buyerMark E T)).prod (sideLaw lamS T (sellerMark E T))) =
      ∫ x : ℕ × (ℕ → ℝ × ℝ), ∑ i ∈ Finset.range x.1, max (E.psiB (x.2 i).2 - η) 0
        ∂(sideLaw lamD T (buyerMark E T)) := j1.symm
  have k2 : ∫ ω : (ℕ × (ℕ → ℝ × ℝ)) × (ℕ × (ℕ → ℝ × ℝ)),
      ∑ i ∈ Finset.range ω.2.1, max (η - E.psiS (ω.2.2 i).2) 0
        ∂((sideLaw lamD T (buyerMark E T)).prod (sideLaw lamS T (sellerMark E T))) =
      ∫ x : ℕ × (ℕ → ℝ × ℝ), ∑ i ∈ Finset.range x.1, max (η - E.psiS (x.2 i).2) 0
        ∂(sideLaw lamS T (sellerMark E T)) := j2.symm
  show (∫ ω : (ℕ × (ℕ → ℝ × ℝ)) × (ℕ × (ℕ → ℝ × ℝ)),
      ∑ i ∈ Finset.range ω.1.1, max (E.psiB (ω.1.2 i).2 - η) 0
        ∂((sideLaw lamD T (buyerMark E T)).prod (sideLaw lamS T (sellerMark E T)))) +
      (∫ ω : (ℕ × (ℕ → ℝ × ℝ)) × (ℕ × (ℕ → ℝ × ℝ)),
      ∑ i ∈ Finset.range ω.2.1, max (η - E.psiS (ω.2.2 i).2) 0
        ∂((sideLaw lamD T (buyerMark E T)).prod (sideLaw lamS T (sellerMark E T)))) = _
  have hbmdef : buyerMark E T = (timeLaw T).prod (valLaw E) := rfl
  have hsmdef : sellerMark E T = (timeLaw T).prod (costLaw E) := rfl
  rw [k1, k2, hWB2, hWS2, hbmdef, hsmdef, hBv, hSv, valLaw_integral, costLaw_integral,
    max_eq_left (by positivity : (0:ℝ) ≤ lamD * T), max_eq_left (by positivity : (0:ℝ) ≤ lamS * T)]

open MechanismDesign.BilateralTrade in
lemma SB_value (E : Environment) (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hreg : E.Regular) (η p : ℝ) (hp : p ∈ Set.Icc E.loB E.hiB)
    (h1 : η ≤ E.psiB p) (h2 : E.loB < p → E.psiB p ≤ η) :
    ∫ x in Set.Icc E.loB E.hiB, E.fB x * max (E.psiB x - η) 0 = (p - η) * (1 - E.cdfB p) := by
  obtain ⟨hc, hm, h0, h1B⟩ := cdfB_props E
  have hlo : E.loB ∈ Set.Icc E.loB E.hiB := Set.left_mem_Icc.2 E.loB_lt_hiB.le
  have hhi : E.hiB ∈ Set.Icc E.loB E.hiB := Set.right_mem_Icc.2 E.loB_lt_hiB.le
  have gBc : ContinuousOn (fun x => max (E.psiB x - η) 0) (Set.Icc E.loB E.hiB) :=
    (continuous_id.max continuous_const).comp_continuousOn
      ((psiB_cont E hcontB).sub continuousOn_const)
  have hint : ∀ a b : ℝ, a ∈ Set.Icc E.loB E.hiB → b ∈ Set.Icc E.loB E.hiB →
      IntervalIntegrable (fun x => E.fB x * max (E.psiB x - η) 0) volume a b := fun a b ha hb =>
    ((hcontB.mul gBc).mono (Set.uIcc_subset_Icc ha hb)).intervalIntegrable
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le E.loB_lt_hiB.le,
    ← intervalIntegral.integral_add_adjacent_intervals (hint _ _ hlo hp) (hint _ _ hp hhi)]
  have z1 : ∫ x in E.loB..p, E.fB x * max (E.psiB x - η) 0 = 0 := by
    rcases eq_or_lt_of_le hp.1 with he | hl
    · rw [← he]; simp
    · have : Set.EqOn (fun x => E.fB x * max (E.psiB x - η) 0) (fun _ => 0) (Set.uIcc E.loB p) := by
        intro x hx
        rw [Set.uIcc_of_le hp.1] at hx
        have hx' : x ∈ Set.Icc E.loB E.hiB := ⟨hx.1, hx.2.trans hp.2⟩
        have := hreg.2 hx' hp hx.2
        have h3 := h2 hl
        have : max (E.psiB x - η) 0 = 0 := max_eq_right (by linarith)
        simp [this]
      rw [intervalIntegral.integral_congr this]; simp
  have z2 : ∫ x in p..E.hiB, E.fB x * max (E.psiB x - η) 0 =
      ∫ x in p..E.hiB, (E.psiB x - η) * E.fB x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hp.2] at hx
    have hx' : x ∈ Set.Icc E.loB E.hiB := ⟨hp.1.trans hx.1, hx.2⟩
    have := hreg.2 hp hx' hx.1
    have : max (E.psiB x - η) 0 = E.psiB x - η := max_eq_left (by linarith)
    simp only [this]; ring
  rw [z1, z2, ← psiB_tail E hcontB η hp hhi hp.2, h1B]
  ring

open MechanismDesign.BilateralTrade in
lemma SS_value (E : Environment) (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (η w : ℝ) (hw : w ∈ Set.Icc E.loS E.hiS)
    (h1 : E.psiS w ≤ η) (h2 : w < E.hiS → η ≤ E.psiS w) :
    ∫ x in Set.Icc E.loS E.hiS, E.fS x * max (η - E.psiS x) 0 = (η - w) * E.cdfS w := by
  obtain ⟨hc, hm, h0, h1S⟩ := cdfS_props E
  have hlo : E.loS ∈ Set.Icc E.loS E.hiS := Set.left_mem_Icc.2 E.loS_lt_hiS.le
  have hhi : E.hiS ∈ Set.Icc E.loS E.hiS := Set.right_mem_Icc.2 E.loS_lt_hiS.le
  have gSc : ContinuousOn (fun x => max (η - E.psiS x) 0) (Set.Icc E.loS E.hiS) :=
    (continuous_id.max continuous_const).comp_continuousOn
      (continuousOn_const.sub (psiS_cont E hcontS))
  have hint : ∀ a b : ℝ, a ∈ Set.Icc E.loS E.hiS → b ∈ Set.Icc E.loS E.hiS →
      IntervalIntegrable (fun x => E.fS x * max (η - E.psiS x) 0) volume a b := fun a b ha hb =>
    ((hcontS.mul gSc).mono (Set.uIcc_subset_Icc ha hb)).intervalIntegrable
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le E.loS_lt_hiS.le,
    ← intervalIntegral.integral_add_adjacent_intervals (hint _ _ hlo hw) (hint _ _ hw hhi)]
  have z1 : ∫ x in w..E.hiS, E.fS x * max (η - E.psiS x) 0 = 0 := by
    rcases eq_or_lt_of_le hw.2 with he | hl
    · rw [he]; simp
    · have : Set.EqOn (fun x => E.fS x * max (η - E.psiS x) 0) (fun _ => 0) (Set.uIcc w E.hiS) := by
        intro x hx
        rw [Set.uIcc_of_le hw.2] at hx
        have hx' : x ∈ Set.Icc E.loS E.hiS := ⟨hw.1.trans hx.1, hx.2⟩
        have := hreg.1 hw hx' hx.1
        have h3 := h2 hl
        have : max (η - E.psiS x) 0 = 0 := max_eq_right (by linarith)
        simp [this]
      rw [intervalIntegral.integral_congr this]; simp
  have z2 : ∫ x in E.loS..w, E.fS x * max (η - E.psiS x) 0 =
      ∫ x in E.loS..w, (η - E.psiS x) * E.fS x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hw.1] at hx
    have hx' : x ∈ Set.Icc E.loS E.hiS := ⟨hx.1, hx.2.trans hw.2⟩
    have := hreg.1 hx' hw hx.2
    have : max (η - E.psiS x) 0 = η - E.psiS x := max_eq_left (by linarith)
    simp only [this]; ring
  rw [z1, z2, ← psiS_tail E hcontS η hlo hw hw.1, h0]
  ring

lemma worth_ge_single {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ) (i : M) (j : N) :
    a i j ≤ AssignmentGame.CoreLP.worth a Finset.univ Finset.univ := by
  classical
  unfold AssignmentGame.CoreLP.worth
  have hmem : ({(i, j)} : Finset (M × N)) ∈
      AssignmentGame.CoreLP.matchings Finset.univ Finset.univ := by
    simp [AssignmentGame.CoreLP.matchings, AssignmentGame.CoreLP.IsMatching]
  have := Finset.le_sup' (fun P => ∑ p ∈ P, a p.1 p.2) hmem
  simpa using this

open MechanismDesign.BilateralTrade in
lemma Jbar_integral_pos (E : Environment) (lamD lamS T b h : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hgap : E.loS < E.hiB)
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (hint : Integrable (Jbar E b h) (P E lamD lamS T)) :
    0 < ∫ ω, Jbar E b h ω ∂P E lamD lamS T := by
  have hg0 : 0 < E.hiB - E.loS := by linarith
  set g := E.hiB - E.loS with hg
  obtain ⟨δ1, hδ1, hB⟩ : ∃ δ1 > 0, ∀ v ∈ Set.Icc E.loB E.hiB, E.hiB - δ1 < v →
      E.hiB - g / 4 < E.psiB v := by
    have hc := (psiB_cont E hcontB) E.hiB ⟨E.loB_lt_hiB.le, le_rfl⟩
    have hval : E.psiB E.hiB = E.hiB := by
      unfold Environment.psiB; rw [(cdfB_props E).2.2.2]; simp
    rw [Metric.continuousWithinAt_iff] at hc
    obtain ⟨δ, hδ, H⟩ := hc (g / 4) (by linarith)
    refine ⟨δ, hδ, fun v hv hlt => ?_⟩
    have hdist : dist v E.hiB < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hv.2]
    have := H hv hdist
    rw [hval, Real.dist_eq, abs_lt] at this
    linarith [this.1]
  obtain ⟨δ2, hδ2, hS⟩ : ∃ δ2 > 0, ∀ c ∈ Set.Icc E.loS E.hiS, c < E.loS + δ2 →
      E.psiS c < E.loS + g / 4 := by
    have hc := (psiS_cont E hcontS) E.loS ⟨le_rfl, E.loS_lt_hiS.le⟩
    have hval : E.psiS E.loS = E.loS := by
      unfold Environment.psiS; rw [(cdfS_props E).2.2.1]; simp
    rw [Metric.continuousWithinAt_iff] at hc
    obtain ⟨δ, hδ, H⟩ := hc (g / 4) (by linarith)
    refine ⟨δ, hδ, fun c hc' hlt => ?_⟩
    have hdist : dist c E.loS < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hc'.1]
    have := H hc' hdist
    rw [hval, Real.dist_eq, abs_lt] at this
    linarith [this.2]
  set κ := min T (g / (4 * (b + h + 1))) with hκ
  have hκpos : 0 < κ := lt_min hT (by positivity)
  have hκT : κ ≤ T := min_le_left _ _
  have hκg : b * κ + h * κ ≤ g / 4 := by
    have h1 : κ ≤ g / (4 * (b + h + 1)) := min_le_right _ _
    have h2 : κ * (4 * (b + h + 1)) ≤ g := by
      rw [le_div_iff₀ (by positivity)] at h1; exact h1
    nlinarith
  set a := max E.loB (E.hiB - δ1 / 2) with ha
  have haB : a < E.hiB := max_lt E.loB_lt_hiB (by linarith)
  set c' := min E.hiS (E.loS + δ2 / 2) with hc'
  have hcS : E.loS < c' := lt_min E.loS_lt_hiS (by linarith)
  set Iset : Set ℝ := Set.Icc 0 κ with hIset
  set Vset : Set ℝ := Set.Icc a E.hiB with hVset
  set Cset : Set ℝ := Set.Icc E.loS c' with hCset
  set A : Set Ω := (({1} : Set ℕ) ×ˢ {x : ℕ → ℝ × ℝ | x 0 ∈ Iset ×ˢ Vset}) ×ˢ
      (({1} : Set ℕ) ×ˢ {x : ℕ → ℝ × ℝ | x 0 ∈ Iset ×ˢ Cset}) with hA
  have hpre : ∀ (R : Set (ℝ × ℝ)), MeasurableSet R →
      MeasurableSet {x : ℕ → ℝ × ℝ | x 0 ∈ R} :=
    fun R hR => (measurable_pi_apply 0) hR
  have hAm : MeasurableSet A :=
    ((measurableSet_singleton 1).prod (hpre _ (measurableSet_Icc.prod measurableSet_Icc))).prod
      ((measurableSet_singleton 1).prod (hpre _ (measurableSet_Icc.prod measurableSet_Icc)))
  have hlow : ∀ ω, A.indicator (fun _ => g / 4) ω ≤ Jbar E b h ω := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hω
      simp only [Set.mem_singleton_iff] at h1 h3
      simp only [Set.mem_setOf_eq, Set.mem_prod] at h2 h4
      have i0 : 0 < ω.1.1 := by rw [h1]; norm_num
      have j0 : 0 < ω.2.1 := by rw [h3]; norm_num
      refine le_trans ?_ (worth_ge_single (assignmentWeight E b h ω) ⟨0, j0⟩ ⟨0, i0⟩)
      unfold assignmentWeight buyerValue sellerCost buyerTime sellerTime
      obtain ⟨⟨t1a, t1b⟩, v1a, v1b⟩ := h2
      obtain ⟨⟨t2a, t2b⟩, c1a, c1b⟩ := h4
      have hv : E.hiB - g / 4 < E.psiB (ω.1.2 0).2 :=
        hB _ ⟨le_trans (le_max_left _ _) v1a, v1b⟩
          (by linarith [le_max_right E.loB (E.hiB - δ1 / 2)])
      have hc2 : E.psiS (ω.2.2 0).2 < E.loS + g / 4 :=
        hS _ ⟨c1a, le_trans c1b (min_le_left _ _)⟩
          (by linarith [min_le_right E.hiS (E.loS + δ2 / 2)])
      have m1 : max ((ω.2.2 0).1 - (ω.1.2 0).1) 0 ≤ κ := max_le (by linarith) hκpos.le
      have m2 : max ((ω.1.2 0).1 - (ω.2.2 0).1) 0 ≤ κ := max_le (by linarith) hκpos.le
      have e1 : b * max ((ω.2.2 0).1 - (ω.1.2 0).1) 0 ≤ b * κ :=
        mul_le_mul_of_nonneg_left m1 hb
      have e2 : h * max ((ω.1.2 0).1 - (ω.2.2 0).1) 0 ≤ h * κ :=
        mul_le_mul_of_nonneg_left m2 hh
      linarith
    · rw [Set.indicator_of_notMem hω]; exact Jbar_nonneg E b h ω
  haveI : IsProbabilityMeasure (timeLaw T) := timeLaw_prob T hT
  haveI : IsProbabilityMeasure (valLaw E) := valLaw_prob E
  haveI : IsProbabilityMeasure (costLaw E) := costLaw_prob E
  haveI hbm : IsProbabilityMeasure (buyerMark E T) := by unfold buyerMark; infer_instance
  haveI hsm : IsProbabilityMeasure (sellerMark E T) := by unfold sellerMark; infer_instance
  haveI := sideLaw_prob lamD T (buyerMark E T)
  haveI := sideLaw_prob lamS T (sellerMark E T)
  haveI hP : IsProbabilityMeasure (P E lamD lamS T) := by unfold P; infer_instance
  have hTime : timeLaw T Iset ≠ 0 := by
    unfold timeLaw
    rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Icc, smul_eq_mul]
    have : Iset ∩ Set.Icc 0 T = Iset := Set.inter_eq_left.2 (Set.Icc_subset_Icc le_rfl hκT)
    rw [this, hIset, Real.volume_Icc]
    exact mul_ne_zero (ENNReal.ofReal_pos.2 (by positivity)).ne'
      (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hVal : valLaw E Vset ≠ 0 := by
    unfold valLaw
    rw [Ne, withDensity_apply_eq_zero' E.fB_measurable.ennreal_ofReal.aemeasurable,
      Measure.restrict_apply' measurableSet_Icc]
    have hsub : Vset ⊆ {x | ENNReal.ofReal (E.fB x) ≠ 0} ∩ Vset ∩ Set.Icc E.loB E.hiB := by
      intro x hx
      have hxI : x ∈ Set.Icc E.loB E.hiB := ⟨le_trans (le_max_left _ _) hx.1, hx.2⟩
      exact ⟨⟨(ENNReal.ofReal_pos.2 (E.fB_pos x hxI)).ne', hx⟩, hxI⟩
    intro h0
    have := measure_mono_null hsub h0
    rw [hVset, Real.volume_Icc] at this
    exact (ENNReal.ofReal_pos.2 (by linarith)).ne' this
  have hCost : costLaw E Cset ≠ 0 := by
    unfold costLaw
    rw [Ne, withDensity_apply_eq_zero' E.fS_measurable.ennreal_ofReal.aemeasurable,
      Measure.restrict_apply' measurableSet_Icc]
    have hsub : Cset ⊆ {x | ENNReal.ofReal (E.fS x) ≠ 0} ∩ Cset ∩ Set.Icc E.loS E.hiS := by
      intro x hx
      have hxI : x ∈ Set.Icc E.loS E.hiS := ⟨hx.1, le_trans hx.2 (min_le_left _ _)⟩
      exact ⟨⟨(ENNReal.ofReal_pos.2 (E.fS_pos x hxI)).ne', hx⟩, hxI⟩
    intro h0
    have := measure_mono_null hsub h0
    rw [hCset, Real.volume_Icc] at this
    exact (ENNReal.ofReal_pos.2 (by linarith)).ne' this
  have hIP : ∀ (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q] (R : Set (ℝ × ℝ)),
      MeasurableSet R → Measure.infinitePi (fun _ : ℕ => Q) {x | x 0 ∈ R} = Q R := by
    intro Q _ R hR
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => Q) 0).measure_preimage
      hR.nullMeasurableSet
  have hPo : ∀ r : ℝ, 0 < r →
      ProbabilityTheory.poissonMeasure ⟨max (r * T) 0, le_max_right _ _⟩ {1} ≠ 0 := by
    intro r hr h0
    have hρ : (0 : NNReal) < ⟨max (r * T) 0, le_max_right _ _⟩ := by
      exact NNReal.coe_pos.1 (lt_max_of_lt_left (mul_pos hr hT))
    have := ProbabilityTheory.poissonMeasure_real_singleton_pos (r := ⟨max (r * T) 0, le_max_right _ _⟩) 1 hρ
    rw [measureReal_def, h0] at this
    simp at this
  have hPA : P E lamD lamS T A ≠ 0 := by
    unfold P sideLaw
    rw [hA, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod,
      hIP _ _ (measurableSet_Icc.prod measurableSet_Icc),
      hIP _ _ (measurableSet_Icc.prod measurableSet_Icc)]
    refine mul_ne_zero (mul_ne_zero (hPo lamD hd) ?_) (mul_ne_zero (hPo lamS hs) ?_)
    · unfold buyerMark; rw [Measure.prod_prod]; exact mul_ne_zero hTime hVal
    · unfold sellerMark; rw [Measure.prod_prod]; exact mul_ne_zero hTime hCost
  have hint_ind : Integrable (A.indicator (fun _ => g / 4)) (P E lamD lamS T) :=
    (integrable_const (g / 4)).indicator hAm
  have h1 := integral_mono hint_ind hint hlow
  rw [integral_indicator_const _ hAm, smul_eq_mul] at h1
  have h2 : 0 < (P E lamD lamS T).real A := by
    rw [measureReal_def]; exact ENNReal.toReal_pos hPA (measure_ne_top _ _)
  have h3 : 0 < (P E lamD lamS T).real A * (g / 4) := mul_pos h2 (by linarith)
  linarith

open MechanismDesign.BilateralTrade in
/-- C3. Clairvoyant benchmark: integrable, positive, and at most the fluid value
(LP weak duality with a threshold `η` between `ψ_S(w*)` and `ψ_B(p*)`). -/
theorem clairvoyant_bound (E : Environment) (lamD lamS T b h : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hgap : E.loS < E.hiB)
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T)
    (hb : 0 ≤ b) (hh : 0 ≤ h) :
    Integrable (Jbar E b h) (P E lamD lamS T) ∧
    0 < ∫ ω, Jbar E b h ω ∂P E lamD lamS T ∧
    ∫ ω, Jbar E b h ω ∂P E lamD lamS T ≤
      muStar E lamD lamS T * (pStar E lamD lamS T - wStar E lamD lamS T) := by
  obtain ⟨hpos, hmem, hp, hw, hFp, hFw, hsp⟩ := core E lamD lamS T hcontB hcontS hgap hd hs hT
  obtain ⟨η, ha, hb', hc', hd'⟩ := eta_exists E lamD lamS T hcontB hcontS hgap hd hs hT
  obtain ⟨hSint, hSval⟩ := Seta_facts E lamD lamS T η hcontB hcontS hd hs hT
  have hJint : Integrable (Jbar E b h) (P E lamD lamS T) :=
    Integrable.mono' hSint (Jbar_measurable E b h).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_of_nonneg (Jbar_nonneg E b h ω)]
        exact Jbar_le E b h η hb hh ω))
  refine ⟨hJint, Jbar_integral_pos E lamD lamS T b h hcontB hcontS hreg hgap hd hs hT hb hh hJint, ?_⟩
  have hle : ∫ ω, Jbar E b h ω ∂P E lamD lamS T ≤ ∫ ω : Ω, ((∑ i : Fin ω.1.1,
      max (E.psiB (buyerValue ω i) - η) 0) +
        (∑ j : Fin ω.2.1, max (η - E.psiS (sellerCost ω j)) 0)) ∂(P E lamD lamS T) :=
    integral_mono hJint hSint (fun ω => Jbar_le E b h η hb hh ω)
  rw [hSval, SB_value E hcontB hreg η _ hp hb' hc', SS_value E hcontS hreg η _ hw ha hd'] at hle
  have hDT : 0 < lamD * T := mul_pos hd hT
  have hST : 0 < lamS * T := mul_pos hs hT
  have e1 : 1 - E.cdfB (pStar E lamD lamS T) = muStar E lamD lamS T / (lamD * T) := by
    rw [← FdBar_eq E hp, hFp]
  have e2 : E.cdfS (wStar E lamD lamS T) = muStar E lamD lamS T / (lamS * T) := by
    rw [← Fs_eq E hw, hFw]
  rw [e1, e2] at hle
  refine hle.trans (le_of_eq ?_)
  field_simp
  ring


section GenPart
open ProbabilityTheory
open scoped NNReal Nat

lemma sideLaw_eq' (r T : ℝ) (Q : Measure (ℝ × ℝ)) :
    sideLaw r T Q = (poissonMeasure ⟨max (r * T) 0, le_max_right _ _⟩).prod
      (Measure.infinitePi (fun _ : ℕ => Q)) := rfl

lemma poisson_mix {X : Type*} [MeasurableSpace X] (ρ : ℝ≥0) (μ : Measure X) [SFinite μ]
    (F : ℕ × X → ℝ) (hF : Measurable F) (hnn : ∀ z, 0 ≤ F z) (c : ℕ → ℝ)
    (hci : ∀ n, Integrable (fun x => F (n, x)) μ) (hcv : ∀ n, ∫ x, F (n, x) ∂μ = c n) (S : ℝ)
    (hS : HasSum (fun n : ℕ => (Real.exp (-ρ) * (ρ:ℝ) ^ n / (n)!) * c n) S) :
    Integrable F ((poissonMeasure ρ).prod μ) ∧ ∫ z, F z ∂((poissonMeasure ρ).prod μ) = S := by
  have hI : Integrable F ((poissonMeasure ρ).prod μ) := by
    refine (integrable_prod_iff hF.aestronglyMeasurable).2
      ⟨Filter.Eventually.of_forall hci, ?_⟩
    rw [integrable_poissonMeasure_iff]
    refine hS.summable.congr (fun n => ?_)
    have e : (fun x => ‖F (n, x)‖) = fun x => F (n, x) := funext (fun x => Real.norm_of_nonneg (hnn _))
    simp only [e]
    rw [Real.norm_of_nonneg (integral_nonneg (fun x => hnn _)), hcv n]
  refine ⟨hI, ?_⟩
  rw [integral_prod _ hI]
  simp_rw [hcv]
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  exact hS.tsum_eq

/-- Count of the first `s.1` marks that fall into `A`. -/
noncomputable def cnt (A : Set (ℝ × ℝ)) (s : ℕ × (ℕ → ℝ × ℝ)) : ℝ :=
  ∑ k ∈ Finset.range s.1, A.indicator (1 : ℝ × ℝ → ℝ) (s.2 k)

lemma cnt_meas (A : Set (ℝ × ℝ)) (hA : MeasurableSet A) : Measurable (cnt A) := by
  apply measurable_from_prod_countable_right
  intro n
  show Measurable fun y : ℕ → ℝ × ℝ => ∑ k ∈ Finset.range n, A.indicator (1 : ℝ × ℝ → ℝ) (y k)
  exact Finset.measurable_sum _ (fun k _ => (measurable_one.indicator hA).comp (measurable_pi_apply k))

lemma cnt_nonneg (A : Set (ℝ × ℝ)) (s : ℕ × (ℕ → ℝ × ℝ)) : 0 ≤ cnt A s :=
  Finset.sum_nonneg (fun k _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)

lemma ind_bound (A : Set (ℝ × ℝ)) (z : ℝ × ℝ) : ‖A.indicator (1 : ℝ × ℝ → ℝ) z‖ ≤ 1 := by
  by_cases hz : z ∈ A
  · simp [Set.indicator_of_mem hz]
  · simp [Set.indicator_of_notMem hz]

lemma pair_integral (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q] (g : ℝ × ℝ → ℝ)
    (hg : Measurable g) (k l : ℕ) (hkl : k ≠ l) :
    ∫ x, g (x k) * g (x l) ∂(Measure.infinitePi (fun _ : ℕ => Q)) =
      (∫ z, g z ∂Q) * (∫ z, g z ∂Q) := by
  have hmap := Measure.infinitePi_map_eval_prod (P := fun _ : ℕ => Q) hkl
  have hm : Measurable (fun ω : ℕ → ℝ × ℝ => (ω k, ω l)) := by fun_prop
  have hgm : Measurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => g z.1 * g z.2) :=
    (hg.comp measurable_fst).mul (hg.comp measurable_snd)
  have : ∫ x, g (x k) * g (x l) ∂(Measure.infinitePi (fun _ : ℕ => Q)) =
      ∫ z, g z.1 * g z.2 ∂((Measure.infinitePi (fun _ : ℕ => Q)).map (fun ω => (ω k, ω l))) :=
    (integral_map (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) => g z.1 * g z.2) hm.aemeasurable
      hgm.aestronglyMeasurable).symm
  rw [this, hmap, integral_prod_mul]

lemma cnt_fiber (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q] (A : Set (ℝ × ℝ))
    (hA : MeasurableSet A) (n : ℕ) :
    Integrable (fun x => cnt A (n, x)) (Measure.infinitePi (fun _ : ℕ => Q)) ∧
    ∫ x, cnt A (n, x) ∂(Measure.infinitePi (fun _ : ℕ => Q)) = n * Q.real A ∧
    Integrable (fun x => cnt A (n, x) ^ 2) (Measure.infinitePi (fun _ : ℕ => Q)) ∧
    ∫ x, cnt A (n, x) ^ 2 ∂(Measure.infinitePi (fun _ : ℕ => Q)) =
      n * Q.real A + (n * (n - 1 : ℝ)) * Q.real A ^ 2 := by
  set IP := Measure.infinitePi (fun _ : ℕ => Q)
  set g : ℝ × ℝ → ℝ := A.indicator 1 with hgdef
  have hg : Measurable g := measurable_one.indicator hA
  have hev : ∀ i : ℕ, MeasurePreserving (fun x : ℕ → ℝ × ℝ => x i) IP Q :=
    fun i => measurePreserving_eval_infinitePi _ i
  have hgi : ∀ k : ℕ, Integrable (fun x : ℕ → ℝ × ℝ => g (x k)) IP := fun k =>
    Integrable.mono' (integrable_const (1:ℝ)) (hg.comp (measurable_pi_apply k)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => ind_bound A (x k)))
  have hgv : ∀ k : ℕ, ∫ x, g (x k) ∂IP = Q.real A := by
    intro k
    have := integral_map (μ := IP) (hev k).measurable.aemeasurable (f := g) hg.aestronglyMeasurable
    rw [(hev k).map_eq] at this
    rw [← this, hgdef, integral_indicator_one hA]
  have hgg : ∀ k l : ℕ, Integrable (fun x : ℕ → ℝ × ℝ => g (x k) * g (x l)) IP := fun k l =>
    Integrable.mono' (integrable_const (1:ℝ))
      ((hg.comp (measurable_pi_apply k)).mul (hg.comp (measurable_pi_apply l))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by
        rw [norm_mul]
        have h1 := ind_bound A (x k)
        have h2 := ind_bound A (x l)
        have h3 : 0 ≤ ‖g (x k)‖ := norm_nonneg _
        have h4 : 0 ≤ ‖g (x l)‖ := norm_nonneg _
        nlinarith))
  have hsq : ∀ z, g z * g z = g z := by
    intro z
    by_cases hz : z ∈ A
    · simp [hgdef, Set.indicator_of_mem hz]
    · simp [hgdef, Set.indicator_of_notMem hz]
  have hpair : ∀ k l : ℕ, ∫ x, g (x k) * g (x l) ∂IP =
      Q.real A ^ 2 + (if k = l then Q.real A - Q.real A ^ 2 else 0) := by
    intro k l
    by_cases hkl : k = l
    · subst hkl
      simp only [hsq, if_true, hgv]
      ring
    · rw [if_neg hkl, pair_integral Q g hg k l hkl]
      have : ∫ z, g z ∂Q = Q.real A := by rw [hgdef, integral_indicator_one hA]
      rw [this]; ring
  have hcnt : (fun x => cnt A (n, x)) = fun x => ∑ k ∈ Finset.range n, g (x k) := rfl
  have hcnt2 : (fun x => cnt A (n, x) ^ 2) =
      fun x => ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, g (x k) * g (x l) := by
    funext x
    show (∑ k ∈ Finset.range n, g (x k)) ^ 2 = _
    rw [sq, Finset.sum_mul_sum]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcnt]; exact integrable_finsetSum _ (fun k _ => hgi k)
  · rw [hcnt, integral_finsetSum _ (fun k _ => hgi k)]
    simp [hgv]
  · rw [hcnt2]
    exact integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hgg k l))
  · rw [hcnt2, integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hgg k l))]
    have hin : ∀ k ∈ Finset.range n, ∫ x, ∑ l ∈ Finset.range n, g (x k) * g (x l) ∂IP =
        n * Q.real A ^ 2 + (Q.real A - Q.real A ^ 2) := by
      intro k hk
      rw [integral_finsetSum _ (fun l _ => hgg k l)]
      simp only [hpair]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq (Finset.range n) k, if_pos hk]
      simp
    rw [Finset.sum_congr rfl hin]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring

lemma cnt_moments (r T : ℝ) (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q] (A : Set (ℝ × ℝ))
    (hA : MeasurableSet A) :
    Integrable (cnt A) (sideLaw r T Q) ∧
    ∫ s, cnt A s ∂(sideLaw r T Q) = max (r * T) 0 * Q.real A ∧
    Integrable (fun s => cnt A s ^ 2) (sideLaw r T Q) ∧
    ∫ s, cnt A s ^ 2 ∂(sideLaw r T Q) =
      max (r * T) 0 * Q.real A + (max (r * T) 0 * Q.real A) ^ 2 := by
  set ρ : ℝ≥0 := ⟨max (r * T) 0, le_max_right _ _⟩ with hρ
  have hρv : (ρ : ℝ) = max (r * T) 0 := rfl
  have hfib := cnt_fiber Q A hA
  obtain ⟨h1, h2⟩ := poisson_mix ρ (Measure.infinitePi (fun _ : ℕ => Q)) (cnt A) (cnt_meas A hA)
    (cnt_nonneg A) (fun n => n * Q.real A) (fun n => (hfib n).1) (fun n => (hfib n).2.1)
    ((ρ : ℝ) * Q.real A) (by
      have := (poisson_hasSum_mean ρ).mul_right (Q.real A)
      simpa only [mul_assoc] using this)
  obtain ⟨h3, h4⟩ := poisson_mix ρ (Measure.infinitePi (fun _ : ℕ => Q)) (fun s => cnt A s ^ 2)
    ((cnt_meas A hA).pow_const 2) (fun s => sq_nonneg _)
    (fun n => n * Q.real A + (n * (n - 1 : ℝ)) * Q.real A ^ 2) (fun n => (hfib n).2.2.1)
    (fun n => (hfib n).2.2.2)
    ((ρ : ℝ) * Q.real A + ((ρ : ℝ) * Q.real A) ^ 2) (by
      have h' := ((poisson_hasSum_mean ρ).mul_right (Q.real A)).add
        ((poisson_hasSum_fact2 ρ).mul_right (Q.real A ^ 2))
      have e : (fun n : ℕ => (Real.exp (-ρ) * (ρ:ℝ) ^ n / (n)!) *
          (n * Q.real A + (n * (n - 1 : ℝ)) * Q.real A ^ 2)) =
          fun n : ℕ => (Real.exp (-ρ) * (ρ:ℝ) ^ n / (n)!) * n * Q.real A +
            (Real.exp (-ρ) * (ρ:ℝ) ^ n / (n)!) * (n * (n - 1 : ℝ)) * Q.real A ^ 2 := by
        funext n; ring
      have e1 : ((ρ:ℝ) * Q.real A + ((ρ:ℝ) * Q.real A) ^ 2) =
          (ρ:ℝ) * Q.real A + (ρ:ℝ) ^ 2 * Q.real A ^ 2 := by ring
      rw [e, e1]; exact h')
  exact ⟨h1, by rw [sideLaw_eq']; exact h2, h3, by rw [sideLaw_eq']; exact h4⟩

end GenPart

/-- Generic difference bound for independent coordinates with Poisson-like moments. -/
lemma diff_bound {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : α → ℝ) (Y : β → ℝ) (m : ℝ)
    (hX : Integrable X μ) (hX2 : Integrable (fun a => X a ^ 2) μ)
    (hY : Integrable Y ν) (hY2 : Integrable (fun b => Y b ^ 2) ν)
    (hXm : ∫ a, X a ∂μ = m) (hYm : ∫ b, Y b ∂ν = m)
    (hX2m : ∫ a, X a ^ 2 ∂μ = m + m ^ 2) (hY2m : ∫ b, Y b ^ 2 ∂ν = m + m ^ 2) :
    Integrable (fun z : α × β => X z.1 - Y z.2) (μ.prod ν) ∧
    ∫ z, (X z.1 - Y z.2) ∂(μ.prod ν) = 0 ∧
    Integrable (fun z : α × β => |X z.1 - Y z.2|) (μ.prod ν) ∧
    ∫ z, |X z.1 - Y z.2| ∂(μ.prod ν) ≤ Real.sqrt (2 * m) := by
  have pf : MeasurePreserving Prod.fst (μ.prod ν) μ := measurePreserving_fst
  have ps : MeasurePreserving Prod.snd (μ.prod ν) ν := measurePreserving_snd
  have iX : Integrable (fun z : α × β => X z.1) (μ.prod ν) := pf.integrable_comp_of_integrable hX
  have iY : Integrable (fun z : α × β => Y z.2) (μ.prod ν) := ps.integrable_comp_of_integrable hY
  have iX2 : Integrable (fun z : α × β => X z.1 ^ 2) (μ.prod ν) :=
    pf.integrable_comp_of_integrable hX2
  have iY2 : Integrable (fun z : α × β => Y z.2 ^ 2) (μ.prod ν) :=
    ps.integrable_comp_of_integrable hY2
  have iXY : Integrable (fun z : α × β => X z.1 * Y z.2) (μ.prod ν) := hX.mul_prod hY
  have vX : ∫ z : α × β, X z.1 ∂(μ.prod ν) = m := by
    rw [integral_fun_fst]; simp [hXm]
  have vY : ∫ z : α × β, Y z.2 ∂(μ.prod ν) = m := by
    rw [integral_fun_snd]; simp [hYm]
  have vX2 : ∫ z : α × β, X z.1 ^ 2 ∂(μ.prod ν) = m + m ^ 2 := by
    rw [integral_fun_fst (f := fun a => X a ^ 2)]; simp [hX2m]
  have vY2 : ∫ z : α × β, Y z.2 ^ 2 ∂(μ.prod ν) = m + m ^ 2 := by
    rw [integral_fun_snd (f := fun b => Y b ^ 2)]; simp [hY2m]
  have vXY : ∫ z : α × β, X z.1 * Y z.2 ∂(μ.prod ν) = m * m := by
    rw [integral_prod_mul, hXm, hYm]
  have iD : Integrable (fun z : α × β => X z.1 - Y z.2) (μ.prod ν) := iX.sub iY
  have iA : Integrable (fun z : α × β => |X z.1 - Y z.2|) (μ.prod ν) := iD.abs
  have iD2 : Integrable (fun z : α × β => (X z.1 - Y z.2) ^ 2) (μ.prod ν) := by
    have : (fun z : α × β => (X z.1 - Y z.2) ^ 2) =
        fun z => X z.1 ^ 2 - 2 * (X z.1 * Y z.2) + Y z.2 ^ 2 := by funext z; ring
    rw [this]; exact (iX2.sub (iXY.const_mul 2)).add iY2
  have vD2 : ∫ z : α × β, (X z.1 - Y z.2) ^ 2 ∂(μ.prod ν) = 2 * m := by
    have : (fun z : α × β => (X z.1 - Y z.2) ^ 2) =
        fun z => X z.1 ^ 2 - 2 * (X z.1 * Y z.2) + Y z.2 ^ 2 := by funext z; ring
    have i1 : Integrable (fun z : α × β => X z.1 ^ 2 - 2 * (X z.1 * Y z.2)) (μ.prod ν) :=
      iX2.sub (iXY.const_mul 2)
    rw [this, integral_add i1 iY2, integral_sub iX2 (iXY.const_mul 2),
      integral_const_mul, vX2, vXY, vY2]
    ring
  refine ⟨iD, ?_, iA, ?_⟩
  · rw [integral_sub iX iY, vX, vY]; ring
  · set a := ∫ z, |X z.1 - Y z.2| ∂(μ.prod ν) with ha
    have ha0 : 0 ≤ a := integral_nonneg (fun z => abs_nonneg _)
    have key : 0 ≤ ∫ z : α × β, (|X z.1 - Y z.2| - a) ^ 2 ∂(μ.prod ν) :=
      integral_nonneg (fun z => sq_nonneg _)
    have e : (fun z : α × β => (|X z.1 - Y z.2| - a) ^ 2) =
        fun z => (X z.1 - Y z.2) ^ 2 - (2 * a) * |X z.1 - Y z.2| + a ^ 2 := by
      funext z; rw [sub_sq, sq_abs]; ring
    have i2 : Integrable (fun z : α × β => (X z.1 - Y z.2) ^ 2 - (2 * a) * |X z.1 - Y z.2|)
        (μ.prod ν) := iD2.sub (iA.const_mul (2 * a))
    rw [e, integral_add i2 (integrable_const _),
      integral_sub iD2 (iA.const_mul (2 * a)), integral_const_mul, vD2, integral_const] at key
    rw [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at key
    rw [← ha] at key
    have h2 : a ^ 2 ≤ 2 * m := by nlinarith
    calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha0).symm
      _ ≤ Real.sqrt (2 * m) := Real.sqrt_le_sqrt h2



/-! ### C4b specialisation -/

lemma Nd_eq (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (t : ℝ) :
    (Nd E lamD lamS T ω t : ℝ) = cnt (Set.Iic t ×ˢ Set.Ici (pStar E lamD lamS T)) ω.1 := by
  unfold Nd reqB cnt
  rw [Finset.filter_filter, Finset.card_filter]
  push_cast
  rw [← Fin.sum_univ_eq_sum_range (fun k => (Set.Iic t ×ˢ Set.Ici (pStar E lamD lamS T)).indicator
    (1 : ℝ × ℝ → ℝ) (ω.1.2 k))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold buyerValue buyerTime
  rw [Set.indicator_apply]
  simp only [Set.mem_prod, Set.mem_Iic, Set.mem_Ici, Pi.one_apply]
  by_cases h1 : pStar E lamD lamS T ≤ (ω.1.2 i).2 <;> by_cases h2 : (ω.1.2 i).1 ≤ t <;>
    simp [h1, h2]

lemma Ns_eq (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (t : ℝ) :
    (Ns E lamD lamS T ω t : ℝ) = cnt (Set.Iic t ×ˢ Set.Iic (wStar E lamD lamS T)) ω.2 := by
  unfold Ns reqS cnt
  rw [Finset.filter_filter, Finset.card_filter]
  push_cast
  rw [← Fin.sum_univ_eq_sum_range (fun k => (Set.Iic t ×ˢ Set.Iic (wStar E lamD lamS T)).indicator
    (1 : ℝ × ℝ → ℝ) (ω.2.2 k))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold sellerCost sellerTime
  rw [Set.indicator_apply]
  simp only [Set.mem_prod, Set.mem_Iic, Pi.one_apply]
  by_cases h1 : (ω.2.2 i).2 ≤ wStar E lamD lamS T <;> by_cases h2 : (ω.2.2 i).1 ≤ t <;>
    simp [h1, h2]

lemma timeLaw_Iic (T t : ℝ) (hT : 0 < T) (ht0 : 0 ≤ t) (htT : t ≤ T) :
    (timeLaw T).real (Set.Iic t) = t / T := by
  unfold timeLaw
  rw [measureReal_def, Measure.smul_apply, Measure.restrict_apply measurableSet_Iic, smul_eq_mul]
  have : Set.Iic t ∩ Set.Icc 0 T = Set.Icc 0 t := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]; constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, le_trans h2 htT⟩
  rw [this, Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.toReal_ofReal (by positivity)]
  ring

open MechanismDesign.BilateralTrade in
lemma valLaw_Ici (E : Environment) {p : ℝ} (hp : p ∈ Set.Icc E.loB E.hiB) :
    (valLaw E).real (Set.Ici p) = 1 - E.cdfB p := by
  rw [← integral_indicator_one measurableSet_Ici, valLaw_integral]
  have e1 : (fun x => E.fB x * (Set.Ici p).indicator (1 : ℝ → ℝ) x) =
      (Set.Ici p).indicator E.fB := by
    funext x; by_cases hx : x ∈ Set.Ici p <;> simp [hx]
  rw [e1, setIntegral_indicator measurableSet_Ici]
  have e2 : Set.Icc E.loB E.hiB ∩ Set.Ici p = Set.Icc p E.hiB := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]; constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨le_trans hp.1 h1, h2⟩, h1⟩
  rw [e2, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hp.2, fB_int E hp]

open MechanismDesign.BilateralTrade in
lemma costLaw_Iic (E : Environment) {w : ℝ} (hw : w ∈ Set.Icc E.loS E.hiS) :
    (costLaw E).real (Set.Iic w) = E.cdfS w := by
  rw [← integral_indicator_one measurableSet_Iic, costLaw_integral]
  have e1 : (fun x => E.fS x * (Set.Iic w).indicator (1 : ℝ → ℝ) x) =
      (Set.Iic w).indicator E.fS := by
    funext x; by_cases hx : x ∈ Set.Iic w <;> simp [hx]
  rw [e1, setIntegral_indicator measurableSet_Iic]
  have e2 : Set.Icc E.loS E.hiS ∩ Set.Iic w = Set.Icc E.loS w := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]; constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, le_trans h2 hw.2⟩, h2⟩
  rw [e2, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hw.1]
  rfl

lemma real_prod_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν] (s : Set α) (t : Set β) :
    (μ.prod ν).real (s ×ˢ t) = μ.real s * ν.real t := by
  rw [measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]; rfl

open MechanismDesign.BilateralTrade in
lemma side_moments (E : Environment) (lamD lamS T : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hgap : E.loS < E.hiB)
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T) (t : ℝ) (ht0 : 0 ≤ t) (htT : t ≤ T) :
    let m := muStar E lamD lamS T * t / T
    let X := cnt (Set.Iic t ×ˢ Set.Ici (pStar E lamD lamS T))
    let Y := cnt (Set.Iic t ×ˢ Set.Iic (wStar E lamD lamS T))
    Integrable X (sideLaw lamD T (buyerMark E T)) ∧
    Integrable (fun s => X s ^ 2) (sideLaw lamD T (buyerMark E T)) ∧
    ∫ s, X s ∂(sideLaw lamD T (buyerMark E T)) = m ∧
    ∫ s, X s ^ 2 ∂(sideLaw lamD T (buyerMark E T)) = m + m ^ 2 ∧
    Integrable Y (sideLaw lamS T (sellerMark E T)) ∧
    Integrable (fun s => Y s ^ 2) (sideLaw lamS T (sellerMark E T)) ∧
    ∫ s, Y s ∂(sideLaw lamS T (sellerMark E T)) = m ∧
    ∫ s, Y s ^ 2 ∂(sideLaw lamS T (sellerMark E T)) = m + m ^ 2 := by
  intro m X Y
  obtain ⟨hpos, hmem, hp, hw, hFp, hFw, hsp⟩ := core E lamD lamS T hcontB hcontS hgap hd hs hT
  have := timeLaw_prob T hT
  have := valLaw_prob E
  have := costLaw_prob E
  have hbm : IsProbabilityMeasure (buyerMark E T) := by unfold buyerMark; infer_instance
  have hsm : IsProbabilityMeasure (sellerMark E T) := by unfold sellerMark; infer_instance
  have hDT : 0 < lamD * T := mul_pos hd hT
  have hST : 0 < lamS * T := mul_pos hs hT
  have hT0 : T ≠ 0 := hT.ne'
  have hd0 : lamD ≠ 0 := hd.ne'
  have hs0 : lamS ≠ 0 := hs.ne'
  have qB : max (lamD * T) 0 * (buyerMark E T).real (Set.Iic t ×ˢ Set.Ici (pStar E lamD lamS T)) =
      muStar E lamD lamS T * t / T := by
    unfold buyerMark
    rw [real_prod_prod, timeLaw_Iic T t hT ht0 htT, valLaw_Ici E hp, ← FdBar_eq E hp, hFp,
      max_eq_left hDT.le]
    field_simp
  have qS : max (lamS * T) 0 * (sellerMark E T).real (Set.Iic t ×ˢ Set.Iic (wStar E lamD lamS T)) =
      muStar E lamD lamS T * t / T := by
    unfold sellerMark
    rw [real_prod_prod, timeLaw_Iic T t hT ht0 htT, costLaw_Iic E hw, ← Fs_eq E hw, hFw,
      max_eq_left hST.le]
    field_simp
  obtain ⟨b1, b2, b3, b4⟩ := cnt_moments lamD T (buyerMark E T) _
    (measurableSet_Iic.prod measurableSet_Ici)
  obtain ⟨s1, s2, s3, s4⟩ := cnt_moments lamS T (sellerMark E T) _
    (measurableSet_Iic.prod measurableSet_Iic)
  rw [qB] at b2 b4
  rw [qS] at s2 s4
  exact ⟨b1, b3, b2, b4, s1, s3, s2, s4⟩

lemma cnt_param_meas (S : Set ((ℝ × ℝ) × ℝ)) (hS : MeasurableSet S) :
    Measurable (fun q : (ℕ × (ℕ → ℝ × ℝ)) × ℝ => cnt {z | (z, q.2) ∈ S} q.1) := by
  have h1 : Measurable (fun q : ℕ × ((ℕ → ℝ × ℝ) × ℝ) =>
      ∑ k ∈ Finset.range q.1, S.indicator (1 : (ℝ × ℝ) × ℝ → ℝ) (q.2.1 k, q.2.2)) := by
    apply measurable_from_prod_countable_right
    intro n
    show Measurable fun y : (ℕ → ℝ × ℝ) × ℝ =>
      ∑ k ∈ Finset.range n, S.indicator (1 : (ℝ × ℝ) × ℝ → ℝ) (y.1 k, y.2)
    exact Finset.measurable_sum _ (fun k _ => (measurable_one.indicator hS).comp (by fun_prop))
  have h2 : (fun q : (ℕ × (ℕ → ℝ × ℝ)) × ℝ => cnt {z | (z, q.2) ∈ S} q.1) =
      (fun q : ℕ × ((ℕ → ℝ × ℝ) × ℝ) =>
        ∑ k ∈ Finset.range q.1, S.indicator (1 : (ℝ × ℝ) × ℝ → ℝ) (q.2.1 k, q.2.2)) ∘
      (fun q => (q.1.1, (q.1.2, q.2))) := by
    funext q
    simp only [cnt, Function.comp]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : (q.1.2 k, q.2) ∈ S
    · rw [Set.indicator_of_mem hk,
        Set.indicator_of_mem (show q.1.2 k ∈ {z | (z, q.2) ∈ S} from hk)]
      simp
    · rw [Set.indicator_of_notMem hk,
        Set.indicator_of_notMem (show q.1.2 k ∉ {z | (z, q.2) ∈ S} from hk)]
  rw [h2]; exact h1.comp (by fun_prop)

lemma cnt_le_univ (A : Set (ℝ × ℝ)) (s : ℕ × (ℕ → ℝ × ℝ)) : cnt A s ≤ cnt Set.univ s :=
  Finset.sum_le_sum (fun k _ => Set.indicator_le_indicator_of_subset (Set.subset_univ _)
    (fun _ => zero_le_one) _)

lemma min_formula (x y : ℝ) : min x y = (x + y - |x - y|) / 2 := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

lemma pos_part_formula (b h D : ℝ) :
    b * max D 0 + h * max (-D) 0 = (b - h) / 2 * D + (b + h) / 2 * |D| := by
  rcases le_total D 0 with hD | hD
  · rw [max_eq_right hD, max_eq_left (by linarith), abs_of_nonpos hD]; ring
  · rw [max_eq_left hD, max_eq_right (by linarith), abs_of_nonneg hD]; ring

noncomputable def waitF (E : Environment) (lamD lamS T b h : ℝ) (ω : Ω) (t : ℝ) : ℝ :=
  b * max ((Nd E lamD lamS T ω t : ℝ) - (Ns E lamD lamS T ω t : ℝ)) 0 +
    h * max ((Ns E lamD lamS T ω t : ℝ) - (Nd E lamD lamS T ω t : ℝ)) 0

open MechanismDesign.BilateralTrade in
/-- C4b. Poisson moment bounds. -/
theorem poisson_bounds (E : Environment) (lamD lamS T b h : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hgap : E.loS < E.hiB)
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T)
    (hb : 0 ≤ b) (hh : 0 ≤ h) :
    muStar E lamD lamS T - Real.sqrt (muStar E lamD lamS T) ≤
      ∫ ω, ((min (Nd E lamD lamS T ω T) (Ns E lamD lamS T ω T) : ℕ) : ℝ)
        ∂P E lamD lamS T ∧
    ∫ ω, (∫ t in (0 : ℝ)..T,
        (b * max ((Nd E lamD lamS T ω t : ℝ) - (Ns E lamD lamS T ω t : ℝ)) 0 +
         h * max ((Ns E lamD lamS T ω t : ℝ) - (Nd E lamD lamS T ω t : ℝ)) 0))
          ∂P E lamD lamS T
      ≤ (2 / 3 : ℝ) * ((b + h) * T) * Real.sqrt (muStar E lamD lamS T) := by
  obtain ⟨hpos, hmem, hp, hw, hFp, hFw, hsp⟩ := core E lamD lamS T hcontB hcontS hgap hd hs hT
  set μs := muStar E lamD lamS T with hμs
  set pS := pStar E lamD lamS T
  set wS := wStar E lamD lamS T
  have := timeLaw_prob T hT
  have := valLaw_prob E
  have := costLaw_prob E
  have hbm : IsProbabilityMeasure (buyerMark E T) := by unfold buyerMark; infer_instance
  have hsm : IsProbabilityMeasure (sellerMark E T) := by unfold sellerMark; infer_instance
  have hA : IsProbabilityMeasure (sideLaw lamD T (buyerMark E T)) := sideLaw_prob _ _ _
  have hB : IsProbabilityMeasure (sideLaw lamS T (sellerMark E T)) := sideLaw_prob _ _ _
  have hPdef : P E lamD lamS T = (sideLaw lamD T (buyerMark E T)).prod
      (sideLaw lamS T (sellerMark E T)) := rfl
  -- per-time facts
  have perT : ∀ t, 0 ≤ t → t ≤ T →
      Integrable (fun z : Ω => cnt (Set.Iic t ×ˢ Set.Ici pS) z.1 -
        cnt (Set.Iic t ×ˢ Set.Iic wS) z.2) (P E lamD lamS T) ∧
      ∫ z, (cnt (Set.Iic t ×ˢ Set.Ici pS) z.1 - cnt (Set.Iic t ×ˢ Set.Iic wS) z.2)
        ∂(P E lamD lamS T) = 0 ∧
      Integrable (fun z : Ω => |cnt (Set.Iic t ×ˢ Set.Ici pS) z.1 -
        cnt (Set.Iic t ×ˢ Set.Iic wS) z.2|) (P E lamD lamS T) ∧
      ∫ z, |cnt (Set.Iic t ×ˢ Set.Ici pS) z.1 - cnt (Set.Iic t ×ˢ Set.Iic wS) z.2|
        ∂(P E lamD lamS T) ≤ Real.sqrt (2 * (μs * t / T)) := by
    intro t ht0 htT
    obtain ⟨b1, b2, b3, b4, s1, s2, s3, s4⟩ :=
      side_moments E lamD lamS T hcontB hcontS hgap hd hs hT t ht0 htT
    rw [hPdef]
    exact diff_bound _ _ _ _ (μs * t / T) b1 b2 s1 s2 b3 s3 b4 s4
  constructor
  · -- part (i)
    obtain ⟨b1, b2, b3, b4, s1, s2, s3, s4⟩ :=
      side_moments E lamD lamS T hcontB hcontS hgap hd hs hT T hT.le le_rfl
    obtain ⟨d1, d2, d3, d4⟩ := perT T hT.le le_rfl
    have e : (fun ω : Ω => ((min (Nd E lamD lamS T ω T) (Ns E lamD lamS T ω T) : ℕ) : ℝ)) =
        fun z : Ω => (cnt (Set.Iic T ×ˢ Set.Ici pS) z.1 + cnt (Set.Iic T ×ˢ Set.Iic wS) z.2 -
          |cnt (Set.Iic T ×ˢ Set.Ici pS) z.1 - cnt (Set.Iic T ×ˢ Set.Iic wS) z.2|) / 2 := by
      funext ω
      rw [Nat.cast_min, Nd_eq, Ns_eq, min_formula]
    have pf : MeasurePreserving Prod.fst (P E lamD lamS T) (sideLaw lamD T (buyerMark E T)) := by
      rw [hPdef]; exact measurePreserving_fst
    have ps : MeasurePreserving Prod.snd (P E lamD lamS T) (sideLaw lamS T (sellerMark E T)) := by
      rw [hPdef]; exact measurePreserving_snd
    have iX : Integrable (fun z : Ω => cnt (Set.Iic T ×ˢ Set.Ici pS) z.1) (P E lamD lamS T) :=
      pf.integrable_comp_of_integrable b1
    have iY : Integrable (fun z : Ω => cnt (Set.Iic T ×ˢ Set.Iic wS) z.2) (P E lamD lamS T) :=
      ps.integrable_comp_of_integrable s1
    have vX : ∫ z : Ω, cnt (Set.Iic T ×ˢ Set.Ici pS) z.1 ∂(P E lamD lamS T) = μs * T / T := by
      rw [hPdef, integral_fun_fst]; simp only [probReal_univ, one_smul]; exact b3
    have vY : ∫ z : Ω, cnt (Set.Iic T ×ˢ Set.Iic wS) z.2 ∂(P E lamD lamS T) = μs * T / T := by
      rw [hPdef, integral_fun_snd]; simp only [probReal_univ, one_smul]; exact s3
    have iXY : Integrable (fun z : Ω => cnt (Set.Iic T ×ˢ Set.Ici pS) z.1 +
        cnt (Set.Iic T ×ˢ Set.Iic wS) z.2) (P E lamD lamS T) := iX.add iY
    rw [e, integral_div, integral_sub iXY d3, integral_add iX iY, vX, vY]
    have hTT : μs * T / T = μs := by field_simp
    rw [hTT] at d4 ⊢
    have hsq : Real.sqrt (2 * μs) ≤ 2 * Real.sqrt μs := by
      have h1 : Real.sqrt (2 * μs) ≤ Real.sqrt (4 * μs) := Real.sqrt_le_sqrt (by linarith)
      have h2 : Real.sqrt (4 * μs) = 2 * Real.sqrt μs := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
      linarith
    linarith
  · -- part (ii)
    show ∫ ω, (∫ t in (0 : ℝ)..T, waitF E lamD lamS T b h ω t) ∂P E lamD lamS T ≤ _
    set ν : Measure ℝ := volume.restrict (Set.Ioc 0 T) with hν
    haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 (by simp)
    have hP : IsProbabilityMeasure (P E lamD lamS T) := by rw [hPdef]; infer_instance
    have hSB : MeasurableSet {q : (ℝ × ℝ) × ℝ | q.1.1 ≤ q.2 ∧ pS ≤ q.1.2} := by
      rw [Set.setOf_and]
      exact (measurableSet_le (f := fun q : (ℝ × ℝ) × ℝ => q.1.1) (g := fun q => q.2)
        (by fun_prop) (by fun_prop)).inter
        (measurableSet_le (f := fun _ : (ℝ × ℝ) × ℝ => pS) (g := fun q => q.1.2)
          (by fun_prop) (by fun_prop))
    have hSS : MeasurableSet {q : (ℝ × ℝ) × ℝ | q.1.1 ≤ q.2 ∧ q.1.2 ≤ wS} := by
      rw [Set.setOf_and]
      exact (measurableSet_le (f := fun q : (ℝ × ℝ) × ℝ => q.1.1) (g := fun q => q.2)
        (by fun_prop) (by fun_prop)).inter
        (measurableSet_le (f := fun q : (ℝ × ℝ) × ℝ => q.1.2) (g := fun _ => wS)
          (by fun_prop) (by fun_prop))
    have eB : ∀ t : ℝ, {z : ℝ × ℝ | (z, t) ∈ {q : (ℝ × ℝ) × ℝ | q.1.1 ≤ q.2 ∧ pS ≤ q.1.2}} =
        Set.Iic t ×ˢ Set.Ici pS := by
      intro t; ext z; simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Iic, Set.mem_Ici]
    have eS : ∀ t : ℝ, {z : ℝ × ℝ | (z, t) ∈ {q : (ℝ × ℝ) × ℝ | q.1.1 ≤ q.2 ∧ q.1.2 ≤ wS}} =
        Set.Iic t ×ˢ Set.Iic wS := by
      intro t; ext z; simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Iic, Set.mem_Ici]
    have mNd : Measurable (fun z : Ω × ℝ => (Nd E lamD lamS T z.1 z.2 : ℝ)) := by
      have h1 := (cnt_param_meas _ hSB).comp
        (show Measurable (fun z : Ω × ℝ => (z.1.1, z.2)) by fun_prop)
      have e : (fun z : Ω × ℝ => (Nd E lamD lamS T z.1 z.2 : ℝ)) =
          (fun q : (ℕ × (ℕ → ℝ × ℝ)) × ℝ =>
            cnt {z | (z, q.2) ∈ {q : (ℝ × ℝ) × ℝ | q.1.1 ≤ q.2 ∧ pS ≤ q.1.2}} q.1) ∘
          (fun z : Ω × ℝ => (z.1.1, z.2)) := by
        funext z; simp only [Function.comp]; rw [Nd_eq, eB]
      rw [e]; exact h1
    have mNs : Measurable (fun z : Ω × ℝ => (Ns E lamD lamS T z.1 z.2 : ℝ)) := by
      have h1 := (cnt_param_meas _ hSS).comp
        (show Measurable (fun z : Ω × ℝ => (z.1.2, z.2)) by fun_prop)
      have e : (fun z : Ω × ℝ => (Ns E lamD lamS T z.1 z.2 : ℝ)) =
          (fun q : (ℕ × (ℕ → ℝ × ℝ)) × ℝ =>
            cnt {z | (z, q.2) ∈ {q : (ℝ × ℝ) × ℝ | q.1.1 ≤ q.2 ∧ q.1.2 ≤ wS}} q.1) ∘
          (fun z : Ω × ℝ => (z.1.2, z.2)) := by
        funext z; simp only [Function.comp]; rw [Ns_eq, eS]
      rw [e]; exact h1
    have mF : Measurable (Function.uncurry (waitF E lamD lamS T b h)) := by
      show Measurable (fun z : Ω × ℝ => waitF E lamD lamS T b h z.1 z.2)
      unfold waitF
      exact (measurable_const.mul ((mNd.sub mNs).max measurable_const)).add
        (measurable_const.mul ((mNs.sub mNd).max measurable_const))
    -- bound
    have pf : MeasurePreserving Prod.fst (P E lamD lamS T) (sideLaw lamD T (buyerMark E T)) := by
      rw [hPdef]; exact measurePreserving_fst
    have ps : MeasurePreserving Prod.snd (P E lamD lamS T) (sideLaw lamS T (sellerMark E T)) := by
      rw [hPdef]; exact measurePreserving_snd
    have iU : Integrable (fun ω : Ω => (b + h) * (cnt Set.univ ω.1 + cnt Set.univ ω.2))
        (P E lamD lamS T) := by
      have u1 := (cnt_moments lamD T (buyerMark E T) Set.univ MeasurableSet.univ).1
      have u2 := (cnt_moments lamS T (sellerMark E T) Set.univ MeasurableSet.univ).1
      exact ((pf.integrable_comp_of_integrable u1).add
        (ps.integrable_comp_of_integrable u2)).const_mul (b + h)
    have wnn : ∀ ω t, 0 ≤ waitF E lamD lamS T b h ω t := fun ω t =>
      add_nonneg (mul_nonneg hb (le_max_right _ _)) (mul_nonneg hh (le_max_right _ _))
    have wle : ∀ ω t, waitF E lamD lamS T b h ω t ≤
        (b + h) * (cnt Set.univ ω.1 + cnt Set.univ ω.2) := by
      intro ω t
      unfold waitF
      have a1 : (Nd E lamD lamS T ω t : ℝ) ≤ cnt Set.univ ω.1 := by
        rw [Nd_eq]; exact cnt_le_univ _ _
      have a2 : (Ns E lamD lamS T ω t : ℝ) ≤ cnt Set.univ ω.2 := by
        rw [Ns_eq]; exact cnt_le_univ _ _
      have a3 : (0 : ℝ) ≤ Nd E lamD lamS T ω t := Nat.cast_nonneg _
      have a4 : (0 : ℝ) ≤ Ns E lamD lamS T ω t := Nat.cast_nonneg _
      have m1 : max ((Nd E lamD lamS T ω t : ℝ) - Ns E lamD lamS T ω t) 0 ≤
          cnt Set.univ ω.1 + cnt Set.univ ω.2 := max_le (by linarith) (by linarith)
      have m2 : max ((Ns E lamD lamS T ω t : ℝ) - Nd E lamD lamS T ω t) 0 ≤
          cnt Set.univ ω.1 + cnt Set.univ ω.2 := max_le (by linarith) (by linarith)
      have := mul_le_mul_of_nonneg_left m1 hb
      have := mul_le_mul_of_nonneg_left m2 hh
      nlinarith
    have hInt : Integrable (Function.uncurry (waitF E lamD lamS T b h))
        ((P E lamD lamS T).prod ν) := by
      refine Integrable.mono' (iU.mul_prod (integrable_const (1 : ℝ))) mF.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun z => ?_))
      show ‖waitF E lamD lamS T b h z.1 z.2‖ ≤ _
      rw [Real.norm_of_nonneg (wnn z.1 z.2), mul_one]
      exact wle z.1 z.2
    have e1 : ∫ ω, (∫ t in (0 : ℝ)..T, waitF E lamD lamS T b h ω t) ∂P E lamD lamS T =
        ∫ ω, (∫ t, waitF E lamD lamS T b h ω t ∂ν) ∂P E lamD lamS T :=
      integral_congr_ae (Filter.Eventually.of_forall
        (fun ω => intervalIntegral.integral_of_le hT.le))
    rw [e1, integral_integral_swap hInt]
    -- pointwise in t
    set c := (b + h) / 2 * Real.sqrt (2 * μs) with hc
    have hc0 : 0 ≤ c := by positivity
    have point : ∀ t ∈ Set.Ioc 0 T, ∫ ω, waitF E lamD lamS T b h ω t ∂P E lamD lamS T ≤
        c / 2 + c / (2 * T) * t := by
      intro t ht
      obtain ⟨d1, d2, d3, d4⟩ := perT t ht.1.le ht.2
      have ew : (fun ω : Ω => waitF E lamD lamS T b h ω t) = fun z : Ω =>
          (b - h) / 2 * (cnt (Set.Iic t ×ˢ Set.Ici pS) z.1 - cnt (Set.Iic t ×ˢ Set.Iic wS) z.2) +
          (b + h) / 2 * |cnt (Set.Iic t ×ˢ Set.Ici pS) z.1 - cnt (Set.Iic t ×ˢ Set.Iic wS) z.2| := by
        funext ω
        unfold waitF
        rw [← pos_part_formula, Nd_eq, Ns_eq, neg_sub]
      have i1 : Integrable (fun z : Ω => (b - h) / 2 *
          (cnt (Set.Iic t ×ˢ Set.Ici pS) z.1 - cnt (Set.Iic t ×ˢ Set.Iic wS) z.2))
          (P E lamD lamS T) := d1.const_mul _
      have i2 : Integrable (fun z : Ω => (b + h) / 2 *
          |cnt (Set.Iic t ×ˢ Set.Ici pS) z.1 - cnt (Set.Iic t ×ˢ Set.Iic wS) z.2|)
          (P E lamD lamS T) := d3.const_mul _
      rw [ew, integral_add i1 i2, integral_const_mul, integral_const_mul, d2, mul_zero, zero_add]
      have hst : Real.sqrt (2 * (μs * t / T)) ≤ Real.sqrt (2 * μs) * ((1 + t / T) / 2) := by
        have htT : 0 ≤ t / T := div_nonneg ht.1.le hT.le
        have e2 : 2 * (μs * t / T) = (2 * μs) * (t / T) := by ring
        rw [e2, Real.sqrt_mul (by positivity)]
        have hs1 := Real.sq_sqrt htT
        have hs2 := Real.sqrt_nonneg (t / T)
        have : Real.sqrt (t / T) ≤ (1 + t / T) / 2 := by
          nlinarith [sq_nonneg (Real.sqrt (t / T) - 1)]
        exact mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)
      have hbh : 0 ≤ (b + h) / 2 := by positivity
      calc (b + h) / 2 * ∫ z, |cnt (Set.Iic t ×ˢ Set.Ici pS) z.1 -
            cnt (Set.Iic t ×ˢ Set.Iic wS) z.2| ∂(P E lamD lamS T)
          ≤ (b + h) / 2 * (Real.sqrt (2 * μs) * ((1 + t / T) / 2)) :=
            mul_le_mul_of_nonneg_left (d4.trans hst) hbh
        _ = c / 2 + c / (2 * T) * t := by rw [hc]; field_simp
    have hG : Continuous (fun t : ℝ => c / 2 + c / (2 * T) * t) := by fun_prop
    have hmono := setIntegral_mono_on
      (hInt.integral_prod_right : Integrable (fun t => ∫ ω, waitF E lamD lamS T b h ω t
        ∂P E lamD lamS T) ν)
      ((hG.integrableOn_Icc (a := 0) (b := T)).mono_set Set.Ioc_subset_Icc_self)
      measurableSet_Ioc point
    refine hmono.trans ?_
    have hI : ∫ x in (0:ℝ)..T, (c / 2 + c / (2 * T) * x) =
        (T - 0) • (c / 2) + c / (2 * T) * ((T ^ 2 - 0 ^ 2) / 2) := by
      rw [intervalIntegral.integral_add (f := fun _ => c / 2) (g := fun x => c / (2 * T) * x)
        intervalIntegrable_const
        (by exact (continuous_const.mul continuous_id).intervalIntegrable 0 T)]
      rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
    rw [← intervalIntegral.integral_of_le hT.le, hI]
    have hsq : Real.sqrt (2 * μs) ≤ 3 / 2 * Real.sqrt μs := by
      have h1 : Real.sqrt (2 * μs) ≤ Real.sqrt (9 / 4 * μs) := Real.sqrt_le_sqrt (by linarith)
      have h2 : Real.sqrt (9 / 4 * μs) = 3 / 2 * Real.sqrt μs := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 9 / 4)]
        rw [show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3 / 2)]
      linarith
    have hval : (T - 0) • (c / 2) + c / (2 * T) * ((T ^ 2 - 0 ^ 2) / 2) =
        3 / 8 * (b + h) * T * Real.sqrt (2 * μs) := by
      rw [smul_eq_mul, hc]; field_simp; ring
    rw [hval]
    have hbhT : 0 ≤ (b + h) * T := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hsq hbhT]



lemma measurable_decide' {α : Type*} [MeasurableSpace α] (P : α → Prop) [DecidablePred P]
    (hP : MeasurableSet {a | P a}) : Measurable (fun a => decide (P a)) := by
  refine measurable_to_countable' (fun b => ?_)
  cases b
  · have : (fun a => decide (P a)) ⁻¹' {false} = {a | P a}ᶜ := by ext a; simp
    rw [this]; exact hP.compl
  · have : (fun a => decide (P a)) ⁻¹' {true} = {a | P a} := by ext a; simp
    rw [this]; exact hP

lemma measurable_of_bits {α K : Type*} [MeasurableSpace α] [MeasurableSpace K] [Countable K]
    [MeasurableSingletonClass K] {γ : Type*} [MeasurableSpace γ] (β : α → K) (hβ : Measurable β)
    (g : K → α → γ) (hg : ∀ k, Measurable (g k)) : Measurable (fun a => g (β a) a) := by
  have : Measurable (fun p : K × α => g p.1 p.2) :=
    measurable_from_prod_countable_right (fun k => hg k)
  exact this.comp (hβ.prodMk measurable_id)

lemma measurable_nat_of_cast {α : Type*} [MeasurableSpace α] (f : α → ℕ)
    (hf : Measurable (fun a => (f a : ℝ))) : Measurable f := by
  refine measurable_to_countable' (fun c => ?_)
  have : f ⁻¹' {c} = (fun a => (f a : ℝ)) ⁻¹' {(c : ℝ)} := by ext a; simp
  rw [this]; exact hf (measurableSet_singleton _)

lemma measurable_nat_pair {α : Type*} [MeasurableSpace α] (f g : α → ℕ) (hf : Measurable f)
    (hg : Measurable g) (S : Set (ℕ × ℕ)) : MeasurableSet {a | (f a, g a) ∈ S} :=
  (hf.prodMk hg) (Set.to_countable S).measurableSet

lemma insertionSort_congr {α : Type*} (r r' : α → α → Prop) [DecidableRel r] [DecidableRel r']
    (h : ∀ a b, r a b ↔ r' a b) (l : List α) : l.insertionSort r = l.insertionSort r' := by
  have : r = r' := funext fun a => funext fun b => propext (h a b)
  subst this
  congr

/-- Comparison bits of one side's first `m` marks. -/
abbrev Bits (m : ℕ) := (Fin m → Bool) × (Fin m → Fin m → Bool) × (Fin m → Fin m → Bool)

noncomputable def sortBits (m : ℕ) (k : Bits m) : List (Fin m) :=
  (Finset.univ.filter (fun j => k.1 j = true)).toList.insertionSort
    (fun i j => k.2.1 i j = true ∨ (k.2.2 i j = true ∧ i ≤ j))

noncomputable def bitsS (w : ℝ) (m : ℕ) (y : ℕ → ℝ × ℝ) : Bits m :=
  (fun j => decide ((y j).2 ≤ w), fun i j => decide ((y i).1 < (y j).1),
    fun i j => decide ((y i).1 = (y j).1))

noncomputable def bitsB (p : ℝ) (n : ℕ) (x : ℕ → ℝ × ℝ) : Bits n :=
  (fun j => decide (p ≤ (x j).2), fun i j => decide ((x i).1 < (x j).1),
    fun i j => decide ((x i).1 = (x j).1))

lemma bitsS_meas (w : ℝ) (m : ℕ) : Measurable (bitsS w m) := by
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · refine measurable_pi_lambda _ (fun j => measurable_decide' _ ?_)
    exact measurableSet_le (by fun_prop) measurable_const
  · refine measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => measurable_decide' _ ?_))
    exact measurableSet_lt (by fun_prop) (by fun_prop)
  · refine measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => measurable_decide' _ ?_))
    exact measurableSet_eq_fun (by fun_prop) (by fun_prop)

lemma bitsB_meas (p : ℝ) (n : ℕ) : Measurable (bitsB p n) := by
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · refine measurable_pi_lambda _ (fun j => measurable_decide' _ ?_)
    exact measurableSet_le measurable_const (by fun_prop)
  · refine measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => measurable_decide' _ ?_))
    exact measurableSet_lt (by fun_prop) (by fun_prop)
  · refine measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => measurable_decide' _ ?_))
    exact measurableSet_eq_fun (by fun_prop) (by fun_prop)

lemma sortedS_eq (E : Environment) (lamD lamS T : ℝ) (ω : Ω) :
    sortedS E lamD lamS T ω = sortBits ω.2.1 (bitsS (wStar E lamD lamS T) ω.2.1 ω.2.2) := by
  unfold sortedS sortBits reqS bitsS sellerCost sellerTime
  have hf : (Finset.univ.filter (fun j : Fin ω.2.1 => (ω.2.2 j).2 ≤ wStar E lamD lamS T)) =
      Finset.univ.filter (fun j : Fin ω.2.1 => decide ((ω.2.2 j).2 ≤ wStar E lamD lamS T) = true) := by
    simp
  rw [hf]
  apply insertionSort_congr
  intro a b
  simp

lemma sortedB_eq (E : Environment) (lamD lamS T : ℝ) (ω : Ω) :
    sortedB E lamD lamS T ω = sortBits ω.1.1 (bitsB (pStar E lamD lamS T) ω.1.1 ω.1.2) := by
  unfold sortedB sortBits reqB bitsB buyerValue buyerTime
  have hf : (Finset.univ.filter (fun j : Fin ω.1.1 => pStar E lamD lamS T ≤ (ω.1.2 j).2)) =
      Finset.univ.filter (fun j : Fin ω.1.1 => decide (pStar E lamD lamS T ≤ (ω.1.2 j).2) = true) := by
    simp
  rw [hf]
  apply insertionSort_congr
  intro a b
  simp

/-- Strict count of marks of a side satisfying `c` before time `t`. -/
noncomputable def rk (c : ℝ → Prop) [DecidablePred c] (s : ℕ × (ℕ → ℝ × ℝ)) (t : ℝ) : ℕ :=
  ((Finset.range s.1).filter (fun k => c (s.2 k).2 ∧ (s.2 k).1 < t)).card

lemma rk_meas (c : ℝ → Prop) [DecidablePred c] (hc : MeasurableSet {v | c v}) :
    Measurable (fun z : (ℕ × (ℕ → ℝ × ℝ)) × ℝ => rk c z.1 z.2) := by
  apply measurable_nat_of_cast
  have h1 : Measurable (fun q : ℕ × ((ℕ → ℝ × ℝ) × ℝ) =>
      ∑ k ∈ Finset.range q.1, (if c (q.2.1 k).2 ∧ (q.2.1 k).1 < q.2.2 then (1:ℝ) else 0)) := by
    apply measurable_from_prod_countable_right
    intro n
    show Measurable fun y : (ℕ → ℝ × ℝ) × ℝ =>
      ∑ k ∈ Finset.range n, (if c (y.1 k).2 ∧ (y.1 k).1 < y.2 then (1:ℝ) else 0)
    refine Finset.measurable_sum _ (fun k _ => Measurable.ite ?_ measurable_const measurable_const)
    have e : {y : (ℕ → ℝ × ℝ) × ℝ | c (y.1 k).2 ∧ (y.1 k).1 < y.2} =
        (fun y : (ℕ → ℝ × ℝ) × ℝ => (y.1 k).2) ⁻¹' {v | c v} ∩
          {y | (y.1 k).1 < y.2} := by
      ext y; simp
    rw [e]
    exact ((by fun_prop : Measurable (fun y : (ℕ → ℝ × ℝ) × ℝ => (y.1 k).2)) hc).inter
      (measurableSet_lt (by fun_prop) (by fun_prop))
  have e : (fun z : (ℕ × (ℕ → ℝ × ℝ)) × ℝ => (rk c z.1 z.2 : ℝ)) =
      (fun q : ℕ × ((ℕ → ℝ × ℝ) × ℝ) =>
        ∑ k ∈ Finset.range q.1, (if c (q.2.1 k).2 ∧ (q.2.1 k).1 < q.2.2 then (1:ℝ) else 0)) ∘
      (fun z => (z.1.1, (z.1.2, z.2))) := by
    funext z
    simp only [rk, Function.comp, Finset.card_filter]
    push_cast
    rfl
  rw [e]; exact h1.comp (by fun_prop)

lemma rank_B_eq (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (t : ℝ) :
    taggedBuyerRank E lamD lamS T ω t = rk (fun v => pStar E lamD lamS T ≤ v) ω.1 t := by
  unfold taggedBuyerRank reqB rk buyerValue buyerTime
  rw [Finset.filter_filter, Finset.card_filter, Finset.card_filter]
  rw [← Fin.sum_univ_eq_sum_range (fun k => if pStar E lamD lamS T ≤ (ω.1.2 k).2 ∧ (ω.1.2 k).1 < t
    then 1 else 0)]

lemma rank_S_eq (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (t : ℝ) :
    taggedSellerRank E lamD lamS T ω t = rk (fun v => v ≤ wStar E lamD lamS T) ω.2 t := by
  unfold taggedSellerRank reqS rk sellerCost sellerTime
  rw [Finset.filter_filter, Finset.card_filter, Finset.card_filter]
  rw [← Fin.sum_univ_eq_sum_range (fun k => if (ω.2.2 k).2 ≤ wStar E lamD lamS T ∧ (ω.2.2 k).1 < t
    then 1 else 0)]

lemma rankB_meas (E : Environment) (lamD lamS T : ℝ) :
    Measurable (fun z : Ω × ℝ => taggedBuyerRank E lamD lamS T z.1 z.2) := by
  have h := (rk_meas (fun v => pStar E lamD lamS T ≤ v) measurableSet_Ici).comp
    (show Measurable (fun z : Ω × ℝ => (z.1.1, z.2)) by fun_prop)
  have e : (fun z : Ω × ℝ => taggedBuyerRank E lamD lamS T z.1 z.2) =
      (fun z : (ℕ × (ℕ → ℝ × ℝ)) × ℝ => rk (fun v => pStar E lamD lamS T ≤ v) z.1 z.2) ∘
        (fun z : Ω × ℝ => (z.1.1, z.2)) := funext (fun z => rank_B_eq E lamD lamS T z.1 z.2)
  rw [e]; exact h

lemma rankS_meas (E : Environment) (lamD lamS T : ℝ) :
    Measurable (fun z : Ω × ℝ => taggedSellerRank E lamD lamS T z.1 z.2) := by
  have h := (rk_meas (fun v => v ≤ wStar E lamD lamS T) measurableSet_Iic).comp
    (show Measurable (fun z : Ω × ℝ => (z.1.2, z.2)) by fun_prop)
  have e : (fun z : Ω × ℝ => taggedSellerRank E lamD lamS T z.1 z.2) =
      (fun z : (ℕ × (ℕ → ℝ × ℝ)) × ℝ => rk (fun v => v ≤ wStar E lamD lamS T) z.1 z.2) ∘
        (fun z : Ω × ℝ => (z.1.2, z.2)) := funext (fun z => rank_S_eq E lamD lamS T z.1 z.2)
  rw [e]; exact h

/-- Measurability through a countable index and finitely many bits. -/
lemma meas_via {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ] (N : α → ℕ)
    (hN : Measurable N) (K : ℕ → Type) [∀ m, MeasurableSpace (K m)] [∀ m, Countable (K m)]
    [∀ m, MeasurableSingletonClass (K m)] (β : (m : ℕ) → α → K m) (hβ : ∀ m, Measurable (β m))
    (Φ : (m : ℕ) → K m → α → γ) (hΦ : ∀ m k, Measurable (Φ m k)) :
    Measurable (fun a => Φ (N a) (β (N a) a) a) := by
  have hF : Measurable (fun p : ℕ × α => Φ p.1 (β p.1 p.2) p.2) :=
    measurable_from_prod_countable_right
      (fun m => measurable_of_bits (β m) (hβ m) (Φ m) (hΦ m))
  exact hF.comp (hN.prodMk measurable_id)

noncomputable def WdL (T : ℝ) (L : List ℕ) (r : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  match L[r]? with
  | some j => max t (ω.2.2 j).1 - t
  | none => T - t

noncomputable def WsL (T : ℝ) (L : List ℕ) (r : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  match L[r]? with
  | some i => max t (ω.1.2 i).1 - t
  | none => T - t

lemma WdL_meas (T : ℝ) (L : List ℕ) (r : ℕ) :
    Measurable (fun z : Ω × ℝ => WdL T L r z.1 z.2) := by
  unfold WdL
  cases L[r]? with
  | none => fun_prop
  | some j => exact (measurable_snd.max (by fun_prop)).sub measurable_snd

lemma WsL_meas (T : ℝ) (L : List ℕ) (r : ℕ) :
    Measurable (fun z : Ω × ℝ => WsL T L r z.1 z.2) := by
  unfold WsL
  cases L[r]? with
  | none => fun_prop
  | some j => exact (measurable_snd.max (by fun_prop)).sub measurable_snd

lemma Wd_eq (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (t : ℝ) :
    Wd E lamD lamS T ω t = WdL T ((sortBits ω.2.1
      (bitsS (wStar E lamD lamS T) ω.2.1 ω.2.2)).map Fin.val)
      (taggedBuyerRank E lamD lamS T ω t) ω t := by
  unfold Wd WdL
  rw [← sortedS_eq, List.getElem?_map]
  cases (sortedS E lamD lamS T ω)[taggedBuyerRank E lamD lamS T ω t]? <;> simp [sellerTime]

lemma Ws_eq (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (t : ℝ) :
    Ws E lamD lamS T ω t = WsL T ((sortBits ω.1.1
      (bitsB (pStar E lamD lamS T) ω.1.1 ω.1.2)).map Fin.val)
      (taggedSellerRank E lamD lamS T ω t) ω t := by
  unfold Ws WsL
  rw [← sortedB_eq, List.getElem?_map]
  cases (sortedB E lamD lamS T ω)[taggedSellerRank E lamD lamS T ω t]? <;> simp [buyerTime]

lemma Wd_meas (E : Environment) (lamD lamS T : ℝ) :
    Measurable (fun z : Ω × ℝ => Wd E lamD lamS T z.1 z.2) := by
  have e : (fun z : Ω × ℝ => Wd E lamD lamS T z.1 z.2) = fun z =>
      (fun (m : ℕ) (k : Bits m) (z : Ω × ℝ) => WdL T ((sortBits m k).map Fin.val)
        (taggedBuyerRank E lamD lamS T z.1 z.2) z.1 z.2) z.1.2.1
        ((fun (m : ℕ) (z : Ω × ℝ) => bitsS (wStar E lamD lamS T) m z.1.2.2) z.1.2.1 z) z :=
    funext (fun z => Wd_eq E lamD lamS T z.1 z.2)
  rw [e]
  refine meas_via (fun z : Ω × ℝ => z.1.2.1) (by fun_prop) Bits
    (fun (m : ℕ) (z : Ω × ℝ) => bitsS (wStar E lamD lamS T) m z.1.2.2)
    (fun m => (bitsS_meas _ m).comp (by fun_prop))
    (fun (m : ℕ) (k : Bits m) (z : Ω × ℝ) => WdL T ((sortBits m k).map Fin.val)
        (taggedBuyerRank E lamD lamS T z.1 z.2) z.1 z.2) (fun m k => ?_)
  exact measurable_of_bits (fun z : Ω × ℝ => taggedBuyerRank E lamD lamS T z.1 z.2)
    (rankB_meas E lamD lamS T) (fun r z => WdL T ((sortBits m k).map Fin.val) r z.1 z.2)
    (fun r => WdL_meas T _ r)

lemma Ws_meas (E : Environment) (lamD lamS T : ℝ) :
    Measurable (fun z : Ω × ℝ => Ws E lamD lamS T z.1 z.2) := by
  have e : (fun z : Ω × ℝ => Ws E lamD lamS T z.1 z.2) = fun z =>
      (fun (m : ℕ) (k : Bits m) (z : Ω × ℝ) => WsL T ((sortBits m k).map Fin.val)
        (taggedSellerRank E lamD lamS T z.1 z.2) z.1 z.2) z.1.1.1
        ((fun (m : ℕ) (z : Ω × ℝ) => bitsB (pStar E lamD lamS T) m z.1.1.2) z.1.1.1 z) z :=
    funext (fun z => Ws_eq E lamD lamS T z.1 z.2)
  rw [e]
  refine meas_via (fun z : Ω × ℝ => z.1.1.1) (by fun_prop) Bits
    (fun (m : ℕ) (z : Ω × ℝ) => bitsB (pStar E lamD lamS T) m z.1.1.2)
    (fun m => (bitsB_meas _ m).comp (by fun_prop))
    (fun (m : ℕ) (k : Bits m) (z : Ω × ℝ) => WsL T ((sortBits m k).map Fin.val)
        (taggedSellerRank E lamD lamS T z.1 z.2) z.1 z.2) (fun m k => ?_)
  exact measurable_of_bits (fun z : Ω × ℝ => taggedSellerRank E lamD lamS T z.1 z.2)
    (rankS_meas E lamD lamS T) (fun r z => WsL T ((sortBits m k).map Fin.val) r z.1 z.2)
    (fun r => WsL_meas T _ r)

lemma lenS_meas (E : Environment) (lamD lamS T : ℝ) :
    Measurable (fun ω : Ω => (sortedS E lamD lamS T ω).length) := by
  have e : (fun ω : Ω => (sortedS E lamD lamS T ω).length) = fun ω =>
      (fun (m : ℕ) (k : Bits m) (_ : Ω) => (sortBits m k).length) ω.2.1
        ((fun (m : ℕ) (ω : Ω) => bitsS (wStar E lamD lamS T) m ω.2.2) ω.2.1 ω) ω := by
    funext ω; simp only [sortedS_eq]
  rw [e]
  exact meas_via (fun ω : Ω => ω.2.1) (by fun_prop) Bits
    (fun (m : ℕ) (ω : Ω) => bitsS (wStar E lamD lamS T) m ω.2.2)
    (fun m => (bitsS_meas _ m).comp (by fun_prop))
    (fun (m : ℕ) (k : Bits m) (_ : Ω) => (sortBits m k).length) (fun m k => measurable_const)

lemma lenB_meas (E : Environment) (lamD lamS T : ℝ) :
    Measurable (fun ω : Ω => (sortedB E lamD lamS T ω).length) := by
  have e : (fun ω : Ω => (sortedB E lamD lamS T ω).length) = fun ω =>
      (fun (m : ℕ) (k : Bits m) (_ : Ω) => (sortBits m k).length) ω.1.1
        ((fun (m : ℕ) (ω : Ω) => bitsB (pStar E lamD lamS T) m ω.1.2) ω.1.1 ω) ω := by
    funext ω; simp only [sortedB_eq]
  rw [e]
  exact meas_via (fun ω : Ω => ω.1.1) (by fun_prop) Bits
    (fun (m : ℕ) (ω : Ω) => bitsB (pStar E lamD lamS T) m ω.1.2)
    (fun m => (bitsB_meas _ m).comp (by fun_prop))
    (fun (m : ℕ) (k : Bits m) (_ : Ω) => (sortBits m k).length) (fun m k => measurable_const)

lemma Md_meas (E : Environment) (lamD lamS T : ℝ) :
    Measurable (fun z : Ω × ℝ => Md E lamD lamS T z.1 z.2) := by
  unfold Md
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurable_nat_pair _ _ (rankB_meas E lamD lamS T)
    ((lenS_meas E lamD lamS T).comp measurable_fst) {p | p.1 < p.2}

lemma Ms_meas (E : Environment) (lamD lamS T : ℝ) :
    Measurable (fun z : Ω × ℝ => Ms E lamD lamS T z.1 z.2) := by
  unfold Ms
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurable_nat_pair _ _ (rankS_meas E lamD lamS T)
    ((lenB_meas E lamD lamS T).comp measurable_fst) {p | p.1 < p.2}

lemma Iminus_le_iff (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (t : ℝ) :
    Iminus E lamD lamS T ω t ≤ 0 ↔
      taggedSellerRank E lamD lamS T ω t ≤ taggedBuyerRank E lamD lamS T ω t := by
  unfold Iminus taggedSellerRank taggedBuyerRank
  omega

lemma ind_meas (E : Environment) (lamD lamS T : ℝ) :
    MeasurableSet {z : Ω × ℝ | Iminus E lamD lamS T z.1 z.2 ≤ 0} := by
  have e : {z : Ω × ℝ | Iminus E lamD lamS T z.1 z.2 ≤ 0} =
      {z | (taggedSellerRank E lamD lamS T z.1 z.2, taggedBuyerRank E lamD lamS T z.1 z.2) ∈
        {p : ℕ × ℕ | p.1 ≤ p.2}} := by
    ext z; simp only [Set.mem_setOf_eq, Iminus_le_iff]
  rw [e]
  exact measurable_nat_pair _ _ (rankS_meas E lamD lamS T) (rankB_meas E lamD lamS T) _

lemma compD_meas (E : Environment) (lamD lamS T : ℝ) [SFinite (P E lamD lamS T)] :
    Measurable (compD E lamD lamS T) := by
  have h1 : Measurable (fun z : Ω × ℝ => Wd E lamD lamS T z.1 z.2 *
      (if Iminus E lamD lamS T z.1 z.2 ≤ 0 then (1 : ℝ) else 0)) :=
    (Wd_meas E lamD lamS T).mul (Measurable.ite (ind_meas E lamD lamS T) measurable_const
      measurable_const)
  have h2 : Measurable (fun z : Ω × ℝ => Md E lamD lamS T z.1 z.2 *
      (if Iminus E lamD lamS T z.1 z.2 ≤ 0 then (1 : ℝ) else 0)) :=
    (Md_meas E lamD lamS T).mul (Measurable.ite (ind_meas E lamD lamS T) measurable_const
      measurable_const)
  have g1 := (h1.stronglyMeasurable.integral_prod_left' (μ := P E lamD lamS T)).measurable
  have g2 := (h2.stronglyMeasurable.integral_prod_left' (μ := P E lamD lamS T)).measurable
  exact g1.div g2

lemma compS_meas (E : Environment) (lamD lamS T : ℝ) [SFinite (P E lamD lamS T)] :
    Measurable (compS E lamD lamS T) := by
  have g1 := ((Ws_meas E lamD lamS T).stronglyMeasurable.integral_prod_left'
    (μ := P E lamD lamS T)).measurable
  have g2 := ((Ms_meas E lamD lamS T).stronglyMeasurable.integral_prod_left'
    (μ := P E lamD lamS T)).measurable
  exact g1.div g2

lemma ask_meas (E : Environment) (lamD lamS T b : ℝ) [SFinite (P E lamD lamS T)] :
    Measurable (fun z : Ω × ℝ => askPrice E lamD lamS T b z.1 z.2) := by
  unfold askPrice
  exact measurable_const.sub (measurable_const.mul (Measurable.ite (ind_meas E lamD lamS T)
    ((compD_meas E lamD lamS T).comp measurable_snd) measurable_const))

lemma bid_meas (E : Environment) (lamD lamS T h : ℝ) [SFinite (P E lamD lamS T)] :
    Measurable (bidPrice E lamD lamS T h) := by
  unfold bidPrice
  exact measurable_const.add (measurable_const.mul (compS_meas E lamD lamS T))

/-- Sums over greedy pairs of jointly measurable summands are measurable. -/
lemma pairs_sum_meas (E : Environment) (lamD lamS T : ℝ) (F : Ω → ℕ → ℕ → ℝ)
    (hF : ∀ i j, Measurable (fun ω => F ω i j)) :
    Measurable (fun ω : Ω => ∑ p ∈ (greedyPairs E lamD lamS T ω).toFinset, F ω p.2 p.1) := by
  have e : (fun ω : Ω => ∑ p ∈ (greedyPairs E lamD lamS T ω).toFinset, F ω p.2 p.1) = fun ω =>
      (fun (n : ℕ) (kB : Bits n) (ω : Ω) =>
        (fun (m : ℕ) (kS : Bits m) (ω : Ω) =>
          ∑ p ∈ ((sortBits m kS).zip (sortBits n kB)).toFinset, F ω p.2 p.1) ω.2.1
          (bitsS (wStar E lamD lamS T) ω.2.1 ω.2.2) ω) ω.1.1
        (bitsB (pStar E lamD lamS T) ω.1.1 ω.1.2) ω := by
    funext ω
    unfold greedyPairs
    rw [sortedS_eq, sortedB_eq]
  rw [e]
  refine meas_via (fun ω : Ω => ω.1.1) (by fun_prop) Bits
    (fun (n : ℕ) (ω : Ω) => bitsB (pStar E lamD lamS T) n ω.1.2)
    (fun n => (bitsB_meas _ n).comp (by fun_prop))
    (fun (n : ℕ) (kB : Bits n) (ω : Ω) =>
        (fun (m : ℕ) (kS : Bits m) (ω : Ω) =>
          ∑ p ∈ ((sortBits m kS).zip (sortBits n kB)).toFinset, F ω p.2 p.1) ω.2.1
          (bitsS (wStar E lamD lamS T) ω.2.1 ω.2.2) ω) (fun n kB => ?_)
  refine meas_via (fun ω : Ω => ω.2.1) (by fun_prop) Bits
    (fun (m : ℕ) (ω : Ω) => bitsS (wStar E lamD lamS T) m ω.2.2)
    (fun m => (bitsS_meas _ m).comp (by fun_prop))
    (fun (m : ℕ) (kS : Bits m) (ω : Ω) =>
          ∑ p ∈ ((sortBits m kS).zip (sortBits n kB)).toFinset, F ω p.2 p.1) (fun m kS => ?_)
  exact Finset.measurable_sum _ (fun p _ => hF p.2 p.1)

lemma profit_meas (E : Environment) (lamD lamS T b h : ℝ) [SFinite (P E lamD lamS T)] :
    Measurable (profit E lamD lamS T b h) := by
  have := pairs_sum_meas E lamD lamS T
    (fun ω i j => askPrice E lamD lamS T b ω (ω.1.2 i).1 - bidPrice E lamD lamS T h (ω.2.2 j).1)
    (fun i j => ((ask_meas E lamD lamS T b).comp (measurable_id.prodMk (by fun_prop))).sub
      ((bid_meas E lamD lamS T h).comp (by fun_prop)))
  exact this



lemma card_lt_le_pos {α : Type*} [DecidableEq α] (R : α → α → Prop) (τ : α → ℝ)
    (hR : ∀ a b, R a b → τ a ≤ τ b) (L : List α) (hL : L.Pairwise R) (r : ℕ)
    (hr : r < L.length) :
    (L.toFinset.filter (fun k => τ k < τ L[r])).card ≤ r := by
  have hsplit : L = L.take r ++ (L[r] :: L.drop (r + 1)) := by
    rw [← List.drop_eq_getElem_cons hr, List.take_append_drop]
  have hp : (L[r] :: L.drop (r + 1)).Pairwise R := by
    have h2 := hL
    rw [hsplit] at h2
    exact (List.pairwise_append.1 h2).2.1
  have hsub : L.toFinset.filter (fun k => τ k < τ L[r]) ⊆ (L.take r).toFinset := by
    intro k hk
    rw [Finset.mem_filter, List.mem_toFinset] at hk
    rw [List.mem_toFinset]
    obtain ⟨hkL, hlt⟩ := hk
    rw [hsplit, List.mem_append, List.mem_cons] at hkL
    rcases hkL with h | h | h
    · exact h
    · exfalso; rw [h] at hlt; exact lt_irrefl _ hlt
    · exfalso
      have := hR _ _ ((List.pairwise_cons.1 hp).1 k h)
      linarith
  calc _ ≤ (L.take r).toFinset.card := Finset.card_le_card hsub
    _ ≤ (L.take r).length := List.toFinset_card_le _
    _ ≤ r := List.length_take_le _ _

lemma card_rank_ge {ι : Type*} [DecidableEq ι] (B : Finset ι) (τ : ι → ℝ) (s : ℝ) (m : ℕ) :
    (B.filter (fun i => τ i < s ∧ m ≤ (B.filter (fun k => τ k < τ i)).card)).card ≤
      (B.filter (fun i => τ i < s)).card - m := by
  set A := B.filter (fun i => τ i < s ∧ m ≤ (B.filter (fun k => τ k < τ i)).card) with hA
  rcases A.eq_empty_or_nonempty with h0 | hne
  · rw [h0]; simp
  obtain ⟨i0, hi0, hmin⟩ := A.exists_min_image τ hne
  have hi0' := hi0
  rw [hA, Finset.mem_filter] at hi0'
  obtain ⟨hi0B, hi0s, hi0m⟩ := hi0'
  set C := B.filter (fun k => τ k < τ i0) with hC
  have hdisj : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro k hkA hkC
    have h1 := hmin k hkA
    rw [hC, Finset.mem_filter] at hkC
    linarith [hkC.2]
  have hunion : A ∪ C ⊆ B.filter (fun i => τ i < s) := by
    intro k hk
    rw [Finset.mem_union] at hk
    rw [Finset.mem_filter]
    rcases hk with hk | hk
    · rw [hA, Finset.mem_filter] at hk; exact ⟨hk.1, hk.2.1⟩
    · rw [hC, Finset.mem_filter] at hk; exact ⟨hk.1, lt_trans hk.2 hi0s⟩
  have hcard := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  omega

lemma natsub_cast (a b : ℕ) : ((a - b : ℕ) : ℝ) = max ((a : ℝ) - b) 0 := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h, max_eq_left (by simp [h])]
  · rw [Nat.sub_eq_zero_of_le h, max_eq_right (by simp [h])]; simp

lemma zip_nodup {α β : Type*} : ∀ (l1 : List α) (l2 : List β), l1.Nodup → (l1.zip l2).Nodup
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: l1, b :: l2, h => by
    rw [List.zip_cons_cons, List.nodup_cons]
    rw [List.nodup_cons] at h
    exact ⟨fun hm => h.1 (List.of_mem_zip hm).1, zip_nodup l1 l2 h.2⟩

section Sorted
variable (E : Environment) (lamD lamS T : ℝ)

lemma sortedB_pairwise (ω : Ω) :
    (sortedB E lamD lamS T ω).Pairwise (fun i j => buyerTime ω i < buyerTime ω j ∨
      (buyerTime ω i = buyerTime ω j ∧ i ≤ j)) := by
  haveI : IsTotal (Fin ω.1.1) (fun i j => buyerTime ω i < buyerTime ω j ∨
      (buyerTime ω i = buyerTime ω j ∧ i ≤ j)) :=
    ⟨fun i j => by
      rcases lt_trichotomy (buyerTime ω i) (buyerTime ω j) with h | h | h
      · exact Or.inl (Or.inl h)
      · rcases le_total i j with h' | h'
        · exact Or.inl (Or.inr ⟨h, h'⟩)
        · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
      · exact Or.inr (Or.inl h)⟩
  haveI : IsTrans (Fin ω.1.1) (fun i j => buyerTime ω i < buyerTime ω j ∨
      (buyerTime ω i = buyerTime ω j ∧ i ≤ j)) :=
    ⟨fun i j k hij hjk => by
      rcases hij with h1 | ⟨h1, h1'⟩ <;> rcases hjk with h2 | ⟨h2, h2'⟩
      · exact Or.inl (lt_trans h1 h2)
      · exact Or.inl (lt_of_lt_of_eq h1 h2)
      · exact Or.inl (lt_of_eq_of_lt h1 h2)
      · exact Or.inr ⟨h1.trans h2, h1'.trans h2'⟩⟩
  exact List.pairwise_insertionSort _ _

lemma sortedS_pairwise (ω : Ω) :
    (sortedS E lamD lamS T ω).Pairwise (fun i j => sellerTime ω i < sellerTime ω j ∨
      (sellerTime ω i = sellerTime ω j ∧ i ≤ j)) := by
  haveI : IsTotal (Fin ω.2.1) (fun i j => sellerTime ω i < sellerTime ω j ∨
      (sellerTime ω i = sellerTime ω j ∧ i ≤ j)) :=
    ⟨fun i j => by
      rcases lt_trichotomy (sellerTime ω i) (sellerTime ω j) with h | h | h
      · exact Or.inl (Or.inl h)
      · rcases le_total i j with h' | h'
        · exact Or.inl (Or.inr ⟨h, h'⟩)
        · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
      · exact Or.inr (Or.inl h)⟩
  haveI : IsTrans (Fin ω.2.1) (fun i j => sellerTime ω i < sellerTime ω j ∨
      (sellerTime ω i = sellerTime ω j ∧ i ≤ j)) :=
    ⟨fun i j k hij hjk => by
      rcases hij with h1 | ⟨h1, h1'⟩ <;> rcases hjk with h2 | ⟨h2, h2'⟩
      · exact Or.inl (lt_trans h1 h2)
      · exact Or.inl (lt_of_lt_of_eq h1 h2)
      · exact Or.inl (lt_of_eq_of_lt h1 h2)
      · exact Or.inr ⟨h1.trans h2, h1'.trans h2'⟩⟩
  exact List.pairwise_insertionSort _ _

lemma sortedB_toFinset (ω : Ω) : (sortedB E lamD lamS T ω).toFinset = reqB E lamD lamS T ω := by
  unfold sortedB
  rw [List.toFinset_eq_of_perm _ _ (List.perm_insertionSort _ _), Finset.toList_toFinset]

lemma sortedS_toFinset (ω : Ω) : (sortedS E lamD lamS T ω).toFinset = reqS E lamD lamS T ω := by
  unfold sortedS
  rw [List.toFinset_eq_of_perm _ _ (List.perm_insertionSort _ _), Finset.toList_toFinset]

lemma sortedB_nodup (ω : Ω) : (sortedB E lamD lamS T ω).Nodup := by
  unfold sortedB
  exact (List.perm_insertionSort _ _).nodup_iff.2 (Finset.nodup_toList _)

lemma sortedS_nodup (ω : Ω) : (sortedS E lamD lamS T ω).Nodup := by
  unfold sortedS
  exact (List.perm_insertionSort _ _).nodup_iff.2 (Finset.nodup_toList _)

lemma sortedB_length (ω : Ω) : (sortedB E lamD lamS T ω).length = (reqB E lamD lamS T ω).card := by
  unfold sortedB; rw [List.length_insertionSort, Finset.length_toList]

lemma sortedS_length (ω : Ω) : (sortedS E lamD lamS T ω).length = (reqS E lamD lamS T ω).card := by
  unfold sortedS; rw [List.length_insertionSort, Finset.length_toList]

/-- The buyer at position `r` of the FCFS list has strict rank at most `r`. -/
lemma rankB_le_pos (ω : Ω) (r : ℕ) (hr : r < (sortedB E lamD lamS T ω).length) :
    taggedBuyerRank E lamD lamS T ω (buyerTime ω (sortedB E lamD lamS T ω)[r]) ≤ r := by
  unfold taggedBuyerRank
  rw [← sortedB_toFinset E lamD lamS T ω]
  exact card_lt_le_pos _ (buyerTime ω) (fun a b h => by
    rcases h with h | ⟨h, _⟩
    · exact h.le
    · exact h.le) _ (sortedB_pairwise E lamD lamS T ω) r hr

lemma rankS_le_pos (ω : Ω) (r : ℕ) (hr : r < (sortedS E lamD lamS T ω).length) :
    taggedSellerRank E lamD lamS T ω (sellerTime ω (sortedS E lamD lamS T ω)[r]) ≤ r := by
  unfold taggedSellerRank
  rw [← sortedS_toFinset E lamD lamS T ω]
  exact card_lt_le_pos _ (sellerTime ω) (fun a b h => by
    rcases h with h | ⟨h, _⟩
    · exact h.le
    · exact h.le) _ (sortedS_pairwise E lamD lamS T ω) r hr

lemma mem_pairs (ω : Ω) (p : Fin ω.2.1 × Fin ω.1.1)
    (hp : p ∈ (greedyPairs E lamD lamS T ω).toFinset) :
    ∃ r, ∃ h1 : r < (sortedS E lamD lamS T ω).length, ∃ h2 : r < (sortedB E lamD lamS T ω).length,
      p = ((sortedS E lamD lamS T ω)[r], (sortedB E lamD lamS T ω)[r]) := by
  unfold greedyPairs at hp
  obtain ⟨r, hr, hpr⟩ := List.mem_iff_getElem.1 (List.mem_toFinset.1 hp)
  rw [List.length_zip] at hr
  refine ⟨r, lt_of_lt_of_le hr (min_le_left _ _), lt_of_lt_of_le hr (min_le_right _ _), ?_⟩
  rw [← hpr, List.getElem_zip]

/-- Step 1 (buyer side): matched buyers are tagged-matchable. -/
lemma pairs_buyer_le (ω : Ω) (f : Fin ω.1.1 → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ p ∈ (greedyPairs E lamD lamS T ω).toFinset, f p.2 ≤
      ∑ i ∈ reqB E lamD lamS T ω, Md E lamD lamS T ω (buyerTime ω i) * f i := by
  classical
  have hinj : Set.InjOn Prod.snd (((greedyPairs E lamD lamS T ω).toFinset :
      Finset (Fin ω.2.1 × Fin ω.1.1)) : Set (Fin ω.2.1 × Fin ω.1.1)) := by
    intro p hp q hq hpq
    obtain ⟨r, h1, h2, rfl⟩ := mem_pairs E lamD lamS T ω p hp
    obtain ⟨r', h1', h2', rfl⟩ := mem_pairs E lamD lamS T ω q hq
    have : r = r' := (List.Nodup.getElem_inj_iff (sortedB_nodup E lamD lamS T ω)).1 hpq
    subst this
    rfl
  rw [← Finset.sum_image (f := f) hinj]
  have key : ∀ i ∈ (greedyPairs E lamD lamS T ω).toFinset.image Prod.snd,
      i ∈ reqB E lamD lamS T ω ∧ Md E lamD lamS T ω (buyerTime ω i) = 1 := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
    obtain ⟨r, h1, h2, rfl⟩ := mem_pairs E lamD lamS T ω p hp
    refine ⟨?_, ?_⟩
    · rw [← sortedB_toFinset E lamD lamS T ω, List.mem_toFinset]
      exact List.getElem_mem h2
    · unfold Md
      rw [if_pos]
      exact lt_of_le_of_lt (rankB_le_pos E lamD lamS T ω r h2) h1
  calc ∑ i ∈ (greedyPairs E lamD lamS T ω).toFinset.image Prod.snd, f i
      = ∑ i ∈ (greedyPairs E lamD lamS T ω).toFinset.image Prod.snd,
          Md E lamD lamS T ω (buyerTime ω i) * f i :=
        Finset.sum_congr rfl (fun i hi => by rw [(key i hi).2, one_mul])
    _ ≤ ∑ i ∈ reqB E lamD lamS T ω, Md E lamD lamS T ω (buyerTime ω i) * f i := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => (key i hi).1) ?_
        intro i _ _
        unfold Md
        split_ifs
        · rw [one_mul]; exact hf i
        · rw [zero_mul]

lemma pairs_seller_le (ω : Ω) (f : Fin ω.2.1 → ℝ) (hf : ∀ j, 0 ≤ f j) :
    ∑ p ∈ (greedyPairs E lamD lamS T ω).toFinset, f p.1 ≤
      ∑ j ∈ reqS E lamD lamS T ω, Ms E lamD lamS T ω (sellerTime ω j) * f j := by
  classical
  have hinj : Set.InjOn Prod.fst (((greedyPairs E lamD lamS T ω).toFinset :
      Finset (Fin ω.2.1 × Fin ω.1.1)) : Set (Fin ω.2.1 × Fin ω.1.1)) := by
    intro p hp q hq hpq
    obtain ⟨r, h1, h2, rfl⟩ := mem_pairs E lamD lamS T ω p hp
    obtain ⟨r', h1', h2', rfl⟩ := mem_pairs E lamD lamS T ω q hq
    have : r = r' := (List.Nodup.getElem_inj_iff (sortedS_nodup E lamD lamS T ω)).1 hpq
    subst this
    rfl
  rw [← Finset.sum_image (f := f) hinj]
  have key : ∀ j ∈ (greedyPairs E lamD lamS T ω).toFinset.image Prod.fst,
      j ∈ reqS E lamD lamS T ω ∧ Ms E lamD lamS T ω (sellerTime ω j) = 1 := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hj
    obtain ⟨r, h1, h2, rfl⟩ := mem_pairs E lamD lamS T ω p hp
    refine ⟨?_, ?_⟩
    · rw [← sortedS_toFinset E lamD lamS T ω, List.mem_toFinset]
      exact List.getElem_mem h1
    · unfold Ms
      rw [if_pos]
      exact lt_of_le_of_lt (rankS_le_pos E lamD lamS T ω r h1) h2
  calc ∑ j ∈ (greedyPairs E lamD lamS T ω).toFinset.image Prod.fst, f j
      = ∑ j ∈ (greedyPairs E lamD lamS T ω).toFinset.image Prod.fst,
          Ms E lamD lamS T ω (sellerTime ω j) * f j :=
        Finset.sum_congr rfl (fun j hj => by rw [(key j hj).2, one_mul])
    _ ≤ ∑ j ∈ reqS E lamD lamS T ω, Ms E lamD lamS T ω (sellerTime ω j) * f j := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => (key j hj).1) ?_
        intro j _ _
        unfold Ms
        split_ifs
        · rw [one_mul]; exact hf j
        · rw [zero_mul]

lemma pairs_card (ω : Ω) :
    min (Nd E lamD lamS T ω T) (Ns E lamD lamS T ω T) ≤
      (greedyPairs E lamD lamS T ω).toFinset.card := by
  unfold greedyPairs
  rw [List.toFinset_card_of_nodup (zip_nodup _ _ (sortedS_nodup E lamD lamS T ω)),
    List.length_zip, sortedS_length, sortedB_length, min_comm]
  unfold Nd Ns
  exact min_le_min (Finset.card_filter_le _ _) (Finset.card_filter_le _ _)

lemma ii_of_bound (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  (intervalIntegrable_const (c := C)).mono_fun hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by
      simp only [Real.norm_eq_abs]; exact (hC x).trans (le_abs_self C)))

lemma Ns_mono (ω : Ω) : Monotone (fun s => (Ns E lamD lamS T ω s : ℝ)) := by
  intro a b hab
  simp only [Nat.cast_le]
  exact Finset.card_le_card (fun j hj => by
    rw [Finset.mem_filter] at hj ⊢; exact ⟨hj.1, le_trans hj.2 hab⟩)

lemma Nd_mono (ω : Ω) : Monotone (fun s => (Nd E lamD lamS T ω s : ℝ)) := by
  intro a b hab
  simp only [Nat.cast_le]
  exact Finset.card_le_card (fun j hj => by
    rw [Finset.mem_filter] at hj ⊢; exact ⟨hj.1, le_trans hj.2 hab⟩)

lemma indNs_meas (ω : Ω) (r : ℕ) :
    Measurable (fun s : ℝ => if Ns E lamD lamS T ω s ≤ r then (1:ℝ) else 0) := by
  refine Measurable.ite ?_ measurable_const measurable_const
  have : {s : ℝ | Ns E lamD lamS T ω s ≤ r} = {s | (Ns E lamD lamS T ω s : ℝ) ≤ (r:ℝ)} := by
    ext s; simp
  rw [this]
  exact measurableSet_le (Ns_mono E lamD lamS T ω).measurable measurable_const

lemma indNd_meas (ω : Ω) (r : ℕ) :
    Measurable (fun s : ℝ => if Nd E lamD lamS T ω s ≤ r then (1:ℝ) else 0) := by
  refine Measurable.ite ?_ measurable_const measurable_const
  have : {s : ℝ | Nd E lamD lamS T ω s ≤ r} = {s | (Nd E lamD lamS T ω s : ℝ) ≤ (r:ℝ)} := by
    ext s; simp
  rw [this]
  exact measurableSet_le (Nd_mono E lamD lamS T ω).measurable measurable_const

lemma ite_abs_le (p : Prop) [Decidable p] : |(if p then (1:ℝ) else 0)| ≤ 1 := by
  split_ifs <;> simp

lemma int_Iio (t T τ : ℝ) (htT : t ≤ T) (hτT : τ ≤ T) :
    ∫ s in t..T, (Set.Iio τ).indicator (1 : ℝ → ℝ) s = max t τ - t := by
  rw [intervalIntegral.integral_of_le htT, integral_indicator_one measurableSet_Iio,
    measureReal_def, Measure.restrict_apply measurableSet_Iio]
  have : Set.Iio τ ∩ Set.Ioc t T = Set.Ioo t τ := by
    ext s; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_Ioo]; constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, le_trans h2.le hτT⟩
  rw [this, Real.volume_Ioo, ENNReal.toReal_ofReal']
  rcases le_total t τ with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

/-- Tagged buyer wait is at most the time the seller count stays at most its rank. -/
lemma Wd_le_int (ω : Ω) (t : ℝ) (htT : t ≤ T)
    (hS : ∀ j : Fin ω.2.1, sellerTime ω j ≤ T) :
    Wd E lamD lamS T ω t ≤ ∫ s in t..T,
      (if Ns E lamD lamS T ω s ≤ taggedBuyerRank E lamD lamS T ω t then (1:ℝ) else 0) := by
  set r := taggedBuyerRank E lamD lamS T ω t with hr
  have hgi : IntervalIntegrable (fun s : ℝ => if Ns E lamD lamS T ω s ≤ r then (1:ℝ) else 0)
      volume t T := ii_of_bound _ (indNs_meas E lamD lamS T ω r) 1 (fun x => ite_abs_le _) t T
  unfold Wd
  rw [← hr]
  cases hS' : (sortedS E lamD lamS T ω)[r]? with
  | none =>
    have hlen : (sortedS E lamD lamS T ω).length ≤ r := List.getElem?_eq_none_iff.1 hS'
    have h1 : ∀ s, (if Ns E lamD lamS T ω s ≤ r then (1:ℝ) else 0) = 1 := by
      intro s
      rw [if_pos]
      calc Ns E lamD lamS T ω s ≤ (reqS E lamD lamS T ω).card := Finset.card_filter_le _ _
        _ = (sortedS E lamD lamS T ω).length := (sortedS_length E lamD lamS T ω).symm
        _ ≤ r := hlen
    simp only [h1, intervalIntegral.integral_const, smul_eq_mul, mul_one]
    exact le_rfl
  | some j =>
    obtain ⟨hrl, hj⟩ := List.getElem?_eq_some_iff.1 hS'
    have hτT : sellerTime ω j ≤ T := hS j
    have hlow : ∀ s, (Set.Iio (sellerTime ω j)).indicator (1 : ℝ → ℝ) s ≤
        (if Ns E lamD lamS T ω s ≤ r then (1:ℝ) else 0) := by
      intro s
      by_cases hs : s < sellerTime ω j
      · have hN : Ns E lamD lamS T ω s ≤ r := by
          have hrk := rankS_le_pos E lamD lamS T ω r hrl
          rw [hj] at hrk
          refine le_trans (Finset.card_le_card (fun k hk => ?_)) hrk
          rw [Finset.mem_filter] at hk ⊢
          exact ⟨hk.1, lt_of_le_of_lt hk.2 hs⟩
        rw [Set.indicator_of_mem (show s ∈ Set.Iio (sellerTime ω j) from hs), if_pos hN]; simp
      · rw [Set.indicator_of_notMem (show s ∉ Set.Iio (sellerTime ω j) from hs)]
        split_ifs <;> norm_num
    have hii : IntervalIntegrable ((Set.Iio (sellerTime ω j)).indicator (1 : ℝ → ℝ)) volume t T :=
      ii_of_bound _ (measurable_one.indicator measurableSet_Iio) 1 (fun x => by
        by_cases hx : x ∈ Set.Iio (sellerTime ω j)
        · simp [Set.indicator_of_mem hx]
        · simp [Set.indicator_of_notMem hx]) t T
    calc max t (sellerTime ω j) - t
        = ∫ s in t..T, (Set.Iio (sellerTime ω j)).indicator (1 : ℝ → ℝ) s :=
          (int_Iio t T _ htT hτT).symm
      _ ≤ _ := intervalIntegral.integral_mono_on htT hii hgi (fun s _ => hlow s)

lemma Ws_le_int (ω : Ω) (t : ℝ) (htT : t ≤ T)
    (hB : ∀ i : Fin ω.1.1, buyerTime ω i ≤ T) :
    Ws E lamD lamS T ω t ≤ ∫ s in t..T,
      (if Nd E lamD lamS T ω s ≤ taggedSellerRank E lamD lamS T ω t then (1:ℝ) else 0) := by
  set r := taggedSellerRank E lamD lamS T ω t with hr
  have hgi : IntervalIntegrable (fun s : ℝ => if Nd E lamD lamS T ω s ≤ r then (1:ℝ) else 0)
      volume t T := ii_of_bound _ (indNd_meas E lamD lamS T ω r) 1 (fun x => ite_abs_le _) t T
  unfold Ws
  rw [← hr]
  cases hS' : (sortedB E lamD lamS T ω)[r]? with
  | none =>
    have hlen : (sortedB E lamD lamS T ω).length ≤ r := List.getElem?_eq_none_iff.1 hS'
    have h1 : ∀ s, (if Nd E lamD lamS T ω s ≤ r then (1:ℝ) else 0) = 1 := by
      intro s
      rw [if_pos]
      calc Nd E lamD lamS T ω s ≤ (reqB E lamD lamS T ω).card := Finset.card_filter_le _ _
        _ = (sortedB E lamD lamS T ω).length := (sortedB_length E lamD lamS T ω).symm
        _ ≤ r := hlen
    simp only [h1, intervalIntegral.integral_const, smul_eq_mul, mul_one]
    exact le_rfl
  | some j =>
    obtain ⟨hrl, hj⟩ := List.getElem?_eq_some_iff.1 hS'
    have hτT : buyerTime ω j ≤ T := hB j
    have hlow : ∀ s, (Set.Iio (buyerTime ω j)).indicator (1 : ℝ → ℝ) s ≤
        (if Nd E lamD lamS T ω s ≤ r then (1:ℝ) else 0) := by
      intro s
      by_cases hs : s < buyerTime ω j
      · have hN : Nd E lamD lamS T ω s ≤ r := by
          have hrk := rankB_le_pos E lamD lamS T ω r hrl
          rw [hj] at hrk
          refine le_trans (Finset.card_le_card (fun k hk => ?_)) hrk
          rw [Finset.mem_filter] at hk ⊢
          exact ⟨hk.1, lt_of_le_of_lt hk.2 hs⟩
        rw [Set.indicator_of_mem (show s ∈ Set.Iio (buyerTime ω j) from hs), if_pos hN]; simp
      · rw [Set.indicator_of_notMem (show s ∉ Set.Iio (buyerTime ω j) from hs)]
        split_ifs <;> norm_num
    have hii : IntervalIntegrable ((Set.Iio (buyerTime ω j)).indicator (1 : ℝ → ℝ)) volume t T :=
      ii_of_bound _ (measurable_one.indicator measurableSet_Iio) 1 (fun x => by
        by_cases hx : x ∈ Set.Iio (buyerTime ω j)
        · simp [Set.indicator_of_mem hx]
        · simp [Set.indicator_of_notMem hx]) t T
    calc max t (buyerTime ω j) - t
        = ∫ s in t..T, (Set.Iio (buyerTime ω j)).indicator (1 : ℝ → ℝ) s :=
          (int_Iio t T _ htT hτT).symm
      _ ≤ _ := intervalIntegral.integral_mono_on htT hii hgi (fun s _ => hlow s)

noncomputable def gB (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (i : Fin ω.1.1) (s : ℝ) : ℝ :=
  (Set.Ioi (buyerTime ω i)).indicator
    (fun s => if Ns E lamD lamS T ω s ≤ taggedBuyerRank E lamD lamS T ω (buyerTime ω i)
      then (1:ℝ) else 0) s

noncomputable def gS (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (i : Fin ω.2.1) (s : ℝ) : ℝ :=
  (Set.Ioi (sellerTime ω i)).indicator
    (fun s => if Nd E lamD lamS T ω s ≤ taggedSellerRank E lamD lamS T ω (sellerTime ω i)
      then (1:ℝ) else 0) s

lemma sum_Wd_le (ω : Ω) (hT : 0 ≤ T)
    (hB : ∀ i : Fin ω.1.1, 0 ≤ buyerTime ω i ∧ buyerTime ω i ≤ T)
    (hS : ∀ j : Fin ω.2.1, sellerTime ω j ≤ T) :
    ∑ i ∈ reqB E lamD lamS T ω, Wd E lamD lamS T ω (buyerTime ω i) ≤
      ∫ s in (0:ℝ)..T, max ((Nd E lamD lamS T ω s : ℝ) - (Ns E lamD lamS T ω s : ℝ)) 0 := by
  have hgm : ∀ i, Measurable (gB E lamD lamS T ω i) := fun i =>
    (indNs_meas E lamD lamS T ω _).indicator measurableSet_Ioi
  have hgb : ∀ i s, |gB E lamD lamS T ω i s| ≤ 1 := by
    intro i s
    unfold gB
    by_cases hs : s ∈ Set.Ioi (buyerTime ω i)
    · rw [Set.indicator_of_mem hs]; exact ite_abs_le _
    · rw [Set.indicator_of_notMem hs]; simp
  have step1 : ∀ i ∈ reqB E lamD lamS T ω,
      Wd E lamD lamS T ω (buyerTime ω i) ≤ ∫ s in (0:ℝ)..T, gB E lamD lamS T ω i s := by
    intro i _
    refine (Wd_le_int E lamD lamS T ω (buyerTime ω i) (hB i).2 hS).trans (le_of_eq ?_)
    rw [intervalIntegral.integral_of_le (hB i).2, intervalIntegral.integral_of_le hT]
    unfold gB
    have hset : Set.Ioc (0:ℝ) T ∩ Set.Ioi (buyerTime ω i) = Set.Ioc (buyerTime ω i) T := by
      ext s; simp only [Set.mem_Ioc, Set.mem_inter_iff, Set.mem_Ioi]; constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨lt_of_le_of_lt (hB i).1 h1, h2⟩, h1⟩
    rw [setIntegral_indicator measurableSet_Ioi, hset]
  have hsm : Measurable (fun s => ∑ i ∈ reqB E lamD lamS T ω, gB E lamD lamS T ω i s) :=
    Finset.measurable_sum _ (fun i _ => hgm i)
  have hrm : Measurable (fun s => max ((Nd E lamD lamS T ω s : ℝ) -
      (Ns E lamD lamS T ω s : ℝ)) 0) :=
    ((Nd_mono E lamD lamS T ω).measurable.sub (Ns_mono E lamD lamS T ω).measurable).max
      measurable_const
  calc ∑ i ∈ reqB E lamD lamS T ω, Wd E lamD lamS T ω (buyerTime ω i)
      ≤ ∑ i ∈ reqB E lamD lamS T ω, ∫ s in (0:ℝ)..T, gB E lamD lamS T ω i s := Finset.sum_le_sum step1
    _ = ∫ s in (0:ℝ)..T, ∑ i ∈ reqB E lamD lamS T ω, gB E lamD lamS T ω i s :=
        (intervalIntegral.integral_finset_sum
          (fun i _ => ii_of_bound _ (hgm i) 1 (hgb i) 0 T)).symm
    _ ≤ _ := by
      refine intervalIntegral.integral_mono_on hT
        (ii_of_bound _ hsm ((reqB E lamD lamS T ω).card) (fun s => ?_) 0 T)
        (ii_of_bound _ hrm ((reqB E lamD lamS T ω).card) (fun s => ?_) 0 T) (fun s _ => ?_)
      · calc |∑ i ∈ reqB E lamD lamS T ω, gB E lamD lamS T ω i s|
            ≤ ∑ i ∈ reqB E lamD lamS T ω, |gB E lamD lamS T ω i s| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i ∈ reqB E lamD lamS T ω, (1:ℝ) := Finset.sum_le_sum (fun i _ => hgb i s)
          _ = _ := by simp
      · have h0 : (0:ℝ) ≤ Nd E lamD lamS T ω s := Nat.cast_nonneg _
        have h0' : (0:ℝ) ≤ Ns E lamD lamS T ω s := Nat.cast_nonneg _
        have h1 : (Nd E lamD lamS T ω s : ℝ) ≤ (reqB E lamD lamS T ω).card := by
          exact_mod_cast Finset.card_filter_le _ _
        rw [abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith) (by positivity)
      · have hsum : ∑ i ∈ reqB E lamD lamS T ω, gB E lamD lamS T ω i s =
            (((reqB E lamD lamS T ω).filter (fun i => buyerTime ω i < s ∧
              Ns E lamD lamS T ω s ≤ taggedBuyerRank E lamD lamS T ω (buyerTime ω i))).card : ℝ) := by
          rw [Finset.card_filter]; push_cast
          refine Finset.sum_congr rfl (fun i _ => ?_)
          unfold gB
          simp only [Set.indicator_apply, Set.mem_Ioi]
          by_cases h1 : buyerTime ω i < s <;>
            by_cases h2 : Ns E lamD lamS T ω s ≤ taggedBuyerRank E lamD lamS T ω (buyerTime ω i) <;>
            simp [h1, h2]
        rw [hsum]
        have h1 : ((reqB E lamD lamS T ω).filter (fun i => buyerTime ω i < s ∧
              Ns E lamD lamS T ω s ≤ taggedBuyerRank E lamD lamS T ω (buyerTime ω i))).card ≤
            ((reqB E lamD lamS T ω).filter (fun i => buyerTime ω i < s)).card - Ns E lamD lamS T ω s :=
          card_rank_ge (reqB E lamD lamS T ω) (buyerTime ω) s (Ns E lamD lamS T ω s)
        have h2 : ((reqB E lamD lamS T ω).filter (fun i => buyerTime ω i < s)).card ≤
            Nd E lamD lamS T ω s :=
          Finset.card_le_card (fun k hk => by
            rw [Finset.mem_filter] at hk ⊢; exact ⟨hk.1, hk.2.le⟩)
        have h3 := le_trans h1 (Nat.sub_le_sub_right h2 (Ns E lamD lamS T ω s))
        rw [← natsub_cast]
        exact_mod_cast h3


lemma sum_Ws_le (ω : Ω) (hT : 0 ≤ T)
    (hS : ∀ i : Fin ω.2.1, 0 ≤ sellerTime ω i ∧ sellerTime ω i ≤ T)
    (hB : ∀ j : Fin ω.1.1, buyerTime ω j ≤ T) :
    ∑ i ∈ reqS E lamD lamS T ω, Ws E lamD lamS T ω (sellerTime ω i) ≤
      ∫ s in (0:ℝ)..T, max ((Ns E lamD lamS T ω s : ℝ) - (Nd E lamD lamS T ω s : ℝ)) 0 := by
  have hgm : ∀ i, Measurable (gS E lamD lamS T ω i) := fun i =>
    (indNd_meas E lamD lamS T ω _).indicator measurableSet_Ioi
  have hgb : ∀ i s, |gS E lamD lamS T ω i s| ≤ 1 := by
    intro i s
    unfold gS
    by_cases hs : s ∈ Set.Ioi (sellerTime ω i)
    · rw [Set.indicator_of_mem hs]; exact ite_abs_le _
    · rw [Set.indicator_of_notMem hs]; simp
  have step1 : ∀ i ∈ reqS E lamD lamS T ω,
      Ws E lamD lamS T ω (sellerTime ω i) ≤ ∫ s in (0:ℝ)..T, gS E lamD lamS T ω i s := by
    intro i _
    refine (Ws_le_int E lamD lamS T ω (sellerTime ω i) (hS i).2 hB).trans (le_of_eq ?_)
    rw [intervalIntegral.integral_of_le (hS i).2, intervalIntegral.integral_of_le hT]
    unfold gS
    have hset : Set.Ioc (0:ℝ) T ∩ Set.Ioi (sellerTime ω i) = Set.Ioc (sellerTime ω i) T := by
      ext s; simp only [Set.mem_Ioc, Set.mem_inter_iff, Set.mem_Ioi]; constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨lt_of_le_of_lt (hS i).1 h1, h2⟩, h1⟩
    rw [setIntegral_indicator measurableSet_Ioi, hset]
  have hsm : Measurable (fun s => ∑ i ∈ reqS E lamD lamS T ω, gS E lamD lamS T ω i s) :=
    Finset.measurable_sum _ (fun i _ => hgm i)
  have hrm : Measurable (fun s => max ((Ns E lamD lamS T ω s : ℝ) -
      (Nd E lamD lamS T ω s : ℝ)) 0) :=
    ((Ns_mono E lamD lamS T ω).measurable.sub (Nd_mono E lamD lamS T ω).measurable).max
      measurable_const
  calc ∑ i ∈ reqS E lamD lamS T ω, Ws E lamD lamS T ω (sellerTime ω i)
      ≤ ∑ i ∈ reqS E lamD lamS T ω, ∫ s in (0:ℝ)..T, gS E lamD lamS T ω i s := Finset.sum_le_sum step1
    _ = ∫ s in (0:ℝ)..T, ∑ i ∈ reqS E lamD lamS T ω, gS E lamD lamS T ω i s :=
        (intervalIntegral.integral_finset_sum
          (fun i _ => ii_of_bound _ (hgm i) 1 (hgb i) 0 T)).symm
    _ ≤ _ := by
      refine intervalIntegral.integral_mono_on hT
        (ii_of_bound _ hsm ((reqS E lamD lamS T ω).card) (fun s => ?_) 0 T)
        (ii_of_bound _ hrm ((reqS E lamD lamS T ω).card) (fun s => ?_) 0 T) (fun s _ => ?_)
      · calc |∑ i ∈ reqS E lamD lamS T ω, gS E lamD lamS T ω i s|
            ≤ ∑ i ∈ reqS E lamD lamS T ω, |gS E lamD lamS T ω i s| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i ∈ reqS E lamD lamS T ω, (1:ℝ) := Finset.sum_le_sum (fun i _ => hgb i s)
          _ = _ := by simp
      · have h0 : (0:ℝ) ≤ Ns E lamD lamS T ω s := Nat.cast_nonneg _
        have h0' : (0:ℝ) ≤ Nd E lamD lamS T ω s := Nat.cast_nonneg _
        have h1 : (Ns E lamD lamS T ω s : ℝ) ≤ (reqS E lamD lamS T ω).card := by
          exact_mod_cast Finset.card_filter_le _ _
        rw [abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith) (by positivity)
      · have hsum : ∑ i ∈ reqS E lamD lamS T ω, gS E lamD lamS T ω i s =
            (((reqS E lamD lamS T ω).filter (fun i => sellerTime ω i < s ∧
              Nd E lamD lamS T ω s ≤ taggedSellerRank E lamD lamS T ω (sellerTime ω i))).card : ℝ) := by
          rw [Finset.card_filter]; push_cast
          refine Finset.sum_congr rfl (fun i _ => ?_)
          unfold gS
          simp only [Set.indicator_apply, Set.mem_Ioi]
          by_cases h1 : sellerTime ω i < s <;>
            by_cases h2 : Nd E lamD lamS T ω s ≤ taggedSellerRank E lamD lamS T ω (sellerTime ω i) <;>
            simp [h1, h2]
        rw [hsum]
        have h1 : ((reqS E lamD lamS T ω).filter (fun i => sellerTime ω i < s ∧
              Nd E lamD lamS T ω s ≤ taggedSellerRank E lamD lamS T ω (sellerTime ω i))).card ≤
            ((reqS E lamD lamS T ω).filter (fun i => sellerTime ω i < s)).card - Nd E lamD lamS T ω s :=
          card_rank_ge (reqS E lamD lamS T ω) (sellerTime ω) s (Nd E lamD lamS T ω s)
        have h2 : ((reqS E lamD lamS T ω).filter (fun i => sellerTime ω i < s)).card ≤
            Ns E lamD lamS T ω s :=
          Finset.card_le_card (fun k hk => by
            rw [Finset.mem_filter] at hk ⊢; exact ⟨hk.1, hk.2.le⟩)
        have h3 := le_trans h1 (Nat.sub_le_sub_right h2 (Nd E lamD lamS T ω s))
        rw [← natsub_cast]
        exact_mod_cast h3

end Sorted



section MeckePart
open ProbabilityTheory
open scoped NNReal Nat ENNReal

/-- Index map that skips position `i`. -/
def skipIdx (i k : ℕ) : ℕ := if k < i then k else k + 1

/-- Delete the `i`-th mark of a side configuration. -/
def delPt (i : ℕ) (s : ℕ × (ℕ → ℝ × ℝ)) : ℕ × (ℕ → ℝ × ℝ) :=
  (s.1 - 1, fun k => s.2 (skipIdx i k))

/-- `H y (n, x)` only depends on the first `n` marks. -/
def IsLocal (H : ℝ × ℝ → ℕ × (ℕ → ℝ × ℝ) → ℝ≥0∞) : Prop :=
  ∀ y n (x x' : ℕ → ℝ × ℝ), (∀ k < n, x k = x' k) → H y (n, x) = H y (n, x')

def restN (n : ℕ) (x : ℕ → ℝ × ℝ) : Fin n → ℝ × ℝ := fun k => x k

def extN (n : ℕ) (g : Fin n → ℝ × ℝ) : ℕ → ℝ × ℝ := fun k => if h : k < n then g ⟨k, h⟩ else 0

lemma restN_meas (n : ℕ) : Measurable (restN n) :=
  measurable_pi_lambda _ (fun k => measurable_pi_apply _)

lemma extN_meas (n : ℕ) : Measurable (extN n) := by
  refine measurable_pi_lambda _ (fun k => ?_)
  by_cases h : k < n
  · simp only [extN, dif_pos h]; exact measurable_pi_apply _
  · simp only [extN, dif_neg h]; exact measurable_const

lemma map_restN (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q] (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => Q)).map (restN n) = Measure.pi (fun _ : Fin n => Q) := by
  classical
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply (restN_meas n) (MeasurableSet.univ_pi hs)]
  set t : ℕ → Set (ℝ × ℝ) := fun k => if h : k < n then s ⟨k, h⟩ else Set.univ with ht
  have hset : restN n ⁻¹' Set.univ.pi s = Set.pi (↑(Finset.range n)) t := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_pi, Finset.coe_range, Set.mem_Iio,
      restN, ht]
    constructor
    · intro hx k hk; rw [dif_pos hk]; exact hx ⟨k, hk⟩ (Set.mem_univ _)
    · intro hx k _; have := hx k k.2; rw [dif_pos k.2] at this; exact this
  have htm : ∀ k ∈ Finset.range n, MeasurableSet (t k) := by
    intro k _
    simp only [ht]
    split_ifs
    · exact hs _
    · exact MeasurableSet.univ
  have hpi := Measure.infinitePi_pi (μ := fun _ : ℕ => Q) (s := Finset.range n) (t := t) htm
  rw [hset, hpi]
  rw [← Fin.prod_univ_eq_prod_range (fun k => Q (t k)) n]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  simp only [ht, dif_pos k.2]

lemma lintegral_restN (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q] (n : ℕ)
    (Φ : (Fin n → ℝ × ℝ) → ℝ≥0∞) (hΦ : Measurable Φ) :
    ∫⁻ x, Φ (restN n x) ∂(Measure.infinitePi (fun _ : ℕ => Q)) =
      ∫⁻ f, Φ f ∂(Measure.pi (fun _ : Fin n => Q)) := by
  rw [← map_restN Q n, lintegral_map hΦ (restN_meas n)]

lemma succAbove_val (m i : ℕ) (hi : i < m + 1) (k : ℕ) (hk : k < m) :
    (((⟨i, hi⟩ : Fin (m + 1)).succAbove ⟨k, hk⟩ : Fin (m + 1)) : ℕ) = skipIdx i k := by
  unfold skipIdx Fin.succAbove
  split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def]

lemma fiber_mecke (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q]
    (H : ℝ × ℝ → ℕ × (ℕ → ℝ × ℝ) → ℝ≥0∞) (hH : Measurable (Function.uncurry H))
    (hloc : IsLocal H) (m i : ℕ) (hi : i < m + 1) :
    ∫⁻ x, H (x i) (m, fun k => x (skipIdx i k)) ∂(Measure.infinitePi (fun _ : ℕ => Q)) =
      ∫⁻ y, ∫⁻ x, H y (m, x) ∂(Measure.infinitePi (fun _ : ℕ => Q)) ∂Q := by
  set IP := Measure.infinitePi (fun _ : ℕ => Q) with hIP
  set I : Fin (m + 1) := ⟨i, hi⟩ with hI
  set Φ : (ℝ × ℝ) × (Fin m → ℝ × ℝ) → ℝ≥0∞ := fun p => H p.1 (m, extN m p.2) with hΦdef
  have hΦ : Measurable Φ :=
    hH.comp (measurable_fst.prodMk (measurable_const.prodMk ((extN_meas m).comp measurable_snd)))
  have e1 : ∀ x : ℕ → ℝ × ℝ, H (x i) (m, fun k => x (skipIdx i k)) =
      Φ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ × ℝ) I (restN (m + 1) x)) := by
    intro x
    simp only [hΦdef, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply]
    show H (x i) _ = H (x i) _
    apply hloc
    intro k hk
    simp only [extN, dif_pos hk, Fin.removeNth, restN]
    rw [succAbove_val m i hi k hk]
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => Q) I
  calc ∫⁻ x, H (x i) (m, fun k => x (skipIdx i k)) ∂IP
      = ∫⁻ x, Φ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ × ℝ) I
          (restN (m + 1) x)) ∂IP := lintegral_congr (fun x => e1 x)
    _ = ∫⁻ f, Φ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ × ℝ) I f)
          ∂(Measure.pi (fun _ : Fin (m + 1) => Q)) :=
        lintegral_restN Q (m + 1) _ (hΦ.comp (MeasurableEquiv.measurable _))
    _ = ∫⁻ p, Φ p ∂(Q.prod (Measure.pi (fun _ : Fin m => Q))) := hmp.lintegral_comp hΦ
    _ = ∫⁻ y, ∫⁻ g, Φ (y, g) ∂(Measure.pi (fun _ : Fin m => Q)) ∂Q :=
        lintegral_prod _ hΦ.aemeasurable
    _ = ∫⁻ y, ∫⁻ x, H y (m, x) ∂IP ∂Q := by
        refine lintegral_congr (fun y => ?_)
        have hy : Measurable (fun g : Fin m → ℝ × ℝ => Φ (y, g)) :=
          hΦ.comp (measurable_const.prodMk measurable_id)
        rw [← lintegral_restN Q m _ hy]
        refine lintegral_congr (fun x => ?_)
        simp only [hΦdef]
        apply hloc
        intro k hk
        simp only [extN, dif_pos hk, restN]

lemma poisson_succ_weight (ρ : ℝ≥0) (m : ℕ) :
    ENNReal.ofReal (Real.exp (-ρ) * (ρ:ℝ) ^ (m + 1) / ((m + 1)! : ℝ)) * ((m + 1 : ℕ) : ℝ≥0∞) =
      ENNReal.ofReal (ρ : ℝ) * ENNReal.ofReal (Real.exp (-ρ) * (ρ:ℝ) ^ m / (m ! : ℝ)) := by
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

lemma lintegral_poisson (ρ : ℝ≥0) (f : ℕ → ℝ≥0∞) :
    ∫⁻ n, f n ∂(poissonMeasure ρ) =
      ∑' n, ENNReal.ofReal (Real.exp (-ρ) * (ρ:ℝ) ^ n / (n ! : ℝ)) * f n := by
  rw [poissonMeasure, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

lemma delPt_meas (i n : ℕ) : Measurable (fun x : ℕ → ℝ × ℝ => delPt i (n, x)) := by
  simp only [delPt]
  exact measurable_const.prodMk (measurable_pi_lambda _ (fun k => measurable_pi_apply _))

/-- Mecke formula for a marked Poisson count: sum over points with the point deleted. -/
theorem mecke (r T : ℝ) (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q]
    (H : ℝ × ℝ → ℕ × (ℕ → ℝ × ℝ) → ℝ≥0∞) (hH : Measurable (Function.uncurry H))
    (hloc : IsLocal H) :
    ∫⁻ s, ∑ i ∈ Finset.range s.1, H (s.2 i) (delPt i s) ∂(sideLaw r T Q) =
      ENNReal.ofReal (max (r * T) 0) * ∫⁻ y, ∫⁻ s, H y s ∂(sideLaw r T Q) ∂Q := by
  set ρ : ℝ≥0 := ⟨max (r * T) 0, le_max_right _ _⟩ with hρ
  set IP := Measure.infinitePi (fun _ : ℕ => Q) with hIP
  have hside : sideLaw r T Q = (poissonMeasure ρ).prod IP := rfl
  have hρv : ENNReal.ofReal (max (r * T) 0) = ENNReal.ofReal (ρ : ℝ) := rfl
  have hmi : ∀ n i : ℕ, Measurable (fun x : ℕ → ℝ × ℝ => H (x i) (delPt i (n, x))) :=
    fun n i => hH.comp ((measurable_pi_apply i).prodMk (delPt_meas i n))
  have hmeasL : Measurable (fun s : ℕ × (ℕ → ℝ × ℝ) =>
      ∑ i ∈ Finset.range s.1, H (s.2 i) (delPt i s)) := by
    apply measurable_from_prod_countable_right
    intro n
    show Measurable fun x : ℕ → ℝ × ℝ => ∑ i ∈ Finset.range n, H (x i) (delPt i (n, x))
    exact Finset.measurable_sum _ (fun i _ => hmi n i)
  have hfib : ∀ m : ℕ, ∫⁻ x, ∑ i ∈ Finset.range (m + 1), H (x i) (delPt i (m + 1, x)) ∂IP =
      ((m + 1 : ℕ) : ℝ≥0∞) * ∫⁻ y, ∫⁻ x, H y (m, x) ∂IP ∂Q := by
    intro m
    rw [lintegral_finset_sum (f := fun i x => H (x i) (delPt i (m + 1, x))) _
      (fun i _ => hmi (m + 1) i)]
    have : ∀ i ∈ Finset.range (m + 1),
        ∫⁻ x, H (x i) (delPt i (m + 1, x)) ∂IP = ∫⁻ y, ∫⁻ x, H y (m, x) ∂IP ∂Q := by
      intro i hi
      exact fiber_mecke Q H hH hloc m i (Finset.mem_range.1 hi)
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hfib0 : ∫⁻ x, ∑ i ∈ Finset.range 0, H (x i) (delPt i (0, x)) ∂IP = 0 := by simp
  have hR : ∀ y, ∫⁻ s, H y s ∂((poissonMeasure ρ).prod IP) =
      ∑' m, ENNReal.ofReal (Real.exp (-ρ) * (ρ:ℝ) ^ m / (m ! : ℝ)) * ∫⁻ x, H y (m, x) ∂IP := by
    intro y
    have hy : Measurable (fun s : ℕ × (ℕ → ℝ × ℝ) => H y s) :=
      hH.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_prod _ hy.aemeasurable, lintegral_poisson]
  have hLHS : ∫⁻ s, ∑ i ∈ Finset.range s.1, H (s.2 i) (delPt i s) ∂((poissonMeasure ρ).prod IP) =
      ∑' n, ENNReal.ofReal (Real.exp (-ρ) * (ρ:ℝ) ^ n / (n ! : ℝ)) *
        ∫⁻ x, ∑ i ∈ Finset.range n, H (x i) (delPt i (n, x)) ∂IP := by
    rw [lintegral_prod _ hmeasL.aemeasurable, lintegral_poisson]
  rw [hside, hLHS, hρv, tsum_eq_zero_add' ENNReal.summable, hfib0, mul_zero, zero_add]
  simp_rw [hfib, hR]
  have hm : ∀ m : ℕ, AEMeasurable (fun y => ENNReal.ofReal (Real.exp (-ρ) * (ρ:ℝ) ^ m / (m ! : ℝ)) *
      ∫⁻ x, H y (m, x) ∂IP) Q := fun m =>
    (((hH.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))).lintegral_prod_right'
      (ν := IP)).const_mul _).aemeasurable
  rw [lintegral_tsum hm, ← ENNReal.tsum_mul_left]
  refine tsum_congr (fun m => ?_)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, poisson_succ_weight, mul_assoc]

end MeckePart



/-! ### Deletion invariance and side-wise Mecke -/

lemma sum_range_skip (f : ℕ → ℕ) (m k : ℕ) (hk : k < m + 1) :
    ∑ j ∈ Finset.range (m + 1), f j = f k + ∑ j ∈ Finset.range m, f (skipIdx k j) := by
  rw [← Fin.sum_univ_eq_sum_range f (m + 1), Fin.sum_univ_succAbove _ (⟨k, hk⟩ : Fin (m + 1)),
    ← Fin.sum_univ_eq_sum_range (fun j => f (skipIdx k j)) m]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have := succAbove_val m k hk j.1 j.2
  simp only [Fin.eta] at this
  rw [this]

lemma rk_local (c : ℝ → Prop) [DecidablePred c] (n : ℕ) (x x' : ℕ → ℝ × ℝ)
    (h : ∀ k < n, x k = x' k) (t : ℝ) : rk c (n, x) t = rk c (n, x') t := by
  unfold rk
  congr 1
  exact Finset.filter_congr (fun k hk => by simp only; rw [h k (Finset.mem_range.1 hk)])

lemma rk_delPt (c : ℝ → Prop) [DecidablePred c] (s : ℕ × (ℕ → ℝ × ℝ)) (k : ℕ) (hk : k < s.1)
    (t : ℝ) (hnot : ¬ (c (s.2 k).2 ∧ (s.2 k).1 < t)) : rk c (delPt k s) t = rk c s t := by
  obtain ⟨n, x⟩ := s
  simp only at hk hnot
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold rk delPt
  simp only [Nat.add_sub_cancel]
  rw [Finset.card_filter, Finset.card_filter,
    sum_range_skip (fun j => if c (x j).2 ∧ (x j).1 < t then 1 else 0) m k hk]
  have hfk : (if c (x k).2 ∧ (x k).1 < t then 1 else 0) = 0 := if_neg hnot
  simp only [hfk, zero_add]

lemma rk_delPt_self (c : ℝ → Prop) [DecidablePred c] (s : ℕ × (ℕ → ℝ × ℝ)) (k : ℕ)
    (hk : k < s.1) : rk c (delPt k s) (s.2 k).1 = rk c s (s.2 k).1 :=
  rk_delPt c s k hk _ (fun h => lt_irrefl _ h.2)

section Inv
variable (E : Environment) (lamD lamS T : ℝ)

lemma Md_delPt (ω : Ω) (k : ℕ) (hk : k < ω.1.1) :
    Md E lamD lamS T (delPt k ω.1, ω.2) (ω.1.2 k).1 = Md E lamD lamS T ω (ω.1.2 k).1 := by
  unfold Md
  rw [rank_B_eq, rank_B_eq]
  simp only
  rw [rk_delPt_self _ ω.1 k hk]
  rfl

lemma Wd_delPt (ω : Ω) (k : ℕ) (hk : k < ω.1.1) :
    Wd E lamD lamS T (delPt k ω.1, ω.2) (ω.1.2 k).1 = Wd E lamD lamS T ω (ω.1.2 k).1 := by
  rw [Wd_eq, Wd_eq, rank_B_eq, rank_B_eq]
  simp only
  rw [rk_delPt_self _ ω.1 k hk]
  simp only [WdL]

lemma Iminus_delPtB (ω : Ω) (k : ℕ) (hk : k < ω.1.1) :
    (Iminus E lamD lamS T (delPt k ω.1, ω.2) (ω.1.2 k).1 ≤ 0) ↔
      (Iminus E lamD lamS T ω (ω.1.2 k).1 ≤ 0) := by
  rw [Iminus_le_iff, Iminus_le_iff, rank_B_eq, rank_B_eq, rank_S_eq, rank_S_eq]
  simp only
  rw [rk_delPt_self _ ω.1 k hk]

lemma Ms_delPt (ω : Ω) (k : ℕ) (hk : k < ω.2.1) :
    Ms E lamD lamS T (ω.1, delPt k ω.2) (ω.2.2 k).1 = Ms E lamD lamS T ω (ω.2.2 k).1 := by
  unfold Ms
  rw [rank_S_eq, rank_S_eq]
  simp only
  rw [rk_delPt_self _ ω.2 k hk]
  rfl

lemma Ws_delPt (ω : Ω) (k : ℕ) (hk : k < ω.2.1) :
    Ws E lamD lamS T (ω.1, delPt k ω.2) (ω.2.2 k).1 = Ws E lamD lamS T ω (ω.2.2 k).1 := by
  rw [Ws_eq, Ws_eq, rank_S_eq, rank_S_eq]
  simp only
  rw [rk_delPt_self _ ω.2 k hk]
  simp only [WsL]

lemma Md_local (n : ℕ) (x x' : ℕ → ℝ × ℝ) (ω2 : ℕ × (ℕ → ℝ × ℝ)) (h : ∀ k < n, x k = x' k)
    (t : ℝ) : Md E lamD lamS T ((n, x), ω2) t = Md E lamD lamS T ((n, x'), ω2) t := by
  unfold Md
  rw [rank_B_eq, rank_B_eq]
  simp only
  rw [rk_local _ n x x' h]
  rfl

lemma Wd_local (n : ℕ) (x x' : ℕ → ℝ × ℝ) (ω2 : ℕ × (ℕ → ℝ × ℝ)) (h : ∀ k < n, x k = x' k)
    (t : ℝ) : Wd E lamD lamS T ((n, x), ω2) t = Wd E lamD lamS T ((n, x'), ω2) t := by
  rw [Wd_eq, Wd_eq, rank_B_eq, rank_B_eq]
  simp only
  rw [rk_local _ n x x' h]
  simp only [WdL]

lemma Iminus_localB (n : ℕ) (x x' : ℕ → ℝ × ℝ) (ω2 : ℕ × (ℕ → ℝ × ℝ))
    (h : ∀ k < n, x k = x' k) (t : ℝ) :
    (Iminus E lamD lamS T ((n, x), ω2) t ≤ 0) ↔ (Iminus E lamD lamS T ((n, x'), ω2) t ≤ 0) := by
  rw [Iminus_le_iff, Iminus_le_iff, rank_B_eq, rank_B_eq, rank_S_eq, rank_S_eq]
  simp only
  rw [rk_local _ n x x' h]

lemma Ms_local (m : ℕ) (y y' : ℕ → ℝ × ℝ) (ω1 : ℕ × (ℕ → ℝ × ℝ)) (h : ∀ k < m, y k = y' k)
    (t : ℝ) : Ms E lamD lamS T (ω1, (m, y)) t = Ms E lamD lamS T (ω1, (m, y')) t := by
  unfold Ms
  rw [rank_S_eq, rank_S_eq]
  simp only
  rw [rk_local _ m y y' h]
  rfl

lemma Ws_local (m : ℕ) (y y' : ℕ → ℝ × ℝ) (ω1 : ℕ × (ℕ → ℝ × ℝ)) (h : ∀ k < m, y k = y' k)
    (t : ℝ) : Ws E lamD lamS T (ω1, (m, y)) t = Ws E lamD lamS T (ω1, (m, y')) t := by
  rw [Ws_eq, Ws_eq, rank_S_eq, rank_S_eq]
  simp only
  rw [rk_local _ m y y' h]
  simp only [WsL]

end Inv


section SideMecke
open scoped ENNReal

/-- Buyer-side Mecke integrand with the seller configuration as a parameter. -/
noncomputable def HB (c : Set ℝ) (G : Ω → ℝ → ℝ≥0∞) (ω2 : ℕ × (ℕ → ℝ × ℝ)) (y : ℝ × ℝ)
    (s : ℕ × (ℕ → ℝ × ℝ)) : ℝ≥0∞ :=
  c.indicator (fun _ => G (s, ω2) y.1) y.2

lemma HB_meas3 (c : Set ℝ) (hc : MeasurableSet c) (G : Ω → ℝ → ℝ≥0∞)
    (hG : Measurable (fun z : Ω × ℝ => G z.1 z.2)) :
    Measurable (fun p : ((ℝ × ℝ) × (ℕ × (ℕ → ℝ × ℝ))) × (ℕ × (ℕ → ℝ × ℝ)) =>
      HB c G p.1.2 p.1.1 p.2) := by
  unfold HB
  have h1 : Measurable (fun p : ((ℝ × ℝ) × (ℕ × (ℕ → ℝ × ℝ))) × (ℕ × (ℕ → ℝ × ℝ)) =>
      G (p.2, p.1.2) p.1.1.1) := hG.comp
    (show Measurable (fun p : ((ℝ × ℝ) × (ℕ × (ℕ → ℝ × ℝ))) × (ℕ × (ℕ → ℝ × ℝ)) =>
      ((p.2, p.1.2), p.1.1.1)) by fun_prop)
  have e : (fun p : ((ℝ × ℝ) × (ℕ × (ℕ → ℝ × ℝ))) × (ℕ × (ℕ → ℝ × ℝ)) =>
      c.indicator (fun _ => G (p.2, p.1.2) p.1.1.1) p.1.1.2) =
      ((fun p : ((ℝ × ℝ) × (ℕ × (ℕ → ℝ × ℝ))) × (ℕ × (ℕ → ℝ × ℝ)) => p.1.1.2) ⁻¹' c).indicator
        (fun p => G (p.2, p.1.2) p.1.1.1) := by
    funext p; rfl
  rw [e]
  exact h1.indicator ((by fun_prop : Measurable (fun p : ((ℝ × ℝ) × (ℕ × (ℕ → ℝ × ℝ))) ×
    (ℕ × (ℕ → ℝ × ℝ)) => p.1.1.2)) hc)

/-- Mecke formula on the buyer side of `P`, for functionals that see the other buyers only
through quantities invariant under deleting the tagged buyer. -/
theorem mecke_buyer (E : Environment) (lamD lamS T : ℝ) (Q2 : Measure (ℕ × (ℕ → ℝ × ℝ)))
    [SFinite Q2] (hPdef : P E lamD lamS T = (sideLaw lamD T (buyerMark E T)).prod Q2)
    [IsProbabilityMeasure (buyerMark E T)]
    (G : Ω → ℝ → ℝ≥0∞) (hG : Measurable (fun z : Ω × ℝ => G z.1 z.2))
    (hloc : ∀ n (x x' : ℕ → ℝ × ℝ) ω2 t, (∀ k < n, x k = x' k) →
      G ((n, x), ω2) t = G ((n, x'), ω2) t)
    (hinv : ∀ (ω : Ω) k, k < ω.1.1 → G (delPt k ω.1, ω.2) (ω.1.2 k).1 = G ω (ω.1.2 k).1)
    (c : Set ℝ) (hc : MeasurableSet c) :
    ∫⁻ ω, ∑ k ∈ Finset.range ω.1.1, c.indicator (fun _ => G ω (ω.1.2 k).1) (ω.1.2 k).2
      ∂P E lamD lamS T =
      ENNReal.ofReal (max (lamD * T) 0) *
        ∫⁻ y, c.indicator (fun _ => ∫⁻ ω, G ω y.1 ∂P E lamD lamS T) y.2 ∂(buyerMark E T) := by
  haveI : SFinite (sideLaw lamD T (buyerMark E T)) := by unfold sideLaw; infer_instance
  have hHm : ∀ ω2, Measurable (Function.uncurry (HB c G ω2)) := by
    intro ω2
    exact (HB_meas3 c hc G hG).comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  have hHloc : ∀ ω2, IsLocal (HB c G ω2) := by
    intro ω2 y n x x' h
    unfold HB
    rw [hloc n x x' ω2 y.1 h]
  have hk : ∀ k, Measurable (fun z : Ω => c.indicator (fun _ => G z (z.1.2 k).1) (z.1.2 k).2) := by
    intro k
    have h1 : Measurable (fun z : Ω => G z (z.1.2 k).1) :=
      hG.comp (measurable_id.prodMk (by fun_prop))
    have e : (fun z : Ω => c.indicator (fun _ => G z (z.1.2 k).1) (z.1.2 k).2) =
        ((fun z : Ω => (z.1.2 k).2) ⁻¹' c).indicator (fun z => G z (z.1.2 k).1) := by
      funext z; rfl
    rw [e]
    exact h1.indicator ((by fun_prop : Measurable (fun z : Ω => (z.1.2 k).2)) hc)
  have hjoint : Measurable (fun z : Ω => ∑ k ∈ Finset.range z.1.1,
      c.indicator (fun _ => G z (z.1.2 k).1) (z.1.2 k).2) := by
    have : Measurable (fun p : ℕ × Ω => ∑ k ∈ Finset.range p.1,
        c.indicator (fun _ => G p.2 (p.2.1.2 k).1) (p.2.1.2 k).2) :=
      measurable_from_prod_countable_right (fun n => by
        show Measurable fun z : Ω => ∑ k ∈ Finset.range n,
          c.indicator (fun _ => G z (z.1.2 k).1) (z.1.2 k).2
        exact Finset.measurable_sum _ (fun k _ => hk k))
    exact this.comp ((by fun_prop : Measurable (fun z : Ω => z.1.1)).prodMk measurable_id)
  have step : ∀ ω2, ∫⁻ s, ∑ k ∈ Finset.range s.1,
      c.indicator (fun _ => G (s, ω2) (s.2 k).1) (s.2 k).2 ∂(sideLaw lamD T (buyerMark E T)) =
      ENNReal.ofReal (max (lamD * T) 0) *
        ∫⁻ y, ∫⁻ s, HB c G ω2 y s ∂(sideLaw lamD T (buyerMark E T)) ∂(buyerMark E T) := by
    intro ω2
    rw [← mecke lamD T (buyerMark E T) (HB c G ω2) (hHm ω2) (hHloc ω2)]
    refine lintegral_congr (fun s => Finset.sum_congr rfl (fun k hk' => ?_))
    unfold HB
    have := hinv (s, ω2) k (Finset.mem_range.1 hk')
    try simp only at this
    rw [this]
  have hjoint' : AEMeasurable (fun z : Ω => ∑ k ∈ Finset.range z.1.1,
      c.indicator (fun _ => G z (z.1.2 k).1) (z.1.2 k).2)
      ((sideLaw lamD T (buyerMark E T)).prod Q2) := hjoint.aemeasurable
  rw [hPdef, lintegral_prod_symm _ hjoint']
  simp only []
  simp_rw [step]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  have hsw3 : Measurable (fun p : ((ℕ × (ℕ → ℝ × ℝ)) × (ℝ × ℝ)) × (ℕ × (ℕ → ℝ × ℝ)) =>
      HB c G p.1.1 p.1.2 p.2) :=
    (HB_meas3 c hc G hG).comp (show Measurable (fun p : ((ℕ × (ℕ → ℝ × ℝ)) × (ℝ × ℝ)) ×
      (ℕ × (ℕ → ℝ × ℝ)) => ((p.1.2, p.1.1), p.2)) by fun_prop)
  have hsw : AEMeasurable (Function.uncurry (fun (ω2 : ℕ × (ℕ → ℝ × ℝ)) (y : ℝ × ℝ) =>
      ∫⁻ s, HB c G ω2 y s ∂(sideLaw lamD T (buyerMark E T)))) (Q2.prod (buyerMark E T)) :=
    (hsw3.lintegral_prod_right' (ν := sideLaw lamD T (buyerMark E T))).aemeasurable
  rw [lintegral_lintegral_swap hsw]
  refine lintegral_congr (fun y => ?_)
  unfold HB
  by_cases hy : y.2 ∈ c
  · simp only [Set.indicator_of_mem hy]
    exact (lintegral_prod_symm (f := fun ω : Ω => G ω y.1)
      (hG.comp (measurable_id.prodMk measurable_const)).aemeasurable).symm
  · simp only [Set.indicator_of_notMem hy, lintegral_zero]

end SideMecke


/-! ### C4a final: seller Mecke, chains, assembly -/

section SellerMecke
open scoped ENNReal

/-- Seller-side Mecke integrand with the buyer configuration as a parameter. -/
noncomputable def HS (c : Set ℝ) (G : Ω → ℝ → ℝ≥0∞) (ω1 : ℕ × (ℕ → ℝ × ℝ)) (y : ℝ × ℝ)
    (s : ℕ × (ℕ → ℝ × ℝ)) : ℝ≥0∞ :=
  c.indicator (fun _ => G (ω1, s) y.1) y.2

lemma HS_meas3 (c : Set ℝ) (hc : MeasurableSet c) (G : Ω → ℝ → ℝ≥0∞)
    (hG : Measurable (fun z : Ω × ℝ => G z.1 z.2)) :
    Measurable (fun p : ((ℝ × ℝ) × (ℕ × (ℕ → ℝ × ℝ))) × (ℕ × (ℕ → ℝ × ℝ)) =>
      HS c G p.1.2 p.1.1 p.2) := by
  unfold HS
  have h1 : Measurable (fun p : ((ℝ × ℝ) × (ℕ × (ℕ → ℝ × ℝ))) × (ℕ × (ℕ → ℝ × ℝ)) =>
      G (p.1.2, p.2) p.1.1.1) := hG.comp
    (show Measurable (fun p : ((ℝ × ℝ) × (ℕ × (ℕ → ℝ × ℝ))) × (ℕ × (ℕ → ℝ × ℝ)) =>
      ((p.1.2, p.2), p.1.1.1)) by fun_prop)
  have e : (fun p : ((ℝ × ℝ) × (ℕ × (ℕ → ℝ × ℝ))) × (ℕ × (ℕ → ℝ × ℝ)) =>
      c.indicator (fun _ => G (p.1.2, p.2) p.1.1.1) p.1.1.2) =
      ((fun p : ((ℝ × ℝ) × (ℕ × (ℕ → ℝ × ℝ))) × (ℕ × (ℕ → ℝ × ℝ)) => p.1.1.2) ⁻¹' c).indicator
        (fun p => G (p.1.2, p.2) p.1.1.1) := by
    funext p; rfl
  rw [e]
  exact h1.indicator ((by fun_prop : Measurable (fun p : ((ℝ × ℝ) × (ℕ × (ℕ → ℝ × ℝ))) ×
    (ℕ × (ℕ → ℝ × ℝ)) => p.1.1.2)) hc)

/-- Mecke formula on the seller side of `P`. -/
theorem mecke_seller (E : Environment) (lamD lamS T : ℝ) (Q1 : Measure (ℕ × (ℕ → ℝ × ℝ)))
    [SFinite Q1] (hPdef : P E lamD lamS T = Q1.prod (sideLaw lamS T (sellerMark E T)))
    [IsProbabilityMeasure (sellerMark E T)]
    (G : Ω → ℝ → ℝ≥0∞) (hG : Measurable (fun z : Ω × ℝ => G z.1 z.2))
    (hloc : ∀ m (y y' : ℕ → ℝ × ℝ) ω1 t, (∀ k < m, y k = y' k) →
      G (ω1, (m, y)) t = G (ω1, (m, y')) t)
    (hinv : ∀ (ω : Ω) k, k < ω.2.1 → G (ω.1, delPt k ω.2) (ω.2.2 k).1 = G ω (ω.2.2 k).1)
    (c : Set ℝ) (hc : MeasurableSet c) :
    ∫⁻ ω, ∑ k ∈ Finset.range ω.2.1, c.indicator (fun _ => G ω (ω.2.2 k).1) (ω.2.2 k).2
      ∂P E lamD lamS T =
      ENNReal.ofReal (max (lamS * T) 0) *
        ∫⁻ y, c.indicator (fun _ => ∫⁻ ω, G ω y.1 ∂P E lamD lamS T) y.2 ∂(sellerMark E T) := by
  haveI : SFinite (sideLaw lamS T (sellerMark E T)) := by unfold sideLaw; infer_instance
  have hHm : ∀ ω1, Measurable (Function.uncurry (HS c G ω1)) := by
    intro ω1
    exact (HS_meas3 c hc G hG).comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  have hHloc : ∀ ω1, IsLocal (HS c G ω1) := by
    intro ω1 y n x x' h
    unfold HS
    rw [hloc n x x' ω1 y.1 h]
  have hk : ∀ k, Measurable (fun z : Ω => c.indicator (fun _ => G z (z.2.2 k).1) (z.2.2 k).2) := by
    intro k
    have h1 : Measurable (fun z : Ω => G z (z.2.2 k).1) :=
      hG.comp (measurable_id.prodMk (by fun_prop))
    have e : (fun z : Ω => c.indicator (fun _ => G z (z.2.2 k).1) (z.2.2 k).2) =
        ((fun z : Ω => (z.2.2 k).2) ⁻¹' c).indicator (fun z => G z (z.2.2 k).1) := by
      funext z; rfl
    rw [e]
    exact h1.indicator ((by fun_prop : Measurable (fun z : Ω => (z.2.2 k).2)) hc)
  have hjoint : Measurable (fun z : Ω => ∑ k ∈ Finset.range z.2.1,
      c.indicator (fun _ => G z (z.2.2 k).1) (z.2.2 k).2) := by
    have : Measurable (fun p : ℕ × Ω => ∑ k ∈ Finset.range p.1,
        c.indicator (fun _ => G p.2 (p.2.2.2 k).1) (p.2.2.2 k).2) :=
      measurable_from_prod_countable_right (fun n => by
        show Measurable fun z : Ω => ∑ k ∈ Finset.range n,
          c.indicator (fun _ => G z (z.2.2 k).1) (z.2.2 k).2
        exact Finset.measurable_sum _ (fun k _ => hk k))
    exact this.comp ((by fun_prop : Measurable (fun z : Ω => z.2.1)).prodMk measurable_id)
  have step : ∀ ω1, ∫⁻ s, ∑ k ∈ Finset.range s.1,
      c.indicator (fun _ => G (ω1, s) (s.2 k).1) (s.2 k).2 ∂(sideLaw lamS T (sellerMark E T)) =
      ENNReal.ofReal (max (lamS * T) 0) *
        ∫⁻ y, ∫⁻ s, HS c G ω1 y s ∂(sideLaw lamS T (sellerMark E T)) ∂(sellerMark E T) := by
    intro ω1
    rw [← mecke lamS T (sellerMark E T) (HS c G ω1) (hHm ω1) (hHloc ω1)]
    refine lintegral_congr (fun s => Finset.sum_congr rfl (fun k hk' => ?_))
    unfold HS
    have := hinv (ω1, s) k (Finset.mem_range.1 hk')
    try simp only at this
    rw [this]
  have hjoint' : AEMeasurable (fun z : Ω => ∑ k ∈ Finset.range z.2.1,
      c.indicator (fun _ => G z (z.2.2 k).1) (z.2.2 k).2)
      (Q1.prod (sideLaw lamS T (sellerMark E T))) := hjoint.aemeasurable
  rw [hPdef, lintegral_prod _ hjoint']
  simp only []
  simp_rw [step]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  have hsw3 : Measurable (fun p : ((ℕ × (ℕ → ℝ × ℝ)) × (ℝ × ℝ)) × (ℕ × (ℕ → ℝ × ℝ)) =>
      HS c G p.1.1 p.1.2 p.2) :=
    (HS_meas3 c hc G hG).comp (show Measurable (fun p : ((ℕ × (ℕ → ℝ × ℝ)) × (ℝ × ℝ)) ×
      (ℕ × (ℕ → ℝ × ℝ)) => ((p.1.2, p.1.1), p.2)) by fun_prop)
  have hsw : AEMeasurable (Function.uncurry (fun (ω1 : ℕ × (ℕ → ℝ × ℝ)) (y : ℝ × ℝ) =>
      ∫⁻ s, HS c G ω1 y s ∂(sideLaw lamS T (sellerMark E T)))) (Q1.prod (sellerMark E T)) :=
    (hsw3.lintegral_prod_right' (ν := sideLaw lamS T (sellerMark E T))).aemeasurable
  rw [lintegral_lintegral_swap hsw]
  refine lintegral_congr (fun y => ?_)
  unfold HS
  by_cases hy : y.2 ∈ c
  · simp only [Set.indicator_of_mem hy]
    exact (lintegral_prod (f := fun ω : Ω => G ω y.1)
      (hG.comp (measurable_id.prodMk measurable_const)).aemeasurable).symm
  · simp only [Set.indicator_of_notMem hy, lintegral_zero]

end SellerMecke

section C4aFinal
open scoped ENNReal

lemma P_def (E : Environment) (lamD lamS T : ℝ) : P E lamD lamS T =
    (sideLaw lamD T (buyerMark E T)).prod (sideLaw lamS T (sellerMark E T)) := rfl

lemma marks_prob (E : Environment) (T : ℝ) (hT : 0 < T) :
    IsProbabilityMeasure (buyerMark E T) ∧ IsProbabilityMeasure (sellerMark E T) := by
  have := timeLaw_prob T hT
  have := valLaw_prob E
  have := costLaw_prob E
  exact ⟨by unfold buyerMark; infer_instance, by unfold sellerMark; infer_instance⟩

lemma P_prob (E : Environment) (lamD lamS T : ℝ) (hT : 0 < T) :
    IsProbabilityMeasure (P E lamD lamS T) := by
  obtain ⟨h1, h2⟩ := marks_prob E T hT
  have := sideLaw_prob lamD T (buyerMark E T)
  have := sideLaw_prob lamS T (sellerMark E T)
  rw [P_def]; infer_instance

lemma P_sfinite (E : Environment) (lamD lamS T : ℝ) (hT : 0 < T) : SFinite (P E lamD lamS T) := by
  haveI := P_prob E lamD lamS T hT; infer_instance

lemma ind_nonneg' (p : Prop) [Decidable p] : 0 ≤ (if p then (1:ℝ) else 0) := by
  split_ifs <;> norm_num

lemma ind_le_one' (p : Prop) [Decidable p] : (if p then (1:ℝ) else 0) ≤ 1 := by
  split_ifs <;> norm_num

lemma Md_nonneg (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (t : ℝ) :
    0 ≤ Md E lamD lamS T ω t := by
  unfold Md; split_ifs <;> norm_num

lemma Md_le_one (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (t : ℝ) :
    Md E lamD lamS T ω t ≤ 1 := by
  unfold Md; split_ifs <;> norm_num

lemma Ms_nonneg (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (t : ℝ) :
    0 ≤ Ms E lamD lamS T ω t := by
  unfold Ms; split_ifs <;> norm_num

lemma Ms_le_one (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (t : ℝ) :
    Ms E lamD lamS T ω t ≤ 1 := by
  unfold Ms; split_ifs <;> norm_num

lemma Wd_nonneg (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (t : ℝ) (ht : t ≤ T) :
    0 ≤ Wd E lamD lamS T ω t := by
  unfold Wd
  split
  · exact sub_nonneg.2 (le_max_left _ _)
  · linarith

lemma Ws_nonneg (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (t : ℝ) (ht : t ≤ T) :
    0 ≤ Ws E lamD lamS T ω t := by
  unfold Ws
  split
  · exact sub_nonneg.2 (le_max_left _ _)
  · linarith

lemma compD_nonneg (E : Environment) (lamD lamS T : ℝ) (t : ℝ) (ht : t ≤ T) :
    0 ≤ compD E lamD lamS T t := by
  unfold compD
  exact div_nonneg
    (integral_nonneg (fun ω => mul_nonneg (Wd_nonneg E lamD lamS T ω t ht) (ind_nonneg' _)))
    (integral_nonneg (fun ω => mul_nonneg (Md_nonneg E lamD lamS T ω t) (ind_nonneg' _)))

lemma compS_nonneg (E : Environment) (lamD lamS T : ℝ) (t : ℝ) (ht : t ≤ T) :
    0 ≤ compS E lamD lamS T t := by
  unfold compS
  exact div_nonneg (integral_nonneg (fun ω => Ws_nonneg E lamD lamS T ω t ht))
    (integral_nonneg (fun ω => Ms_nonneg E lamD lamS T ω t))

lemma ofReal_int_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hi : Integrable f μ
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf0)]
  · rw [integral_undef hi]; simp

/-- The ratio identity behind `compD`/`compS`: `g · (∫w / ∫g)` integrates to at most `∫ w`. -/
lemma key_gen {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (g w w' : α → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    (hw0 : ∀ x, 0 ≤ w x) (hww : ∀ x, w x ≤ w' x) :
    ∫⁻ x, ENNReal.ofReal (g x * ((∫ y, w y ∂μ) / (∫ y, g y ∂μ))) ∂μ ≤
      ∫⁻ x, ENNReal.ofReal (w' x) ∂μ := by
  have gi : Integrable g μ := (integrable_const (1:ℝ)).mono' hg.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by rw [Real.norm_of_nonneg (hg0 x)]; exact hg1 x))
  have hc : 0 ≤ (∫ y, w y ∂μ) / (∫ y, g y ∂μ) :=
    div_nonneg (integral_nonneg hw0) (integral_nonneg hg0)
  rw [← ofReal_integral_eq_lintegral_ofReal (gi.mul_const _)
    (Filter.Eventually.of_forall (fun x => mul_nonneg (hg0 x) hc)), integral_mul_const]
  calc ENNReal.ofReal ((∫ y, g y ∂μ) * ((∫ y, w y ∂μ) / (∫ y, g y ∂μ)))
      ≤ ENNReal.ofReal (∫ y, w y ∂μ) := by
        apply ENNReal.ofReal_le_ofReal
        by_cases hD : (∫ y, g y ∂μ) = 0
        · rw [hD, zero_mul]; exact integral_nonneg hw0
        · have : (∫ y, g y ∂μ) * ((∫ y, w y ∂μ) / (∫ y, g y ∂μ)) = ∫ y, w y ∂μ := by
            field_simp
          rw [this]
    _ ≤ ∫⁻ x, ENNReal.ofReal (w x) ∂μ := ofReal_int_le μ w hw0
    _ ≤ ∫⁻ x, ENNReal.ofReal (w' x) ∂μ :=
        lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hww x))

lemma key_buyer (E : Environment) (lamD lamS T : ℝ) (hT : 0 < T) (t : ℝ) (ht : t ≤ T) :
    ∫⁻ ω, ENNReal.ofReal (Md E lamD lamS T ω t *
      (if Iminus E lamD lamS T ω t ≤ 0 then (1:ℝ) else 0) * compD E lamD lamS T t)
        ∂P E lamD lamS T ≤
    ∫⁻ ω, ENNReal.ofReal (Wd E lamD lamS T ω t) ∂P E lamD lamS T := by
  haveI := P_prob E lamD lamS T hT
  have h2 : Measurable (fun z : Ω × ℝ => Md E lamD lamS T z.1 z.2 *
      (if Iminus E lamD lamS T z.1 z.2 ≤ 0 then (1 : ℝ) else 0)) :=
    (Md_meas E lamD lamS T).mul (Measurable.ite (ind_meas E lamD lamS T) measurable_const
      measurable_const)
  have := key_gen (P E lamD lamS T)
    (fun ω => Md E lamD lamS T ω t * (if Iminus E lamD lamS T ω t ≤ 0 then (1:ℝ) else 0))
    (fun ω => Wd E lamD lamS T ω t * (if Iminus E lamD lamS T ω t ≤ 0 then (1:ℝ) else 0))
    (fun ω => Wd E lamD lamS T ω t)
    (h2.comp (measurable_id.prodMk measurable_const))
    (fun ω => mul_nonneg (Md_nonneg E lamD lamS T ω t) (ind_nonneg' _))
    (fun ω => mul_le_one₀ (Md_le_one E lamD lamS T ω t) (ind_nonneg' _) (ind_le_one' _))
    (fun ω => mul_nonneg (Wd_nonneg E lamD lamS T ω t ht) (ind_nonneg' _))
    (fun ω => mul_le_of_le_one_right (Wd_nonneg E lamD lamS T ω t ht) (ind_le_one' _))
  unfold compD
  exact this

lemma key_seller (E : Environment) (lamD lamS T : ℝ) (hT : 0 < T) (t : ℝ) (ht : t ≤ T) :
    ∫⁻ ω, ENNReal.ofReal (Ms E lamD lamS T ω t * compS E lamD lamS T t) ∂P E lamD lamS T ≤
    ∫⁻ ω, ENNReal.ofReal (Ws E lamD lamS T ω t) ∂P E lamD lamS T := by
  haveI := P_prob E lamD lamS T hT
  have := key_gen (P E lamD lamS T)
    (fun ω => Ms E lamD lamS T ω t) (fun ω => Ws E lamD lamS T ω t) (fun ω => Ws E lamD lamS T ω t)
    ((Ms_meas E lamD lamS T).comp (measurable_id.prodMk measurable_const))
    (fun ω => Ms_nonneg E lamD lamS T ω t) (fun ω => Ms_le_one E lamD lamS T ω t)
    (fun ω => Ws_nonneg E lamD lamS T ω t ht) (fun ω => le_rfl)
  unfold compS
  exact this

lemma sum_reqB_ind (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (H : ℝ → ℝ≥0∞) :
    ∑ i ∈ reqB E lamD lamS T ω, H (buyerTime ω i) =
      ∑ k ∈ Finset.range ω.1.1,
        (Set.Ici (pStar E lamD lamS T)).indicator (fun _ => H (ω.1.2 k).1) (ω.1.2 k).2 := by
  unfold reqB
  rw [Finset.sum_filter, ← Fin.sum_univ_eq_sum_range (fun k =>
    (Set.Ici (pStar E lamD lamS T)).indicator (fun _ => H (ω.1.2 k).1) (ω.1.2 k).2)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Set.indicator_apply, Set.mem_Ici, buyerValue, buyerTime]
  by_cases hc : pStar E lamD lamS T ≤ (ω.1.2 i).2 <;> simp [hc]

lemma sum_reqS_ind (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (H : ℝ → ℝ≥0∞) :
    ∑ j ∈ reqS E lamD lamS T ω, H (sellerTime ω j) =
      ∑ k ∈ Finset.range ω.2.1,
        (Set.Iic (wStar E lamD lamS T)).indicator (fun _ => H (ω.2.2 k).1) (ω.2.2 k).2 := by
  unfold reqS
  rw [Finset.sum_filter, ← Fin.sum_univ_eq_sum_range (fun k =>
    (Set.Iic (wStar E lamD lamS T)).indicator (fun _ => H (ω.2.2 k).1) (ω.2.2 k).2)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Set.indicator_apply, Set.mem_Iic, sellerCost, sellerTime]
  by_cases hc : (ω.2.2 i).2 ≤ wStar E lamD lamS T <;> simp [hc]

/-- All arrival times lie in `[0,T]` almost surely. -/
lemma good_ae (E : Environment) (lamD lamS T : ℝ) (hT : 0 < T) :
    ∀ᵐ ω ∂P E lamD lamS T, (∀ k, (ω.1.2 k).1 ∈ Set.Icc 0 T) ∧ (∀ k, (ω.2.2 k).1 ∈ Set.Icc 0 T) := by
  obtain ⟨hbm, hsm⟩ := marks_prob E T hT
  have := timeLaw_prob T hT
  have := valLaw_prob E
  have := costLaw_prob E
  have hA := sideLaw_prob lamD T (buyerMark E T)
  have hB := sideLaw_prob lamS T (sellerMark E T)
  have htime : ∀ᵐ x ∂(timeLaw T), x ∈ Set.Icc 0 T := by
    unfold timeLaw
    exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _
  have pf : MeasurePreserving Prod.fst (P E lamD lamS T) (sideLaw lamD T (buyerMark E T)) := by
    rw [P_def]; exact measurePreserving_fst
  have ps : MeasurePreserving Prod.snd (P E lamD lamS T) (sideLaw lamS T (sellerMark E T)) := by
    rw [P_def]; exact measurePreserving_snd
  have q2 : ∀ (r : ℝ) (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q],
      MeasurePreserving Prod.snd (sideLaw r T Q) (Measure.infinitePi (fun _ : ℕ => Q)) := by
    intro r Q _
    have h2' : ∀ ρ : NNReal, IsProbabilityMeasure (ProbabilityTheory.poissonMeasure ρ) :=
      fun ρ => inferInstance
    have h2 := h2' ⟨max (r * T) 0, le_max_right _ _⟩
    unfold sideLaw; exact measurePreserving_snd
  have bm : MeasurePreserving Prod.fst (buyerMark E T) (timeLaw T) := by
    unfold buyerMark; exact measurePreserving_fst
  have sm : MeasurePreserving Prod.fst (sellerMark E T) (timeLaw T) := by
    unfold sellerMark; exact measurePreserving_fst
  refine Filter.Eventually.and (ae_all_iff.2 (fun k => ?_)) (ae_all_iff.2 (fun k => ?_))
  · have hmp := bm.comp ((measurePreserving_eval_infinitePi (fun _ : ℕ => buyerMark E T) k).comp
      ((q2 lamD (buyerMark E T)).comp pf))
    exact hmp.quasiMeasurePreserving.ae htime
  · have hmp := sm.comp ((measurePreserving_eval_infinitePi (fun _ : ℕ => sellerMark E T) k).comp
      ((q2 lamS (sellerMark E T)).comp ps))
    exact hmp.quasiMeasurePreserving.ae htime

lemma marks_time_ae (E : Environment) (T : ℝ) (hT : 0 < T) :
    (∀ᵐ y ∂(buyerMark E T), y.1 ∈ Set.Icc 0 T) ∧ (∀ᵐ y ∂(sellerMark E T), y.1 ∈ Set.Icc 0 T) := by
  have := timeLaw_prob T hT
  have := valLaw_prob E
  have := costLaw_prob E
  have htime : ∀ᵐ x ∂(timeLaw T), x ∈ Set.Icc 0 T := by
    unfold timeLaw
    exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _
  have bm : MeasurePreserving Prod.fst (buyerMark E T) (timeLaw T) := by
    unfold buyerMark; exact measurePreserving_fst
  have sm : MeasurePreserving Prod.fst (sellerMark E T) (timeLaw T) := by
    unfold sellerMark; exact measurePreserving_fst
  exact ⟨bm.quasiMeasurePreserving.ae htime, sm.quasiMeasurePreserving.ae htime⟩

/-- Demand-side waiting charge of a buyer. -/
noncomputable def fD (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (i : Fin ω.1.1) : ℝ :=
  if Iminus E lamD lamS T ω (buyerTime ω i) ≤ 0 then compD E lamD lamS T (buyerTime ω i) else 0

noncomputable def SD (E : Environment) (lamD lamS T : ℝ) (ω : Ω) : ℝ :=
  ∑ p ∈ (greedyPairs E lamD lamS T ω).toFinset, fD E lamD lamS T ω p.2

noncomputable def SS (E : Environment) (lamD lamS T : ℝ) (ω : Ω) : ℝ :=
  ∑ p ∈ (greedyPairs E lamD lamS T ω).toFinset, compS E lamD lamS T (sellerTime ω p.1)

noncomputable def qD (E : Environment) (lamD lamS T : ℝ) (ω : Ω) : ℝ :=
  ∫ s in (0:ℝ)..T, max ((Nd E lamD lamS T ω s : ℝ) - (Ns E lamD lamS T ω s : ℝ)) 0

noncomputable def qS (E : Environment) (lamD lamS T : ℝ) (ω : Ω) : ℝ :=
  ∫ s in (0:ℝ)..T, max ((Ns E lamD lamS T ω s : ℝ) - (Nd E lamD lamS T ω s : ℝ)) 0

noncomputable def GB1 (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Md E lamD lamS T ω t *
    (if Iminus E lamD lamS T ω t ≤ 0 then (1:ℝ) else 0) * compD E lamD lamS T t)

noncomputable def GB2 (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Wd E lamD lamS T ω t)

noncomputable def GS1 (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Ms E lamD lamS T ω t * compS E lamD lamS T t)

noncomputable def GS2 (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Ws E lamD lamS T ω t)

lemma fD_nonneg (E : Environment) (lamD lamS T : ℝ) (ω : Ω)
    (hB : ∀ k, (ω.1.2 k).1 ∈ Set.Icc 0 T) (i : Fin ω.1.1) : 0 ≤ fD E lamD lamS T ω i := by
  unfold fD
  split_ifs
  · exact compD_nonneg E lamD lamS T _ (hB i).2
  · exact le_rfl

/-- Buyer chain: the expected demand-side waiting charge is at most the expected
integrated buyer queue. -/
lemma buyer_lint (E : Environment) (lamD lamS T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ENNReal.ofReal (SD E lamD lamS T ω) ∂P E lamD lamS T ≤
      ∫⁻ ω, ENNReal.ofReal (qD E lamD lamS T ω) ∂P E lamD lamS T := by
  obtain ⟨hbm, hsm⟩ := marks_prob E T hT
  haveI := hbm
  haveI : SFinite (sideLaw lamS T (sellerMark E T)) := by unfold sideLaw; infer_instance
  haveI := P_sfinite E lamD lamS T hT
  have h2 : Measurable (fun z : Ω × ℝ => Md E lamD lamS T z.1 z.2 *
      (if Iminus E lamD lamS T z.1 z.2 ≤ 0 then (1 : ℝ) else 0)) :=
    (Md_meas E lamD lamS T).mul (Measurable.ite (ind_meas E lamD lamS T) measurable_const
      measurable_const)
  have hG1 : Measurable (fun z : Ω × ℝ => GB1 E lamD lamS T z.1 z.2) :=
    ENNReal.measurable_ofReal.comp (h2.mul ((compD_meas E lamD lamS T).comp measurable_snd))
  have hG2 : Measurable (fun z : Ω × ℝ => GB2 E lamD lamS T z.1 z.2) :=
    ENNReal.measurable_ofReal.comp (Wd_meas E lamD lamS T)
  have hloc1 : ∀ n (x x' : ℕ → ℝ × ℝ) ω2 t, (∀ k < n, x k = x' k) →
      GB1 E lamD lamS T ((n, x), ω2) t = GB1 E lamD lamS T ((n, x'), ω2) t := by
    intro n x x' ω2 t h
    unfold GB1
    rw [Md_local E lamD lamS T n x x' ω2 h t]
    simp only [Iminus_localB E lamD lamS T n x x' ω2 h t]
  have hloc2 : ∀ n (x x' : ℕ → ℝ × ℝ) ω2 t, (∀ k < n, x k = x' k) →
      GB2 E lamD lamS T ((n, x), ω2) t = GB2 E lamD lamS T ((n, x'), ω2) t := by
    intro n x x' ω2 t h
    unfold GB2
    rw [Wd_local E lamD lamS T n x x' ω2 h t]
  have hinv1 : ∀ (ω : Ω) k, k < ω.1.1 →
      GB1 E lamD lamS T (delPt k ω.1, ω.2) (ω.1.2 k).1 = GB1 E lamD lamS T ω (ω.1.2 k).1 := by
    intro ω k hk
    unfold GB1
    rw [Md_delPt E lamD lamS T ω k hk]
    simp only [Iminus_delPtB E lamD lamS T ω k hk]
  have hinv2 : ∀ (ω : Ω) k, k < ω.1.1 →
      GB2 E lamD lamS T (delPt k ω.1, ω.2) (ω.1.2 k).1 = GB2 E lamD lamS T ω (ω.1.2 k).1 := by
    intro ω k hk
    unfold GB2
    rw [Wd_delPt E lamD lamS T ω k hk]
  have M1 := mecke_buyer E lamD lamS T (sideLaw lamS T (sellerMark E T)) rfl
    (GB1 E lamD lamS T) hG1 hloc1 hinv1 (Set.Ici (pStar E lamD lamS T)) measurableSet_Ici
  have M2 := mecke_buyer E lamD lamS T (sideLaw lamS T (sellerMark E T)) rfl
    (GB2 E lamD lamS T) hG2 hloc2 hinv2 (Set.Ici (pStar E lamD lamS T)) measurableSet_Ici
  have hgood := good_ae E lamD lamS T hT
  have hy := (marks_time_ae E T hT).1
  calc ∫⁻ ω, ENNReal.ofReal (SD E lamD lamS T ω) ∂P E lamD lamS T
      ≤ ∫⁻ ω, ∑ k ∈ Finset.range ω.1.1, (Set.Ici (pStar E lamD lamS T)).indicator
          (fun _ => GB1 E lamD lamS T ω (ω.1.2 k).1) (ω.1.2 k).2 ∂P E lamD lamS T := by
        refine lintegral_mono_ae (hgood.mono (fun ω hω => ?_))
        have hf := fD_nonneg E lamD lamS T ω hω.1
        rw [← sum_reqB_ind E lamD lamS T ω (GB1 E lamD lamS T ω)]
        calc ENNReal.ofReal (SD E lamD lamS T ω)
            ≤ ENNReal.ofReal (∑ i ∈ reqB E lamD lamS T ω,
                Md E lamD lamS T ω (buyerTime ω i) * fD E lamD lamS T ω i) :=
              ENNReal.ofReal_le_ofReal (pairs_buyer_le E lamD lamS T ω _ hf)
          _ = ∑ i ∈ reqB E lamD lamS T ω,
                ENNReal.ofReal (Md E lamD lamS T ω (buyerTime ω i) * fD E lamD lamS T ω i) :=
              ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (Md_nonneg _ _ _ _ _ _) (hf i))
          _ = ∑ i ∈ reqB E lamD lamS T ω, GB1 E lamD lamS T ω (buyerTime ω i) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              unfold GB1 fD
              split_ifs <;> simp
    _ = ENNReal.ofReal (max (lamD * T) 0) * ∫⁻ y, (Set.Ici (pStar E lamD lamS T)).indicator
          (fun _ => ∫⁻ ω, GB1 E lamD lamS T ω y.1 ∂P E lamD lamS T) y.2 ∂(buyerMark E T) := M1
    _ ≤ ENNReal.ofReal (max (lamD * T) 0) * ∫⁻ y, (Set.Ici (pStar E lamD lamS T)).indicator
          (fun _ => ∫⁻ ω, GB2 E lamD lamS T ω y.1 ∂P E lamD lamS T) y.2 ∂(buyerMark E T) := by
        refine mul_le_mul_of_nonneg_left (lintegral_mono_ae (hy.mono (fun y hy1 => ?_))) (by simp)
        exact Set.indicator_le_indicator (key_buyer E lamD lamS T hT y.1 hy1.2)
    _ = ∫⁻ ω, ∑ k ∈ Finset.range ω.1.1, (Set.Ici (pStar E lamD lamS T)).indicator
          (fun _ => GB2 E lamD lamS T ω (ω.1.2 k).1) (ω.1.2 k).2 ∂P E lamD lamS T := M2.symm
    _ ≤ ∫⁻ ω, ENNReal.ofReal (qD E lamD lamS T ω) ∂P E lamD lamS T := by
        refine lintegral_mono_ae (hgood.mono (fun ω hω => ?_))
        rw [← sum_reqB_ind E lamD lamS T ω (GB2 E lamD lamS T ω)]
        have hW : ∀ i ∈ reqB E lamD lamS T ω, 0 ≤ Wd E lamD lamS T ω (buyerTime ω i) :=
          fun i _ => Wd_nonneg E lamD lamS T ω _ (hω.1 i).2
        unfold GB2
        rw [← ENNReal.ofReal_sum_of_nonneg hW]
        exact ENNReal.ofReal_le_ofReal (sum_Wd_le E lamD lamS T ω hT.le (fun i => hω.1 i)
          (fun j => (hω.2 j).2))

/-- Seller chain. -/
lemma seller_lint (E : Environment) (lamD lamS T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ENNReal.ofReal (SS E lamD lamS T ω) ∂P E lamD lamS T ≤
      ∫⁻ ω, ENNReal.ofReal (qS E lamD lamS T ω) ∂P E lamD lamS T := by
  obtain ⟨hbm, hsm⟩ := marks_prob E T hT
  haveI := hsm
  haveI : SFinite (sideLaw lamD T (buyerMark E T)) := by unfold sideLaw; infer_instance
  haveI := P_sfinite E lamD lamS T hT
  have hG1 : Measurable (fun z : Ω × ℝ => GS1 E lamD lamS T z.1 z.2) :=
    ENNReal.measurable_ofReal.comp ((Ms_meas E lamD lamS T).mul
      ((compS_meas E lamD lamS T).comp measurable_snd))
  have hG2 : Measurable (fun z : Ω × ℝ => GS2 E lamD lamS T z.1 z.2) :=
    ENNReal.measurable_ofReal.comp (Ws_meas E lamD lamS T)
  have hloc1 : ∀ m (y y' : ℕ → ℝ × ℝ) ω1 t, (∀ k < m, y k = y' k) →
      GS1 E lamD lamS T (ω1, (m, y)) t = GS1 E lamD lamS T (ω1, (m, y')) t := by
    intro m y y' ω1 t h
    unfold GS1
    rw [Ms_local E lamD lamS T m y y' ω1 h t]
  have hloc2 : ∀ m (y y' : ℕ → ℝ × ℝ) ω1 t, (∀ k < m, y k = y' k) →
      GS2 E lamD lamS T (ω1, (m, y)) t = GS2 E lamD lamS T (ω1, (m, y')) t := by
    intro m y y' ω1 t h
    unfold GS2
    rw [Ws_local E lamD lamS T m y y' ω1 h t]
  have hinv1 : ∀ (ω : Ω) k, k < ω.2.1 →
      GS1 E lamD lamS T (ω.1, delPt k ω.2) (ω.2.2 k).1 = GS1 E lamD lamS T ω (ω.2.2 k).1 := by
    intro ω k hk
    unfold GS1
    rw [Ms_delPt E lamD lamS T ω k hk]
  have hinv2 : ∀ (ω : Ω) k, k < ω.2.1 →
      GS2 E lamD lamS T (ω.1, delPt k ω.2) (ω.2.2 k).1 = GS2 E lamD lamS T ω (ω.2.2 k).1 := by
    intro ω k hk
    unfold GS2
    rw [Ws_delPt E lamD lamS T ω k hk]
  have M1 := mecke_seller E lamD lamS T (sideLaw lamD T (buyerMark E T)) rfl
    (GS1 E lamD lamS T) hG1 hloc1 hinv1 (Set.Iic (wStar E lamD lamS T)) measurableSet_Iic
  have M2 := mecke_seller E lamD lamS T (sideLaw lamD T (buyerMark E T)) rfl
    (GS2 E lamD lamS T) hG2 hloc2 hinv2 (Set.Iic (wStar E lamD lamS T)) measurableSet_Iic
  have hgood := good_ae E lamD lamS T hT
  have hy := (marks_time_ae E T hT).2
  calc ∫⁻ ω, ENNReal.ofReal (SS E lamD lamS T ω) ∂P E lamD lamS T
      ≤ ∫⁻ ω, ∑ k ∈ Finset.range ω.2.1, (Set.Iic (wStar E lamD lamS T)).indicator
          (fun _ => GS1 E lamD lamS T ω (ω.2.2 k).1) (ω.2.2 k).2 ∂P E lamD lamS T := by
        refine lintegral_mono_ae (hgood.mono (fun ω hω => ?_))
        have hf : ∀ j : Fin ω.2.1, 0 ≤ compS E lamD lamS T (sellerTime ω j) :=
          fun j => compS_nonneg E lamD lamS T _ (hω.2 j).2
        rw [← sum_reqS_ind E lamD lamS T ω (GS1 E lamD lamS T ω)]
        calc ENNReal.ofReal (SS E lamD lamS T ω)
            ≤ ENNReal.ofReal (∑ j ∈ reqS E lamD lamS T ω,
                Ms E lamD lamS T ω (sellerTime ω j) * compS E lamD lamS T (sellerTime ω j)) :=
              ENNReal.ofReal_le_ofReal (pairs_seller_le E lamD lamS T ω
                (fun j => compS E lamD lamS T (sellerTime ω j)) hf)
          _ = ∑ j ∈ reqS E lamD lamS T ω, GS1 E lamD lamS T ω (sellerTime ω j) :=
              ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (Ms_nonneg _ _ _ _ _ _) (hf j))
    _ = ENNReal.ofReal (max (lamS * T) 0) * ∫⁻ y, (Set.Iic (wStar E lamD lamS T)).indicator
          (fun _ => ∫⁻ ω, GS1 E lamD lamS T ω y.1 ∂P E lamD lamS T) y.2 ∂(sellerMark E T) := M1
    _ ≤ ENNReal.ofReal (max (lamS * T) 0) * ∫⁻ y, (Set.Iic (wStar E lamD lamS T)).indicator
          (fun _ => ∫⁻ ω, GS2 E lamD lamS T ω y.1 ∂P E lamD lamS T) y.2 ∂(sellerMark E T) := by
        refine mul_le_mul_of_nonneg_left (lintegral_mono_ae (hy.mono (fun y hy1 => ?_))) (by simp)
        exact Set.indicator_le_indicator (key_seller E lamD lamS T hT y.1 hy1.2)
    _ = ∫⁻ ω, ∑ k ∈ Finset.range ω.2.1, (Set.Iic (wStar E lamD lamS T)).indicator
          (fun _ => GS2 E lamD lamS T ω (ω.2.2 k).1) (ω.2.2 k).2 ∂P E lamD lamS T := M2.symm
    _ ≤ ∫⁻ ω, ENNReal.ofReal (qS E lamD lamS T ω) ∂P E lamD lamS T := by
        refine lintegral_mono_ae (hgood.mono (fun ω hω => ?_))
        rw [← sum_reqS_ind E lamD lamS T ω (GS2 E lamD lamS T ω)]
        have hW : ∀ j ∈ reqS E lamD lamS T ω, 0 ≤ Ws E lamD lamS T ω (sellerTime ω j) :=
          fun j _ => Ws_nonneg E lamD lamS T ω _ (hω.2 j).2
        unfold GS2
        rw [← ENNReal.ofReal_sum_of_nonneg hW]
        exact ENNReal.ofReal_le_ofReal (sum_Ws_le E lamD lamS T ω hT.le (fun i => hω.2 i)
          (fun j => (hω.1 j).2))

end C4aFinal


section C4aAssembly
open scoped ENNReal

lemma cnt_univ_eq (s : ℕ × (ℕ → ℝ × ℝ)) : cnt Set.univ s = s.1 := by
  simp [cnt]

lemma Nd_le_cnt (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (t : ℝ) :
    (Nd E lamD lamS T ω t : ℝ) ≤ cnt Set.univ ω.1 := by
  rw [Nd_eq]; exact cnt_le_univ _ _

lemma Ns_le_cnt (E : Environment) (lamD lamS T : ℝ) (ω : Ω) (t : ℝ) :
    (Ns E lamD lamS T ω t : ℝ) ≤ cnt Set.univ ω.2 := by
  rw [Ns_eq]; exact cnt_le_univ _ _

lemma cnt_int (E : Environment) (lamD lamS T : ℝ) (hT : 0 < T) :
    Integrable (fun ω : Ω => cnt Set.univ ω.1) (P E lamD lamS T) ∧
    Integrable (fun ω : Ω => cnt Set.univ ω.2) (P E lamD lamS T) := by
  obtain ⟨hbm, hsm⟩ := marks_prob E T hT
  have hA := sideLaw_prob lamD T (buyerMark E T)
  have hB := sideLaw_prob lamS T (sellerMark E T)
  have pf : MeasurePreserving Prod.fst (P E lamD lamS T) (sideLaw lamD T (buyerMark E T)) := by
    rw [P_def]; exact measurePreserving_fst
  have ps : MeasurePreserving Prod.snd (P E lamD lamS T) (sideLaw lamS T (sellerMark E T)) := by
    rw [P_def]; exact measurePreserving_snd
  exact ⟨pf.integrable_comp_of_integrable
      (cnt_moments lamD T (buyerMark E T) Set.univ MeasurableSet.univ).1,
    ps.integrable_comp_of_integrable
      (cnt_moments lamS T (sellerMark E T) Set.univ MeasurableSet.univ).1⟩

lemma Nd_joint (E : Environment) (lamD lamS T : ℝ) :
    Measurable (fun z : Ω × ℝ => (Nd E lamD lamS T z.1 z.2 : ℝ)) := by
  have hSB : MeasurableSet {q : (ℝ × ℝ) × ℝ | q.1.1 ≤ q.2 ∧ pStar E lamD lamS T ≤ q.1.2} := by
    rw [Set.setOf_and]
    exact (measurableSet_le (f := fun q : (ℝ × ℝ) × ℝ => q.1.1) (g := fun q => q.2)
      (by fun_prop) (by fun_prop)).inter
      (measurableSet_le (f := fun _ : (ℝ × ℝ) × ℝ => pStar E lamD lamS T) (g := fun q => q.1.2)
        (by fun_prop) (by fun_prop))
  have eB : ∀ t : ℝ, {z : ℝ × ℝ | (z, t) ∈
      {q : (ℝ × ℝ) × ℝ | q.1.1 ≤ q.2 ∧ pStar E lamD lamS T ≤ q.1.2}} =
      Set.Iic t ×ˢ Set.Ici (pStar E lamD lamS T) := by
    intro t; ext z; simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Iic, Set.mem_Ici]
  have h1 := (cnt_param_meas _ hSB).comp
    (show Measurable (fun z : Ω × ℝ => (z.1.1, z.2)) by fun_prop)
  have e : (fun z : Ω × ℝ => (Nd E lamD lamS T z.1 z.2 : ℝ)) =
      (fun q : (ℕ × (ℕ → ℝ × ℝ)) × ℝ =>
        cnt {z | (z, q.2) ∈ {q : (ℝ × ℝ) × ℝ | q.1.1 ≤ q.2 ∧ pStar E lamD lamS T ≤ q.1.2}} q.1) ∘
      (fun z : Ω × ℝ => (z.1.1, z.2)) := by
    funext z; simp only [Function.comp]; rw [Nd_eq, eB]
  rw [e]; exact h1

lemma Ns_joint (E : Environment) (lamD lamS T : ℝ) :
    Measurable (fun z : Ω × ℝ => (Ns E lamD lamS T z.1 z.2 : ℝ)) := by
  have hSS : MeasurableSet {q : (ℝ × ℝ) × ℝ | q.1.1 ≤ q.2 ∧ q.1.2 ≤ wStar E lamD lamS T} := by
    rw [Set.setOf_and]
    exact (measurableSet_le (f := fun q : (ℝ × ℝ) × ℝ => q.1.1) (g := fun q => q.2)
      (by fun_prop) (by fun_prop)).inter
      (measurableSet_le (f := fun q : (ℝ × ℝ) × ℝ => q.1.2) (g := fun _ => wStar E lamD lamS T)
        (by fun_prop) (by fun_prop))
  have eS : ∀ t : ℝ, {z : ℝ × ℝ | (z, t) ∈
      {q : (ℝ × ℝ) × ℝ | q.1.1 ≤ q.2 ∧ q.1.2 ≤ wStar E lamD lamS T}} =
      Set.Iic t ×ˢ Set.Iic (wStar E lamD lamS T) := by
    intro t; ext z; simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Iic, Set.mem_Ici]
  have h1 := (cnt_param_meas _ hSS).comp
    (show Measurable (fun z : Ω × ℝ => (z.1.2, z.2)) by fun_prop)
  have e : (fun z : Ω × ℝ => (Ns E lamD lamS T z.1 z.2 : ℝ)) =
      (fun q : (ℕ × (ℕ → ℝ × ℝ)) × ℝ =>
        cnt {z | (z, q.2) ∈ {q : (ℝ × ℝ) × ℝ | q.1.1 ≤ q.2 ∧ q.1.2 ≤ wStar E lamD lamS T}} q.1) ∘
      (fun z : Ω × ℝ => (z.1.2, z.2)) := by
    funext z; simp only [Function.comp]; rw [Ns_eq, eS]
  rw [e]; exact h1

lemma Nd_at (E : Environment) (lamD lamS T t : ℝ) :
    Measurable (fun ω : Ω => (Nd E lamD lamS T ω t : ℝ)) := by
  have e : (fun ω : Ω => (Nd E lamD lamS T ω t : ℝ)) =
      fun ω => cnt (Set.Iic t ×ˢ Set.Ici (pStar E lamD lamS T)) ω.1 :=
    funext (fun ω => Nd_eq E lamD lamS T ω t)
  rw [e]; exact (cnt_meas _ (measurableSet_Iic.prod measurableSet_Ici)).comp measurable_fst

lemma Ns_at (E : Environment) (lamD lamS T t : ℝ) :
    Measurable (fun ω : Ω => (Ns E lamD lamS T ω t : ℝ)) := by
  have e : (fun ω : Ω => (Ns E lamD lamS T ω t : ℝ)) =
      fun ω => cnt (Set.Iic t ×ˢ Set.Iic (wStar E lamD lamS T)) ω.2 :=
    funext (fun ω => Ns_eq E lamD lamS T ω t)
  rw [e]; exact (cnt_meas _ (measurableSet_Iic.prod measurableSet_Iic)).comp measurable_snd

lemma cnt_univ_nonneg (s : ℕ × (ℕ → ℝ × ℝ)) : 0 ≤ cnt Set.univ s := by
  rw [cnt_univ_eq]; exact Nat.cast_nonneg _

lemma q_facts (E : Environment) (lamD lamS T : ℝ) (hT : 0 < T) :
    (Integrable (qD E lamD lamS T) (P E lamD lamS T) ∧ ∀ ω, 0 ≤ qD E lamD lamS T ω) ∧
    (Integrable (qS E lamD lamS T) (P E lamD lamS T) ∧ ∀ ω, 0 ≤ qS E lamD lamS T ω) := by
  set ν : Measure ℝ := volume.restrict (Set.Ioc 0 T) with hν
  obtain ⟨c1, c2⟩ := cnt_int E lamD lamS T hT
  have mD := Nd_joint E lamD lamS T
  have mS := Ns_joint E lamD lamS T
  have hF1 : Measurable (fun z : Ω × ℝ =>
      max ((Nd E lamD lamS T z.1 z.2 : ℝ) - (Ns E lamD lamS T z.1 z.2 : ℝ)) 0) :=
    (mD.sub mS).max measurable_const
  have hF2 : Measurable (fun z : Ω × ℝ =>
      max ((Ns E lamD lamS T z.1 z.2 : ℝ) - (Nd E lamD lamS T z.1 z.2 : ℝ)) 0) :=
    (mS.sub mD).max measurable_const
  have m1 : Measurable (qD E lamD lamS T) := by
    have := (hF1.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
    have e : qD E lamD lamS T = fun ω => ∫ s,
        max ((Nd E lamD lamS T ω s : ℝ) - (Ns E lamD lamS T ω s : ℝ)) 0 ∂ν := by
      funext ω; unfold qD; exact intervalIntegral.integral_of_le hT.le
    rw [e]; exact this
  have m2 : Measurable (qS E lamD lamS T) := by
    have := (hF2.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
    have e : qS E lamD lamS T = fun ω => ∫ s,
        max ((Ns E lamD lamS T ω s : ℝ) - (Nd E lamD lamS T ω s : ℝ)) 0 ∂ν := by
      funext ω; unfold qS; exact intervalIntegral.integral_of_le hT.le
    rw [e]; exact this
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · refine (c1.mul_const |T - 0|).mono' m1.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    unfold qD
    refine intervalIntegral.norm_integral_le_of_norm_le_const (C := cnt Set.univ ω.1) (fun s _ => ?_)
    rw [Real.norm_of_nonneg (le_max_right _ _)]
    have a1 := Nd_le_cnt E lamD lamS T ω s
    have a2 : (0:ℝ) ≤ Ns E lamD lamS T ω s := Nat.cast_nonneg _
    exact max_le (by linarith) (cnt_univ_nonneg _)
  · intro ω; unfold qD
    exact intervalIntegral.integral_nonneg hT.le (fun s _ => le_max_right _ _)
  · refine (c2.mul_const |T - 0|).mono' m2.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    unfold qS
    refine intervalIntegral.norm_integral_le_of_norm_le_const (C := cnt Set.univ ω.2) (fun s _ => ?_)
    rw [Real.norm_of_nonneg (le_max_right _ _)]
    have a1 := Ns_le_cnt E lamD lamS T ω s
    have a2 : (0:ℝ) ≤ Nd E lamD lamS T ω s := Nat.cast_nonneg _
    exact max_le (by linarith) (cnt_univ_nonneg _)
  · intro ω; unfold qS
    exact intervalIntegral.integral_nonneg hT.le (fun s _ => le_max_right _ _)

lemma int_le_of_lint {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g : α → ℝ)
    (hf : Measurable f) (hf0 : 0 ≤ᵐ[μ] f) (hg : Integrable g μ) (hg0 : ∀ x, 0 ≤ g x)
    (hle : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ) :
    Integrable f μ ∧ ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ := by
  have hgl : ∫⁻ x, ENNReal.ofReal (g x) ∂μ = ENNReal.ofReal (∫ x, g x ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall hg0)).symm
  have hfin : ∫⁻ x, ENNReal.ofReal (f x) ∂μ < ⊤ :=
    lt_of_le_of_lt hle (by rw [hgl]; exact ENNReal.ofReal_lt_top)
  have hfi : Integrable f μ := ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hf0).2 hfin⟩
  refine ⟨hfi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hf0 hf.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg0) hg.aestronglyMeasurable]
  exact ENNReal.toReal_mono (by rw [hgl]; exact ENNReal.ofReal_ne_top) hle

noncomputable def askD (E : Environment) (lamD lamS T : ℝ) (z : Ω × ℝ) : ℝ :=
  if Iminus E lamD lamS T z.1 z.2 ≤ 0 then compD E lamD lamS T z.2 else 0

lemma askD_meas (E : Environment) (lamD lamS T : ℝ) (hT : 0 < T) :
    Measurable (askD E lamD lamS T) := by
  haveI := P_sfinite E lamD lamS T hT
  unfold askD
  exact Measurable.ite (ind_meas E lamD lamS T) ((compD_meas E lamD lamS T).comp measurable_snd)
    measurable_const

lemma SD_meas (E : Environment) (lamD lamS T : ℝ) (hT : 0 < T) :
    Measurable (SD E lamD lamS T) := by
  have hJ := askD_meas E lamD lamS T hT
  have hF : ∀ (i _j : ℕ), Measurable (fun ω : Ω => askD E lamD lamS T (ω, (ω.1.2 i).1)) := by
    intro i _
    exact hJ.comp (measurable_id.prodMk (by fun_prop : Measurable (fun ω : Ω => (ω.1.2 i).1)))
  have h1 := pairs_sum_meas E lamD lamS T
    (fun ω i _ => askD E lamD lamS T (ω, (ω.1.2 i).1)) hF
  have e : SD E lamD lamS T = fun ω => ∑ p ∈ (greedyPairs E lamD lamS T ω).toFinset,
      askD E lamD lamS T (ω, (ω.1.2 p.2).1) := by
    funext ω; rfl
  rw [e]; exact h1

lemma SS_meas (E : Environment) (lamD lamS T : ℝ) (hT : 0 < T) :
    Measurable (SS E lamD lamS T) := by
  haveI := P_sfinite E lamD lamS T hT
  have hF : ∀ (_i j : ℕ), Measurable (fun ω : Ω => compS E lamD lamS T (ω.2.2 j).1) := by
    intro _ j
    exact (compS_meas E lamD lamS T).comp (by fun_prop : Measurable (fun ω : Ω => (ω.2.2 j).1))
  have h1 := pairs_sum_meas E lamD lamS T (fun ω _ j => compS E lamD lamS T (ω.2.2 j).1) hF
  have e : SS E lamD lamS T = fun ω => ∑ p ∈ (greedyPairs E lamD lamS T ω).toFinset,
      compS E lamD lamS T (ω.2.2 p.1).1 := by
    funext ω; rfl
  rw [e]; exact h1

lemma card_meas (E : Environment) (lamD lamS T : ℝ) :
    Measurable (fun ω : Ω => ((greedyPairs E lamD lamS T ω).toFinset.card : ℝ)) := by
  have := pairs_sum_meas E lamD lamS T (fun _ _ _ => (1:ℝ)) (fun _ _ => measurable_const)
  simpa using this

lemma card_le_cnt (E : Environment) (lamD lamS T : ℝ) (ω : Ω) :
    ((greedyPairs E lamD lamS T ω).toFinset.card : ℝ) ≤ cnt Set.univ ω.1 := by
  rw [cnt_univ_eq]
  have h1 : (greedyPairs E lamD lamS T ω).toFinset.card ≤ ω.1.1 := by
    calc (greedyPairs E lamD lamS T ω).toFinset.card
        ≤ (greedyPairs E lamD lamS T ω).length := List.toFinset_card_le _
      _ ≤ (sortedB E lamD lamS T ω).length := by
          unfold greedyPairs; rw [List.length_zip]; exact min_le_right _ _
      _ = (reqB E lamD lamS T ω).card := sortedB_length E lamD lamS T ω
      _ ≤ ω.1.1 := by simpa using Finset.card_le_univ (reqB E lamD lamS T ω)
  exact_mod_cast h1

lemma profit_eq (E : Environment) (lamD lamS T b h : ℝ) (ω : Ω) :
    profit E lamD lamS T b h ω =
      (pStar E lamD lamS T - wStar E lamD lamS T) *
        ((greedyPairs E lamD lamS T ω).toFinset.card : ℝ) -
      b * SD E lamD lamS T ω - h * SS E lamD lamS T ω := by
  unfold profit SD SS
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  unfold askPrice bidPrice fD
  push_cast
  split_ifs <;> ring

lemma wait_split (E : Environment) (lamD lamS T b h : ℝ) (ω : Ω) :
    (∫ t in (0 : ℝ)..T,
        (b * max ((Nd E lamD lamS T ω t : ℝ) - (Ns E lamD lamS T ω t : ℝ)) 0 +
         h * max ((Ns E lamD lamS T ω t : ℝ) - (Nd E lamD lamS T ω t : ℝ)) 0)) =
      b * qD E lamD lamS T ω + h * qS E lamD lamS T ω := by
  have c1 := cnt_univ_nonneg ω.1
  have c2 := cnt_univ_nonneg ω.2
  have ii1 : IntervalIntegrable
      (fun s => max ((Nd E lamD lamS T ω s : ℝ) - (Ns E lamD lamS T ω s : ℝ)) 0) volume 0 T :=
    ii_of_bound (fun s => max ((Nd E lamD lamS T ω s : ℝ) - (Ns E lamD lamS T ω s : ℝ)) 0)
      (((Nd_mono E lamD lamS T ω).measurable.sub
      (Ns_mono E lamD lamS T ω).measurable).max measurable_const)
      (cnt Set.univ ω.1 + cnt Set.univ ω.2) (fun s => by
        show |max ((Nd E lamD lamS T ω s : ℝ) - (Ns E lamD lamS T ω s : ℝ)) 0| ≤ _
        rw [abs_of_nonneg (le_max_right _ _)]
        have a1 := Nd_le_cnt E lamD lamS T ω s
        have a2 : (0:ℝ) ≤ Ns E lamD lamS T ω s := Nat.cast_nonneg _
        exact max_le (by linarith) (by linarith)) 0 T
  have ii2 : IntervalIntegrable
      (fun s => max ((Ns E lamD lamS T ω s : ℝ) - (Nd E lamD lamS T ω s : ℝ)) 0) volume 0 T :=
    ii_of_bound (fun s => max ((Ns E lamD lamS T ω s : ℝ) - (Nd E lamD lamS T ω s : ℝ)) 0)
      (((Ns_mono E lamD lamS T ω).measurable.sub
      (Nd_mono E lamD lamS T ω).measurable).max measurable_const)
      (cnt Set.univ ω.1 + cnt Set.univ ω.2) (fun s => by
        show |max ((Ns E lamD lamS T ω s : ℝ) - (Nd E lamD lamS T ω s : ℝ)) 0| ≤ _
        rw [abs_of_nonneg (le_max_right _ _)]
        have a1 := Ns_le_cnt E lamD lamS T ω s
        have a2 : (0:ℝ) ≤ Nd E lamD lamS T ω s := Nat.cast_nonneg _
        exact max_le (by linarith) (by linarith)) 0 T
  unfold qD qS
  rw [intervalIntegral.integral_add (ii1.const_mul b) (ii2.const_mul h),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- C4a. Palm/Mecke accounting of the posted-price profit: matches earn the spread,
waiting adjustments cost at most the integrated queue lengths. -/
theorem profit_lower (E : Environment) (lamD lamS T b h : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hgap : E.loS < E.hiB)
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T)
    (hb : 0 ≤ b) (hh : 0 ≤ h) :
    Integrable (profit E lamD lamS T b h) (P E lamD lamS T) ∧
    (pStar E lamD lamS T - wStar E lamD lamS T) *
        ∫ ω, ((min (Nd E lamD lamS T ω T) (Ns E lamD lamS T ω T) : ℕ) : ℝ)
          ∂P E lamD lamS T -
      ∫ ω, (∫ t in (0 : ℝ)..T,
        (b * max ((Nd E lamD lamS T ω t : ℝ) - (Ns E lamD lamS T ω t : ℝ)) 0 +
         h * max ((Ns E lamD lamS T ω t : ℝ) - (Nd E lamD lamS T ω t : ℝ)) 0))
          ∂P E lamD lamS T
      ≤ policyProfit E lamD lamS T b h := by
  have hwp := (fluid_primitives E lamD lamS T hcontB hcontS hreg hgap hd hs hT).2.1
  haveI := P_prob E lamD lamS T hT
  have hd0 : 0 ≤ pStar E lamD lamS T - wStar E lamD lamS T := by linarith
  obtain ⟨⟨iqD, qD0⟩, ⟨iqS, qS0⟩⟩ := q_facts E lamD lamS T hT
  have hgood := good_ae E lamD lamS T hT
  have SD0 : 0 ≤ᵐ[P E lamD lamS T] SD E lamD lamS T := hgood.mono (fun ω hω =>
    Finset.sum_nonneg (fun p _ => fD_nonneg E lamD lamS T ω hω.1 p.2))
  have SS0 : 0 ≤ᵐ[P E lamD lamS T] SS E lamD lamS T := hgood.mono (fun ω hω =>
    Finset.sum_nonneg (fun p _ => compS_nonneg E lamD lamS T _ (hω.2 p.1).2))
  obtain ⟨iSD, hSD⟩ := int_le_of_lint _ _ _ (SD_meas E lamD lamS T hT) SD0 iqD qD0
    (buyer_lint E lamD lamS T hT)
  obtain ⟨iSS, hSS⟩ := int_le_of_lint _ _ _ (SS_meas E lamD lamS T hT) SS0 iqS qS0
    (seller_lint E lamD lamS T hT)
  have icnt := (cnt_int E lamD lamS T hT).1
  have icard : Integrable (fun ω : Ω => ((greedyPairs E lamD lamS T ω).toFinset.card : ℝ))
      (P E lamD lamS T) :=
    icnt.mono' (card_meas E lamD lamS T).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]; exact card_le_cnt E lamD lamS T ω))
  have imin : Integrable (fun ω : Ω => ((min (Nd E lamD lamS T ω T) (Ns E lamD lamS T ω T) : ℕ) : ℝ))
      (P E lamD lamS T) := by
    have e : (fun ω : Ω => ((min (Nd E lamD lamS T ω T) (Ns E lamD lamS T ω T) : ℕ) : ℝ)) =
        fun ω => min (Nd E lamD lamS T ω T : ℝ) (Ns E lamD lamS T ω T : ℝ) := by
      funext ω; rw [Nat.cast_min]
    have mm : Measurable (fun ω : Ω => min (Nd E lamD lamS T ω T : ℝ) (Ns E lamD lamS T ω T : ℝ)) :=
      (Nd_at E lamD lamS T T).min (Ns_at E lamD lamS T T)
    rw [e]
    refine icnt.mono' mm.aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => ?_))
    have a1 := Nd_le_cnt E lamD lamS T ω T
    rw [Real.norm_of_nonneg (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    exact (min_le_left _ _).trans a1
  have hpe : profit E lamD lamS T b h = fun ω =>
      (pStar E lamD lamS T - wStar E lamD lamS T) *
        ((greedyPairs E lamD lamS T ω).toFinset.card : ℝ) -
      b * SD E lamD lamS T ω - h * SS E lamD lamS T ω :=
    funext (fun ω => profit_eq E lamD lamS T b h ω)
  have iA := icard.const_mul (pStar E lamD lamS T - wStar E lamD lamS T)
  have iB := iSD.const_mul b
  have iC := iSS.const_mul h
  have iAB : Integrable (fun ω : Ω => (pStar E lamD lamS T - wStar E lamD lamS T) *
        ((greedyPairs E lamD lamS T ω).toFinset.card : ℝ) - b * SD E lamD lamS T ω)
      (P E lamD lamS T) := iA.sub iB
  refine ⟨by rw [hpe]; exact iAB.sub iC, ?_⟩
  have hw : ∫ ω, (∫ t in (0 : ℝ)..T,
        (b * max ((Nd E lamD lamS T ω t : ℝ) - (Ns E lamD lamS T ω t : ℝ)) 0 +
         h * max ((Ns E lamD lamS T ω t : ℝ) - (Nd E lamD lamS T ω t : ℝ)) 0))
          ∂P E lamD lamS T =
      ∫ ω, (b * qD E lamD lamS T ω + h * qS E lamD lamS T ω) ∂P E lamD lamS T :=
    integral_congr_ae (Filter.Eventually.of_forall (fun ω => wait_split E lamD lamS T b h ω))
  have hpp : policyProfit E lamD lamS T b h =
      ∫ ω, ((pStar E lamD lamS T - wStar E lamD lamS T) *
        ((greedyPairs E lamD lamS T ω).toFinset.card : ℝ) -
      b * SD E lamD lamS T ω - h * SS E lamD lamS T ω) ∂P E lamD lamS T := by
    unfold policyProfit; rw [hpe]
  rw [hw, hpp, integral_add (iqD.const_mul b) (iqS.const_mul h), integral_sub iAB iC,
    integral_sub iA iB, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul]
  have hcm : ∫ ω, ((min (Nd E lamD lamS T ω T) (Ns E lamD lamS T ω T) : ℕ) : ℝ) ∂P E lamD lamS T ≤
      ∫ ω, ((greedyPairs E lamD lamS T ω).toFinset.card : ℝ) ∂P E lamD lamS T :=
    integral_mono imin icard (fun ω => Nat.cast_le.2 (pairs_card E lamD lamS T ω))
  nlinarith [mul_le_mul_of_nonneg_left hcm hd0, mul_le_mul_of_nonneg_left hSD hb,
    mul_le_mul_of_nonneg_left hSS hh]

end C4aAssembly

/-- Assembly at fixed rates from the child lemmas. -/
theorem ratio_core (E : Environment) (lamD lamS T b h : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hgap : E.loS < E.hiB)
    (hloB : 0 ≤ E.loB) (hloS : 0 ≤ E.loS)
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T)
    (hb : 0 ≤ b) (hh : 0 ≤ h) :
    Integrable (profit E lamD lamS T b h) (P E lamD lamS T) ∧
    Integrable (Jbar E b h) (P E lamD lamS T) ∧
    0 < ∫ ω, Jbar E b h ω ∂P E lamD lamS T ∧ 0 < fluidValue E lamD lamS T ∧
    1 - (1 + (2 / 3 : ℝ) * ((b + h) * T) /
      (pStar E lamD lamS T - wStar E lamD lamS T)) /
      Real.sqrt (muStar E lamD lamS T) ≤
        policyProfit E lamD lamS T b h / fluidValue E lamD lamS T ∧
    (0 ≤ policyProfit E lamD lamS T b h →
      policyProfit E lamD lamS T b h / fluidValue E lamD lamS T ≤
        policyProfit E lamD lamS T b h / ∫ ω, Jbar E b h ω ∂P E lamD lamS T) := by
  obtain ⟨hmu, hwp, -, -⟩ :=
    fluid_primitives E lamD lamS T hcontB hcontS hreg hgap hd hs hT
  have hJs := fluid_value E lamD lamS T hcontB hcontS hreg hgap hloB hloS hd hs hT
  obtain ⟨hJbarInt, hEJpos, hEJle⟩ :=
    clairvoyant_bound E lamD lamS T b h hcontB hcontS hreg hgap hd hs hT hb hh
  obtain ⟨hprofInt, hprofLB⟩ :=
    profit_lower E lamD lamS T b h hcontB hcontS hreg hgap hd hs hT hb hh
  obtain ⟨hmin, hwait⟩ :=
    poisson_bounds E lamD lamS T b h hcontB hcontS hreg hgap hd hs hT hb hh
  set μ := muStar E lamD lamS T with hμ
  set d := pStar E lamD lamS T - wStar E lamD lamS T with hdd
  set J := policyProfit E lamD lamS T b h with hJ
  set EJ := ∫ ω, Jbar E b h ω ∂P E lamD lamS T with hEJ
  set K := (2 / 3 : ℝ) * ((b + h) * T) with hK
  have hdpos : 0 < d := by rw [hdd]; linarith
  have hKnn : 0 ≤ K := by rw [hK]; positivity
  set s := Real.sqrt μ with hs_def
  have hspos : 0 < s := Real.sqrt_pos.mpr hmu
  have hss : s * s = μ := Real.mul_self_sqrt hmu.le
  have hJsval : fluidValue E lamD lamS T = μ * d := hJs
  have hJspos : 0 < fluidValue E lamD lamS T := by rw [hJsval]; positivity
  have hJlb : d * (μ - s) - K * s ≤ J := by
    have h1 : d * (μ - s) ≤ d * ∫ ω, ((min (Nd E lamD lamS T ω T)
        (Ns E lamD lamS T ω T) : ℕ) : ℝ) ∂P E lamD lamS T :=
      mul_le_mul_of_nonneg_left hmin hdpos.le
    have h2 : d * ∫ ω, ((min (Nd E lamD lamS T ω T)
        (Ns E lamD lamS T ω T) : ℕ) : ℝ) ∂P E lamD lamS T - K * s ≤ J := by
      linarith
    linarith
  refine ⟨hprofInt, hJbarInt, hEJpos, hJspos, ?_, ?_⟩
  · rw [hJsval, le_div_iff₀ (by positivity)]
    have key : (1 - (1 + K / d) / s) * (μ * d) = μ * d - (d + K) * s := by
      rw [← hss]; field_simp
    rw [key]
    have : d * (μ - s) - K * s = μ * d - (d + K) * s := by ring
    linarith
  · intro hJnn
    rw [hJsval]
    exact div_le_div_of_nonneg_left hJnn hEJpos (hJsval ▸ hEJle)

/-- The parent, assembled from the children. -/
theorem main_core (E : Environment) (lamD lamS T b h : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hgap : E.loS < E.hiB)
    (hloB : 0 ≤ E.loB) (hloS : 0 ≤ E.loS)
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T)
    (hb : 0 ≤ b) (hh : 0 ≤ h) :
    let J := policyProfit E lamD lamS T b h
    let EJ := ∫ ω, Jbar E b h ω ∂P E lamD lamS T
    let Js := fluidValue E lamD lamS T
    Integrable (profit E lamD lamS T b h) (P E lamD lamS T) ∧
    Integrable (Jbar E b h) (P E lamD lamS T) ∧
    0 < muStar E lamD lamS T ∧
    wStar E lamD lamS T < pStar E lamD lamS T ∧
    0 < EJ ∧ 0 < Js ∧
    1 - (1 + (2 / 3 : ℝ) * ((b + h) * T) /
      (pStar E lamD lamS T - wStar E lamD lamS T)) /
      Real.sqrt (muStar E lamD lamS T) ≤ J / Js ∧
    (0 ≤ J → J / Js ≤ J / EJ) ∧
    (∀ αd αs : ℝ, 0 < αd → 0 < αs →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
        let ld := (n : ℝ) ^ αd * lamD
        let ls := (n : ℝ) ^ αs * lamS
        let Jn := policyProfit E ld ls T b h
        let EJn := ∫ ω, Jbar E b h ω ∂P E ld ls T
        let Jsn := fluidValue E ld ls T
        Integrable (profit E ld ls T b h) (P E ld ls T) ∧
        Integrable (Jbar E b h) (P E ld ls T) ∧
        0 < EJn ∧ 0 < Jsn ∧
        1 - C / Real.sqrt ((n : ℝ) ^ min αd αs) ≤ Jn / Jsn ∧
        (0 ≤ Jn → Jn / Jsn ≤ Jn / EJn)) := by
  intro J EJ Js
  obtain ⟨hmu, hwp, -, -⟩ :=
    fluid_primitives E lamD lamS T hcontB hcontS hreg hgap hd hs hT
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    ratio_core E lamD lamS T b h hcontB hcontS hreg hgap hloB hloS hd hs hT hb hh
  refine ⟨h1, h2, hmu, hwp, h3, h4, h5, h6, ?_⟩
  intro αd αs had has
  obtain ⟨c, δ, hc, hδ, hscale⟩ :=
    scaling_uniform E lamD lamS T hcontB hcontS hreg hgap hd hs hT αd αs had has
  have hKnn : 0 ≤ (2 / 3 : ℝ) * ((b + h) * T) := by positivity
  refine ⟨(1 + (2 / 3 : ℝ) * ((b + h) * T) / δ) / Real.sqrt c, by positivity,
    fun n hn => ?_⟩
  intro ld ls Jn EJn Jsn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hld : 0 < ld := by positivity
  have hls : 0 < ls := by positivity
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ :=
    ratio_core E ld ls T b h hcontB hcontS hreg hgap hloB hloS hld hls hT hb hh
  obtain ⟨hμn, hδn⟩ := hscale n hn
  refine ⟨g1, g2, g3, g4, le_trans ?_ g5, g6⟩
  have hpow : 0 < (n : ℝ) ^ min αd αs := by positivity
  have hnum : 1 + (2 / 3 : ℝ) * ((b + h) * T) / (pStar E ld ls T - wStar E ld ls T) ≤
      1 + (2 / 3 : ℝ) * ((b + h) * T) / δ := by
    have := div_le_div_of_nonneg_left hKnn hδ hδn
    linarith
  have hden : Real.sqrt c * Real.sqrt ((n : ℝ) ^ min αd αs) ≤
      Real.sqrt (muStar E ld ls T) := by
    rw [← Real.sqrt_mul hc.le]
    exact Real.sqrt_le_sqrt hμn
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsn : 0 < Real.sqrt ((n : ℝ) ^ min αd αs) := Real.sqrt_pos.mpr hpow
  have hfin : (1 + (2 / 3 : ℝ) * ((b + h) * T) / (pStar E ld ls T - wStar E ld ls T)) /
      Real.sqrt (muStar E ld ls T) ≤
      (1 + (2 / 3 : ℝ) * ((b + h) * T) / δ) / Real.sqrt c /
        Real.sqrt ((n : ℝ) ^ min αd αs) := by
    rw [div_div]
    exact div_le_div₀ (by positivity) hnum (by positivity) hden
  linarith

end TwoSidedMatching.Guarantee

open MeasureTheory TwoSidedMatching.Guarantee in
theorem solution (E : Environment) (lamD lamS T b h : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hgap : E.loS < E.hiB)
    (hloB : 0 ≤ E.loB) (hloS : 0 ≤ E.loS)
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T)
    (hb : 0 ≤ b) (hh : 0 ≤ h) :
    let J := policyProfit E lamD lamS T b h
    let EJ := ∫ ω, Jbar E b h ω ∂P E lamD lamS T
    let Js := fluidValue E lamD lamS T
    Integrable (profit E lamD lamS T b h) (P E lamD lamS T) ∧
    Integrable (Jbar E b h) (P E lamD lamS T) ∧
    0 < muStar E lamD lamS T ∧
    wStar E lamD lamS T < pStar E lamD lamS T ∧
    0 < EJ ∧ 0 < Js ∧
    1 - (1 + (2 / 3 : ℝ) * ((b + h) * T) /
      (pStar E lamD lamS T - wStar E lamD lamS T)) /
      Real.sqrt (muStar E lamD lamS T) ≤ J / Js ∧
    (0 ≤ J → J / Js ≤ J / EJ) ∧
    (∀ αd αs : ℝ, 0 < αd → 0 < αs →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
        let ld := (n : ℝ) ^ αd * lamD
        let ls := (n : ℝ) ^ αs * lamS
        let Jn := policyProfit E ld ls T b h
        let EJn := ∫ ω, Jbar E b h ω ∂P E ld ls T
        let Jsn := fluidValue E ld ls T
        Integrable (profit E ld ls T b h) (P E ld ls T) ∧
        Integrable (Jbar E b h) (P E ld ls T) ∧
        0 < EJn ∧ 0 < Jsn ∧
        1 - C / Real.sqrt ((n : ℝ) ^ min αd αs) ≤ Jn / Jsn ∧
        (0 ≤ Jn → Jn / Jsn ≤ Jn / EJn)) := by
  exact main_core E lamD lamS T b h hcontB hcontS hreg hgap hloB hloS hd hs hT hb hh
