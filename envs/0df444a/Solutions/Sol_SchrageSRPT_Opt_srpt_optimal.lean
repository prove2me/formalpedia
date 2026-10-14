-- Prove2me | solution 1 for SchrageSRPT.Opt.srpt_optimal
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-13T06:23:54.960879+00:00
-- url     : https://prove2.me/submissions/4ddd9582-f1c5-4beb-bcbf-cfd2f9a2688a

-- Complete checked reconstruction of the full native arbitrary-measurable SRPT optimality theorem.
-- Licensed under Apache 2.0.
import Definitions.Def_SchrageSRPT_Opt_Model
import Mathlib
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm


-- Begin Canonical
section ModuleScope_Canonical

end ModuleScope_Canonical
-- End Canonical

-- Begin ScheduleIntegral
section ModuleScope_ScheduleIntegral

namespace SchrageSRPT.Opt.Proof
open MeasureTheory

variable {A : ℕ → ℝ} {δ : ℕ → ℝ → ℝ}

lemma schedule_nonneg (hδ : IsSchedule A δ) (i : ℕ) (t : ℝ) : 0 ≤ δ i t := by
  rcases hδ.1 i t with h | h <;> simp [h]

lemma schedule_le_one (hδ : IsSchedule A δ) (i : ℕ) (t : ℝ) : δ i t ≤ 1 := by
  rcases hδ.1 i t with h | h <;> simp [h]

lemma schedule_norm_le (hδ : IsSchedule A δ) (i : ℕ) (t : ℝ) : ‖δ i t‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (schedule_nonneg hδ i t)]
  exact schedule_le_one hδ i t

lemma schedule_locallyIntegrable (hδ : IsSchedule A δ) (i : ℕ) :
    LocallyIntegrable (δ i) volume := by
  refine (locallyIntegrable_const (1 : ℝ)).mono (hδ.2.1 i).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun t => by simpa using schedule_norm_le hδ i t

lemma schedule_intervalIntegrable (hδ : IsSchedule A δ) (i : ℕ) (a b : ℝ) :
    IntervalIntegrable (δ i) volume a b := by
  exact intervalIntegrable_iff.mpr
    (((schedule_locallyIntegrable hδ i).integrableOn_isCompact isCompact_uIcc).mono_set
      Set.uIoc_subset_uIcc)

lemma schedule_integral_nonneg (hδ : IsSchedule A δ) (i : ℕ) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ ∫ t in a..b, δ i t :=
  intervalIntegral.integral_nonneg_of_forall hab (schedule_nonneg hδ i)

lemma schedule_sum_le_one (hδ : IsSchedule A δ) (S : Finset ℕ) (t : ℝ) :
    ∑ i ∈ S, δ i t ≤ 1 := by
  classical
  by_cases h : ∃ i ∈ S, δ i t = 1
  · obtain ⟨i, hi, hione⟩ := h
    have heq : ∑ j ∈ S, δ j t = δ i t := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        rcases hδ.1 j t with hj | hj
        · exact hj
        · exact False.elim (hji (hδ.2.2.2 t j i hj hione))
      · simp [hi]
    rw [heq, hione]
  · have hz : ∀ i ∈ S, δ i t = 0 := by
      intro i hi
      rcases hδ.1 i t with hz | ho
      · exact hz
      · exact False.elim (h ⟨i, hi, ho⟩)
    simp [Finset.sum_eq_zero hz]

lemma schedule_integral_sum_le (hδ : IsSchedule A δ) (S : Finset ℕ)
    {a b : ℝ} (hab : a ≤ b) :
    ∑ i ∈ S, (∫ t in a..b, δ i t) ≤ b - a := by
  rw [← intervalIntegral.integral_finsetSum (fun i _ => schedule_intervalIntegrable hδ i a b)]
  have h := intervalIntegral.integral_mono_on hab
    (IntervalIntegrable.sum S (fun i _ => schedule_intervalIntegrable hδ i a b))
    (intervalIntegrable_const (c := (1 : ℝ))) (fun t _ => by simpa only [Finset.sum_apply] using schedule_sum_le_one hδ S t)
  simpa using h

lemma remaining_sub (P : ℕ → ℝ) (hδ : IsSchedule A δ) (i : ℕ) (a b : ℝ) :
    remaining A P δ i a - remaining A P δ i b = ∫ t in a..b, δ i t := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (schedule_intervalIntegrable hδ i (A i) a) (schedule_intervalIntegrable hδ i a b)
  unfold remaining
  linarith

lemma remaining_lipschitz (P : ℕ → ℝ) (hδ : IsSchedule A δ) (i : ℕ) :
    LipschitzWith 1 (remaining A P δ i) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := (1 : ℝ)) (fun t _ => schedule_norm_le hδ i t)
  simpa [Real.dist_eq, remaining_sub P hδ i a b, Real.norm_eq_abs, abs_sub_comm] using h

lemma remaining_antitone (P : ℕ → ℝ) (hδ : IsSchedule A δ) (i : ℕ) :
    Antitone (remaining A P δ i) := by
  intro a b hab
  have h := schedule_integral_nonneg hδ i hab
  rw [← remaining_sub P hδ i a b] at h
  linarith

end SchrageSRPT.Opt.Proof
end ModuleScope_ScheduleIntegral
-- End ScheduleIntegral

-- Begin ClippedRemaining
section ModuleScope_ClippedRemaining

namespace SchrageSRPT.Opt.Proof
open MeasureTheory

noncomputable def clippedRemaining (A P : ℕ → ℝ) (δ : ℕ → ℝ → ℝ)
    (i : ℕ) (t : ℝ) : ℝ := max 0 (remaining A P δ i t)

variable {A P : ℕ → ℝ} {δ : ℕ → ℝ → ℝ}

lemma clipped_nonneg (i : ℕ) (t : ℝ) : 0 ≤ clippedRemaining A P δ i t := le_max_left _ _

lemma clipped_pos_iff (i : ℕ) (t : ℝ) :
    0 < clippedRemaining A P δ i t ↔ 0 < remaining A P δ i t := by
  simp [clippedRemaining]

lemma clipped_eq_of_pos {i : ℕ} {t : ℝ} (h : 0 < clippedRemaining A P δ i t) :
    clippedRemaining A P δ i t = remaining A P δ i t :=
  max_eq_right ((clipped_pos_iff i t).mp h).le

lemma clipped_lipschitz (hδ : IsSchedule A δ) (i : ℕ) :
    LipschitzWith 1 (clippedRemaining A P δ i) :=
  (remaining_lipschitz P hδ i).const_max 0

lemma clipped_antitone (hδ : IsSchedule A δ) (i : ℕ) :
    Antitone (clippedRemaining A P δ i) := by
  intro a b hab
  exact max_le_max_left 0 (remaining_antitone P hδ i hab)

lemma clipped_before_arrival (hδ : IsSchedule A δ) (i : ℕ) {t : ℝ} (ht : t ≤ A i) :
    clippedRemaining A P δ i t = max 0 (P i) := by
  have hz : (∫ x in t..A i, δ i x) = 0 := by
    calc
      _ = ∫ _ in t..A i, (0 : ℝ) :=
        intervalIntegral.integral_congr_Ioo_of_le ht (fun x hx => hδ.2.2.1 i x hx.2)
      _ = 0 := by simp
  have hz' : (∫ x in A i..t, δ i x) = 0 := by
    rw [intervalIntegral.integral_symm, hz, neg_zero]
  simp [clippedRemaining, remaining, hz']

lemma clipped_loss_le (hδ : IsSchedule A δ) (i : ℕ) {a b : ℝ} (hab : a ≤ b) :
    clippedRemaining A P δ i a - clippedRemaining A P δ i b ≤
      ∫ t in a..b, δ i t := by
  have hr := remaining_sub P hδ i a b
  have hi := schedule_integral_nonneg hδ i hab
  unfold clippedRemaining
  rcases le_total 0 (remaining A P δ i b) with hb | hb
  · have ha : 0 ≤ remaining A P δ i a := by linarith
    rw [max_eq_right ha, max_eq_right hb, hr]
  · rw [max_eq_left hb, sub_zero]
    apply max_le
    · linarith
    · linarith

lemma clipped_sum_loss_le (hδ : IsSchedule A δ) (S : Finset ℕ)
    {a b : ℝ} (hab : a ≤ b) :
    ∑ i ∈ S, (clippedRemaining A P δ i a - clippedRemaining A P δ i b) ≤ b - a := by
  exact (Finset.sum_le_sum fun i _ => clipped_loss_le hδ i hab).trans
    (schedule_integral_sum_le hδ S hab)

end SchrageSRPT.Opt.Proof
end ModuleScope_ClippedRemaining
-- End ClippedRemaining

-- Begin ClippedDerivative
section ModuleScope_ClippedDerivative

namespace SchrageSRPT.Opt.Proof
open MeasureTheory Filter
open scoped Topology

variable {A P : ℕ → ℝ} {δ : ℕ → ℝ → ℝ}

lemma ae_clipped_derivative (hδ : IsSchedule A δ) (i : ℕ) :
    ∀ᵐ t : ℝ, HasDerivAt (clippedRemaining A P δ i)
      (if 0 < clippedRemaining A P δ i t then -δ i t else 0) t := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral (schedule_locallyIntegrable hδ i),
    (clipped_lipschitz (P := P) hδ i).ae_differentiableAt_real] with t ht hd
  by_cases hp : 0 < clippedRemaining A P δ i t
  · rw [if_pos hp]
    have hr : HasDerivAt (remaining A P δ i) (-δ i t) t := by
      convert! (ht (A i)).const_sub (P i) using 1
    apply hr.congr_of_eventuallyEq
    have hpos : ∀ᶠ x in 𝓝 t, 0 < remaining A P δ i x :=
      (remaining_lipschitz P hδ i).continuous.continuousAt.eventually
        (isOpen_Ioi.mem_nhds ((clipped_pos_iff i t).mp hp))
    filter_upwards [hpos] with x hx
    exact max_eq_right hx.le
  · rw [if_neg hp]
    have hz : clippedRemaining A P δ i t = 0 := le_antisymm (le_of_not_gt hp)
      (clipped_nonneg i t)
    have hm : IsLocalMin (clippedRemaining A P δ i) t := by
      exact Filter.Eventually.of_forall fun x => by rw [hz]; exact clipped_nonneg i x
    have he := hm.hasDerivAt_eq_zero hd.hasDerivAt
    simpa only [he] using hd.hasDerivAt

lemma ae_srpt_selected_derivative {δs : ℕ → ℝ → ℝ} (hs : IsSRPT A P δs)
    (J : Finset ℕ) (a b : ℝ)
    (hJ : ∀ t, a < t → t < b → ∀ i, A i ≤ t ↔ i ∈ J) :
    ∀ᵐ t : ℝ, a < t → t < b → (∃ i ∈ J, 0 < clippedRemaining A P δs i t) →
      ∃ k ∈ J, 0 < clippedRemaining A P δs k t ∧
        (∀ i ∈ J, 0 < clippedRemaining A P δs i t →
          clippedRemaining A P δs k t ≤ clippedRemaining A P δs i t) ∧
        ∀ i ∈ J, HasDerivAt (clippedRemaining A P δs i) (if i = k then -1 else 0) t := by
  classical
  have hall : ∀ᵐ t : ℝ, ∀ i : ℕ,
      HasDerivAt (clippedRemaining A P δs i)
        (if 0 < clippedRemaining A P δs i t then -δs i t else 0) t :=
    ae_all_iff.mpr (fun i => ae_clipped_derivative hs.1 i)
  filter_upwards [hall] with t ht
  intro ha hb hex
  have hsys : (inSystem A P δs t).Nonempty := by
    obtain ⟨i, hi, hp⟩ := hex
    exact ⟨i, (hJ t ha hb i).mpr hi, (clipped_pos_iff i t).mp hp⟩
  obtain ⟨k, hk, hkone, hmin⟩ := hs.2 t hsys
  have hkp : 0 < clippedRemaining A P δs k t := (clipped_pos_iff k t).mpr hk.2
  refine ⟨k, (hJ t ha hb k).mp hk.1, hkp, ?_, ?_⟩
  · intro i hi hp
    rw [clipped_eq_of_pos hkp, clipped_eq_of_pos hp]
    exact hmin i ⟨(hJ t ha hb i).mpr hi, (clipped_pos_iff i t).mp hp⟩
  · intro i _
    by_cases hik : i = k
    · subst i
      simpa [hkp, hkone] using ht k
    · have hzero : δs i t = 0 := by
        rcases hs.1.1 i t with hz | ho
        · exact hz
        · exact False.elim (hik (hs.1.2.2.2 t i k ho hkone))
      simpa [hik, hzero] using ht i

end SchrageSRPT.Opt.Proof
end ModuleScope_ClippedDerivative
-- End ClippedDerivative

-- Begin SubsetOrder
section ModuleScope_SubsetOrder

open Finset
namespace SchrageSRPT.Opt.Proof

 def PrefixLE {ι : Type*} [DecidableEq ι] (J : Finset ι) (r s : ι → ℝ) : Prop :=
  ∀ S, S ⊆ J → ∃ U, U ⊆ J ∧ U.card = S.card ∧ (∑ i ∈ U, r i) ≤ ∑ i ∈ S, s i

 theorem prefixLE_refl {ι : Type*} [DecidableEq ι] (J : Finset ι) (r : ι → ℝ) :
    PrefixLE J r r := fun S hS => ⟨S, hS, rfl, le_rfl⟩

 theorem prefixLE_union {ι : Type*} [DecidableEq ι] {J H : Finset ι} {r s : ι → ℝ}
    (hdisj : Disjoint J H) (h : PrefixLE J r s) (heq : ∀ i ∈ H, r i = s i) :
    PrefixLE (J ∪ H) r s := by
  intro S hS
  obtain ⟨U, hU, hcard, hsum⟩ := h (S ∩ J) inter_subset_right
  have hd : Disjoint U (S ∩ H) := hdisj.mono hU inter_subset_right
  have hsplit : S = (S ∩ J) ∪ (S ∩ H) := by
    ext i
    simp only [mem_union, mem_inter]
    constructor
    · intro hi
      rcases mem_union.mp (hS hi) with hj | hh
      · exact Or.inl ⟨hi, hj⟩
      · exact Or.inr ⟨hi, hh⟩
    · rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
  have hd' : Disjoint (S ∩ J) (S ∩ H) := hdisj.mono inter_subset_right inter_subset_right
  refine ⟨U ∪ (S ∩ H), union_subset (hU.trans subset_union_left)
    (inter_subset_right.trans subset_union_right), ?_, ?_⟩
  · rw [card_union_of_disjoint hd, hcard]
    exact (card_union_of_disjoint hd').symm.trans (congrArg Finset.card hsplit.symm)
  · rw [sum_union hd]
    have he : ∑ i ∈ S ∩ H, r i = ∑ i ∈ S ∩ H, s i :=
      sum_congr rfl fun i hi => heq i (mem_inter.mp hi).2
    rw [he]
    calc
      _ ≤ (∑ i ∈ S ∩ J, s i) + ∑ i ∈ S ∩ H, s i := by linarith
      _ = ∑ i ∈ S, s i := by rw [← sum_union hd', ← hsplit]

 theorem prefixLE_positive_card {ι : Type*} [DecidableEq ι] {J : Finset ι} {r s : ι → ℝ}
    (h : PrefixLE J r s) (hr : ∀ i ∈ J, 0 ≤ r i) (hs : ∀ i ∈ J, 0 ≤ s i) :
    (J.filter fun i => 0 < r i).card ≤ (J.filter fun i => 0 < s i).card := by
  classical
  let C := J.filter fun i => s i = 0
  obtain ⟨U, hU, hcard, hsum⟩ := h C (filter_subset _ _)
  have hc : ∑ i ∈ C, s i = 0 := sum_eq_zero fun i hi => (mem_filter.mp hi).2
  rw [hc] at hsum
  have hz : ∀ i ∈ U, r i = 0 := by
    have he : ∑ i ∈ U, r i = 0 := le_antisymm hsum (sum_nonneg fun i hi => hr i (hU hi))
    exact (sum_eq_zero_iff_of_nonneg (fun i hi => hr i (hU hi))).mp he
  have hsub : U ⊆ J.filter fun i => r i = 0 := fun i hi => mem_filter.mpr ⟨hU hi, hz i hi⟩
  have hle := card_le_card hsub
  have hcr : (J.filter fun i => 0 < r i).card + (J.filter fun i => r i = 0).card = J.card := by
    convert card_filter_add_card_filter_not (s := J) (fun i => 0 < r i) using 2
    apply congrArg Finset.card
    ext i
    simp only [mem_filter]
    constructor
    · rintro ⟨hi, hz'⟩
      exact ⟨hi, by simp [hz']⟩
    · rintro ⟨hi, hn⟩
      exact ⟨hi, le_antisymm (not_lt.mp hn) (hr i hi)⟩
  have hcs : (J.filter fun i => 0 < s i).card + C.card = J.card := by
    convert card_filter_add_card_filter_not (s := J) (fun i => 0 < s i) using 2
    apply congrArg Finset.card
    ext i
    simp only [C, mem_filter]
    constructor
    · rintro ⟨hi, hz'⟩
      exact ⟨hi, by simp [hz']⟩
    · rintro ⟨hi, hn⟩
      exact ⟨hi, le_antisymm (not_lt.mp hn) (hs i hi)⟩
  omega

end SchrageSRPT.Opt.Proof
end ModuleScope_SubsetOrder
-- End SubsetOrder

-- Begin PrefixMinimum
section ModuleScope_PrefixMinimum

open Finset
namespace SchrageSRPT.Opt.Proof

noncomputable def prefixMin {ι : Type*} [DecidableEq ι] (J : Finset ι)
    (h : ℕ) (hh : h ≤ J.card) (r : ι → ℝ) : ℝ :=
  (J.powersetCard h).inf' (powersetCard_nonempty.mpr hh) (fun S => ∑ i ∈ S, r i)

 theorem prefixMin_le {ι : Type*} [DecidableEq ι] {J S : Finset ι}
    {h : ℕ} (hh : h ≤ J.card) (r : ι → ℝ) (hS : S ⊆ J) (hc : S.card = h) :
    prefixMin J h hh r ≤ ∑ i ∈ S, r i :=
  inf'_le _ (mem_powersetCard.mpr ⟨hS, hc⟩)

 theorem prefixMin_attained {ι : Type*} [DecidableEq ι] (J : Finset ι)
    (h : ℕ) (hh : h ≤ J.card) (r : ι → ℝ) :
    ∃ S, S ⊆ J ∧ S.card = h ∧ prefixMin J h hh r = ∑ i ∈ S, r i := by
  obtain ⟨S, hS, he⟩ := (J.powersetCard h).exists_mem_eq_inf' (powersetCard_nonempty.mpr hh)
    (fun S => ∑ i ∈ S, r i)
  exact ⟨S, (mem_powersetCard.mp hS).1, (mem_powersetCard.mp hS).2, he⟩

 theorem prefixMin_nonneg {ι : Type*} [DecidableEq ι] {J : Finset ι}
    {h : ℕ} (hh : h ≤ J.card) {r : ι → ℝ} (hr : ∀ i ∈ J, 0 ≤ r i) :
    0 ≤ prefixMin J h hh r := by
  obtain ⟨S, hS, _, he⟩ := prefixMin_attained J h hh r
  rw [he]
  exact sum_nonneg fun i hi => hr i (hS hi)

 theorem prefixMin_mono {ι : Type*} [DecidableEq ι] {J : Finset ι}
    {h : ℕ} (hh : h ≤ J.card) {r s : ι → ℝ} (hrs : ∀ i ∈ J, r i ≤ s i) :
    prefixMin J h hh r ≤ prefixMin J h hh s := by
  obtain ⟨S, hS, hc, he⟩ := prefixMin_attained J h hh s
  rw [he]
  exact (prefixMin_le hh r hS hc).trans (sum_le_sum fun i hi => hrs i (hS hi))

 theorem prefixLE_iff_min {ι : Type*} [DecidableEq ι] {J : Finset ι} {r s : ι → ℝ} :
    PrefixLE J r s ↔ ∀ h (hh : h ≤ J.card), prefixMin J h hh r ≤ prefixMin J h hh s := by
  constructor
  · intro h h' hh
    obtain ⟨S, hS, hc, he⟩ := prefixMin_attained J h' hh s
    obtain ⟨U, hU, hcard, hsum⟩ := h S hS
    rw [he]
    exact (prefixMin_le hh r hU (hcard.trans hc)).trans hsum
  · intro h S hS
    have hc := card_le_card hS
    obtain ⟨U, hU, hcard, he⟩ := prefixMin_attained J S.card hc r
    refine ⟨U, hU, hcard, ?_⟩
    rw [← he]
    exact (h S.card hc).trans (prefixMin_le hc s hS rfl)

end SchrageSRPT.Opt.Proof
end ModuleScope_PrefixMinimum
-- End PrefixMinimum

-- Begin MinimumRegularity
section ModuleScope_MinimumRegularity

open Finset
open scoped NNReal
namespace SchrageSRPT.Opt.Proof

 theorem prefixMin_lipschitz {ι : Type*} [DecidableEq ι] {J : Finset ι}
    {h : ℕ} (hh : h ≤ J.card) {r : ι → ℝ → ℝ}
    (hr : ∀ i ∈ J, LipschitzWith 1 (r i)) :
    LipschitzWith (h : ℝ≥0) (fun t => prefixMin J h hh (fun i => r i t)) := by
  have hbound : ∀ a b : ℝ,
      prefixMin J h hh (fun i => r i a) - prefixMin J h hh (fun i => r i b) ≤
        (h : ℝ) * |a - b| := by
    intro a b
    obtain ⟨S, hS, hc, he⟩ := prefixMin_attained J h hh (fun i => r i b)
    have hle := prefixMin_le hh (fun i => r i a) hS hc
    have hs : (∑ i ∈ S, r i a) - (∑ i ∈ S, r i b) ≤ (h : ℝ) * |a - b| := by
      rw [← sum_sub_distrib]
      calc
        _ ≤ ∑ _i ∈ S, |a - b| := sum_le_sum fun i hi => by
          have hb := (hr i (hS hi)).dist_le_mul a b
          rw [Real.dist_eq, Real.dist_eq] at hb
          norm_num only [NNReal.coe_one, one_mul] at hb
          exact (le_abs_self _).trans hb
        _ = _ := by simp [hc]
    rw [he]
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [Real.dist_eq, Real.dist_eq]
  change |prefixMin J h hh (fun i => r i a) - prefixMin J h hh (fun i => r i b)| ≤
    (h : ℝ) * |a - b|
  exact abs_le.mpr ⟨by have := hbound b a; rw [abs_sub_comm b a] at this; linarith, hbound a b⟩

 theorem prefixMin_antitone {ι : Type*} [DecidableEq ι] {J : Finset ι}
    {h : ℕ} (hh : h ≤ J.card) {r : ι → ℝ → ℝ}
    (hr : ∀ i ∈ J, Antitone (r i)) :
    Antitone (fun t => prefixMin J h hh (fun i => r i t)) := by
  intro a b hab
  apply prefixMin_mono hh
  intro i hi
  exact hr i hi hab

 theorem prefixMin_service_bound {ι : Type*} [DecidableEq ι] {J : Finset ι}
    {h : ℕ} (hh : h ≤ J.card) {r s : ι → ℝ} {d : ℝ}
    (hdec : ∀ S, S ⊆ J → (∑ i ∈ S, (r i - s i)) ≤ d) :
    prefixMin J h hh r - d ≤ prefixMin J h hh s := by
  obtain ⟨S, hS, hc, he⟩ := prefixMin_attained J h hh s
  have hle := prefixMin_le hh r hS hc
  have hd := hdec S hS
  rw [sum_sub_distrib] at hd
  rw [he]
  linarith

end SchrageSRPT.Opt.Proof
end ModuleScope_MinimumRegularity
-- End MinimumRegularity

-- Begin MinimumSelection
section ModuleScope_MinimumSelection

open Finset
namespace SchrageSRPT.Opt.Proof

 theorem prefixMin_attained_containing {ι : Type*} [DecidableEq ι] {J : Finset ι}
    {h : ℕ} (hh : h ≤ J.card) {r : ι → ℝ} {k : ι} (hk : k ∈ J)
    (hpos : 0 < prefixMin J h hh r)
    (hsmall : ∀ i ∈ J, 0 < r i → r k ≤ r i) :
    ∃ S, S ⊆ J ∧ S.card = h ∧ k ∈ S ∧ prefixMin J h hh r = ∑ i ∈ S, r i := by
  classical
  obtain ⟨S, hS, hc, he⟩ := prefixMin_attained J h hh r
  by_cases hks : k ∈ S
  · exact ⟨S, hS, hc, hks, he⟩
  have hex : ∃ j ∈ S, 0 < r j := by
    by_contra hn
    push Not at hn
    have hs : ∑ i ∈ S, r i ≤ 0 := sum_nonpos fun i hi => hn i hi
    rw [← he] at hs
    linarith
  obtain ⟨j, hj, hjpos⟩ := hex
  let U := insert k (S.erase j)
  have hku : k ∉ S.erase j := fun hi => hks (mem_of_mem_erase hi)
  have hU : U ⊆ J := insert_subset hk ((erase_subset _ _).trans hS)
  have hcard : U.card = h := by
    rw [show U = insert k (S.erase j) from rfl, card_insert_of_notMem hku]
    have hce := card_erase_add_one hj
    omega
  have hsum : ∑ i ∈ U, r i ≤ ∑ i ∈ S, r i := by
    rw [show U = insert k (S.erase j) from rfl, sum_insert hku]
    have hs := sum_erase_add S r hj
    have hm := hsmall j (hS hj) hjpos
    linarith
  refine ⟨U, hU, hcard, mem_insert_self _ _, ?_⟩
  exact le_antisymm (prefixMin_le hh r hU hcard) (by simpa only [he] using hsum)

end SchrageSRPT.Opt.Proof
end ModuleScope_MinimumSelection
-- End MinimumSelection

-- Begin MinimumContact
section ModuleScope_MinimumContact

open Finset
namespace SchrageSRPT.Opt.Proof

 theorem prefixMin_deriv_eq_neg_one {ι : Type*} [DecidableEq ι] {J : Finset ι}
    {h : ℕ} (hh : h ≤ J.card) {r : ι → ℝ → ℝ} {t : ℝ} {k : ι}
    (hk : k ∈ J) (hpos : 0 < prefixMin J h hh (fun i => r i t))
    (hsmall : ∀ i ∈ J, 0 < r i t → r k t ≤ r i t)
    (hd : ∀ i ∈ J, HasDerivAt (r i) (if i = k then -1 else 0) t)
    (hF : DifferentiableAt ℝ (fun u => prefixMin J h hh (fun i => r i u)) t) :
    deriv (fun u => prefixMin J h hh (fun i => r i u)) t = -1 := by
  classical
  obtain ⟨S, hS, hc, hks, he⟩ := prefixMin_attained_containing hh hk hpos hsmall
  have hsum : HasDerivAt (fun u => ∑ i ∈ S, r i u) (-1) t := by
    simpa [hks] using (HasDerivAt.fun_sum (u := S) (fun i hi => hd i (hS hi)))
  have hloc : IsLocalMin (fun u => (∑ i ∈ S, r i u) - prefixMin J h hh (fun i => r i u)) t := by
    apply Filter.Eventually.of_forall
    intro u
    change (∑ i ∈ S, r i t) - prefixMin J h hh (fun i => r i t) ≤
      (∑ i ∈ S, r i u) - prefixMin J h hh (fun i => r i u)
    rw [he, sub_self]
    exact sub_nonneg.mpr (prefixMin_le hh _ hS hc)
  have hz := hloc.hasDerivAt_eq_zero (hsum.sub hF.hasDerivAt)
  linarith

end SchrageSRPT.Opt.Proof
end ModuleScope_MinimumContact
-- End MinimumContact

-- Begin MinimumDynamics
section ModuleScope_MinimumDynamics

open Finset MeasureTheory Filter
open scoped Topology NNReal
namespace SchrageSRPT.Opt.Proof

 theorem prefixMin_exact_drop {ι : Type*} [DecidableEq ι] {J : Finset ι}
    {h : ℕ} (hh : h ≤ J.card) {r : ι → ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hrmono : ∀ i ∈ J, Antitone (r i))
    (hrlip : ∀ i ∈ J, LipschitzWith 1 (r i))
    (hselected : ∀ᵐ t : ℝ, a < t → t < b → (∃ i ∈ J, 0 < r i t) →
      ∃ k ∈ J, 0 < r k t ∧ (∀ i ∈ J, 0 < r i t → r k t ≤ r i t) ∧
        ∀ i ∈ J, HasDerivAt (r i) (if i = k then -1 else 0) t)
    (hp : 0 < prefixMin J h hh (fun i => r i b)) :
    prefixMin J h hh (fun i => r i b) = prefixMin J h hh (fun i => r i a) - (b-a) := by
  classical
  let F := fun t => prefixMin J h hh (fun i => r i t)
  have hLip : LipschitzWith (h : ℝ≥0) F := prefixMin_lipschitz hh hrlip
  have hMono : Antitone F := prefixMin_antitone hh hrmono
  have hneB : ∀ᵐ t : ℝ, t ≠ b := by
    simp only [ae_iff, not_not, Set.ofPred_eq_eq_singleton, measure_singleton]
  have hAE : ∀ᵐ t : ℝ, t ∈ Set.uIoc a b → deriv F t = (-1 : ℝ) := by
    filter_upwards [hselected, hLip.ae_differentiableAt_real, hneB] with t ht hdiff hne
    intro hmem
    rw [Set.uIoc_of_le hab] at hmem
    have htb : t < b := lt_of_le_of_ne hmem.2 hne
    have hp' : 0 < F t := lt_of_lt_of_le hp (hMono hmem.2)
    have hex : ∃ i ∈ J, 0 < r i t := by
      obtain ⟨S, hS, _, he⟩ := prefixMin_attained J h hh (fun i => r i t)
      by_contra hn
      push Not at hn
      have hz : ∑ i ∈ S, r i t ≤ 0 := sum_nonpos fun i hi => hn i (hS hi)
      change 0 < prefixMin J h hh (fun i => r i t) at hp'
      rw [he] at hp'
      linarith
    obtain ⟨k, hk, _, hsmall, hd⟩ := ht hmem.1 htb hex
    exact prefixMin_deriv_eq_neg_one hh hk hp' hsmall hd hdiff
  have hi : (∫ t in a..b, deriv F t) = -(b-a) := by
    rw [intervalIntegral.integral_congr_ae hAE]
    simp
  have hac := hLip.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b)
  rw [hac.integral_deriv_eq_sub] at hi
  change F b = F a - (b-a)
  linarith

end SchrageSRPT.Opt.Proof
end ModuleScope_MinimumDynamics
-- End MinimumDynamics

-- Begin PrefixPropagation
section ModuleScope_PrefixPropagation

open Finset MeasureTheory
namespace SchrageSRPT.Opt.Proof

 theorem prefixLE_interval {ι : Type*} [DecidableEq ι] {J : Finset ι}
    {a b : ℝ} (hab : a ≤ b) {r s : ι → ℝ → ℝ}
    (hrnonneg : ∀ i ∈ J, ∀ t, 0 ≤ r i t)
    (hrmono : ∀ i ∈ J, Antitone (r i))
    (hrlip : ∀ i ∈ J, LipschitzWith 1 (r i))
    (hsnonneg : ∀ i ∈ J, 0 ≤ s i b)
    (hsdec : ∀ S, S ⊆ J → (∑ i ∈ S, (s i a - s i b)) ≤ b-a)
    (hselected : ∀ᵐ t : ℝ, a < t → t < b → (∃ i ∈ J, 0 < r i t) →
      ∃ k ∈ J, 0 < r k t ∧ (∀ i ∈ J, 0 < r i t → r k t ≤ r i t) ∧
        ∀ i ∈ J, HasDerivAt (r i) (if i = k then -1 else 0) t)
    (hold : PrefixLE J (fun i => r i a) (fun i => s i a)) :
    PrefixLE J (fun i => r i b) (fun i => s i b) := by
  apply prefixLE_iff_min.mpr
  intro h hh
  have hcomp := prefixMin_service_bound hh hsdec
  have hprev := prefixLE_iff_min.mp hold h hh
  by_cases hp : 0 < prefixMin J h hh (fun i => r i b)
  · rw [prefixMin_exact_drop hh hab hrmono hrlip hselected hp]
    linarith
  · have hz : prefixMin J h hh (fun i => r i b) = 0 :=
      le_antisymm (not_lt.mp hp) (prefixMin_nonneg hh (fun i hi => hrnonneg i hi b))
    rw [hz]
    exact prefixMin_nonneg hh hsnonneg

end SchrageSRPT.Opt.Proof
end ModuleScope_PrefixPropagation
-- End PrefixPropagation

-- Begin NativeInterval
section ModuleScope_NativeInterval

namespace SchrageSRPT.Opt.Proof

lemma native_prefix_interval {A P : ℕ → ℝ} {δs δ : ℕ → ℝ → ℝ}
    (hs : IsSRPT A P δs) (hδ : IsSchedule A δ) (J : Finset ℕ)
    {a b : ℝ} (hab : a ≤ b)
    (hJ : ∀ t, a < t → t < b → ∀ i, A i ≤ t ↔ i ∈ J)
    (hold : PrefixLE J (fun i => clippedRemaining A P δs i a)
      (fun i => clippedRemaining A P δ i a)) :
    PrefixLE J (fun i => clippedRemaining A P δs i b)
      (fun i => clippedRemaining A P δ i b) := by
  exact prefixLE_interval hab (fun i _ t => clipped_nonneg i t)
    (fun i _ => clipped_antitone hs.1 i) (fun i _ => clipped_lipschitz hs.1 i)
    (fun i _ => clipped_nonneg i b) (fun S _ => clipped_sum_loss_le hδ S hab)
    (ae_srpt_selected_derivative hs J a b hJ) hold

end SchrageSRPT.Opt.Proof
end ModuleScope_NativeInterval
-- End NativeInterval

-- Begin ArrivalTimes
section ModuleScope_ArrivalTimes

namespace SchrageSRPT.Opt.Proof

noncomputable def arrived (A : ℕ → ℝ) (hfin : ∀ t : ℝ, {i | A i ≤ t}.Finite)
    (t : ℝ) : Finset ℕ := (hfin t).toFinset

@[simp] lemma mem_arrived (A : ℕ → ℝ) (hfin : ∀ t : ℝ, {i | A i ≤ t}.Finite)
    (i : ℕ) (t : ℝ) : i ∈ arrived A hfin t ↔ A i ≤ t := by
  simp [arrived]

lemma last_arrival (A : ℕ → ℝ) (hfin : ∀ t : ℝ, {i | A i ≤ t}.Finite)
    (T : ℝ) (hJ : (arrived A hfin T).Nonempty) :
    ∃ a b : ℝ, a < b ∧ b ≤ T ∧
      (∀ i, A i ≤ a ↔ A i < b) ∧
      (∀ i, A i ≤ T → A i ≤ b) ∧ (∃ i, A i = b) := by
  classical
  let J := arrived A hfin T
  let B := J.image A
  have hB : B.Nonempty := hJ.image A
  let b := B.max' hB
  have hbmem : b ∈ B := Finset.max'_mem B hB
  obtain ⟨j, hj, hjb⟩ := Finset.mem_image.mp hbmem
  have hbT : b ≤ T := by rw [← hjb]; exact (mem_arrived A hfin j T).mp hj
  have hmax : ∀ i, A i ≤ T → A i ≤ b := by
    intro i hi
    exact Finset.le_max' B (A i) (Finset.mem_image.mpr ⟨i,
      (mem_arrived A hfin i T).mpr hi, rfl⟩)
  let C := B.filter fun x => x < b
  by_cases hC : C.Nonempty
  · let a := C.max' hC
    have hamem : a ∈ C := Finset.max'_mem C hC
    have hab : a < b := (Finset.mem_filter.mp hamem).2
    refine ⟨a, b, hab, hbT, ?_, hmax, j, hjb⟩
    intro i
    constructor
    · intro hi; exact hi.trans_lt hab
    · intro hi
      apply Finset.le_max' C (A i)
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i,
        (mem_arrived A hfin i T).mpr (hi.le.trans hbT), rfl⟩, hi⟩
  · have hnone : ∀ i, ¬ A i < b := by
      intro i hi
      apply hC
      exact ⟨A i, Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i,
        (mem_arrived A hfin i T).mpr (hi.le.trans hbT), rfl⟩, hi⟩⟩
    refine ⟨b - 1, b, by linarith, hbT, ?_, hmax, j, hjb⟩
    intro i
    constructor
    · intro hi; linarith
    · intro hi; exact False.elim (hnone i hi)

lemma arrived_card_lt_of_last {A : ℕ → ℝ} (hfin : ∀ t : ℝ, {i | A i ≤ t}.Finite)
    {a b T : ℝ} (hab : a < b) (hbT : b ≤ T) (hb : ∃ i, A i = b) :
    (arrived A hfin a).card < (arrived A hfin T).card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro i hi
    exact (mem_arrived A hfin i T).mpr (((mem_arrived A hfin i a).mp hi).trans
      (hab.le.trans hbT))
  · intro he
    obtain ⟨i, hi⟩ := hb
    have hmem : i ∈ arrived A hfin T := (mem_arrived A hfin i T).mpr (hi ▸ hbT)
    rw [← he] at hmem
    have := (mem_arrived A hfin i a).mp hmem
    linarith

end SchrageSRPT.Opt.Proof
end ModuleScope_ArrivalTimes
-- End ArrivalTimes

-- Begin ArrivalInduction
section ModuleScope_ArrivalInduction

namespace SchrageSRPT.Opt.Proof

lemma native_prefix_at_time (A P : ℕ → ℝ) (hfin : ∀ t : ℝ, {i | A i ≤ t}.Finite)
    (δs δ : ℕ → ℝ → ℝ) (hs : IsSRPT A P δs) (hδ : IsSchedule A δ) (T : ℝ) :
    PrefixLE (arrived A hfin T) (fun i => clippedRemaining A P δs i T)
      (fun i => clippedRemaining A P δ i T) := by
  classical
  suffices main : ∀ n : ℕ, ∀ t : ℝ, (arrived A hfin t).card = n →
      PrefixLE (arrived A hfin t) (fun i => clippedRemaining A P δs i t)
        (fun i => clippedRemaining A P δ i t) from main _ T rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro t hcard
    by_cases hne : (arrived A hfin t).Nonempty
    · obtain ⟨a, b, hab, hbt, ha, hb, hbe⟩ := last_arrival A hfin t hne
      have hlt : (arrived A hfin a).card < n := by
        rw [← hcard]
        exact arrived_card_lt_of_last hfin hab hbt hbe
      have hold := ih _ hlt a rfl
      have hatb : PrefixLE (arrived A hfin a) (fun i => clippedRemaining A P δs i b)
          (fun i => clippedRemaining A P δ i b) := by
        apply native_prefix_interval hs hδ _ hab.le ?_ hold
        intro u hau hub i
        rw [mem_arrived]
        constructor
        · intro hi; exact (ha i).mpr (hi.trans_lt hub)
        · intro hi; exact hi.trans hau.le
      let H := (arrived A hfin t).filter fun i => A i = b
      have hdisj : Disjoint (arrived A hfin a) H := by
        apply Finset.disjoint_left.mpr
        intro i hi hh
        have hia := (mem_arrived A hfin i a).mp hi
        have hib := (Finset.mem_filter.mp hh).2
        linarith
      have hsplit : arrived A hfin a ∪ H = arrived A hfin t := by
        ext i
        simp only [Finset.mem_union, Finset.mem_filter, H, mem_arrived]
        constructor
        · rintro (hi | ⟨hi, _⟩)
          · exact hi.trans (hab.le.trans hbt)
          · exact hi
        · intro hi
          rcases lt_or_eq_of_le (hb i hi) with hib | hib
          · exact Or.inl ((ha i).mpr hib)
          · exact Or.inr ⟨hi, hib⟩
      have heq : ∀ i ∈ H, clippedRemaining A P δs i b = clippedRemaining A P δ i b := by
        intro i hi
        have hib := (Finset.mem_filter.mp hi).2
        rw [clipped_before_arrival hs.1 i (by linarith),
          clipped_before_arrival hδ i (by linarith)]
      have hnew := prefixLE_union hdisj hatb heq
      rw [hsplit] at hnew
      apply native_prefix_interval hs hδ _ hbt ?_ hnew
      intro u hbu hut i
      rw [mem_arrived]
      constructor
      · intro hi; exact hi.trans hut.le
      · intro hi; exact (hb i hi).trans hbu.le
    · have he : arrived A hfin t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [he]
      intro S hS
      have hSe : S = ∅ := Finset.subset_empty.mp hS
      subst S
      exact ⟨∅, Finset.Subset.refl _, rfl, le_rfl⟩

end SchrageSRPT.Opt.Proof
end ModuleScope_ArrivalInduction
-- End ArrivalInduction

-- Begin RootAssembly
section ModuleScope_RootAssembly

namespace SchrageSRPT.Opt.Proof

lemma native_count_eq (A P : ℕ → ℝ) (hfin : ∀ t : ℝ, {i | A i ≤ t}.Finite)
    (δ : ℕ → ℝ → ℝ) (t : ℝ) :
    numInSystem A P δ t =
      ((arrived A hfin t).filter fun i => 0 < clippedRemaining A P δ i t).card := by
  classical
  have he : inSystem A P δ t =
      ↑((arrived A hfin t).filter fun i => 0 < clippedRemaining A P δ i t) := by
    ext i
    simp [inSystem, clipped_pos_iff]
  rw [numInSystem, he, Set.ncard_coe_finset]

end SchrageSRPT.Opt.Proof

namespace SchrageSRPT.Opt

theorem srpt_optimal (A P : ℕ → ℝ) (hfin : ∀ t : ℝ, {n | A n ≤ t}.Finite)
    (δs δ : ℕ → ℝ → ℝ) (hs : IsSRPT A P δs) (hδ : IsSchedule A δ) :
    ∀ t : ℝ, numInSystem A P δs t ≤ numInSystem A P δ t := by
  intro t
  rw [Proof.native_count_eq A P hfin δs t, Proof.native_count_eq A P hfin δ t]
  exact Proof.prefixLE_positive_card (Proof.native_prefix_at_time A P hfin δs δ hs hδ t)
    (fun i _ => Proof.clipped_nonneg i t) (fun i _ => Proof.clipped_nonneg i t)

end SchrageSRPT.Opt
end ModuleScope_RootAssembly
-- End RootAssembly

-- Begin Solution
section ModuleScope_Solution

open SchrageSRPT.Opt

theorem solution (A P : ℕ → ℝ) (hfin : ∀ t : ℝ, {n | A n ≤ t}.Finite)
    (δs δ : ℕ → ℝ → ℝ) (hs : IsSRPT A P δs) (hδ : IsSchedule A δ) :
    ∀ t : ℝ, numInSystem A P δs t ≤ numInSystem A P δ t := by
  exact SchrageSRPT.Opt.srpt_optimal A P hfin δs δ hs hδ
end ModuleScope_Solution
-- End Solution
