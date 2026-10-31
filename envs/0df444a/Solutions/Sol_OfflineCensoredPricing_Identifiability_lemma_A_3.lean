-- Prove2me | solution 1 for OfflineCensoredPricing.Identifiability.lemma_A_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T18:21:30.823005+00:00
-- url     : https://prove2.me/submissions/51ee51b7-aa4c-48a6-bcd5-c087264e2d5a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OfflineCensoredPricing_Identifiability_lemma_A_2

open MeasureTheory ProbabilityTheory Set

namespace OCPLemA3Aux

/-- The empirical c.d.f. -/
noncomputable def Fn {n : ℕ} (ω : Fin n → ℝ) (x : ℝ) : ℝ :=
  ((Finset.univ.filter (fun j => ω j ≤ x)).card : ℝ) / (n : ℝ)

/-- The empirical measure of a set. -/
noncomputable def Pn {n : ℕ} (ω : Fin n → ℝ) (s : Set ℝ) : ℝ :=
  (∑ j, s.indicator (fun _ => (1 : ℝ)) (ω j)) / (n : ℝ)

section Intervals

variable (μ : Measure ℝ) [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n) (ω : Fin n → ℝ)
  (δ : ℝ) (hD : ∀ x, |Fn ω x - cdf μ x| ≤ δ)

lemma Pn_Iic (c : ℝ) : Pn ω (Iic c) = Fn ω c := by
  unfold Pn Fn
  congr 1
  rw [Finset.natCast_card_filter]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : ω j ≤ c
  · rw [indicator_of_mem (show ω j ∈ Iic c from h), if_pos h]
  · rw [indicator_of_notMem (show ω j ∉ Iic c from h), if_neg h]

lemma Pn_compl (hn : 0 < n) (s : Set ℝ) : Pn ω sᶜ = 1 - Pn ω s := by
  unfold Pn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have : ∀ j, sᶜ.indicator (fun _ => (1 : ℝ)) (ω j) = 1 - s.indicator (fun _ => (1 : ℝ)) (ω j) := by
    intro j
    by_cases h : ω j ∈ s
    · rw [indicator_of_notMem (show ω j ∉ sᶜ from fun h' => h' h), indicator_of_mem h]; ring
    · rw [indicator_of_mem (show ω j ∈ sᶜ from h), indicator_of_notMem h]; ring
  simp_rw [this]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  field_simp

include hn hD

lemma b_Iic (c : ℝ) : |Pn ω (Iic c) - μ.real (Iic c)| ≤ δ := by
  have := hD c
  rw [cdf_eq_real] at this
  rw [Pn_Iic]
  exact this

lemma b_Ioi (c : ℝ) : |Pn ω (Ioi c) - μ.real (Ioi c)| ≤ δ := by
  have h := b_Iic μ hn ω δ hD c
  rw [← compl_Iic, Pn_compl ω hn, probReal_compl_eq_one_sub measurableSet_Iic]
  rw [abs_sub_comm] at h
  rwa [show 1 - Pn ω (Iic c) - (1 - μ.real (Iic c)) = μ.real (Iic c) - Pn ω (Iic c) by ring]

lemma b_Iio (c : ℝ) : |Pn ω (Iio c) - μ.real (Iio c)| ≤ δ := by
  set x : ℕ → ℝ := fun k => c - 1 / ((k : ℝ) + 1) with hx
  have hxc : ∀ k, x k < c := by
    intro k
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    simp only [hx]; linarith
  have hmono : Monotone (fun k => Iic (x k)) := by
    intro k k' h
    apply Iic_subset_Iic.2
    simp only [hx]
    have : 1 / ((k' : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right h 1)
    linarith
  have hU : (⋃ k, Iic (x k)) = Iio c := by
    ext z; simp only [mem_iUnion, mem_Iic, mem_Iio]
    constructor
    · rintro ⟨k, hk⟩; exact lt_of_le_of_lt hk (hxc k)
    · intro hz
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hz)
      exact ⟨k, by simp only [hx]; linarith⟩
  -- the true measure converges
  have hT : Filter.Tendsto (fun k => μ.real (Iic (x k))) Filter.atTop (nhds (μ.real (Iio c))) := by
    have := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hU] at this
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this
  -- the empirical measure is eventually constant
  have hE : ∀ᶠ k in Filter.atTop, Pn ω (Iic (x k)) = Pn ω (Iio c) := by
    have key : ∀ k, (∀ j, ω j < c → ω j ≤ x k) → Pn ω (Iic (x k)) = Pn ω (Iio c) := by
      intro k hk
      unfold Pn
      congr 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases h : ω j < c
      · rw [indicator_of_mem (show ω j ∈ Iic (x k) from hk j h),
          indicator_of_mem (show ω j ∈ Iio c from h)]
      · have h' : ω j ∉ Iic (x k) := fun h' => h (lt_of_le_of_lt h' (hxc k))
        rw [indicator_of_notMem h', indicator_of_notMem (show ω j ∉ Iio c from h)]
    by_cases hne : (Finset.univ.filter (fun j => ω j < c)).Nonempty
    · obtain ⟨j0, hj0, hmax⟩ := Finset.exists_max_image _ ω hne
      have hj0' : ω j0 < c := by simpa using hj0
      obtain ⟨K, hK⟩ := exists_nat_one_div_lt (sub_pos.2 hj0')
      refine Filter.eventually_atTop.2 ⟨K, fun k hk => key k (fun j hj => ?_)⟩
      have hk' : 1 / ((k : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
      have := hmax j (by simpa using hj)
      simp only [hx]; linarith
    · refine Filter.Eventually.of_forall (fun k => key k (fun j hj => ?_))
      exact absurd ⟨j, by simpa using hj⟩ hne
  have hlim : Filter.Tendsto (fun k => Pn ω (Iic (x k)) - μ.real (Iic (x k))) Filter.atTop
      (nhds (Pn ω (Iio c) - μ.real (Iio c))) := by
    refine Filter.Tendsto.sub ?_ hT
    exact tendsto_const_nhds.congr' (hE.mono (fun k h => h.symm))
  exact le_of_tendsto hlim.abs (Filter.Eventually.of_forall (fun k => b_Iic μ hn ω δ hD (x k)))

lemma b_Ici (c : ℝ) : |Pn ω (Ici c) - μ.real (Ici c)| ≤ δ := by
  have h := b_Iio μ hn ω δ hD c
  rw [← compl_Iio, Pn_compl ω hn, probReal_compl_eq_one_sub measurableSet_Iio]
  rw [abs_sub_comm] at h
  rwa [show 1 - Pn ω (Iio c) - (1 - μ.real (Iio c)) = μ.real (Iio c) - Pn ω (Iio c) by ring]

lemma b_empty : |Pn ω (∅ : Set ℝ) - μ.real ∅| ≤ δ := by
  have := le_trans (abs_nonneg _) (hD 0)
  simpa [Pn] using this

lemma b_univ : |Pn ω (univ : Set ℝ) - μ.real univ| ≤ δ := by
  have := le_trans (abs_nonneg _) (hD 0)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have : Pn ω univ = 1 := by
    unfold Pn; simp [hn']
  rw [this, probReal_univ, sub_self, abs_zero]
  exact le_trans (abs_nonneg _) (hD 0)

end Intervals


/-! ### Upper and lower sets inside `X` are traces of intervals -/

def Good (J : Set ℝ) : Prop :=
  J = ∅ ∨ J = univ ∨ (∃ c, J = Iic c) ∨ (∃ c, J = Iio c) ∨ (∃ c, J = Ioi c) ∨ (∃ c, J = Ici c)

lemma rep_up (X A : Set ℝ) (hup : ∀ x x', x ∈ X → x' ∈ X → x ≤ x' → x ∈ A → x' ∈ A) :
    ∃ J, Good J ∧ A ∩ X = J ∩ X := by
  set B := A ∩ X with hB
  by_cases hne : B.Nonempty
  · by_cases hbdd : BddBelow B
    · set c := sInf B with hc
      by_cases hcB : c ∈ B
      · refine ⟨Ici c, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨c, rfl⟩)))), ?_⟩
        ext x
        simp only [mem_inter_iff, mem_Ici]
        constructor
        · rintro ⟨hxA, hxX⟩; exact ⟨csInf_le hbdd ⟨hxA, hxX⟩, hxX⟩
        · rintro ⟨hcx, hxX⟩; exact ⟨hup c x hcB.2 hxX hcx hcB.1, hxX⟩
      · refine ⟨Ioi c, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, rfl⟩)))), ?_⟩
        ext x
        simp only [mem_inter_iff, mem_Ioi]
        constructor
        · rintro ⟨hxA, hxX⟩
          refine ⟨lt_of_le_of_ne (csInf_le hbdd ⟨hxA, hxX⟩) ?_, hxX⟩
          rintro rfl; exact hcB ⟨hxA, hxX⟩
        · rintro ⟨hcx, hxX⟩
          obtain ⟨b, hb, hbx⟩ := exists_lt_of_csInf_lt hne hcx
          exact ⟨hup b x hb.2 hxX hbx.le hb.1, hxX⟩
    · refine ⟨univ, Or.inr (Or.inl rfl), ?_⟩
      ext x
      simp only [mem_inter_iff, mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro hxX
        rw [not_bddBelow_iff] at hbdd
        obtain ⟨b, hb, hbx⟩ := hbdd x
        exact ⟨hup b x hb.2 hxX hbx.le hb.1, hxX⟩
  · refine ⟨∅, Or.inl rfl, ?_⟩
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, empty_inter]

lemma rep_down (X A : Set ℝ) (hdown : ∀ x x', x ∈ X → x' ∈ X → x' ≤ x → x ∈ A → x' ∈ A) :
    ∃ J, Good J ∧ A ∩ X = J ∩ X := by
  set B := A ∩ X with hB
  by_cases hne : B.Nonempty
  · by_cases hbdd : BddAbove B
    · set c := sSup B with hc
      by_cases hcB : c ∈ B
      · refine ⟨Iic c, Or.inr (Or.inr (Or.inl ⟨c, rfl⟩)), ?_⟩
        ext x
        simp only [mem_inter_iff, mem_Iic]
        constructor
        · rintro ⟨hxA, hxX⟩; exact ⟨le_csSup hbdd ⟨hxA, hxX⟩, hxX⟩
        · rintro ⟨hcx, hxX⟩; exact ⟨hdown c x hcB.2 hxX hcx hcB.1, hxX⟩
      · refine ⟨Iio c, Or.inr (Or.inr (Or.inr (Or.inl ⟨c, rfl⟩))), ?_⟩
        ext x
        simp only [mem_inter_iff, mem_Iio]
        constructor
        · rintro ⟨hxA, hxX⟩
          refine ⟨lt_of_le_of_ne (le_csSup hbdd ⟨hxA, hxX⟩) ?_, hxX⟩
          rintro rfl; exact hcB ⟨hxA, hxX⟩
        · rintro ⟨hcx, hxX⟩
          obtain ⟨b, hb, hbx⟩ := exists_lt_of_lt_csSup hne hcx
          exact ⟨hdown b x hb.2 hxX hbx.le hb.1, hxX⟩
    · refine ⟨univ, Or.inr (Or.inl rfl), ?_⟩
      ext x
      simp only [mem_inter_iff, mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro hxX
        rw [not_bddAbove_iff] at hbdd
        obtain ⟨b, hb, hbx⟩ := hbdd x
        exact ⟨hdown b x hb.2 hxX hbx.le hb.1, hxX⟩
  · refine ⟨∅, Or.inl rfl, ?_⟩
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, empty_inter]

lemma b_good (μ : Measure ℝ) [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n) (ω : Fin n → ℝ)
    (δ : ℝ) (hD : ∀ x, |Fn ω x - cdf μ x| ≤ δ) (J : Set ℝ) (hJ : Good J) :
    |Pn ω J - μ.real J| ≤ δ := by
  rcases hJ with rfl | rfl | ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact b_empty μ hn ω δ hD
  · exact b_univ μ hn ω δ hD
  · exact b_Iic μ hn ω δ hD c
  · exact b_Iio μ hn ω δ hD c
  · exact b_Ioi μ hn ω δ hD c
  · exact b_Ici μ hn ω δ hD c

/-! ### The core inequality: `|P_n g − P g| ≤ M · sup |F_n − F|` for monotone `g` -/

lemma core (μ : Measure ℝ) [IsProbabilityMeasure μ] (X : Set ℝ) (hX : ∀ᵐ x ∂μ, x ∈ X)
    (g : ℝ → ℝ) (hg : Measurable g) (M : ℝ) (hM : 0 < M) (hgX : ∀ x ∈ X, g x ∈ Icc 0 M)
    (hmono : MonotoneOn g X ∨ AntitoneOn g X) {n : ℕ} (hn : 0 < n) (ω : Fin n → ℝ)
    (hω : ∀ j, ω j ∈ X) (δ : ℝ) (hD : ∀ x, |Fn ω x - cdf μ x| ≤ δ) :
    |(∑ j, g (ω j)) / (n : ℝ) - ∫ x, g x ∂μ| ≤ M * δ := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hae0 : 0 ≤ᵐ[μ] g := by
    filter_upwards [hX] with x hx; exact (hgX x hx).1
  have haeM : g ≤ᵐ[μ] (fun _ => M) := by
    filter_upwards [hX] with x hx; exact (hgX x hx).2
  have hint : Integrable g μ := by
    refine Integrable.of_bound hg.aestronglyMeasurable M ?_
    filter_upwards [hX] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hgX x hx).1]; exact (hgX x hx).2
  -- layer cake for the true law
  have hL1 := hint.integral_eq_integral_Ioc_meas_le hae0 haeM
  -- layer cake for the empirical law
  have hind : ∀ a, 0 ≤ a → a ≤ M →
      ∫ t in Ioc 0 M, (Iic a).indicator (fun _ => (1 : ℝ)) t = a := by
    intro a ha0 haM
    rw [integral_indicator_const _ measurableSet_Iic, smul_eq_mul, mul_one,
      measureReal_restrict_apply measurableSet_Iic]
    rw [show Iic a ∩ Ioc 0 M = Ioc 0 a by
      ext t; simp only [mem_inter_iff, mem_Iic, mem_Ioc]; constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, le_trans h2 haM⟩]
    rw [Real.volume_real_Ioc_of_le ha0, sub_zero]
  have hindint : ∀ a, IntegrableOn ((Iic a).indicator (fun _ => (1 : ℝ))) (Ioc 0 M) :=
    fun a => (integrableOn_const (by simp)).indicator measurableSet_Iic
  have hL2 : (∑ j, g (ω j)) / (n : ℝ) =
      ∫ t in Ioc 0 M, (∑ j, (Iic (g (ω j))).indicator (fun _ => (1 : ℝ)) t) / (n : ℝ) := by
    rw [integral_div, integral_finsetSum _ (fun j _ => hindint _)]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact (hind _ (hgX _ (hω j)).1 (hgX _ (hω j)).2).symm
  rw [hL1, hL2, ← integral_sub]
  rotate_left
  · exact (integrable_finsetSum _ (fun j _ => hindint _)).div_const _
  · refine Integrable.of_bound ?_ 1 ?_
    · apply Measurable.aestronglyMeasurable
      refine Measurable.ennreal_toReal ?_
      exact Antitone.measurable (fun _ _ hst => measure_mono (fun _ h => le_trans hst h))
    · refine Filter.Eventually.of_forall (fun t => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  have hvol : (volume : Measure ℝ).real (Ioc 0 M) = M := by
    rw [Real.volume_real_Ioc_of_le hM.le, sub_zero]
  rw [← Real.norm_eq_abs]
  refine le_trans (norm_setIntegral_le_of_norm_le_const (C := δ)
    (measure_Ioc_lt_top (μ := (volume : Measure ℝ))) (fun t ht => ?_)) (le_of_eq (by rw [hvol]; ring))
  rw [Real.norm_eq_abs]
  -- the integrand at level `t`
  set A := {a : ℝ | t ≤ g a} with hA
  have hPn : (∑ j, (Iic (g (ω j))).indicator (fun _ => (1 : ℝ)) t) / (n : ℝ) = Pn ω A := by
    unfold Pn
    rfl
  rw [hPn]
  obtain ⟨J, hJ, hAJ⟩ : ∃ J, Good J ∧ A ∩ X = J ∩ X := by
    rcases hmono with hm | hm
    · exact rep_up X A (fun x x' hx hx' hxx' hxA => le_trans hxA (hm hx hx' hxx'))
    · exact rep_down X A (fun x x' hx hx' hxx' hxA => le_trans hxA (hm hx' hx hxx'))
  have hmem : ∀ x ∈ X, (x ∈ A ↔ x ∈ J) := by
    intro x hx
    constructor
    · intro h; have : x ∈ A ∩ X := ⟨h, hx⟩; rw [hAJ] at this; exact this.1
    · intro h; have : x ∈ J ∩ X := ⟨h, hx⟩; rw [← hAJ] at this; exact this.1
  have e1 : Pn ω A = Pn ω J := by
    unfold Pn
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : ω j ∈ A
    · rw [indicator_of_mem h, indicator_of_mem ((hmem _ (hω j)).1 h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h ((hmem _ (hω j)).2 h'))]
  have e2 : μ.real A = μ.real J := by
    unfold Measure.real
    congr 1
    apply measure_congr
    filter_upwards [hX] with x hx
    exact propext (hmem x hx)
  rw [e1, e2]
  exact b_good μ hn ω δ hD J hJ

end OCPLemA3Aux

open OCPLemA3Aux in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (X Y : Set ℝ) (hX : ∀ᵐ x ∂μ, x ∈ X)
    (f : ℝ → ℝ → ℝ) (hfm : ∀ y ∈ Y, Measurable (fun x => f x y)) {L U : ℝ}
    (hf : ∀ x ∈ X, ∀ y ∈ Y, f x y ∈ Set.Icc L U)
    (hmono : ∀ y ∈ Y, MonotoneOn (fun x => f x y) X ∨ AntitoneOn (fun x => f x y) X)
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Measure.pi (fun _ : Fin n => μ)
        {ω | ∃ y ∈ Y, ε < |(∑ i, f (ω i) y) / (n : ℝ) - ∫ x, f x y ∂μ|} ≤
      ENNReal.ofReal (2 * Real.exp (-(2 * (n : ℝ) * ε ^ 2 / (U - L) ^ 2))) := by
  set E := {ω : Fin n → ℝ | ∃ y ∈ Y, ε < |(∑ i, f (ω i) y) / (n : ℝ) - ∫ x, f x y ∂μ|} with hE
  -- the trivial regime: the bound is at least `1`
  have triv : 1 ≤ 2 * Real.exp (-(2 * (n : ℝ) * ε ^ 2 / (U - L) ^ 2)) →
      Measure.pi (fun _ : Fin n => μ) E ≤
        ENNReal.ofReal (2 * Real.exp (-(2 * (n : ℝ) * ε ^ 2 / (U - L) ^ 2))) := by
    intro h
    refine le_trans prob_le_one ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal h
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · apply triv; subst hn0; simp
  by_cases hLU : L < U
  swap
  · -- either `Y` is empty (no event) or `L = U` (trivial bound)
    by_cases hY : Y.Nonempty
    · obtain ⟨y, hy⟩ := hY
      have hXne : ∃ x, x ∈ X := by
        haveI : (ae μ).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero μ)
        exact hX.exists
      obtain ⟨x, hx⟩ := hXne
      have := hf x hx y hy
      have hUL : U = L := le_antisymm (by push_neg at hLU; exact hLU) (le_trans this.1 this.2)
      apply triv
      rw [hUL, sub_self]; simp
    · have : E = ∅ := by
        ext ω; simp only [hE, mem_setOf_eq, mem_empty_iff_false, iff_false]
        rintro ⟨y, hy, -⟩; exact hY ⟨y, hy⟩
      rw [this, measure_empty]; exact bot_le
  -- main case
  set δ := ε / (U - L) with hδ
  have hδp : 0 < δ := div_pos hε (sub_pos.2 hLU)
  set B := {ω : Fin n → ℝ | ∃ x : ℝ,
      δ < |((Finset.univ.filter (fun j => ω j ≤ x)).card : ℝ) / (n : ℝ) - cdf μ x|} with hB
  set C := ⋃ j : Fin n, (Function.eval j) ⁻¹' {x : ℝ | x ∉ X} with hC
  have hsub : E ⊆ B ∪ C := by
    rintro ω ⟨y, hy, hlt⟩
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    obtain ⟨nB, nC⟩ := hnot
    have hω : ∀ j, ω j ∈ X := by
      intro j; by_contra h; exact nC (mem_iUnion.2 ⟨j, h⟩)
    have hD : ∀ x, |Fn ω x - cdf μ x| ≤ δ := by
      intro x; by_contra h; push_neg at h; exact nB ⟨x, h⟩
    set g : ℝ → ℝ := fun x => f x y - L with hg
    have hgX : ∀ x ∈ X, g x ∈ Icc 0 (U - L) := by
      intro x hx; have := hf x hx y hy
      exact ⟨by simp only [hg]; linarith [this.1], by simp only [hg]; linarith [this.2]⟩
    have hgm : MonotoneOn g X ∨ AntitoneOn g X := by
      rcases hmono y hy with h | h
      · left; intro a ha b hb hab; simp only [hg]; linarith [h ha hb hab]
      · right; intro a ha b hb hab; simp only [hg]; linarith [h ha hb hab]
    have hc := core μ X hX g ((hfm y hy).sub_const L) (U - L) (sub_pos.2 hLU) hgX hgm hn ω hω δ hD
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hintf : Integrable (fun x => f x y) μ := by
      refine Integrable.of_bound (hfm y hy).aestronglyMeasurable (|L| + |U|) ?_
      filter_upwards [hX] with x hx
      have := hf x hx y hy
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [this.1, this.2, neg_abs_le L, le_abs_self U, abs_nonneg L,
        abs_nonneg U]
    have e1 : (∑ j, g (ω j)) / (n : ℝ) = (∑ j, f (ω j) y) / (n : ℝ) - L := by
      simp only [hg]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp
    have e2 : ∫ x, g x ∂μ = ∫ x, f x y ∂μ - L := by
      simp only [hg]
      rw [integral_sub hintf (integrable_const L), integral_const]; simp
    rw [e1, e2, show (∑ j, f (ω j) y) / (n : ℝ) - L - (∫ x, f x y ∂μ - L) =
      (∑ j, f (ω j) y) / (n : ℝ) - ∫ x, f x y ∂μ by ring] at hc
    have : (U - L) * δ = ε := by
      have hne : U - L ≠ 0 := (sub_pos.2 hLU).ne'
      rw [hδ]; field_simp
    linarith
  have hCnull : Measure.pi (fun _ : Fin n => μ) C = 0 := by
    rw [hC]
    refine measure_iUnion_null (fun j => ?_)
    have hmp : MeasurePreserving (Function.eval j) (Measure.pi (fun _ : Fin n => μ)) μ :=
      measurePreserving_eval _ j
    refine le_antisymm (le_trans (Measure.le_map_apply hmp.measurable.aemeasurable _) ?_)
      bot_le
    rw [hmp.map_eq]
    exact le_of_eq (ae_iff.1 hX)
  have hBb := OfflineCensoredPricing.Identifiability.lemma_A_2 μ n hδp
  calc Measure.pi (fun _ : Fin n => μ) E ≤ Measure.pi (fun _ : Fin n => μ) (B ∪ C) :=
        measure_mono hsub
    _ ≤ Measure.pi (fun _ : Fin n => μ) B + Measure.pi (fun _ : Fin n => μ) C :=
        measure_union_le _ _
    _ = Measure.pi (fun _ : Fin n => μ) B := by rw [hCnull, add_zero]
    _ ≤ _ := by
        refine le_trans hBb (le_of_eq ?_)
        congr 3
        rw [hδ]; field_simp
