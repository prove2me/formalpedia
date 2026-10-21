-- Prove2me | solution 1 for PuhaWardFluid.Limit.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T10:25:40.300982+00:00
-- url     : https://prove2.me/submissions/508dee50-bec3-47dc-9389-d49dbe07a6f1

import Mathlib
import Definitions.Def_PuhaWardFluid_Limit_Queue

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace PuhaWardFluid.Limit.L7aux

lemma hazard_meas (g : ℝ → ℝ≥0) (hg : Measurable g) : Measurable (hazard g) := by
  unfold hazard
  have hI : Measurable (fun x : ℝ => ∫⁻ y in Set.Icc 0 x, (g y : ℝ≥0∞)) := by
    apply Monotone.measurable
    intro a b hab
    exact lintegral_mono_set (Set.Icc_subset_Icc le_rfl hab)
  have hcdf : Measurable (cdf g) := by
    unfold cdf
    exact ENNReal.measurable_toReal.comp hI
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_le measurable_const measurable_id).inter
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_id) measurable_const)
  · exact (measurable_coe_nnreal_ennreal.comp hg).div
      (ENNReal.measurable_ofReal.comp (measurable_const.sub hcdf))

lemma cdf_props (g : ℝ → ℝ≥0) (hg : ∫⁻ x, (g x : ℝ≥0∞) ≤ 1) :
    Monotone (cdf g) ∧ ∀ r, 0 ≤ cdf g r ∧ cdf g r ≤ 1 := by
  have hle : ∀ r, ∫⁻ y in Set.Icc 0 r, (g y : ℝ≥0∞) ≤ 1 := fun r =>
    (setLIntegral_le_lintegral _ _).trans hg
  have hfin : ∀ r, ∫⁻ y in Set.Icc 0 r, (g y : ℝ≥0∞) ≠ ⊤ := fun r =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (hle r)
  refine ⟨fun a b hab => ?_, fun r => ⟨ENNReal.toReal_nonneg, ?_⟩⟩
  · unfold cdf
    exact ENNReal.toReal_mono (hfin b) (lintegral_mono_set (Set.Icc_subset_Icc le_rfl hab))
  · unfold cdf
    have := ENNReal.toReal_mono ENNReal.one_ne_top (hle r)
    simpa using this

/-- `∫_0^m h < ∞` for `m < H`: on `[0, m]`, `h ≤ g / (1 − G(m))`. -/
lemma hazard_int_fin (g : ℝ → ℝ≥0) (hg : ∫⁻ x, (g x : ℝ≥0∞) ≤ 1) (m : ℝ)
    (hm : ENNReal.ofReal m < edge g) : ∫⁻ x in Set.Icc 0 m, hazard g x < ⊤ := by
  obtain ⟨hmono, h01⟩ := cdf_props g hg
  have hcm : cdf g m < 1 := by
    unfold edge at hm
    obtain ⟨x, hx⟩ := lt_iSup_iff.1 hm
    obtain ⟨⟨hx0, hx1⟩, hx2⟩ := lt_iSup_iff.1 hx
    have : m < x := by
      rcases lt_or_ge m 0 with h | h
      · linarith
      · exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [ENNReal.ofReal_lt_ofReal_iff'.1 hx2])).1
          hx2 |>.le.lt_of_ne (by rintro rfl; exact lt_irrefl _ hx2)
    exact lt_of_le_of_lt (hmono this.le) hx1
  set δ := 1 - cdf g m with hδ
  have hδpos : 0 < δ := by linarith
  have hbound : ∀ x ∈ Set.Icc 0 m, hazard g x ≤ (g x : ℝ≥0∞) * (ENNReal.ofReal δ)⁻¹ := by
    intro x hx
    unfold hazard
    split_ifs
    · rw [div_eq_mul_inv]
      exact mul_le_mul' le_rfl (ENNReal.inv_le_inv.2
        (ENNReal.ofReal_le_ofReal (by linarith [hmono hx.2])))
    · exact bot_le
  calc ∫⁻ x in Set.Icc 0 m, hazard g x
      ≤ ∫⁻ x in Set.Icc 0 m, (g x : ℝ≥0∞) * (ENNReal.ofReal δ)⁻¹ :=
        setLIntegral_mono' measurableSet_Icc hbound
    _ ≤ ∫⁻ x, (g x : ℝ≥0∞) * (ENNReal.ofReal δ)⁻¹ := setLIntegral_le_lintegral _ _
    _ = (∫⁻ x, (g x : ℝ≥0∞)) * (ENNReal.ofReal δ)⁻¹ :=
        lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (by simpa using hδpos))
    _ < ⊤ := ENNReal.mul_lt_top (lt_of_le_of_lt hg ENNReal.one_lt_top)
        (ENNReal.inv_lt_top.2 (by simpa using hδpos))

variable {H : ℝ≥0∞}

lemma atom_coe (z : EReal) :
    (atomAt H z : Measure (Iv H)) =
      if h : z ≠ ⊤ ∧ ((z.toReal.toNNReal : ℝ≥0) : ℝ≥0∞) < H then
        Measure.dirac (⟨z.toReal.toNNReal, h.2⟩ : Iv H) else 0 := by
  by_cases h : z ≠ ⊤ ∧ ((z.toReal.toNNReal : ℝ≥0) : ℝ≥0∞) < H
  · rw [dif_pos h]
    have : atomAt H z = ⟨Measure.dirac (⟨z.toReal.toNNReal, h.2⟩ : Iv H), inferInstance⟩ := by
      unfold atomAt; exact dif_pos h
    rw [this]; rfl
  · rw [dif_neg h]
    have : atomAt H z = 0 := by
      unfold atomAt; exact dif_neg h
    rw [this]; rfl

lemma pair_atom (f : ℝ → ℝ) (z : EReal) :
    pair f (atomAt H z) =
      if z ≠ ⊤ ∧ ((z.toReal.toNNReal : ℝ≥0) : ℝ≥0∞) < H then f (z.toReal.toNNReal : ℝ) else 0 := by
  unfold pair
  rw [atom_coe]
  by_cases h : z ≠ ⊤ ∧ ((z.toReal.toNNReal : ℝ≥0) : ℝ≥0∞) < H
  · rw [dif_pos h, if_pos h, integral_dirac]
  · rw [dif_neg h, if_neg h]
    simp

lemma integrable_atom (f : ℝ → ℝ) (z : EReal) :
    Integrable (fun x : Iv H => f ((x : ℝ≥0) : ℝ)) (atomAt H z : Measure (Iv H)) := by
  rw [atom_coe]
  by_cases h : z ≠ ⊤ ∧ ((z.toReal.toNNReal : ℝ≥0) : ℝ≥0∞) < H
  · rw [dif_pos h]
    exact integrable_dirac (by exact enorm_lt_top)
  · rw [dif_neg h]
    simp

lemma pair_sum {ι : Type*} (s : Finset ι) (ν : ι → FiniteMeasure (Iv H)) (f : ℝ → ℝ)
    (hν : ∀ i ∈ s, Integrable (fun x : Iv H => f ((x : ℝ≥0) : ℝ)) (ν i : Measure (Iv H))) :
    pair f (∑ i ∈ s, ν i) = ∑ i ∈ s, pair f (ν i) := by
  unfold pair
  rw [FiniteMeasure.toMeasure_sum, integral_finsetSum_measure hν]

lemma pair_ite (f : ℝ → ℝ) (p : Prop) [Decidable p] (μ : FiniteMeasure (Iv H)) :
    pair f (if p then μ else 0) = if p then pair f μ else 0 := by
  split_ifs
  · rfl
  · simp [pair]

/-- The `i`-th summand of the compensator integrand. -/
noncomputable def term (H : ℝ≥0∞) (h : ℝ → ℝ≥0∞) (φ : ℝ → ℝ → ℝ) (k v : EReal) (u : ℝ) : ℝ :=
  open Classical in
  if 0 ≤ ((u.toNNReal : ℝ) : EReal) - k ∧ ((u.toNNReal : ℝ) : EReal) - k < v then
    pair (fun x => φ x u * (h x).toReal)
      (atomAt H (min (max (((u.toNNReal : ℝ) : EReal) - k) 0) v))
  else 0

lemma measurable_term (h : ℝ → ℝ≥0∞) (hh : Measurable h) (φ : ℝ → ℝ → ℝ)
    (hφ : Measurable (Function.uncurry φ)) (k v : EReal) :
    Measurable (term H h φ k v) := by
  have he : Monotone (fun u : ℝ => ((u.toNNReal : ℝ) : EReal) - k) := by
    intro a b hab
    exact EReal.sub_le_sub (EReal.coe_le_coe_iff.2 (by exact_mod_cast Real.toNNReal_mono hab)) le_rfl
  have hem := he.measurable
  have hA : Monotone (fun u : ℝ => min (max (((u.toNNReal : ℝ) : EReal) - k) 0) v) :=
    fun a b hab => min_le_min (max_le_max (he hab) le_rfl) le_rfl
  have hAm := hA.measurable
  have hx : Measurable (fun u : ℝ =>
      (((min (max (((u.toNNReal : ℝ) : EReal) - k) 0) v).toReal.toNNReal : ℝ≥0) : ℝ)) :=
    measurable_coe_nnreal_real.comp (measurable_real_toNNReal.comp (measurable_ereal_toReal.comp hAm))
  unfold term
  simp_rw [pair_atom]
  refine Measurable.ite ((measurableSet_le measurable_const hem).inter
    (measurableSet_lt hem measurable_const)) (Measurable.ite ?_ ?_ measurable_const)
    measurable_const
  · refine (hAm (measurableSet_singleton ⊤).compl).inter ?_
    exact measurableSet_lt (measurable_coe_nnreal_ennreal.comp
      (measurable_real_toNNReal.comp (measurable_ereal_toReal.comp hAm))) measurable_const
  · exact (hφ.comp (hx.prodMk measurable_id)).mul
      (ENNReal.measurable_toReal.comp (hh.comp hx))

/-- The pointwise bound on one summand. -/
lemma term_bound (h : ℝ → ℝ≥0∞) (φ : ℝ → ℝ → ℝ) (k v : EReal) (m S : ℝ)
    (hS : ∀ p ∈ markDom H, |φ p.1 p.2| ≤ S)
    (hφs : ∀ p ∈ markDom H, m < p.1 → φ p.1 p.2 = 0) (u : ℝ) (hu : 0 ≤ u) :
    ENNReal.ofReal |term H h φ k v u| ≤
      if k = ⊤ ∨ k = ⊥ then 0
      else ENNReal.ofReal S * (Set.Icc 0 m).indicator h (u - k.toReal) := by
  have huu : ((u.toNNReal : ℝ) : EReal) = (u : EReal) := by rw [Real.coe_toNNReal _ hu]
  unfold term
  rw [huu]
  split_ifs with hc hk
  · exfalso
    rcases hk with hk | hk
    · subst hk; simp at hc
    · subst hk
      have := hc.2
      simp at this
  · -- k finite
    obtain ⟨hk1, hk2⟩ := not_or.1 hk
    lift k to ℝ using ⟨hk1, hk2⟩
    rw [← EReal.coe_sub] at hc ⊢
    have h0 : (0 : ℝ) ≤ u - k := by exact_mod_cast hc.1
    have hmin : min (max ((u - k : ℝ) : EReal) 0) v = ((u - k : ℝ) : EReal) := by
      rw [max_eq_left (by exact_mod_cast h0), min_eq_left hc.2.le]
    rw [hmin, pair_atom]
    simp only [EReal.toReal_coe, ne_eq, EReal.coe_ne_top, not_false_eq_true, true_and]
    rw [Real.coe_toNNReal _ h0]
    split_ifs with hH
    · have hmd : (u - k, u) ∈ markDom H := by
        refine ⟨h0, ?_, hu⟩
        exact hH
      by_cases hm : u - k ≤ m
      · rw [Set.indicator_of_mem (Set.mem_Icc.2 ⟨h0, hm⟩)]
        rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _), abs_of_nonneg ENNReal.toReal_nonneg]
        gcongr
        · exact hS _ hmd
        · exact ENNReal.ofReal_toReal_le
      · rw [hφs _ hmd (lt_of_not_ge hm)]
        simp
    · simp
  · simp
  · simp

/-- The generic pathwise compensator bound behind Lemma 7. -/
lemma generic (h : ℝ → ℝ≥0∞) (hh : Measurable h) (c : ℕ) (E : ℝ≥0 → ℕ) (hE : Monotone E)
    (k v : ℤ → EReal) (μ : ℝ≥0 → FiniteMeasure (Iv H))
    (hμ : ∀ s, μ s = ∑ i ∈ Finset.Ioc (-(c : ℤ)) (E s : ℤ),
      open Classical in
      if 0 ≤ ((s : ℝ) : EReal) - k i ∧ ((s : ℝ) : EReal) - k i < v i
      then atomAt H (min (max (((s : ℝ) : EReal) - k i) 0) (v i)) else 0)
    (m : ℝ) (t : ℝ≥0) (φ : ℝ → ℝ → ℝ) (hm0 : 0 < m) (hmH : ENNReal.ofReal m < H)
    (hφm : Measurable (Function.uncurry φ))
    (hφb : ∃ C : ℝ, ∀ p ∈ markDom H, |φ p.1 p.2| ≤ C)
    (hφs : ∀ p ∈ markDom H, m < p.1 → φ p.1 p.2 = 0)
    (hfin : ∫⁻ x in Set.Icc (0 : ℝ) m, h x < ⊤) :
    IntegrableOn (fun u : ℝ => pair (fun x => φ x u * (h x).toReal) (μ u.toNNReal))
        (Set.Icc 0 t) ∧
      ENNReal.ofReal |∫ u in Set.Icc (0 : ℝ) t, pair (fun x => φ x u * (h x).toReal)
          (μ u.toNNReal)| ≤
        ENNReal.ofReal (supNormOn H φ * ((c : ℝ) + E t)) * ∫⁻ x in Set.Icc (0 : ℝ) m, h x := by
  classical
  obtain ⟨C, hC⟩ := hφb
  set S := supNormOn H φ with hSdef
  have hbdd : BddAbove ((fun p : ℝ × ℝ => |φ p.1 p.2|) '' markDom H) :=
    ⟨C, by rintro _ ⟨p, hp, rfl⟩; exact hC p hp⟩
  have hS : ∀ p ∈ markDom H, |φ p.1 p.2| ≤ S := fun p hp =>
    le_csSup hbdd (Set.mem_image_of_mem _ hp)
  have h00 : ((0 : ℝ), (0 : ℝ)) ∈ markDom H :=
    ⟨le_rfl, lt_of_le_of_lt (by simp) hmH, le_rfl⟩
  have hS0 : 0 ≤ S := (abs_nonneg _).trans (hS _ h00)
  set T := Finset.Ioc (-(c : ℤ)) (E t : ℤ) with hT
  set F := fun u : ℝ => pair (fun x => φ x u * (h x).toReal) (μ u.toNNReal) with hF
  set G := fun u : ℝ => ∑ i ∈ T, if (i : ℤ) ≤ (E u.toNNReal : ℤ) then
    term H h φ (k i) (v i) u else 0 with hG
  have hFG : ∀ u ∈ Set.Icc (0 : ℝ) t, F u = G u := by
    intro u hu
    have hut : u.toNNReal ≤ t := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu.1]; exact hu.2
    simp only [hF, hG, hμ]
    rw [pair_sum _ _ _ (fun i _ => by
      split_ifs
      · exact integrable_atom (fun x => φ x u * (h x).toReal) _
      · simp)]
    rw [← Finset.sum_filter]
    have hfil : T.filter (fun i => i ≤ (E u.toNNReal : ℤ)) =
        Finset.Ioc (-(c : ℤ)) (E u.toNNReal : ℤ) := by
      ext i
      have := hE hut
      simp only [hT, Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans (by exact_mod_cast this)⟩, h2⟩
    rw [hfil]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pair_ite]
    rfl
  have hGm : Measurable G := by
    refine Finset.measurable_sum _ fun i _ => Measurable.ite ?_
      (measurable_term h hh φ hφm (k i) (v i)) measurable_const
    have hmono : Monotone (fun u : ℝ => (E u.toNNReal : ℤ)) := fun a b hab =>
      Int.ofNat_le.2 (hE (Real.toNNReal_mono hab))
    exact hmono.measurable (MeasurableSet.of_discrete (s := {n : ℤ | i ≤ n}))
  -- bound functions
  set b := fun (i : ℤ) (u : ℝ) => if k i = ⊤ ∨ k i = ⊥ then (0 : ℝ≥0∞)
    else ENNReal.ofReal S * (Set.Icc 0 m).indicator h (u - (k i).toReal) with hb
  have hbm : ∀ i, Measurable (b i) := by
    intro i
    simp only [hb]
    split_ifs
    · exact measurable_const
    · exact measurable_const.mul ((hh.indicator measurableSet_Icc).comp
        (measurable_id.sub measurable_const))
  have hbint : ∀ i, ∫⁻ u, b i u ≤ ENNReal.ofReal S * ∫⁻ x in Set.Icc (0 : ℝ) m, h x := by
    intro i
    simp only [hb]
    split_ifs
    · simp
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_sub_right_eq_self (fun x => (Set.Icc 0 m).indicator h x),
        lintegral_indicator measurableSet_Icc]
  have hpt : ∀ u ∈ Set.Icc (0 : ℝ) t, ‖F u‖ₑ ≤ ∑ i ∈ T, b i u := by
    intro u hu
    rw [hFG u hu, Real.enorm_eq_ofReal_abs]
    refine (ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)).trans ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
    refine Finset.sum_le_sum fun i _ => ?_
    split_ifs with hi
    · exact term_bound h φ (k i) (v i) m S hS hφs u hu.1
    · simp
  have hlint : ∫⁻ u in Set.Icc (0 : ℝ) t, ‖F u‖ₑ ≤
      (T.card : ℝ≥0∞) * (ENNReal.ofReal S * ∫⁻ x in Set.Icc (0 : ℝ) m, h x) := by
    calc ∫⁻ u in Set.Icc (0 : ℝ) t, ‖F u‖ₑ
        ≤ ∫⁻ u in Set.Icc (0 : ℝ) t, ∑ i ∈ T, b i u := setLIntegral_mono' measurableSet_Icc hpt
      _ ≤ ∫⁻ u, ∑ i ∈ T, b i u := setLIntegral_le_lintegral _ _
      _ = ∑ i ∈ T, ∫⁻ u, b i u := lintegral_finsetSum _ fun i _ => hbm i
      _ ≤ ∑ i ∈ T, ENNReal.ofReal S * ∫⁻ x in Set.Icc (0 : ℝ) m, h x :=
          Finset.sum_le_sum fun i _ => hbint i
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (T.card : ℝ≥0∞) = ENNReal.ofReal ((c : ℝ) + E t) := by
    rw [hT, Int.card_Ioc]
    have : ((E t : ℤ) - -(c : ℤ)).toNat = c + E t := by omega
    rw [this, ← ENNReal.ofReal_natCast]
    push_cast; ring_nf
  have hRHS : (T.card : ℝ≥0∞) * (ENNReal.ofReal S * ∫⁻ x in Set.Icc (0 : ℝ) m, h x) =
      ENNReal.ofReal (S * ((c : ℝ) + E t)) * ∫⁻ x in Set.Icc (0 : ℝ) m, h x := by
    rw [hcard, ENNReal.ofReal_mul hS0, ← mul_assoc, mul_comm (ENNReal.ofReal ((c : ℝ) + E t))]
  have hFmeas : AEStronglyMeasurable F (volume.restrict (Set.Icc (0 : ℝ) t)) := by
    refine (hGm.aestronglyMeasurable).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact (hFG u hu).symm
  refine ⟨⟨hFmeas, ?_⟩, ?_⟩
  · unfold HasFiniteIntegral
    refine lt_of_le_of_lt hlint ?_
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  · rw [← Real.enorm_eq_ofReal_abs, ← hRHS]
    exact (enorm_integral_le_lintegral_enorm _).trans hlint

end PuhaWardFluid.Limit.L7aux

open PuhaWardFluid.Limit PuhaWardFluid.Limit.L7aux

theorem solution {J : ℕ} (L : ClassLaws J) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Q : QueueSeq J Ω) (N : ℕ+) (hQ : Q.IsHLPolicy L P N) :
    ∀ᵐ ω ∂P, ∀ j : Fin J,
      (∀ (m : ℝ) (t : ℝ≥0) (φ : ℝ → ℝ → ℝ), 0 < m → ENNReal.ofReal m < L.Hs j →
        Measurable (Function.uncurry φ) →
        (∃ C : ℝ, ∀ p ∈ markDom (L.Hs j), |φ p.1 p.2| ≤ C) →
        (∀ p ∈ markDom (L.Hs j), m < p.1 → φ p.1 p.2 = 0) →
        IntegrableOn (fun u : ℝ => pair (fun x => φ x u * (L.hs j x).toReal)
            (Q.nu L N ω u.toNNReal j)) (Set.Icc 0 t) ∧
        ENNReal.ofReal |Q.Acomp_s L N ω φ t j| ≤
          ENNReal.ofReal (supNormOn (L.Hs j) φ * ((Q.x0 N ω j : ℝ) + Q.E N ω t j)) *
            ∫⁻ x in Set.Icc (0 : ℝ) m, L.hs j x) ∧
      (∀ (m : ℝ) (t : ℝ≥0) (ψ : ℝ → ℝ → ℝ), 0 < m → ENNReal.ofReal m < L.Hr j →
        Measurable (Function.uncurry ψ) →
        (∃ C : ℝ, ∀ p ∈ markDom (L.Hr j), |ψ p.1 p.2| ≤ C) →
        (∀ p ∈ markDom (L.Hr j), m < p.1 → ψ p.1 p.2 = 0) →
        IntegrableOn (fun u : ℝ => pair (fun x => ψ x u * (L.hr j x).toReal)
            (Q.eta L N ω u.toNNReal j)) (Set.Icc 0 t) ∧
        ENNReal.ofReal |Q.Acomp_r L N ω ψ t j| ≤
          ENNReal.ofReal (supNormOn (L.Hr j) ψ * ((Q.m0 N ω j : ℝ) + Q.E N ω t j)) *
            ∫⁻ x in Set.Icc (0 : ℝ) m, L.hr j x) := by
  filter_upwards [hQ.1.1] with ω hω
  intro j
  refine ⟨fun m t φ hm0 hmH hφm hφb hφs => ?_, fun m t ψ hm0 hmH hψm hψb hψs => ?_⟩
  · exact generic (L.hs j) (hazard_meas _ (L.gs_meas j)) (Q.x0 N ω j) (fun s => Q.E N ω s j)
      (hω j).1 (Q.entry N ω j) (Q.serv L N ω j) (fun s => Q.nu L N ω s j) (fun s => rfl)
      m t φ hm0 hmH hφm hφb hφs
      (hazard_int_fin _ (le_of_eq (L.gs_total j)) m hmH)
  · exact generic (L.hr j) (hazard_meas _ (L.gr_meas j)) (Q.m0 N ω j) (fun s => Q.E N ω s j)
      (hω j).1 (Q.arr N ω j) (Q.pat L N ω j) (fun s => Q.eta L N ω s j) (fun s => rfl)
      m t ψ hm0 hmH hψm hψb hψs
      (hazard_int_fin _ (L.gr_total j) m hmH)
