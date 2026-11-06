-- Prove2me | solution 1 for WhittFLT.Composition.theorem_3_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T13:38:17.4462+00:00
-- url     : https://prove2.me/submissions/99d07730-abf5-4cf2-83c1-b514fb032cb5

import Mathlib
import Theorems.Thm_WhittFLT_Composition_billingsley_lemma_1

open WhittFLT.Composition
open Set Filter Topology
open scoped ENNReal

namespace WhittL22

variable {S : Type*} [MetricSpace S]

/-- an increasing homeomorphism `[p,q] → [u,v]` (described by endpoint values). -/
def IsHom (p q u v : ℝ) (f : ℝ → ℝ) : Prop :=
  StrictMonoOn f (Icc p q) ∧ ContinuousOn f (Icc p q) ∧ f p = u ∧ f q = v

lemma image_Icc_of (p q : ℝ) (hpq : p ≤ q) (f : ℝ → ℝ) (hm : StrictMonoOn f (Icc p q))
    (hc : ContinuousOn f (Icc p q)) : f '' Icc p q = Icc (f p) (f q) := by
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    exact ⟨hm.monotoneOn ⟨le_rfl, hpq⟩ ht ht.1, hm.monotoneOn ht ⟨hpq, le_rfl⟩ ht.2⟩
  · exact intermediate_value_Icc hpq hc

lemma isHom_of_tc (a b : ℝ) (hab : a ≤ b) (l : ℝ → ℝ) (h : IsTimeChange a b l) :
    IsHom a b a b l := by
  obtain ⟨hm, hc, him⟩ := h
  rw [image_Icc_of a b hab l hm hc] at him
  have h1 := (Icc_eq_Icc_iff (hm.monotoneOn ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)).1 him
  exact ⟨hm, hc, h1.1, h1.2⟩

lemma tc_of_isHom (a b : ℝ) (hab : a ≤ b) (l : ℝ → ℝ) (h : IsHom a b a b l) :
    IsTimeChange a b l := by
  obtain ⟨hm, hc, ha, hb⟩ := h
  refine ⟨hm, hc, ?_⟩
  rw [image_Icc_of a b hab l hm hc, ha, hb]

lemma isHom_restrict_left {p r u w : ℝ} {f : ℝ → ℝ} (h : IsHom p r u w f) (q : ℝ) (hq : q ≤ r) :
    IsHom p q u (f q) f :=
  ⟨h.1.mono (Icc_subset_Icc le_rfl hq), h.2.1.mono (Icc_subset_Icc le_rfl hq), h.2.2.1, rfl⟩

lemma isHom_restrict_right {p r u w : ℝ} {f : ℝ → ℝ} (h : IsHom p r u w f) (q : ℝ) (hq : p ≤ q) :
    IsHom q r (f q) w f :=
  ⟨h.1.mono (Icc_subset_Icc hq le_rfl), h.2.1.mono (Icc_subset_Icc hq le_rfl), rfl, h.2.2.2⟩

/-- linear map from `[p,q]` to `[u,v]`. -/
noncomputable def lin (p q u v : ℝ) (t : ℝ) : ℝ := u + (v - u) * ((t - p) / (q - p))

lemma isHom_lin (p q u v : ℝ) (hpq : p < q) (huv : u < v) : IsHom p q u v (lin p q u v) := by
  have hqp : 0 < q - p := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s _ t _ hst
    unfold lin
    have : (s - p) / (q - p) < (t - p) / (q - p) := div_lt_div_of_pos_right (by linarith) hqp
    nlinarith
  · unfold lin; fun_prop
  · unfold lin; simp
  · unfold lin; rw [div_self hqp.ne']; ring

lemma lin_sub_left (p q u v t : ℝ) (hpq : p < q) :
    lin p q u v t - t = (u - p) * ((q - t) / (q - p)) + (v - q) * ((t - p) / (q - p)) := by
  unfold lin
  have hqp : q - p ≠ 0 := by linarith [sub_pos.2 hpq]
  field_simp
  ring

/-- gluing two increasing homeomorphisms. -/
noncomputable def glue (q : ℝ) (f g : ℝ → ℝ) (t : ℝ) : ℝ := if t ≤ q then f t else g t

lemma isHom_glue {p q r u v w : ℝ} {f g : ℝ → ℝ} (hpq : p ≤ q) (hqr : q ≤ r)
    (hf : IsHom p q u v f) (hg : IsHom q r v w g) : IsHom p r u w (glue q f g) := by
  obtain ⟨fm, fc, fp, fq⟩ := hf
  obtain ⟨gm, gc, gq, gr⟩ := hg
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs t ht hst
    unfold glue
    by_cases h1 : t ≤ q
    · have h2 : s ≤ q := hst.le.trans h1
      rw [if_pos h1, if_pos h2]
      exact fm ⟨hs.1, h2⟩ ⟨ht.1, h1⟩ hst
    · rw [if_neg h1]
      push_neg at h1
      by_cases h2 : s ≤ q
      · rw [if_pos h2]
        calc f s ≤ f q := fm.monotoneOn ⟨hs.1, h2⟩ ⟨hpq, le_rfl⟩ h2
          _ = g q := by rw [fq, gq]
          _ < g t := gm ⟨le_rfl, hqr⟩ ⟨h1.le, ht.2⟩ h1
      · rw [if_neg h2]
        push_neg at h2
        exact gm ⟨h2.le, hs.2⟩ ⟨h1.le, ht.2⟩ hst
  · have hU : Icc p r = Icc p q ∪ Icc q r := (Icc_union_Icc_eq_Icc hpq hqr).symm
    rw [hU]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · refine fc.congr ?_
      intro t ht; unfold glue; rw [if_pos ht.2]
    · refine gc.congr ?_
      intro t ht; unfold glue
      by_cases h : t ≤ q
      · rw [if_pos h]; have : t = q := le_antisymm h ht.1
        subst this; rw [fq, gq]
      · rw [if_neg h]
  · unfold glue; rw [if_pos hpq, fp]
  · unfold glue
    by_cases h : r ≤ q
    · rw [if_pos h]; have : r = q := le_antisymm h hqr
      subst this; rw [fq, ← gr, gq]
    · rw [if_neg h, gr]

lemma supDist_le_of {E : Type*} [PseudoMetricSpace E] (a b : ℝ) (f g : ℝ → E) (r : ℝ)
    (h : ∀ t ∈ Icc a b, dist (f t) (g t) ≤ r) : supDist a b f g ≤ ENNReal.ofReal r := by
  unfold supDist
  refine iSup₂_le fun t ht => ?_
  rw [edist_dist]; exact ENNReal.ofReal_le_ofReal (h t ht)

lemma j1Dist_le_of (a b : ℝ) (xs x : ℝ → S) (l : ℝ → ℝ) (hl : IsTimeChange a b l) (r : ℝ)
    (h : ∀ t ∈ Icc a b, dist (l t) t ≤ r ∧ dist (xs t) (x (l t)) ≤ r) :
    j1Dist a b xs x ≤ ENNReal.ofReal r := by
  unfold j1Dist
  refine (iInf₂_le l hl).trans ?_
  refine max_le ?_ ?_
  · exact supDist_le_of a b l id r fun t ht => (h t ht).1
  · exact supDist_le_of a b xs (x ∘ l) r fun t ht => (h t ht).2

lemma exists_of_j1Dist_lt (a b : ℝ) (xs x : ℝ → S) (r : ℝ)
    (h : j1Dist a b xs x < ENNReal.ofReal r) :
    ∃ l, IsTimeChange a b l ∧ ∀ t ∈ Icc a b, dist (l t) t < r ∧ dist (xs t) (x (l t)) < r := by
  unfold j1Dist at h
  rw [iInf_lt_iff] at h
  obtain ⟨l, hl⟩ := h
  rw [iInf_lt_iff] at hl
  obtain ⟨hlt, hl⟩ := hl
  refine ⟨l, hlt, fun t ht => ⟨?_, ?_⟩⟩
  · have : edist (l t) (id t) < ENNReal.ofReal r :=
      lt_of_le_of_lt (le_trans (le_iSup₂ (f := fun t _ => edist (l t) (id t)) t ht)
        (le_max_left _ _)) hl
    rw [edist_dist] at this
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).1 this
  · have : edist (xs t) ((x ∘ l) t) < ENNReal.ofReal r :=
      lt_of_le_of_lt (le_trans (le_iSup₂ (f := fun t _ => edist (xs t) ((x ∘ l) t)) t ht)
        (le_max_right _ _)) hl
    rw [edist_dist] at this
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).1 this

lemma tendsto_zero_iff_real (f : ℕ → ℝ≥0∞) :
    Tendsto f atTop (𝓝 0) ↔ ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, f n < ENNReal.ofReal η := by
  constructor
  · intro h η hη
    exact (tendsto_order.1 h).2 _ (ENNReal.ofReal_pos.2 hη)
  · intro h
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    by_cases htop : ε = ⊤
    · exact Eventually.of_forall fun n => htop ▸ le_top
    · have hpos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
      filter_upwards [h _ hpos] with n hn
      rw [ENNReal.ofReal_toReal htop] at hn
      exact hn.le

/-- gluing direction. -/
lemma glue_dir (a b c : ℝ) (hab : a < b) (hbc : b < c) (xs : ℕ → ℝ → S) (x : ℝ → S)
    (h1 : J1TendstoOn a b xs x) (h2 : J1TendstoOn b c xs x) : J1TendstoOn a c xs x := by
  unfold J1TendstoOn at *
  rw [tendsto_zero_iff_real] at *
  intro η hη
  filter_upwards [h1 (η / 2) (by linarith), h2 (η / 2) (by linarith)] with n hn1 hn2
  obtain ⟨l1, hl1, hb1⟩ := exists_of_j1Dist_lt a b (xs n) x _ hn1
  obtain ⟨l2, hl2, hb2⟩ := exists_of_j1Dist_lt b c (xs n) x _ hn2
  have H1 := isHom_of_tc a b hab.le l1 hl1
  have H2 := isHom_of_tc b c hbc.le l2 hl2
  have hl := tc_of_isHom a c (hab.trans hbc).le _ (isHom_glue hab.le hbc.le H1 H2)
  refine lt_of_le_of_lt (j1Dist_le_of a c (xs n) x _ hl (η / 2) ?_)
    ((ENNReal.ofReal_lt_ofReal_iff hη).2 (by linarith))
  intro t ht
  unfold glue
  by_cases h : t ≤ b
  · rw [if_pos h]; exact ⟨(hb1 t ⟨ht.1, h⟩).1.le, (hb1 t ⟨ht.1, h⟩).2.le⟩
  · rw [if_neg h]; push_neg at h
    exact ⟨(hb2 t ⟨h.le, ht.2⟩).1.le, (hb2 t ⟨h.le, ht.2⟩).2.le⟩

/-- restriction to the left piece. -/
lemma restrict_left (a b c : ℝ) (hab : a < b) (hbc : b < c) (xs : ℕ → ℝ → S) (x : ℝ → S)
    (hb : ContinuousAt x b) (h : J1TendstoOn a c xs x) : J1TendstoOn a b xs x := by
  unfold J1TendstoOn at *
  rw [tendsto_zero_iff_real] at *
  intro η hη
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.1 hb (η / 4) (by linarith)
  set hh := min (δ / 2) ((b - a) / 2) with hhdef
  have hh0 : 0 < hh := lt_min (by linarith) (by linarith)
  have hhδ : hh ≤ δ / 2 := min_le_left _ _
  have hhb : hh ≤ (b - a) / 2 := min_le_right _ _
  set r := min (η / 4) (hh / 2) with hrdef
  have hr0 : 0 < r := lt_min (by linarith) (by linarith)
  have hrη : r ≤ η / 4 := min_le_left _ _
  have hrh : r ≤ hh / 2 := min_le_right _ _
  set p := b - hh with hp
  filter_upwards [h r hr0] with n hn
  obtain ⟨l, hl, hbd⟩ := exists_of_j1Dist_lt a c (xs n) x r hn
  have H := isHom_of_tc a c (hab.trans hbc).le l hl
  have hpc : p ≤ c := by linarith
  have hlp := hbd p ⟨by linarith, hpc⟩
  have hlp1 := hlp.1
  rw [Real.dist_eq, abs_lt] at hlp1
  have hlpb : l p < b := by linarith
  have HL := isHom_restrict_left H p hpc
  have Hlin := isHom_lin p b (l p) b (by linarith) hlpb
  have HG := isHom_glue (by linarith) (by linarith) HL Hlin
  have hm := tc_of_isHom a b hab.le _ HG
  refine lt_of_le_of_lt (j1Dist_le_of a b (xs n) x _ hm (3 * (η / 4)) ?_)
    ((ENNReal.ofReal_lt_ofReal_iff hη).2 (by linarith))
  intro t ht
  unfold glue
  by_cases htp : t ≤ p
  · rw [if_pos htp]
    have := hbd t ⟨ht.1, by linarith [ht.2]⟩
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · rw [if_neg htp]; push_neg at htp
    have htc : t ∈ Icc a c := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hbt := hbd t htc
    have hpb : p < b := by linarith
    have hs0 : 0 ≤ (b - t) / (b - p) := div_nonneg (by linarith [ht.2]) (by linarith)
    have hs1 : (b - t) / (b - p) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    have ht0 : 0 ≤ (t - p) / (b - p) := div_nonneg (by linarith) (by linarith)
    have ht1 : (t - p) / (b - p) ≤ 1 := (div_le_one (by linarith)).2 (by linarith [ht.2])
    have hlin := lin_sub_left p b (l p) b t hpb
    simp only [sub_self, zero_mul, add_zero] at hlin
    -- bound on |μ t - t|
    have hμ : |lin p b (l p) b t - t| ≤ r := by
      rw [hlin, abs_mul]
      have : |(b - t) / (b - p)| ≤ 1 := by rw [abs_of_nonneg hs0]; exact hs1
      have h2 : |l p - p| < r := by rw [abs_lt]; constructor <;> linarith
      calc |l p - p| * |(b - t) / (b - p)| ≤ |l p - p| * 1 :=
            mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ ≤ r := by linarith
    refine ⟨?_, ?_⟩
    · rw [Real.dist_eq]; linarith
    · -- triangle via x b
      have hlt := hbt.1
      rw [Real.dist_eq, abs_lt] at hlt
      have e1 : dist (l t) b < δ := by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.2]
      have e2 : dist (lin p b (l p) b t) b < δ := by
        rw [abs_le] at hμ
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.2, hμ.1, hμ.2]
      have d1 := hcont e1
      have d2 := hcont e2
      calc dist (xs n t) (x (lin p b (l p) b t))
          ≤ dist (xs n t) (x (l t)) + dist (x (l t)) (x b) + dist (x b) (x (lin p b (l p) b t)) :=
            dist_triangle4 _ _ _ _
        _ ≤ 3 * (η / 4) := by rw [dist_comm (x b)]; linarith [hbt.2]

/-- restriction to the right piece. -/
lemma restrict_right (a b c : ℝ) (hab : a < b) (hbc : b < c) (xs : ℕ → ℝ → S) (x : ℝ → S)
    (hb : ContinuousAt x b) (h : J1TendstoOn a c xs x) : J1TendstoOn b c xs x := by
  unfold J1TendstoOn at *
  rw [tendsto_zero_iff_real] at *
  intro η hη
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.1 hb (η / 4) (by linarith)
  set hh := min (δ / 2) ((c - b) / 2) with hhdef
  have hh0 : 0 < hh := lt_min (by linarith) (by linarith)
  have hhδ : hh ≤ δ / 2 := min_le_left _ _
  have hhb : hh ≤ (c - b) / 2 := min_le_right _ _
  set r := min (η / 4) (hh / 2) with hrdef
  have hr0 : 0 < r := lt_min (by linarith) (by linarith)
  have hrη : r ≤ η / 4 := min_le_left _ _
  have hrh : r ≤ hh / 2 := min_le_right _ _
  set q := b + hh with hq
  filter_upwards [h r hr0] with n hn
  obtain ⟨l, hl, hbd⟩ := exists_of_j1Dist_lt a c (xs n) x r hn
  have H := isHom_of_tc a c (hab.trans hbc).le l hl
  have haq : a ≤ q := by linarith
  have hlq := hbd q ⟨haq, by linarith⟩
  have hlq1 := hlq.1
  rw [Real.dist_eq, abs_lt] at hlq1
  have hlqb : b < l q := by linarith
  have HR := isHom_restrict_right H q haq
  have Hlin := isHom_lin b q b (l q) (by linarith) hlqb
  have HG := isHom_glue (by linarith) (by linarith) Hlin HR
  have hm := tc_of_isHom b c hbc.le _ HG
  refine lt_of_le_of_lt (j1Dist_le_of b c (xs n) x _ hm (3 * (η / 4)) ?_)
    ((ENNReal.ofReal_lt_ofReal_iff hη).2 (by linarith))
  intro t ht
  unfold glue
  by_cases htq : t ≤ q
  · rw [if_pos htq]
    have htc : t ∈ Icc a c := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hbt := hbd t htc
    have hbq : b < q := by linarith
    have hs0 : 0 ≤ (q - t) / (q - b) := div_nonneg (by linarith) (by linarith)
    have ht0 : 0 ≤ (t - b) / (q - b) := div_nonneg (by linarith [ht.1]) (by linarith)
    have ht1 : (t - b) / (q - b) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    have hlin := lin_sub_left b q b (l q) t hbq
    simp only [sub_self, zero_mul, zero_add] at hlin
    have hμ : |lin b q b (l q) t - t| ≤ r := by
      rw [hlin, abs_mul]
      have : |(t - b) / (q - b)| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1
      have h2 : |l q - q| < r := by rw [abs_lt]; constructor <;> linarith
      calc |l q - q| * |(t - b) / (q - b)| ≤ |l q - q| * 1 :=
            mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ ≤ r := by linarith
    refine ⟨?_, ?_⟩
    · rw [Real.dist_eq]; linarith
    · have hlt := hbt.1
      rw [Real.dist_eq, abs_lt] at hlt
      have e1 : dist (l t) b < δ := by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1]
      have e2 : dist (lin b q b (l q) t) b < δ := by
        rw [abs_le] at hμ
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, hμ.1, hμ.2]
      have d1 := hcont e1
      have d2 := hcont e2
      calc dist (xs n t) (x (lin b q b (l q) t))
          ≤ dist (xs n t) (x (l t)) + dist (x (l t)) (x b) + dist (x b) (x (lin b q b (l q) t)) :=
            dist_triangle4 _ _ _ _
        _ ≤ 3 * (η / 4) := by rw [dist_comm (x b)]; linarith [hbt.2]
  · rw [if_neg htq]; push_neg at htq
    have := hbd t ⟨by linarith [ht.1], ht.2⟩
    exact ⟨by linarith [this.1], by linarith [this.2]⟩

lemma tendsto_zero_of_le (f : ℕ → ℝ≥0∞)
    (h : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, f n ≤ ENNReal.ofReal η) : Tendsto f atTop (𝓝 0) := by
  rw [tendsto_zero_iff_real]
  intro η hη
  filter_upwards [h (η / 2) (by linarith)] with n hn
  exact lt_of_le_of_lt hn ((ENNReal.ofReal_lt_ofReal_iff hη).2 (by linarith))

lemma cadlag_comp {T₁ T₂ T₃ : Set ℝ} (hT₂ : T₂.OrdConnected) (hT₂₃ : T₂ ⊆ T₃)
    {f : ℝ → S} {g : ℝ → ℝ} (hf : IsCadlagOn T₃ f) (hg : IsCadlagOn T₁ g)
    (hgm : MonotoneOn g T₁) (hgT : MapsTo g T₁ T₂) : IsCadlagOn T₁ (f ∘ g) := by
  intro t ht
  have hgt : g t ∈ T₃ := hT₂₃ (hgT ht)
  refine ⟨?_, ?_⟩
  · refine ContinuousWithinAt.comp (hf (g t) hgt).1 (hg t ht).1 ?_
    intro s hs
    exact ⟨hT₂₃ (hgT hs.1), hgm ht hs.1 hs.2⟩
  · obtain ⟨L, hL⟩ := (hg t ht).2
    by_cases hne : (𝓝[T₁ ∩ Iio t] t).NeBot
    · have hle : ∀ s ∈ T₁, s < t → g s ≤ L := by
        intro s hs hst
        apply ge_of_tendsto hL
        have : Ioi s ∈ 𝓝[T₁ ∩ Iio t] t := mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hst)
        filter_upwards [this, self_mem_nhdsWithin] with s' h1 h2
        exact hgm hs h2.1 (le_of_lt h1)
      have hLt : L ≤ g t := by
        apply le_of_tendsto hL
        filter_upwards [self_mem_nhdsWithin] with s' h2
        exact hgm h2.1 ht (le_of_lt h2.2)
      obtain ⟨s₀, hs₀⟩ : (T₁ ∩ Iio t).Nonempty := hne.nonempty_of_mem self_mem_nhdsWithin
      have hLT : L ∈ T₃ := hT₂₃ (hT₂.out (hgT hs₀.1) (hgT ht) ⟨hle s₀ hs₀.1 hs₀.2, hLt⟩)
      by_cases hA : ∃ s ∈ T₁, s < t ∧ g s = L
      · obtain ⟨s, hs, hst, hgs⟩ := hA
        refine ⟨f L, ?_⟩
        apply tendsto_const_nhds.congr'
        have : Ioi s ∈ 𝓝[T₁ ∩ Iio t] t := mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hst)
        filter_upwards [this, self_mem_nhdsWithin] with s' h1 h2
        have : g s' = L := le_antisymm (hle s' h2.1 h2.2) (hgs ▸ hgm hs h2.1 (le_of_lt h1))
        simp [this]
      · push_neg at hA
        obtain ⟨l, hl⟩ := (hf L hLT).2
        refine ⟨l, hl.comp ?_⟩
        rw [tendsto_nhdsWithin_iff]
        refine ⟨hL, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with s' h2
        exact ⟨hT₂₃ (hgT h2.1), lt_of_le_of_ne (hle s' h2.1 h2.2) (hA s' h2.1 h2.2)⟩
    · rw [not_neBot] at hne
      exact ⟨f t, by rw [hne]; exact tendsto_bot⟩

lemma tc_id (a : ℝ) : IsTimeChange a a id :=
  ⟨fun _ _ _ _ h => h, continuousOn_id, by simp⟩

lemma j1_point (t : ℝ) (zs : ℕ → ℝ → S) (z : ℝ → S)
    (h : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, dist (zs n t) (z t) ≤ η) : J1TendstoOn t t zs z := by
  unfold J1TendstoOn
  apply tendsto_zero_of_le
  intro η hη
  filter_upwards [h η hη] with n hn
  apply j1Dist_le_of t t (zs n) z id (tc_id t) η
  intro s hs
  have : s = t := le_antisymm hs.2 hs.1
  subst this
  exact ⟨by simp [hη.le], hn⟩

lemma pointwise_of_j1 (a b : ℝ) (zs : ℕ → ℝ → S) (z : ℝ → S) (h : J1TendstoOn a b zs z)
    (t : ℝ) (ht : t ∈ Icc a b) (hc : ContinuousAt z t) :
    ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, dist (zs n t) (z t) ≤ η := by
  intro η hη
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.1 hc (η / 2) (by linarith)
  unfold J1TendstoOn at h
  rw [tendsto_zero_iff_real] at h
  filter_upwards [h (min δ (η / 2)) (lt_min hδ (by linarith))] with n hn
  obtain ⟨l, _, hbd⟩ := exists_of_j1Dist_lt a b (zs n) z _ hn
  have h1 := (hbd t ht).1
  have h2 := (hbd t ht).2
  have e : dist (l t) t < δ := lt_of_lt_of_le h1 (min_le_left _ _)
  have := hcont e
  calc dist (zs n t) (z t) ≤ dist (zs n t) (z (l t)) + dist (z (l t)) (z t) :=
        dist_triangle _ _ _
    _ ≤ η := by linarith [min_le_right δ (η / 2)]

lemma unif_conv_of_cont (L R : ℝ) (xs : ℕ → ℝ → S) (x : ℝ → S)
    (hx : ContinuousOn x (Icc L R)) (h : J1TendstoOn L R xs x) :
    ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ u ∈ Icc L R, dist (xs n u) (x u) < η := by
  intro η hη
  have huc := (isCompact_Icc.uniformContinuousOn_of_continuous hx)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hd⟩ := huc (η / 2) (by linarith)
  unfold J1TendstoOn at h
  rw [tendsto_zero_iff_real] at h
  filter_upwards [h (min δ (η / 2)) (lt_min hδ (by linarith))] with n hn
  obtain ⟨l, hl, hbd⟩ := exists_of_j1Dist_lt L R (xs n) x _ hn
  intro u hu
  have hlu : l u ∈ Icc L R := by rw [← hl.2.2]; exact mem_image_of_mem l hu
  have e := hd (l u) hlu u hu (lt_of_lt_of_le (hbd u hu).1 (min_le_left _ _))
  calc dist (xs n u) (x u) ≤ dist (xs n u) (x (l u)) + dist (x (l u)) (x u) :=
        dist_triangle _ _ _
    _ < η := by linarith [(hbd u hu).2, min_le_right δ (η / 2)]


lemma cadlag_mono {T T' : Set ℝ} {x : ℝ → S} (hx : IsCadlagOn T x) (h : T' ⊆ T) :
    IsCadlagOn T' x := by
  intro t ht
  obtain ⟨h1, l, hl⟩ := hx t (h ht)
  exact ⟨h1.mono (inter_subset_inter_left _ h), l,
    hl.mono_left (nhdsWithin_mono _ (inter_subset_inter_left _ h))⟩

lemma exists_pos_forall {ι : Type*} [Fintype ι] (P : ι → ℝ → Prop)
    (hP : ∀ i r r', 0 < r' → r' ≤ r → P i r → P i r') (h : ∀ i, ∃ r > 0, P i r) :
    ∃ r > 0, ∀ i, P i r := by
  choose f hf hPf using h
  by_cases hne : Nonempty ι
  · refine ⟨Finset.univ.inf' Finset.univ_nonempty f, ?_, fun i => ?_⟩
    · show 0 < _
      rw [Finset.lt_inf'_iff]; intro i _; exact hf i
    · refine hP i (f i) _ ?_ (Finset.inf'_le _ (Finset.mem_univ i)) (hPf i)
      rw [Finset.lt_inf'_iff]; intro i _; exact hf i
  · exact ⟨1, one_pos, fun i => absurd ⟨i⟩ hne⟩

lemma find_piece (k : ℕ) (u : Fin (k + 1) → ℝ) (hu : StrictMono u) (t : ℝ)
    (ht : t ∈ Ico (u 0) (u (Fin.last k))) :
    ∃ j : Fin k, u j.castSucc ≤ t ∧ t < u j.succ := by
  induction k with
  | zero => exact absurd ht.2 (not_lt.2 (by simp [Fin.last]; exact ht.1))
  | succ k ih =>
    by_cases h : t < u (Fin.castSucc (Fin.last k))
    · obtain ⟨j, hj1, hj2⟩ := ih (u ∘ Fin.castSucc) (hu.comp Fin.strictMono_castSucc)
        ⟨by simpa using ht.1, by simpa using h⟩
      refine ⟨j.castSucc, by simpa using hj1, ?_⟩
      rw [Fin.succ_castSucc]; simpa using hj2
    · push_neg at h
      exact ⟨Fin.last k, h, by rw [Fin.succ_last]; exact ht.2⟩

lemma interp (k : ℕ) (u v : Fin (k + 1) → ℝ) (hu : StrictMono u) (hv : StrictMono v)
    (ρ : ℝ) (hρ : ∀ j, |u j - v j| ≤ ρ) :
    ∃ f : ℝ → ℝ, IsHom (u 0) (u (Fin.last k)) (v 0) (v (Fin.last k)) f ∧
      (∀ j, f (u j) = v j) ∧ ∀ t ∈ Icc (u 0) (u (Fin.last k)), |f t - t| ≤ ρ := by
  induction k with
  | zero =>
    refine ⟨fun t => t + (v 0 - u 0), ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro s _ t _ hst; simp only; linarith
    · fun_prop
    · ring
    · simp [Fin.last]
    · intro j; rw [Fin.fin_one_eq_zero j]; ring
    · intro t _; have := hρ 0; rw [abs_sub_comm] at this; simpa using this
  | succ k ih =>
    obtain ⟨f, hf, hfu, hfb⟩ := ih (u ∘ Fin.castSucc) (v ∘ Fin.castSucc)
      (hu.comp Fin.strictMono_castSucc) (hv.comp Fin.strictMono_castSucc) (fun j => hρ _)
    simp only [Function.comp, Fin.castSucc_zero] at hf hfu hfb
    set p := u (Fin.castSucc (Fin.last k))
    set q := u (Fin.last (k + 1))
    have hpq : p < q := hu (by rw [Fin.lt_def]; simp)
    have hvv : v (Fin.castSucc (Fin.last k)) < v (Fin.last (k + 1)) := hv (by rw [Fin.lt_def]; simp)
    have hl := isHom_lin p q (v (Fin.castSucc (Fin.last k))) (v (Fin.last (k + 1))) hpq hvv
    have h0p : u 0 ≤ p := hu.monotone (Fin.zero_le _)
    refine ⟨glue p f (lin p q (v (Fin.castSucc (Fin.last k))) (v (Fin.last (k + 1)))),
      isHom_glue h0p hpq.le hf hl, ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · unfold glue; rw [if_neg (not_le.2 hpq)]; exact hl.2.2.2
      · unfold glue
        rw [if_pos (hu.monotone (Fin.castSucc_le_castSucc_iff.2 (Fin.le_last i)))]
        exact hfu i
    · intro t ht
      unfold glue
      by_cases htp : t ≤ p
      · rw [if_pos htp]; exact hfb t ⟨ht.1, htp⟩
      · rw [if_neg htp]; push_neg at htp
        rw [lin_sub_left _ _ _ _ _ hpq]
        have w1 : 0 ≤ (q - t) / (q - p) := div_nonneg (by linarith [ht.2]) (by linarith)
        have w2 : 0 ≤ (t - p) / (q - p) := div_nonneg (by linarith) (by linarith)
        have hsum : (q - t) / (q - p) + (t - p) / (q - p) = 1 := by
          rw [← add_div, show q - t + (t - p) = q - p by ring]; exact div_self (sub_pos.2 hpq).ne'
        have e1 := hρ (Fin.castSucc (Fin.last k))
        have e2 := hρ (Fin.last (k + 1))
        rw [abs_sub_comm] at e1 e2
        calc |(v (Fin.castSucc (Fin.last k)) - p) * ((q - t) / (q - p)) +
              (v (Fin.last (k + 1)) - q) * ((t - p) / (q - p))|
            ≤ |v (Fin.castSucc (Fin.last k)) - p| * ((q - t) / (q - p)) +
              |v (Fin.last (k + 1)) - q| * ((t - p) / (q - p)) := by
              refine (abs_add_le _ _).trans ?_
              rw [abs_mul, abs_mul, abs_of_nonneg w1, abs_of_nonneg w2]
          _ ≤ ρ * ((q - t) / (q - p)) + ρ * ((t - p) / (q - p)) := by
              gcongr
          _ = ρ := by rw [← mul_add, hsum, mul_one]

lemma exists_cont_point (x : ℝ → S) (p q : ℝ) (hpq : p < q) (hx : IsCadlagOn (Icc p q) x) :
    ∃ u ∈ Ioo p q, ContinuousAt x u := by
  have hB : ∀ k : ℕ, ∃ (n : ℕ) (t : Fin (n + 1) → ℝ), t 0 = p ∧ t (Fin.last n) = q ∧
      StrictMono t ∧ ∀ j : Fin n, (⨆ s₁ ∈ Ico (t j.castSucc) (t j.succ),
        ⨆ s₂ ∈ Ico (t j.castSucc) (t j.succ), edist (x s₁) (x s₂)) <
          ENNReal.ofReal (1 / ((k : ℝ) + 1)) :=
    fun k => billingsley_lemma_1 p q hpq x hx _ (by positivity)
  choose N t ht0 htl htm hto using hB
  have hcount : (⋃ k, Set.range (t k)).Countable :=
    countable_iUnion fun k => (Set.finite_range _).countable
  obtain ⟨u, hu1, hu2⟩ :=
    (hcount.dense_compl ℝ).inter_open_nonempty (Ioo p q) isOpen_Ioo (nonempty_Ioo.2 hpq)
  refine ⟨u, hu1, ?_⟩
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨j, hj1, hj2⟩ := find_piece (N k) (t k) (htm k) u
    ⟨by rw [ht0]; exact hu1.1.le, by rw [htl]; exact hu1.2⟩
  have hne : t k j.castSucc ≠ u := fun h => hu2 (mem_iUnion.2 ⟨k, j.castSucc, h⟩)
  have hj1' : t k j.castSucc < u := lt_of_le_of_ne hj1 hne
  refine ⟨min (u - t k j.castSucc) (t k j.succ - u), lt_min (by linarith) (by linarith), ?_⟩
  intro v hv
  rw [Real.dist_eq, abs_lt] at hv
  have hv1 : v ∈ Ico (t k j.castSucc) (t k j.succ) :=
    ⟨by linarith [min_le_left (u - t k j.castSucc) (t k j.succ - u)],
      by linarith [min_le_right (u - t k j.castSucc) (t k j.succ - u)]⟩
  have hu' : u ∈ Ico (t k j.castSucc) (t k j.succ) := ⟨hj1, hj2⟩
  have := lt_of_le_of_lt (le_trans (le_iSup₂ (f := fun s₂ _ => edist (x v) (x s₂)) u hu')
    (le_iSup₂ (f := fun s₁ _ => ⨆ s₂ ∈ Ico (t k j.castSucc)
      (t k j.succ), edist (x s₁) (x s₂)) v hv1)) (hto k j)
  rw [edist_lt_ofReal] at this
  linarith

lemma lower3 (T : Set ℝ) (x : ℝ → S) (hx : IsCadlagOn T x) (hT : T.OrdConnected)
    (c : ℝ) (hc : c ∈ T) :
    ∃ c' ∈ T, c' ≤ c ∧ (ContinuousWithinAt x T c' ∨ IsEndpoint T c') ∧
      ∃ m > 0, ∀ u ∈ T, c - m < u → c' ≤ u := by
  by_cases h : ∃ s ∈ T, s < c
  · obtain ⟨s, hs, hsc⟩ := h
    obtain ⟨c', hc'1, hc'2⟩ := exists_cont_point x s c hsc (cadlag_mono hx (hT.out hs hc))
    exact ⟨c', hT.out hs hc (Ioo_subset_Icc_self hc'1), hc'1.2.le,
      Or.inl hc'2.continuousWithinAt, c - c', by linarith [hc'1.2], fun u _ hu => by linarith⟩
  · push_neg at h
    exact ⟨c, hc, le_rfl, Or.inr (Or.inl ⟨hc, fun u hu => h u hu⟩), 1, one_pos,
      fun u hu _ => h u hu⟩

lemma upper3 (T : Set ℝ) (x : ℝ → S) (hx : IsCadlagOn T x) (hT : T.OrdConnected)
    (c : ℝ) (hc : c ∈ T) :
    ∃ c' ∈ T, c ≤ c' ∧ (ContinuousWithinAt x T c' ∨ IsEndpoint T c') ∧
      ∃ m > 0, ∀ u ∈ T, u < c + m → u ≤ c' := by
  by_cases h : ∃ s ∈ T, c < s
  · obtain ⟨s, hs, hsc⟩ := h
    obtain ⟨c', hc'1, hc'2⟩ := exists_cont_point x c s hsc (cadlag_mono hx (hT.out hc hs))
    exact ⟨c', hT.out hc hs (Ioo_subset_Icc_self hc'1), hc'1.1.le,
      Or.inl hc'2.continuousWithinAt, c' - c, by linarith [hc'1.1], fun u _ hu => by linarith⟩
  · push_neg at h
    exact ⟨c, hc, le_rfl, Or.inr (Or.inr ⟨hc, fun u hu => h u hu⟩), 1, one_pos,
      fun u hu _ => h u hu⟩

lemma cont_of_comp {T₁ T₃ : Set ℝ} (hT₁ : T₁.OrdConnected) (y : ℝ → ℝ)
    (hyc : ContinuousOn y T₁) (hym : StrictMonoOn y T₁) (x : ℝ → S) (a : ℝ) (haT : a ∈ T₁)
    (ha : ContinuousWithinAt (x ∘ y) T₁ a ∨ IsEndpoint T₁ a)
    (hB : ∀ t, IsEndpoint T₁ t → ContinuousWithinAt x T₃ (y t)) :
    ContinuousWithinAt x T₃ (y a) := by
  by_cases hE : IsEndpoint T₁ a
  · exact hB a hE
  · have hc : ContinuousWithinAt (x ∘ y) T₁ a := ha.resolve_right hE
    obtain ⟨hnl, hng⟩ := not_or.1 hE
    have : ∃ s ∈ T₁, s < a := by
      by_contra hcon; push_neg at hcon; exact hnl ⟨haT, fun u hu => hcon u hu⟩
    obtain ⟨s, hs, hsa⟩ := this
    have : ∃ s ∈ T₁, a < s := by
      by_contra hcon; push_neg at hcon; exact hng ⟨haT, fun u hu => hcon u hu⟩
    obtain ⟨s', hs', has'⟩ := this
    have hnhds : T₁ ∈ 𝓝 a :=
      mem_of_superset (Ioo_mem_nhds hsa has') (Ioo_subset_Icc_self.trans (hT₁.out hs hs'))
    have hca : ContinuousAt (x ∘ y) a := hc.continuousAt hnhds
    apply ContinuousAt.continuousWithinAt
    rw [Metric.continuousAt_iff] at hca ⊢
    intro ε hε
    obtain ⟨δ0, hδ0, hd0⟩ := hca ε hε
    set h := min δ0 (min (a - s) (s' - a)) / 2 with hh
    have hh0 : 0 < h := by
      have : 0 < min δ0 (min (a - s) (s' - a)) := lt_min hδ0 (lt_min (by linarith) (by linarith))
      linarith
    have hh1 : h < δ0 := by
      have := min_le_left δ0 (min (a - s) (s' - a)); linarith
    have hh2 : h < a - s := by
      have := min_le_right δ0 (min (a - s) (s' - a))
      have := min_le_left (a - s) (s' - a); linarith
    have hh3 : h < s' - a := by
      have := min_le_right δ0 (min (a - s) (s' - a))
      have := min_le_right (a - s) (s' - a); linarith
    have hpT : a - h ∈ T₁ := hT₁.out hs haT ⟨by linarith, by linarith⟩
    have hqT : a + h ∈ T₁ := hT₁.out haT hs' ⟨by linarith, by linarith⟩
    have hsubpq : Icc (a - h) (a + h) ⊆ T₁ := hT₁.out hpT hqT
    have hyp : y (a - h) < y a := hym hpT haT (by linarith)
    have hyq : y a < y (a + h) := hym haT hqT (by linarith)
    refine ⟨min (y a - y (a - h)) (y (a + h) - y a), lt_min (by linarith) (by linarith), ?_⟩
    intro u hu
    rw [Real.dist_eq, abs_lt] at hu
    have hu' : u ∈ Icc (y (a - h)) (y (a + h)) :=
      ⟨by linarith [min_le_left (y a - y (a - h)) (y (a + h) - y a)],
        by linarith [min_le_right (y a - y (a - h)) (y (a + h) - y a)]⟩
    obtain ⟨t, ht, rfl⟩ := intermediate_value_Icc (by linarith) (hyc.mono hsubpq) hu'
    have : dist t a < δ0 := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2]
    exact hd0 this

lemma key_K (a b : ℝ) (hab : a < b) (y : ℝ → ℝ) (hyc : ContinuousOn y (Icc a b))
    (hym : StrictMonoOn y (Icc a b)) (T₃ : Set ℝ) (x : ℝ → S)
    (hx : IsCadlagOn (Icc (y a) (y b)) x) (hcdT : Icc (y a) (y b) ⊆ T₃)
    (hca : ContinuousWithinAt x T₃ (y a)) (hcb : ContinuousWithinAt x T₃ (y b))
    (η : ℝ) (hη : 0 < η) :
    ∃ κ > 0, ∀ z : ℝ → ℝ, MonotoneOn z (Icc a b) →
      (∀ t ∈ Icc a b, ContinuousWithinAt z (Icc a b ∩ Ici t) t) →
      (∀ t ∈ Icc a b, z t ∈ T₃) → (∀ t ∈ Icc a b, |z t - y t| < κ) →
      j1Dist a b (x ∘ z) (x ∘ y) ≤ ENNReal.ofReal η := by
  have haI : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hbI : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  set c := y a with hc
  set d := y b with hd
  have hcd : c < d := hym haI hbI hab
  set ε := η / 3 with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨ρc, hρc, hxc⟩ := Metric.continuousWithinAt_iff.1 hca ε hε
  obtain ⟨ρd, hρd, hxd⟩ := Metric.continuousWithinAt_iff.1 hcb ε hε
  obtain ⟨k, s, hs0, hsl, hsm, hosc⟩ := billingsley_lemma_1 c d hcd x hx ε hε
  have hpiece : ∀ j : Fin k, ∀ u ∈ Ico (s j.castSucc) (s j.succ),
      ∀ v ∈ Ico (s j.castSucc) (s j.succ), dist (x u) (x v) < ε := by
    intro j u hu v hv
    have := lt_of_le_of_lt (le_trans (le_iSup₂ (f := fun s₂ _ => edist (x u) (x s₂)) v hv)
      (le_iSup₂ (f := fun s₁ _ => ⨆ s₂ ∈ Ico (s j.castSucc)
        (s j.succ), edist (x s₁) (x s₂)) u hu)) (hosc j)
    rwa [edist_lt_ofReal] at this
  have hsI : ∀ j, s j ∈ Icc c d := fun j =>
    ⟨hs0 ▸ hsm.monotone (Fin.zero_le j), hsl ▸ hsm.monotone (Fin.le_last j)⟩
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      have : s 0 = s (Fin.last 0) := rfl
      rw [hs0, hsl] at this; linarith
    · exact h0
  have hIVT := intermediate_value_Icc hab.le hyc
  have hτex : ∀ j, ∃ τ ∈ Icc a b, y τ = s j := fun j => hIVT (hsI j)
  choose τ hτI hτy using hτex
  have hτm : StrictMono τ := by
    intro i j hij
    have : y (τ i) < y (τ j) := by rw [hτy, hτy]; exact hsm hij
    exact (hym.lt_iff_lt (hτI i) (hτI j)).1 this
  have hτ0 : τ 0 = a := hym.injOn (hτI 0) haI (by rw [hτy, hs0])
  have hτl : τ (Fin.last k) = b := hym.injOn (hτI _) hbI (by rw [hτy, hsl])
  -- gap
  obtain ⟨g, hg, hgap⟩ := exists_pos_forall (fun (ij : Fin (k + 1) × Fin (k + 1)) r =>
      ij.1 < ij.2 → r ≤ τ ij.2 - τ ij.1)
    (fun ij r r' _ hr' h hlt => le_trans hr' (h hlt))
    (fun ij => by
      by_cases hlt : ij.1 < ij.2
      · exact ⟨τ ij.2 - τ ij.1, by linarith [hτm hlt], fun _ => le_rfl⟩
      · exact ⟨1, one_pos, fun h => absurd h hlt⟩)
  have hgap' : ∀ i j : Fin (k + 1), i < j → g ≤ τ j - τ i := fun i j h => hgap (i, j) h
  set ρ := min (g / 3) η with hρdef
  have hρ0 : 0 < ρ := lt_min (by linarith) hη
  have hρg : ρ ≤ g / 3 := min_le_left _ _
  have hρη : ρ ≤ η := min_le_right _ _
  -- interior points
  have hint : ∀ j : Fin (k + 1), 0 < j.val → j.val < k →
      τ j - ρ ∈ Icc a b ∧ τ j + ρ ∈ Icc a b := by
    intro j h1 h2
    have e1 := hgap' 0 j (by rw [Fin.lt_def]; simpa using h1)
    have e2 := hgap' j (Fin.last k) (by rw [Fin.lt_def]; simpa using h2)
    rw [hτ0] at e1; rw [hτl] at e2
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  obtain ⟨κ0, hκ0, hκj⟩ := exists_pos_forall (fun (j : Fin (k + 1)) r =>
      0 < j.val → j.val < k → y (τ j - ρ) + r ≤ s j ∧ s j ≤ y (τ j + ρ) - r)
    (fun j r r' _ hr' h h1 h2 => ⟨by linarith [(h h1 h2).1], by linarith [(h h1 h2).2]⟩)
    (fun j => by
      by_cases h : 0 < j.val ∧ j.val < k
      · obtain ⟨m1, m2⟩ := hint j h.1 h.2
        have l1 : y (τ j - ρ) < s j := by
          rw [← hτy]; exact hym m1 (hτI j) (by linarith)
        have l2 : s j < y (τ j + ρ) := by
          rw [← hτy]; exact hym (hτI j) m2 (by linarith)
        refine ⟨min (s j - y (τ j - ρ)) (y (τ j + ρ) - s j), lt_min (by linarith) (by linarith),
          fun _ _ => ⟨?_, ?_⟩⟩
        · linarith [min_le_left (s j - y (τ j - ρ)) (y (τ j + ρ) - s j)]
        · linarith [min_le_right (s j - y (τ j - ρ)) (y (τ j + ρ) - s j)]
      · exact ⟨1, one_pos, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩)
  set κ := min κ0 (min ρc ρd) with hκdef
  have hκ0' : 0 < κ := lt_min hκ0 (lt_min hρc hρd)
  have hκκ0 : κ ≤ κ0 := min_le_left _ _
  have hκc : κ ≤ ρc := le_trans (min_le_right _ _) (min_le_left _ _)
  have hκd : κ ≤ ρd := le_trans (min_le_right _ _) (min_le_right _ _)
  -- piece bound
  have hpb : ∀ j : Fin k, ∀ u ∈ T₃, (s j.castSucc ≤ u ∨ (j.val = 0 ∧ c - ρc < u)) →
      (u < s j.succ ∨ (j.val + 1 = k ∧ u < d + ρd)) →
      ∀ v ∈ Ico (s j.castSucc) (s j.succ), dist (x u) (x v) < 3 * ε := by
    intro j u huT hL hU v hv
    by_cases h1 : s j.castSucc ≤ u
    · by_cases h2 : u < s j.succ
      · linarith [hpiece j u ⟨h1, h2⟩ v hv]
      · have hU' := hU.resolve_left h2
        have hjs : j.succ = Fin.last k := Fin.ext (by simp [hU'.1])
        rw [hjs, hsl] at h2 hv
        push_neg at h2
        have e1 : dist (x u) (x d) < ε := hxd huT (by rw [Real.dist_eq, abs_lt]; constructor <;>
          linarith [hU'.2])
        set w := max (s j.castSucc) (d - ρd / 2) with hw
        have hwI : w ∈ Ico (s j.castSucc) d :=
          ⟨le_max_left _ _, max_lt (lt_of_le_of_lt hv.1 hv.2) (by linarith)⟩
        have hwT : w ∈ T₃ := hcdT ⟨le_trans (hsI _).1 hwI.1, hwI.2.le⟩
        have e2 : dist (x w) (x d) < ε := hxd hwT (by
          rw [Real.dist_eq, abs_lt]; constructor <;> linarith [le_max_right (s j.castSucc) (d - ρd / 2), hwI.2])
        have e3 : dist (x w) (x v) < ε := by
          have := hpiece j w (by rw [hjs, hsl]; exact hwI) v (by rw [hjs, hsl]; exact hv)
          exact this
        calc dist (x u) (x v) ≤ dist (x u) (x d) + dist (x d) (x w) + dist (x w) (x v) :=
              dist_triangle4 _ _ _ _
          _ < 3 * ε := by rw [dist_comm (x d)]; linarith
    · have hL' := hL.resolve_left h1
      have hj0 : j.castSucc = 0 := Fin.ext (by simp [hL'.1])
      rw [hj0, hs0] at h1 hv
      push_neg at h1
      have e1 : dist (x u) (x c) < ε := hxc huT (by rw [Real.dist_eq, abs_lt]; constructor <;>
        linarith [hL'.2])
      have hcI : c ∈ Ico (s j.castSucc) (s j.succ) := by rw [hj0, hs0]; exact ⟨le_rfl, hv.1.trans_lt hv.2⟩
      have e2 : dist (x c) (x v) < ε := hpiece j c hcI v (by rw [hj0, hs0]; exact hv)
      calc dist (x u) (x v) ≤ dist (x u) (x c) + dist (x c) (x v) := dist_triangle _ _ _
        _ < 3 * ε := by linarith
  refine ⟨κ, hκ0', ?_⟩
  intro z hzm hzr hzT hzy
  -- crossing times
  let A : Fin (k + 1) → Set ℝ := fun j => {t | t ∈ Icc a b ∧ s j ≤ z t}
  let τn : Fin (k + 1) → ℝ := fun j => if 0 < j.val ∧ j.val < k then sInf (A j) else τ j
  have hAbdd : ∀ j, BddBelow (A j) := fun j => ⟨a, fun t ht => ht.1.1⟩
  have hAmem : ∀ j : Fin (k + 1), 0 < j.val → j.val < k → τ j + ρ ∈ A j := by
    intro j h1 h2
    refine ⟨(hint j h1 h2).2, ?_⟩
    have := hzy _ (hint j h1 h2).2
    rw [abs_lt] at this
    linarith [(hκj j h1 h2).2]
  have hAlow : ∀ j : Fin (k + 1), 0 < j.val → j.val < k → ∀ t ∈ A j, τ j - ρ < t := by
    intro j h1 h2 t ht
    by_contra hcon; push_neg at hcon
    have hm := (hint j h1 h2).1
    have e1 := hzm ht.1 hm hcon
    have e2 := hzy _ hm
    rw [abs_lt] at e2
    linarith [(hκj j h1 h2).1, ht.2]
  have hτn_int : ∀ j : Fin (k + 1), 0 < j.val → j.val < k → τn j = sInf (A j) := by
    intro j h1 h2; simp only [τn]; rw [if_pos ⟨h1, h2⟩]
  have hτn_close : ∀ j, τ j - ρ ≤ τn j ∧ τn j ≤ τ j + ρ := by
    intro j
    by_cases h : 0 < j.val ∧ j.val < k
    · rw [hτn_int j h.1 h.2]
      exact ⟨le_csInf ⟨_, hAmem j h.1 h.2⟩ fun t ht => (hAlow j h.1 h.2 t ht).le,
        csInf_le (hAbdd j) (hAmem j h.1 h.2)⟩
    · simp only [τn]; rw [if_neg h]; constructor <;> linarith
  have hb' : ∀ j : Fin (k + 1), 0 < j.val → j.val < k → ∀ t ∈ Icc a b, t < τn j → z t < s j := by
    intro j h1 h2 t ht htl
    by_contra hcon; push_neg at hcon
    rw [hτn_int j h1 h2] at htl
    exact absurd (csInf_le (hAbdd j) ⟨ht, hcon⟩) (not_le.2 htl)
  have hc' : ∀ j : Fin (k + 1), 0 < j.val → j.val < k → ∀ t ∈ Icc a b, τn j ≤ t → s j ≤ z t := by
    intro j h1 h2 t ht htl
    have hgt : ∀ t' ∈ Icc a b, τn j < t' → s j ≤ z t' := by
      intro t' ht' hlt
      rw [hτn_int j h1 h2] at hlt
      obtain ⟨t'', ht''A, ht''⟩ := exists_lt_of_csInf_lt ⟨_, hAmem j h1 h2⟩ hlt
      exact le_trans ht''A.2 (hzm ht''A.1 ht' ht''.le)
    rcases htl.lt_or_eq with hlt | heq
    · exact hgt t ht hlt
    · -- right continuity
      have htb : t < b := by
        have e2 := hgap' j (Fin.last k) (by rw [Fin.lt_def]; simpa using h2)
        rw [hτl] at e2
        rw [← heq]; linarith [(hτn_close j).2]
      have hlim : Tendsto z (𝓝[Ioo t b] t) (𝓝 (z t)) :=
        (hzr t ht).mono_left (nhdsWithin_mono _ (fun v hv => ⟨⟨ht.1.trans hv.1.le, hv.2.le⟩,
          hv.1.le⟩))
      haveI := left_nhdsWithin_Ioo_neBot htb
      apply ge_of_tendsto hlim
      filter_upwards [self_mem_nhdsWithin] with v hv
      exact hgt v ⟨ht.1.trans hv.1.le, hv.2.le⟩ (heq ▸ hv.1)
  have hτnm : StrictMono τn := by
    intro i j hij
    have := hgap' i j hij
    linarith [(hτn_close i).2, (hτn_close j).1]
  have hτn0 : τn 0 = a := by
    simp only [τn]; rw [if_neg (by simp), hτ0]
  have hτnl : τn (Fin.last k) = b := by
    simp only [τn]; rw [if_neg (by simp), hτl]
  have hτnI : ∀ j, τn j ∈ Icc a b := fun j =>
    ⟨hτn0 ▸ hτnm.monotone (Fin.zero_le j), hτnl ▸ hτnm.monotone (Fin.le_last j)⟩
  obtain ⟨μ, hμ, hμv, hμb⟩ := interp k τn τ hτnm hτm ρ (fun j => by
    rw [abs_le]; constructor <;> linarith [hτn_close j])
  rw [hτn0, hτnl, hτ0, hτl] at hμ
  rw [hτn0, hτnl] at hμb
  have hμtc := tc_of_isHom a b hab.le μ hμ
  apply j1Dist_le_of a b _ _ μ hμtc η
  intro t ht
  refine ⟨by rw [Real.dist_eq]; linarith [hμb t ht], ?_⟩
  show dist (x (z t)) (x (y (μ t))) ≤ η
  rcases ht.2.lt_or_eq with htb | htb
  · obtain ⟨j, hj1, hj2⟩ := find_piece k τn hτnm t ⟨by rw [hτn0]; exact ht.1, by rw [hτnl]; exact htb⟩
    have hμ1 : τ j.castSucc ≤ μ t := by
      rw [← hμv]; exact hμ.1.monotoneOn (hτnI _) ht hj1
    have hμ2 : μ t < τ j.succ := by
      rw [← hμv]; exact hμ.1 ht (hτnI _) hj2
    have hμI : μ t ∈ Icc a b := by
      rw [← hμtc.2.2]; exact mem_image_of_mem μ ht
    have hv : y (μ t) ∈ Ico (s j.castSucc) (s j.succ) := by
      constructor
      · rw [← hτy]; exact hym.monotoneOn (hτI _) hμI hμ1
      · rw [← hτy]; exact hym hμI (hτI _) hμ2
    have hzyt := hzy t ht
    rw [abs_lt] at hzyt
    have hyt1 : c ≤ y t := hym.monotoneOn haI ht ht.1
    have hyt2 : y t ≤ d := hym.monotoneOn ht hbI ht.2
    have hL : s j.castSucc ≤ z t ∨ (j.val = 0 ∧ c - ρc < z t) := by
      by_cases hj0 : j.val = 0
      · exact Or.inr ⟨hj0, by linarith⟩
      · exact Or.inl (hc' j.castSucc (by simp; omega) (by simp) t ht hj1)
    have hU : z t < s j.succ ∨ (j.val + 1 = k ∧ z t < d + ρd) := by
      by_cases hjk : j.val + 1 = k
      · exact Or.inr ⟨hjk, by linarith⟩
      · exact Or.inl (hb' j.succ (by simp) (by simp; omega) t ht hj2)
    have := hpb j (z t) (hzT t ht) hL hU _ hv
    linarith
  · subst htb
    have hμb' : μ t = t := hμ.2.2.2
    rw [hμb']
    have hzyt := hzy t ht
    rw [abs_lt] at hzyt
    have := hxd (hzT t ht) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    linarith

lemma point_case {T₃ : Set ℝ} (hT₃ : T₃.OrdConnected) (xs : ℕ → ℝ → S) (x : ℝ → S)
    (hxs : J1Tendsto T₃ xs x) (c : ℝ) (hcT : c ∈ T₃) (hxc : ContinuousWithinAt x T₃ c)
    (us : ℕ → ℝ) (hus : ∀ n, us n ∈ T₃) (hconv : ∀ r > 0, ∀ᶠ n in atTop, |us n - c| < r) :
    ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, dist (xs n (us n)) (x c) ≤ η := by
  intro η hη
  obtain ⟨c', hc'T, hc'c, hc'e, m, hm, hmc⟩ := lower3 T₃ x hxs.2.1 hT₃ c hcT
  obtain ⟨d', hd'T, hd'c, hd'e, m', hm', hmd⟩ := upper3 T₃ x hxs.2.1 hT₃ c hcT
  have hJ := hxs.2.2 c' d' (by linarith) (hT₃.out hc'T hd'T) hc'e hd'e
  unfold J1TendstoOn at hJ
  rw [tendsto_zero_iff_real] at hJ
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousWithinAt_iff.1 hxc (η / 2) (by linarith)
  set r := min (min (δ / 2) (η / 2)) (min m m') with hr
  have hr0 : 0 < r := lt_min (lt_min (by linarith) (by linarith)) (lt_min hm hm')
  have hr1 : r ≤ δ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hr2 : r ≤ η / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hr3 : r ≤ m := le_trans (min_le_right _ _) (min_le_left _ _)
  have hr4 : r ≤ m' := le_trans (min_le_right _ _) (min_le_right _ _)
  filter_upwards [hJ r hr0, hconv r hr0] with n hn hun
  obtain ⟨l, hl, hbd⟩ := exists_of_j1Dist_lt c' d' (xs n) x r hn
  rw [abs_lt] at hun
  have huI : us n ∈ Icc c' d' := ⟨hmc _ (hus n) (by linarith), hmd _ (hus n) (by linarith)⟩
  have hlI : l (us n) ∈ Icc c' d' := by rw [← hl.2.2]; exact mem_image_of_mem l huI
  have h1 := hbd _ huI
  have h1a := h1.1
  rw [Real.dist_eq, abs_lt] at h1a
  have e := hd (hT₃.out hc'T hd'T hlI) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  calc dist (xs n (us n)) (x c) ≤ dist (xs n (us n)) (x (l (us n))) + dist (x (l (us n))) (x c) :=
        dist_triangle _ _ _
    _ ≤ η := by linarith [h1.2]

end WhittL22

open WhittL22 in
theorem solution {S : Type*} [MetricSpace S] [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (T₁ T₂ T₃ : Set ℝ) (hT₁ : T₁.OrdConnected) (hT₂ : T₂.OrdConnected)
    (hT₃ : T₃.OrdConnected) (hT₁ne : T₁.Nonempty) (hT₂₃ : T₂ ⊆ T₃)
    (xs : ℕ → ℝ → S) (x : ℝ → S) (ys : ℕ → ℝ → ℝ) (y : ℝ → ℝ)
    (hys : ∀ n, MonotoneOn (ys n) T₁ ∧ MapsTo (ys n) T₁ T₂)
    (hy : MonotoneOn y T₁ ∧ MapsTo y T₁ T₂)
    (hxs : J1Tendsto T₃ xs x) (hys' : J1Tendsto T₁ ys y)
    (hy₀ : ContinuousOn y T₁ ∧ StrictMonoOn y T₁)
    (hBauer : ∀ t, IsEndpoint T₁ t → ContinuousWithinAt x T₃ (y t)) :
    J1Tendsto T₁ (fun n => xs n ∘ ys n) (x ∘ y) := by
  obtain ⟨hyc, hym⟩ := hy₀
  refine ⟨fun n => cadlag_comp hT₂ hT₂₃ (hxs.1 n) (hys'.1 n) (hys n).1 (hys n).2,
    cadlag_comp hT₂ hT₂₃ hxs.2.1 hys'.2.1 hy.1 hy.2, ?_⟩
  intro a b hab hsub ha hb
  have haT : a ∈ T₁ := hsub ⟨le_rfl, hab⟩
  have hbT : b ∈ T₁ := hsub ⟨hab, le_rfl⟩
  have hxa := cont_of_comp hT₁ y hyc hym x a haT ha hBauer
  have hxb := cont_of_comp hT₁ y hyc hym x b hbT hb hBauer
  have hJy : J1TendstoOn a b ys y := hys'.2.2 a b hab hsub (Or.inl (hyc a haT)) (Or.inl (hyc b hbT))
  have hunif := unif_conv_of_cont a b ys y (hyc.mono hsub) hJy
  rcases hab.lt_or_eq with hlt | heq
  · have hcd : y a < y b := hym haT hbT hlt
    have hcT : y a ∈ T₃ := hT₂₃ (hy.2 haT)
    have hdT : y b ∈ T₃ := hT₂₃ (hy.2 hbT)
    have hcdT : Icc (y a) (y b) ⊆ T₃ := hT₃.out hcT hdT
    obtain ⟨c', hc'T, hc'c, hc'e, m, hm, hmc⟩ := lower3 T₃ x hxs.2.1 hT₃ (y a) hcT
    obtain ⟨d', hd'T, hd'c, hd'e, m', hm', hmd⟩ := upper3 T₃ x hxs.2.1 hT₃ (y b) hdT
    have hsub3 : Icc c' d' ⊆ T₃ := hT₃.out hc'T hd'T
    have hJx := hxs.2.2 c' d' (by linarith) hsub3 hc'e hd'e
    unfold J1TendstoOn at hJx
    rw [tendsto_zero_iff_real] at hJx
    unfold J1TendstoOn
    apply tendsto_zero_of_le
    intro η hη
    obtain ⟨κ, hκ, hK⟩ := key_K a b hlt y (hyc.mono hsub) (hym.mono hsub) T₃ x
      (cadlag_mono hxs.2.1 hcdT) hcdT hxa hxb (η / 4) (by linarith)
    set r := min (min (κ / 2) (η / 2)) (min m m') with hr
    have hr0 : 0 < r := lt_min (lt_min (by linarith) (by linarith)) (lt_min hm hm')
    have hr1 : r ≤ κ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
    have hr2 : r ≤ η / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hr3 : r ≤ m := le_trans (min_le_right _ _) (min_le_left _ _)
    have hr4 : r ≤ m' := le_trans (min_le_right _ _) (min_le_right _ _)
    filter_upwards [hJx r hr0, hunif r hr0] with n hn hun
    obtain ⟨l, hl, hbd⟩ := exists_of_j1Dist_lt c' d' (xs n) x r hn
    have hysI : ∀ t ∈ Icc a b, ys n t ∈ Icc c' d' := by
      intro t ht
      have h1 := hun t ht
      rw [Real.dist_eq, abs_lt] at h1
      have hT := hT₂₃ ((hys n).2 (hsub ht))
      have e1 : y a ≤ y t := hy.1 haT (hsub ht) ht.1
      have e2 : y t ≤ y b := hy.1 (hsub ht) hbT ht.2
      exact ⟨hmc _ hT (by linarith), hmd _ hT (by linarith)⟩
    have hzm : MonotoneOn (fun t => l (ys n t)) (Icc a b) := by
      intro s hs t ht hst
      exact hl.1.monotoneOn (hysI s hs) (hysI t ht) ((hys n).1 (hsub hs) (hsub ht) hst)
    have hzr : ∀ t ∈ Icc a b, ContinuousWithinAt (fun t => l (ys n t)) (Icc a b ∩ Ici t) t := by
      intro t ht
      refine ContinuousWithinAt.comp (hl.2.1 _ (hysI t ht)) ?_ (fun s hs => hysI s hs.1)
      exact (hys'.1 n t (hsub ht)).1.mono (inter_subset_inter_left _ hsub)
    have hzT : ∀ t ∈ Icc a b, l (ys n t) ∈ T₃ := by
      intro t ht
      apply hsub3
      rw [← hl.2.2]; exact mem_image_of_mem l (hysI t ht)
    have hzy : ∀ t ∈ Icc a b, |l (ys n t) - y t| < κ := by
      intro t ht
      have h1 := (hbd _ (hysI t ht)).1
      have h2 := hun t ht
      rw [Real.dist_eq] at h1 h2
      calc |l (ys n t) - y t| ≤ |l (ys n t) - ys n t| + |ys n t - y t| := abs_sub_le _ _ _
        _ < κ := by linarith
    have hK' := hK _ hzm hzr hzT hzy
    obtain ⟨μ, hμ, hμb⟩ := exists_of_j1Dist_lt a b (x ∘ fun t => l (ys n t)) (x ∘ y) (η / 2)
      (lt_of_le_of_lt hK' ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)))
    apply j1Dist_le_of a b _ _ μ hμ η
    intro t ht
    refine ⟨by linarith [(hμb t ht).1], ?_⟩
    show dist (xs n (ys n t)) (x (y (μ t))) ≤ η
    have e1 := (hbd _ (hysI t ht)).2
    have e2 := (hμb t ht).2
    simp only [Function.comp] at e2
    calc dist (xs n (ys n t)) (x (y (μ t)))
        ≤ dist (xs n (ys n t)) (x (l (ys n t))) + dist (x (l (ys n t))) (x (y (μ t))) :=
          dist_triangle _ _ _
      _ ≤ η := by linarith
  · subst heq
    apply j1_point
    have hcT : y a ∈ T₃ := hT₂₃ (hy.2 haT)
    have := point_case hT₃ xs x hxs (y a) hcT hxa (fun n => ys n a)
      (fun n => hT₂₃ ((hys n).2 haT)) (fun r hr => by
        filter_upwards [hunif r hr] with n hn
        have := hn a ⟨le_rfl, le_rfl⟩
        rwa [Real.dist_eq] at this)
    exact this
