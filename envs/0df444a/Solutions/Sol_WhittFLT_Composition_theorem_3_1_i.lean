-- Prove2me | solution 1 for WhittFLT.Composition.theorem_3_1_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T13:28:38.961377+00:00
-- url     : https://prove2.me/submissions/550323f9-94b3-4594-a675-feb9fb3cfe95

import Mathlib
import Definitions.Def_WhittFLT_Composition_SkorohodD

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

lemma restrict_gen (a' a b b' : ℝ) (h1 : a' ≤ a) (h2 : a ≤ b) (h3 : b ≤ b')
    (zs : ℕ → ℝ → S) (z : ℝ → S)
    (h : J1TendstoOn a' b' zs z) (ha : a = a' ∨ ContinuousAt z a) (hb : b = b' ∨ ContinuousAt z b) :
    J1TendstoOn a b zs z := by
  rcases h2.lt_or_eq with hlt | heq
  · have hab' : J1TendstoOn a b' zs z := by
      rcases ha with ha | hca
      · rw [ha]; exact h
      · rcases h1.lt_or_eq with h1' | h1'
        · exact restrict_right a' a b' h1' (by linarith) zs z hca h
        · rw [← h1']; exact h
    rcases hb with hb | hcb
    · rw [hb]; exact hab'
    · rcases h3.lt_or_eq with h3' | h3'
      · exact restrict_left a b b' hlt h3' zs z hcb hab'
      · rw [h3']; exact hab'
  · subst heq
    rcases ha with ha | hca
    · rcases hb with hb | hcb
      · subst ha; subst hb; exact h
      · exact j1_point _ zs z (pointwise_of_j1 _ _ zs z h _ ⟨h1, h3⟩ hcb)
    · exact j1_point _ zs z (pointwise_of_j1 _ _ zs z h _ ⟨h1, h3⟩ hca)

lemma exists_lower (T : Set ℝ) (v : ℝ) (hv : v ∈ T) :
    ∃ L ∈ T, L ≤ v ∧ ∃ m > 0, ∀ u ∈ T, v - m < u → L ≤ u := by
  by_cases h : ∃ s ∈ T, s < v
  · obtain ⟨s, hs, hsv⟩ := h
    exact ⟨s, hs, hsv.le, v - s, by linarith, fun u _ hu => by linarith⟩
  · push_neg at h
    exact ⟨v, hv, le_rfl, 1, one_pos, fun u hu _ => h u hu⟩

lemma exists_upper (T : Set ℝ) (v : ℝ) (hv : v ∈ T) :
    ∃ R ∈ T, v ≤ R ∧ ∃ m > 0, ∀ u ∈ T, u < v + m → u ≤ R := by
  by_cases h : ∃ s ∈ T, v < s
  · obtain ⟨s, hs, hsv⟩ := h
    exact ⟨s, hs, hsv.le, s - v, by linarith, fun u _ hu => by linarith⟩
  · push_neg at h
    exact ⟨v, hv, le_rfl, 1, one_pos, fun u hu _ => h u hu⟩

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

lemma core_i {T₁ T₂ T₃ : Set ℝ} (hT₃ : T₃.OrdConnected) (hT₂₃ : T₂ ⊆ T₃)
    (xs : ℕ → ℝ → S) (x : ℝ → S) (ys : ℕ → ℝ → ℝ) (y : ℝ → ℝ)
    (hys : ∀ n, MonotoneOn (ys n) T₁ ∧ MapsTo (ys n) T₁ T₂)
    (hy : MonotoneOn y T₁ ∧ MapsTo y T₁ T₂)
    (hxs : J1Tendsto T₃ xs x) (hx : ContinuousOn x T₃)
    (a b : ℝ) (hab : a ≤ b) (hsub : Icc a b ⊆ T₁) (hyab : J1TendstoOn a b ys y) :
    J1TendstoOn a b (fun n => xs n ∘ ys n) (x ∘ y) := by
  have haT : a ∈ T₁ := hsub ⟨le_rfl, hab⟩
  have hbT : b ∈ T₁ := hsub ⟨hab, le_rfl⟩
  obtain ⟨L, hL, hLa, m, hm, hmL⟩ := exists_lower T₃ (y a) (hT₂₃ (hy.2 haT))
  obtain ⟨R, hR, hRb, m', hm', hmR⟩ := exists_upper T₃ (y b) (hT₂₃ (hy.2 hbT))
  have hyab' : y a ≤ y b := hy.1 haT hbT hab
  have hLR : L ≤ R := by linarith
  have hLRsub : Icc L R ⊆ T₃ := hT₃.out hL hR
  have hxLR : ContinuousOn x (Icc L R) := hx.mono hLRsub
  have hJ : J1TendstoOn L R xs x :=
    hxs.2.2 L R hLR hLRsub (Or.inl (hx L hL)) (Or.inl (hx R hR))
  unfold J1TendstoOn
  apply tendsto_zero_of_le
  intro η hη
  have huc := (isCompact_Icc.uniformContinuousOn_of_continuous hxLR)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hd⟩ := huc (η / 3) (by linarith)
  set r := min (min δ η) (min m m') with hr
  have hr0 : 0 < r := lt_min (lt_min hδ hη) (lt_min hm hm')
  have hrδ : r ≤ δ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hrη : r ≤ η := le_trans (min_le_left _ _) (min_le_right _ _)
  have hrm : r ≤ m := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrm' : r ≤ m' := le_trans (min_le_right _ _) (min_le_right _ _)
  unfold J1TendstoOn at hyab
  rw [tendsto_zero_iff_real] at hyab
  filter_upwards [hyab r hr0, unif_conv_of_cont L R xs x hxLR hJ (2 * η / 3) (by linarith)]
    with n hn hun
  obtain ⟨l, hl, hbd⟩ := exists_of_j1Dist_lt a b (ys n) y r hn
  apply j1Dist_le_of a b _ _ l hl η
  intro t ht
  have hlt : l t ∈ Icc a b := by rw [← hl.2.2]; exact mem_image_of_mem l ht
  have hylt1 : y a ≤ y (l t) := hy.1 haT (hsub hlt) hlt.1
  have hylt2 : y (l t) ≤ y b := hy.1 (hsub hlt) hbT hlt.2
  have hu3 : ys n t ∈ T₃ := hT₂₃ ((hys n).2 (hsub ht))
  have hd1 := (hbd t ht).2
  rw [Real.dist_eq, abs_lt] at hd1
  have huL : L ≤ ys n t := hmL _ hu3 (by linarith)
  have huR : ys n t ≤ R := hmR _ hu3 (by linarith)
  refine ⟨by linarith [(hbd t ht).1], ?_⟩
  show dist (xs n (ys n t)) (x (y (l t))) ≤ η
  have e1 := hun (ys n t) ⟨huL, huR⟩
  have e2 := hd (ys n t) ⟨huL, huR⟩ (y (l t)) ⟨by linarith, by linarith⟩
    (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  calc dist (xs n (ys n t)) (x (y (l t)))
      ≤ dist (xs n (ys n t)) (x (ys n t)) + dist (x (ys n t)) (x (y (l t))) :=
        dist_triangle _ _ _
    _ ≤ η := by linarith

lemma choose_left {T₁ : Set ℝ} (hT₁ : T₁.OrdConnected) (y : ℝ → ℝ) (hym : MonotoneOn y T₁)
    (z : ℝ → S) (a : ℝ) (haT : a ∈ T₁) (ha : ContinuousWithinAt z T₁ a ∨ IsEndpoint T₁ a) :
    ∃ a', a' ≤ a ∧ a' ∈ T₁ ∧ (ContinuousWithinAt y T₁ a' ∨ IsEndpoint T₁ a') ∧
      (a = a' ∨ ContinuousAt z a) := by
  by_cases hE : IsEndpoint T₁ a
  · exact ⟨a, le_rfl, haT, Or.inr hE, Or.inl rfl⟩
  · have hc : ContinuousWithinAt z T₁ a := ha.resolve_right hE
    obtain ⟨hnl, hng⟩ := not_or.1 hE
    have : ∃ s ∈ T₁, s < a := by
      by_contra hcon; push_neg at hcon; exact hnl ⟨haT, fun u hu => hcon u hu⟩
    obtain ⟨s, hs, hsa⟩ := this
    have : ∃ s ∈ T₁, a < s := by
      by_contra hcon; push_neg at hcon; exact hng ⟨haT, fun u hu => hcon u hu⟩
    obtain ⟨s', hs', has'⟩ := this
    have hnhds : T₁ ∈ 𝓝 a :=
      mem_of_superset (Ioo_mem_nhds hsa has') (Ioo_subset_Icc_self.trans (hT₁.out hs hs'))
    have hca : ContinuousAt z a := hc.continuousAt hnhds
    have hcount := hym.countable_not_continuousWithinAt
    obtain ⟨a', ha'1, ha'2⟩ :=
      (hcount.dense_compl ℝ).inter_open_nonempty (Ioo s a) isOpen_Ioo (nonempty_Ioo.2 hsa)
    have ha'T : a' ∈ T₁ := hT₁.out hs haT (Ioo_subset_Icc_self ha'1)
    refine ⟨a', ha'1.2.le, ha'T, Or.inl ?_, Or.inr hca⟩
    by_contra hnc
    exact ha'2 ⟨ha'T, hnc⟩

lemma choose_right {T₁ : Set ℝ} (hT₁ : T₁.OrdConnected) (y : ℝ → ℝ) (hym : MonotoneOn y T₁)
    (z : ℝ → S) (a : ℝ) (haT : a ∈ T₁) (ha : ContinuousWithinAt z T₁ a ∨ IsEndpoint T₁ a) :
    ∃ a', a ≤ a' ∧ a' ∈ T₁ ∧ (ContinuousWithinAt y T₁ a' ∨ IsEndpoint T₁ a') ∧
      (a = a' ∨ ContinuousAt z a) := by
  by_cases hE : IsEndpoint T₁ a
  · exact ⟨a, le_rfl, haT, Or.inr hE, Or.inl rfl⟩
  · have hc : ContinuousWithinAt z T₁ a := ha.resolve_right hE
    obtain ⟨hnl, hng⟩ := not_or.1 hE
    have : ∃ s ∈ T₁, s < a := by
      by_contra hcon; push_neg at hcon; exact hnl ⟨haT, fun u hu => hcon u hu⟩
    obtain ⟨s, hs, hsa⟩ := this
    have : ∃ s ∈ T₁, a < s := by
      by_contra hcon; push_neg at hcon; exact hng ⟨haT, fun u hu => hcon u hu⟩
    obtain ⟨s', hs', has'⟩ := this
    have hnhds : T₁ ∈ 𝓝 a :=
      mem_of_superset (Ioo_mem_nhds hsa has') (Ioo_subset_Icc_self.trans (hT₁.out hs hs'))
    have hca : ContinuousAt z a := hc.continuousAt hnhds
    have hcount := hym.countable_not_continuousWithinAt
    obtain ⟨a', ha'1, ha'2⟩ :=
      (hcount.dense_compl ℝ).inter_open_nonempty (Ioo a s') isOpen_Ioo (nonempty_Ioo.2 has')
    have ha'T : a' ∈ T₁ := hT₁.out haT hs' (Ioo_subset_Icc_self ha'1)
    refine ⟨a', ha'1.1.le, ha'T, Or.inl ?_, Or.inr hca⟩
    by_contra hnc
    exact ha'2 ⟨ha'T, hnc⟩

end WhittL22

open WhittL22 in
theorem solution {S : Type*} [MetricSpace S] [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (T₁ T₂ T₃ : Set ℝ) (hT₁ : T₁.OrdConnected) (hT₂ : T₂.OrdConnected)
    (hT₃ : T₃.OrdConnected) (hT₁ne : T₁.Nonempty) (hT₂₃ : T₂ ⊆ T₃)
    (hT₃nt : (interior T₃).Nonempty)
    (xs : ℕ → ℝ → S) (x : ℝ → S) (ys : ℕ → ℝ → ℝ) (y : ℝ → ℝ)
    (hys : ∀ n, MonotoneOn (ys n) T₁ ∧ MapsTo (ys n) T₁ T₂)
    (hy : MonotoneOn y T₁ ∧ MapsTo y T₁ T₂)
    (hxs : J1Tendsto T₃ xs x) (hys' : J1Tendsto T₁ ys y)
    (hx : ContinuousOn x T₃) :
    J1Tendsto T₁ (fun n => xs n ∘ ys n) (x ∘ y) := by
  refine ⟨fun n => cadlag_comp hT₂ hT₂₃ (hxs.1 n) (hys'.1 n) (hys n).1 (hys n).2,
    cadlag_comp hT₂ hT₂₃ hxs.2.1 hys'.2.1 hy.1 hy.2, ?_⟩
  intro a b hab hsub ha hb
  have haT : a ∈ T₁ := hsub ⟨le_rfl, hab⟩
  have hbT : b ∈ T₁ := hsub ⟨hab, le_rfl⟩
  obtain ⟨a', ha'a, ha'T, ha'c, ha'r⟩ := choose_left hT₁ y hy.1 (x ∘ y) a haT ha
  obtain ⟨b', hbb', hb'T, hb'c, hb'r⟩ := choose_right hT₁ y hy.1 (x ∘ y) b hbT hb
  have hsub' : Icc a' b' ⊆ T₁ := hT₁.out ha'T hb'T
  have hyc := hys'.2.2 a' b' (by linarith) hsub' ha'c hb'c
  have hc := core_i hT₃ hT₂₃ xs x ys y hys hy hxs hx a' b' (by linarith) hsub' hyc
  exact restrict_gen a' a b b' ha'a hab hbb' _ _ hc ha'r hb'r
