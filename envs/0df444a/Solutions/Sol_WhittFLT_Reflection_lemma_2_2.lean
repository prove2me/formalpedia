-- Prove2me | solution 1 for WhittFLT.Reflection.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T04:50:03.331206+00:00
-- url     : https://prove2.me/submissions/60c84941-b515-4c73-b96e-297f2ef1bc8b

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

end WhittL22

open WhittL22 in
theorem solution {S : Type*} [MetricSpace S] (a b c : ℝ) (hab : a < b) (hbc : b < c)
    (xs : ℕ → ℝ → S) (x : ℝ → S) (hxs : ∀ n, IsCadlagOn (Icc a c) (xs n))
    (hx : IsCadlagOn (Icc a c) x) (hb : ContinuousAt x b) :
    J1TendstoOn a c xs x ↔ (J1TendstoOn a b xs x ∧ J1TendstoOn b c xs x) :=
  ⟨fun h => ⟨restrict_left a b c hab hbc xs x hb h, restrict_right a b c hab hbc xs x hb h⟩,
    fun h => glue_dir a b c hab hbc xs x h.1 h.2⟩
