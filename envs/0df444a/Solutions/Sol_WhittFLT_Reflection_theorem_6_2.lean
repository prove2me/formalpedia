-- Prove2me | solution 1 for WhittFLT.Reflection.theorem_6_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T05:03:27.270548+00:00
-- url     : https://prove2.me/submissions/502dc4ac-d45e-425b-bfca-bcbc1425a79f

import Mathlib
import Definitions.Def_WhittFLT_Composition_SkorohodD
import Definitions.Def_WhittFLT_Reflection_Supremum
import Theorems.Thm_WhittFLT_Reflection_billingsley_lemma_1
import Theorems.Thm_WhittFLT_Reflection_lemma_2_2

open WhittFLT.Composition WhittFLT.Reflection
open Set Filter Topology Metric
open scoped ENNReal

namespace W64c

/-! ### Generic facts on càdlàg paths and the J₁ distance -/

lemma cadlag_mono {S : Type*} [MetricSpace S] {T T' : Set ℝ} {x : ℝ → S}
    (hx : IsCadlagOn T x) (h : T' ⊆ T) : IsCadlagOn T' x := by
  intro t ht
  obtain ⟨h1, l, hl⟩ := hx t (h ht)
  exact ⟨h1.mono (inter_subset_inter_left _ h), l,
    hl.mono_left (nhdsWithin_mono _ (inter_subset_inter_left _ h))⟩

lemma cadlag_add {T : Set ℝ} {u v : ℝ → ℝ} (hu : IsCadlagOn T u) (hv : IsCadlagOn T v) :
    IsCadlagOn T (fun t => u t + v t) := by
  intro t ht
  obtain ⟨h1, l, hl⟩ := hu t ht
  obtain ⟨h2, m, hm⟩ := hv t ht
  exact ⟨h1.add h2, l + m, hl.add hm⟩

lemma cadlag_neg {T : Set ℝ} {u : ℝ → ℝ} (hu : IsCadlagOn T u) :
    IsCadlagOn T (fun t => -u t) := by
  intro t ht
  obtain ⟨h1, l, hl⟩ := hu t ht
  exact ⟨h1.neg, -l, hl.neg⟩

lemma cadlag_of_continuous {T : Set ℝ} {u : ℝ → ℝ} (hu : Continuous u) : IsCadlagOn T u :=
  fun t _ => ⟨hu.continuousWithinAt, u t, (hu.tendsto t).mono_left nhdsWithin_le_nhds⟩

lemma supDist_le_of {E : Type*} [PseudoMetricSpace E] (a b : ℝ) (f g : ℝ → E) (r : ℝ)
    (h : ∀ t ∈ Icc a b, dist (f t) (g t) ≤ r) : supDist a b f g ≤ ENNReal.ofReal r := by
  unfold supDist
  refine iSup₂_le fun t ht => ?_
  rw [edist_dist]; exact ENNReal.ofReal_le_ofReal (h t ht)

lemma dist_le_of_supDist_lt {E : Type*} [PseudoMetricSpace E] (a b : ℝ) (f g : ℝ → E) (r : ℝ)
    (h : supDist a b f g < ENNReal.ofReal r) : ∀ t ∈ Icc a b, dist (f t) (g t) < r := by
  intro t ht
  have : edist (f t) (g t) < ENNReal.ofReal r :=
    lt_of_le_of_lt (le_iSup₂ (f := fun t _ => edist (f t) (g t)) t ht) h
  rw [edist_dist] at this
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).1 this

lemma tc_id (a b : ℝ) : IsTimeChange a b id :=
  ⟨strictMonoOn_id, continuousOn_id, image_id _⟩

lemma j1Dist_le_of {S : Type*} [MetricSpace S] (a b : ℝ) (xs x : ℝ → S) (l : ℝ → ℝ)
    (hl : IsTimeChange a b l) (r : ℝ)
    (h : ∀ t ∈ Icc a b, dist (l t) t ≤ r ∧ dist (xs t) (x (l t)) ≤ r) :
    j1Dist a b xs x ≤ ENNReal.ofReal r := by
  unfold j1Dist
  refine (iInf₂_le l hl).trans ?_
  refine max_le ?_ ?_
  · exact supDist_le_of a b l id r fun t ht => (h t ht).1
  · exact supDist_le_of a b xs (x ∘ l) r fun t ht => (h t ht).2

lemma exists_of_j1Dist_lt {S : Type*} [MetricSpace S] (a b : ℝ) (xs x : ℝ → S) (r : ℝ)
    (h : j1Dist a b xs x < ENNReal.ofReal r) :
    ∃ l, IsTimeChange a b l ∧ ∀ t ∈ Icc a b, dist (l t) t < r ∧ dist (xs t) (x (l t)) < r := by
  unfold j1Dist at h
  rw [iInf_lt_iff] at h
  obtain ⟨l, hl⟩ := h
  rw [iInf_lt_iff] at hl
  obtain ⟨hlt, hl⟩ := hl
  refine ⟨l, hlt, fun t ht => ⟨?_, ?_⟩⟩
  · exact dist_le_of_supDist_lt a b l id r (lt_of_le_of_lt (le_max_left _ _) hl) t ht
  · exact dist_le_of_supDist_lt a b xs (x ∘ l) r (lt_of_le_of_lt (le_max_right _ _) hl) t ht

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

lemma j1Dist_neg (a b : ℝ) (u v : ℝ → ℝ) :
    j1Dist a b (fun t => -u t) (fun t => -v t) = j1Dist a b u v := by
  simp only [j1Dist, supDist, Function.comp_def, edist_neg_neg]

lemma j1Tendsto_neg {T : Set ℝ} {zs : ℕ → ℝ → ℝ} {z : ℝ → ℝ} (h : J1Tendsto T zs z) :
    J1Tendsto T (fun n t => -zs n t) (fun t => -z t) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun n => cadlag_neg (h1 n), cadlag_neg h2, fun a b hab hT ha hb => ?_⟩
  have ha' : ContinuousWithinAt z T a ∨ IsEndpoint T a := by
    rcases ha with ha | ha
    · left; have := ha.neg; convert this using 1; funext t; simp
    · right; exact ha
  have hb' : ContinuousWithinAt z T b ∨ IsEndpoint T b := by
    rcases hb with hb | hb
    · left; have := hb.neg; convert this using 1; funext t; simp
    · right; exact hb
  have := h3 a b hab hT ha' hb'
  unfold J1TendstoOn at *
  simpa only [j1Dist_neg] using this

/-- Adding paths that converge uniformly to `0` preserves J₁ convergence. -/
lemma j1Tendsto_add_u {T : Set ℝ} {zs : ℕ → ℝ → ℝ} {z : ℝ → ℝ} (h : J1Tendsto T zs z)
    (w : ℕ → ℝ → ℝ) (hw : UTendsto T w (fun _ => 0)) (hwc : ∀ n, IsCadlagOn T (w n)) :
    J1Tendsto T (fun n t => zs n t + w n t) z := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun n => cadlag_add (h1 n) (hwc n), h2, fun a b hab hT ha hb => ?_⟩
  have hz := h3 a b hab hT ha hb
  unfold J1TendstoOn at *
  rw [tendsto_zero_iff_real] at hz ⊢
  intro η hη
  have hw' := (tendsto_zero_iff_real _).1 (hw a b hT) (η / 4) (by positivity)
  filter_upwards [hz (η / 4) (by positivity), hw'] with n hn hwn
  obtain ⟨l, hl, hlb⟩ := exists_of_j1Dist_lt a b (zs n) z _ hn
  have hwb := dist_le_of_supDist_lt a b (w n) (fun _ => 0) _ hwn
  refine lt_of_le_of_lt (j1Dist_le_of a b _ z l hl (η / 2) fun t ht => ⟨?_, ?_⟩)
    ((ENNReal.ofReal_lt_ofReal_iff hη).2 (by linarith))
  · linarith [(hlb t ht).1]
  · have e1 := (hlb t ht).2
    have e2 := hwb t ht
    rw [Real.dist_eq] at e1 e2 ⊢
    rw [sub_zero] at e2
    calc |zs n t + w n t - z (l t)| = |(zs n t - z (l t)) + w n t| := by ring_nf
      _ ≤ |zs n t - z (l t)| + |w n t| := abs_add_le _ _
      _ ≤ η / 2 := by linarith

/-! ### Boundedness and the upper modulus of a càdlàg path without positive jumps -/

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

lemma cadlag_bdd (p q : ℝ) (hpq : p ≤ q) (x : ℝ → ℝ) (hx : IsCadlagOn (Icc p q) x) :
    ∃ M, 0 ≤ M ∧ ∀ t ∈ Icc p q, |x t| ≤ M := by
  rcases eq_or_lt_of_le hpq with h | h
  · subst h
    refine ⟨|x p|, abs_nonneg _, fun t ht => ?_⟩
    rw [le_antisymm ht.2 ht.1]
  · obtain ⟨n, t, ht0, htl, htm, hto⟩ := billingsley_lemma_1 p q h x hx 1 one_pos
    refine ⟨∑ i, |x (t i)| + 1, by positivity, fun s hs => ?_⟩
    rcases eq_or_lt_of_le hs.2 with hsq | hsq
    · rw [hsq, ← htl]
      have := Finset.single_le_sum (f := fun i => |x (t i)|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ (Fin.last n))
      linarith
    · obtain ⟨j, hj1, hj2⟩ := find_piece n t htm s ⟨by rw [ht0]; exact hs.1, by rw [htl]; exact hsq⟩
      have hmem1 : s ∈ Ico (t j.castSucc) (t j.succ) := ⟨hj1, hj2⟩
      have hmem2 : t j.castSucc ∈ Ico (t j.castSucc) (t j.succ) := ⟨le_rfl, lt_of_le_of_lt hj1 hj2⟩
      have hlt := lt_of_le_of_lt (le_trans
        (le_iSup₂ (f := fun s₂ _ => edist (x s) (x s₂)) _ hmem2)
        (le_iSup₂ (f := fun s₁ _ => ⨆ s₂ ∈ Ico (t j.castSucc)
          (t j.succ), edist (x s₁) (x s₂)) s hmem1)) (hto j)
      rw [edist_lt_ofReal, Real.dist_eq] at hlt
      have := Finset.single_le_sum (f := fun i => |x (t i)|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ j.castSucc)
      have h3 : |x s| ≤ |x s - x (t j.castSucc)| + |x (t j.castSucc)| := by
        have := abs_add_le (x s - x (t j.castSucc)) (x (t j.castSucc))
        simpa using this
      linarith

/-- Local form of the upper modulus. -/
lemma local_upper (B : ℝ) (x : ℝ → ℝ) (hx : IsCadlagOn (Icc 0 B) x)
    (hj : ∀ t ∈ Icc 0 B, 0 < t → x t ≤ Function.leftLim x t) (ε : ℝ) (hε : 0 < ε)
    (p : ℝ) (hp : p ∈ Icc 0 B) :
    ∃ r > 0, ∀ u v, u ∈ Icc 0 B → v ∈ Icc 0 B → u ≤ v → dist u p < r → dist v p < r →
      x v - x u ≤ ε := by
  obtain ⟨hrc, l, hl⟩ := hx p hp
  obtain ⟨r1, hr1, hr1'⟩ := Metric.continuousWithinAt_iff.1 hrc (ε / 2) (by positivity)
  by_cases hp0 : 0 < p
  · obtain ⟨r2, hr2, hr2'⟩ := Metric.tendsto_nhdsWithin_nhds.1 hl (ε / 2) (by positivity)
    have hll : Function.leftLim x p = l := by
      apply leftLim_eq_of_tendsto
      have hmem : Icc 0 B ∈ 𝓝[<] p :=
        mem_of_superset (Ioo_mem_nhdsLT hp0) (fun s hs => ⟨hs.1.le, hs.2.le.trans hp.2⟩)
      rw [← nhdsWithin_inter_of_mem hmem]
      exact hl
    have hxp : x p ≤ l := hll ▸ hj p hp hp0
    refine ⟨min r1 r2, lt_min hr1 hr2, fun u v hu hv huv hup hvp => ?_⟩
    have hup1 := lt_of_lt_of_le hup (min_le_left _ _)
    have hup2 := lt_of_lt_of_le hup (min_le_right _ _)
    have hvp1 := lt_of_lt_of_le hvp (min_le_left _ _)
    have hvp2 := lt_of_lt_of_le hvp (min_le_right _ _)
    by_cases hvl : v < p
    · have a1 := hr2' ⟨hu, lt_of_le_of_lt huv hvl⟩ hup2
      have a2 := hr2' ⟨hv, hvl⟩ hvp2
      rw [Real.dist_eq] at a1 a2
      linarith [abs_lt.1 a1, abs_lt.1 a2]
    · push_neg at hvl
      have a2 := hr1' ⟨hv, hvl⟩ hvp1
      rw [Real.dist_eq] at a2
      by_cases hul : u < p
      · have a1 := hr2' ⟨hu, hul⟩ hup2
        rw [Real.dist_eq] at a1
        linarith [abs_lt.1 a1, abs_lt.1 a2]
      · push_neg at hul
        have a1 := hr1' ⟨hu, hul⟩ hup1
        rw [Real.dist_eq] at a1
        linarith [abs_lt.1 a1, abs_lt.1 a2]
  · have hp0' : p = 0 := le_antisymm (not_lt.1 hp0) hp.1
    refine ⟨r1, hr1, fun u v hu hv huv hup hvp => ?_⟩
    have a1 := hr1' ⟨hu, hp0' ▸ hu.1⟩ hup
    have a2 := hr1' ⟨hv, hp0' ▸ hv.1⟩ hvp
    rw [Real.dist_eq] at a1 a2
    linarith [abs_lt.1 a1, abs_lt.1 a2]

/-- Uniform upper modulus of a càdlàg path without positive jumps. -/
lemma upper_modulus (B : ℝ) (x : ℝ → ℝ) (hx : IsCadlagOn (Icc 0 B) x)
    (hj : ∀ t ∈ Icc 0 B, 0 < t → x t ≤ Function.leftLim x t) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ u v, u ∈ Icc 0 B → v ∈ Icc 0 B → u ≤ v → v - u < δ → x v - x u ≤ ε := by
  choose! r hr hr' using local_upper B x hx hj ε hε
  obtain ⟨δ, hδ, hδ'⟩ := lebesgue_number_lemma_of_metric (c := fun p : Icc 0 B => ball (p : ℝ) (r p))
    isCompact_Icc (fun _ => isOpen_ball)
    (fun p hp => mem_iUnion.2 ⟨⟨p, hp⟩, mem_ball_self (hr p hp)⟩)
  refine ⟨δ, hδ, fun u v hu hv huv hvu => ?_⟩
  obtain ⟨⟨p, hp⟩, hball⟩ := hδ' u hu
  have hu' : u ∈ ball p (r p) := hball (mem_ball_self hδ)
  have hv' : v ∈ ball p (r p) := hball (by rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  exact hr' p hp u v hu hv huv hu' hv'


lemma exists_cont_point {S : Type*} [MetricSpace S] (x : ℝ → S) (p q : ℝ) (hpq : p < q)
    (hx : IsCadlagOn (Icc p q) x) : ∃ u ∈ Ioo p q, ContinuousAt x u := by
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

lemma upper3 {S : Type*} [MetricSpace S] (T : Set ℝ) (x : ℝ → S) (hx : IsCadlagOn T x)
    (hT : T.OrdConnected) (c : ℝ) (hc : c ∈ T) :
    ∃ c' ∈ T, c ≤ c' ∧ (ContinuousWithinAt x T c' ∨ IsEndpoint T c') := by
  by_cases h : ∃ s ∈ T, c < s
  · obtain ⟨s, hs, hsc⟩ := h
    obtain ⟨c', hc'1, hc'2⟩ := exists_cont_point x c s hsc (cadlag_mono hx (hT.out hc hs))
    exact ⟨c', hT.out hc hs (Ioo_subset_Icc_self hc'1), hc'1.1.le,
      Or.inl hc'2.continuousWithinAt⟩
  · push_neg at h
    exact ⟨c, hc, le_rfl, Or.inr (Or.inr ⟨hc, fun u hu => h u hu⟩)⟩

lemma runSup_neg (u : ℝ → ℝ) (t : ℝ) : runSup (fun s => -u s) t = -runInf u t := by
  unfold runSup runInf
  rw [show (fun s => -u s) '' Icc 0 t = -(u '' Icc 0 t) by
    rw [← Set.image_neg_eq_neg, Set.image_image]]
  exact Real.sSup_neg _


/-! ### Running supremum: càdlàg property and the time-change estimate -/

lemma bdd_on (T : Set ℝ) (hT : T.OrdConnected) (h0 : IsLeast T 0) (u : ℝ → ℝ)
    (hu : IsCadlagOn T u) (t : ℝ) (ht : t ∈ T) : ∃ M, 0 ≤ M ∧ ∀ s ∈ Icc 0 t, |u s| ≤ M :=
  cadlag_bdd 0 t (h0.2 ht) u (cadlag_mono hu (hT.out h0.1 ht))

lemma bddAbove_of_abs (u : ℝ → ℝ) (I J : Set ℝ) (hIJ : I ⊆ J) (M : ℝ)
    (hM : ∀ s ∈ J, |u s| ≤ M) : BddAbove (u '' I) :=
  ⟨M, by rintro _ ⟨v, hv, rfl⟩; exact (abs_le.1 (hM v (hIJ hv))).2⟩

lemma runSup_mono (u : ℝ → ℝ) (s s' : ℝ) (hs : 0 ≤ s) (hss : s ≤ s')
    (hb : BddAbove (u '' Icc 0 s')) : runSup u s ≤ runSup u s' :=
  csSup_le_csSup hb ((nonempty_Icc.2 hs).image u) (image_mono (Icc_subset_Icc le_rfl hss))

lemma runSup_cadlag (T : Set ℝ) (hT : T.OrdConnected) (h0 : IsLeast T 0) (u : ℝ → ℝ)
    (hu : IsCadlagOn T u) : IsCadlagOn T (runSup u) := by
  intro t ht
  have ht0 : 0 ≤ t := h0.2 ht
  constructor
  · rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨r, hr, hr'⟩ := Metric.continuousWithinAt_iff.1 (hu t ht).1 (ε / 2) (by positivity)
    refine ⟨r, hr, fun {s} hs hst => ?_⟩
    obtain ⟨M, -, hM⟩ := bdd_on T hT h0 u hu s hs.1
    have hbs : BddAbove (u '' Icc 0 s) := bddAbove_of_abs u _ _ subset_rfl M hM
    have hbt : BddAbove (u '' Icc 0 t) :=
      bddAbove_of_abs u _ _ (Icc_subset_Icc le_rfl hs.2) M hM
    have h1 : runSup u t ≤ runSup u s := runSup_mono u t s ht0 hs.2 hbs
    have hut : u t ≤ runSup u t := le_csSup hbt (mem_image_of_mem u ⟨ht0, le_rfl⟩)
    have h2 : runSup u s ≤ runSup u t + ε / 2 := by
      unfold runSup
      apply csSup_le ((nonempty_Icc.2 (ht0.trans hs.2)).image u)
      rintro _ ⟨v, hv, rfl⟩
      by_cases hvt : v ≤ t
      · have := le_csSup hbt (mem_image_of_mem u ⟨hv.1, hvt⟩); linarith
      · push_neg at hvt
        have hvT : v ∈ T := hT.out h0.1 hs.1 hv
        have hd : dist v t < r := by
          rw [Real.dist_eq] at hst ⊢; rw [abs_lt] at hst ⊢
          constructor <;> linarith [hv.2]
        have := hr' ⟨hvT, hvt.le⟩ hd
        rw [Real.dist_eq, abs_lt] at this
        unfold runSup at hut
        linarith [this.2]
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  · by_cases ht0' : t = 0
    · subst ht0'
      refine ⟨0, ?_⟩
      have : T ∩ Iio 0 = ∅ := by
        ext s; simp only [mem_inter_iff, mem_Iio, mem_empty_iff_false, iff_false, not_and, not_lt]
        intro hs; exact h0.2 hs
      rw [this, nhdsWithin_empty]
      exact tendsto_bot
    · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht0')
      obtain ⟨M, -, hM⟩ := bdd_on T hT h0 u hu t ht
      have hbt : BddAbove (u '' Icc 0 t) := bddAbove_of_abs u _ _ subset_rfl M hM
      have Mf : MonotoneOn (runSup u) (Ioo 0 t) := fun a ha b hb hab =>
        runSup_mono u a b ha.1.le hab (bddAbove_of_abs u _ _ (Icc_subset_Icc le_rfl hb.2.le) M hM)
      have hbdd : BddAbove (runSup u '' Ioo 0 t) :=
        ⟨runSup u t, by rintro _ ⟨a, ha, rfl⟩; exact runSup_mono u a t ha.1.le ha.2.le hbt⟩
      exact ⟨_, (Mf.tendsto_nhdsWithin_Ioo_left (nonempty_Ioo.2 htpos) hbdd).mono_left
        (nhdsWithin_mono _ inter_subset_right)⟩

lemma image_Icc_of (p q : ℝ) (hpq : p ≤ q) (f : ℝ → ℝ) (hm : StrictMonoOn f (Icc p q))
    (hc : ContinuousOn f (Icc p q)) : f '' Icc p q = Icc (f p) (f q) := by
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    exact ⟨hm.monotoneOn ⟨le_rfl, hpq⟩ ht ht.1, hm.monotoneOn ht ⟨hpq, le_rfl⟩ ht.2⟩
  · exact intermediate_value_Icc hpq hc

lemma tc_ends (b : ℝ) (hb : 0 ≤ b) (l : ℝ → ℝ) (h : IsTimeChange 0 b l) : l 0 = 0 ∧ l b = b := by
  obtain ⟨hm, hc, him⟩ := h
  rw [image_Icc_of 0 b hb l hm hc] at him
  exact (Icc_eq_Icc_iff (hm.monotoneOn ⟨le_rfl, hb⟩ ⟨hb, le_rfl⟩ hb)).1 him

lemma sSup_le_add (I : Set ℝ) (hI : I.Nonempty) (f g : ℝ → ℝ) (d : ℝ)
    (hg : BddAbove (g '' I)) (h : ∀ s ∈ I, f s ≤ g s + d) :
    sSup (f '' I) ≤ sSup (g '' I) + d := by
  apply csSup_le (hI.image f)
  rintro _ ⟨s, hs, rfl⟩
  have := le_csSup hg (mem_image_of_mem g hs)
  linarith [h s hs]

lemma runSup_tc (B : ℝ) (hB : 0 ≤ B) (l : ℝ → ℝ) (hl : IsTimeChange 0 B l) (u v : ℝ → ℝ)
    (Mu Mv d : ℝ) (hu : ∀ s ∈ Icc 0 B, |u s| ≤ Mu) (hv : ∀ s ∈ Icc 0 B, |v s| ≤ Mv)
    (hd : ∀ s ∈ Icc 0 B, |u s - v (l s)| ≤ d) :
    ∀ t ∈ Icc 0 B, |runSup u t - runSup v (l t)| ≤ d := by
  intro t ht
  have hlmem : ∀ s ∈ Icc 0 B, l s ∈ Icc 0 B := fun s hs => hl.2.2 ▸ mem_image_of_mem l hs
  have hI : Icc 0 t ⊆ Icc 0 B := Icc_subset_Icc le_rfl ht.2
  have himg : l '' Icc 0 t = Icc 0 (l t) := by
    rw [image_Icc_of 0 t ht.1 l (hl.1.mono hI) (hl.2.1.mono hI), (tc_ends B hB l hl).1]
  have hne : (Icc (0:ℝ) t).Nonempty := ⟨0, le_rfl, ht.1⟩
  have hry : runSup v (l t) = sSup ((v ∘ l) '' Icc 0 t) := by
    unfold runSup; rw [image_comp, himg]
  have hbx : BddAbove (u '' Icc 0 t) := bddAbove_of_abs u _ _ hI Mu hu
  have hby : BddAbove ((v ∘ l) '' Icc 0 t) := ⟨Mv, by
    rintro _ ⟨s, hs, rfl⟩; exact (abs_le.1 (hv (l s) (hlmem s (hI hs)))).2⟩
  have e1 := sSup_le_add (Icc 0 t) hne u (v ∘ l) d hby fun s hs => by
    have := abs_le.1 (hd s (hI hs)); simp only [Function.comp]; linarith
  have e2 := sSup_le_add (Icc 0 t) hne (v ∘ l) u d hbx fun s hs => by
    have := abs_le.1 (hd s (hI hs)); simp only [Function.comp]; linarith
  rw [hry, abs_le]
  unfold runSup
  constructor <;> linarith

lemma runInf_tc (B : ℝ) (hB : 0 ≤ B) (l : ℝ → ℝ) (hl : IsTimeChange 0 B l) (u v : ℝ → ℝ)
    (Mu Mv d : ℝ) (hu : ∀ s ∈ Icc 0 B, |u s| ≤ Mu) (hv : ∀ s ∈ Icc 0 B, |v s| ≤ Mv)
    (hd : ∀ s ∈ Icc 0 B, |u s - v (l s)| ≤ d) :
    ∀ t ∈ Icc 0 B, |runInf u t - runInf v (l t)| ≤ d := by
  intro t ht
  have := runSup_tc B hB l hl (fun s => -u s) (fun s => -v s) Mu Mv d
    (fun s hs => by simpa using hu s hs) (fun s hs => by simpa using hv s hs)
    (fun s hs => by
      have := hd s hs
      rw [show -u s - -v (l s) = -(u s - v (l s)) by ring, abs_neg]; exact this) t ht
  rw [runSup_neg, runSup_neg, show -runInf u t - -runInf v (l t) = -(runInf u t - runInf v (l t))
    by ring, abs_neg] at this
  exact this

lemma barrier_eq (u : ℝ → ℝ) : barrier u = fun t => u t + runSup (fun s => -u s) t := by
  funext t; rw [runSup_neg]; unfold barrier; ring

lemma barrier_cadlag' (T : Set ℝ) (hT : T.OrdConnected) (h0 : IsLeast T 0) (u : ℝ → ℝ)
    (hu : IsCadlagOn T u) : IsCadlagOn T (barrier u) := by
  rw [barrier_eq]
  exact cadlag_add hu (runSup_cadlag T hT h0 _ (cadlag_neg hu))

/-! ### From initial intervals `[0, B]` to all admissible compact intervals -/

lemma pointwise_of_j1 (B : ℝ) (hB : 0 ≤ B) (ws : ℕ → ℝ → ℝ) (w : ℝ → ℝ)
    (h : J1TendstoOn 0 B ws w) (a : ℝ) (ha : a ∈ Icc 0 B)
    (hc : a = 0 ∨ a = B ∨ ContinuousAt w a) : Tendsto (fun n => ws n a) atTop (𝓝 (w a)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  unfold J1TendstoOn at h
  rw [tendsto_zero_iff_real] at h
  obtain ⟨r, hr, hr'⟩ : ∃ r > 0, r ≤ ε / 2 ∧ ∀ s, dist s a < r → dist (w s) (w a) < ε / 2 ∨
      a = 0 ∨ a = B := by
    rcases hc with hc | hc | hc
    · exact ⟨ε / 2, by positivity, le_rfl, fun _ _ => Or.inr (Or.inl hc)⟩
    · exact ⟨ε / 2, by positivity, le_rfl, fun _ _ => Or.inr (Or.inr hc)⟩
    · obtain ⟨r, hr, hr'⟩ := Metric.continuousAt_iff.1 hc (ε / 2) (by positivity)
      exact ⟨min r (ε / 2), lt_min hr (by positivity), min_le_right _ _,
        fun s hs => Or.inl (hr' (lt_of_lt_of_le hs (min_le_left _ _)))⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h r hr)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨l, hl, hlb⟩ := exists_of_j1Dist_lt 0 B _ w r (hN n hn)
  have e1 := (hlb a ha).2
  have hends := tc_ends B hB l hl
  rcases hr'.2 (l a) (hlb a ha).1 with h2 | h2 | h2
  · calc dist (ws n a) (w a) ≤ dist (ws n a) (w (l a)) + dist (w (l a)) (w a) := dist_triangle _ _ _
      _ < ε := by linarith [hr'.1]
  · subst h2; rw [hends.1] at e1; linarith [hr'.1]
  · subst h2; rw [hends.2] at e1; linarith [hr'.1]

lemma j1_point (a : ℝ) (ws : ℕ → ℝ → ℝ) (w : ℝ → ℝ)
    (h : Tendsto (fun n => ws n a) atTop (𝓝 (w a))) : J1TendstoOn a a ws w := by
  unfold J1TendstoOn
  rw [tendsto_zero_iff_real]
  intro η hη
  filter_upwards [(Metric.tendsto_nhds.1 h) (η / 2) (by positivity)] with n hn
  refine lt_of_le_of_lt (j1Dist_le_of a a _ _ id (tc_id a a) (η / 2) fun t ht => ⟨?_, ?_⟩)
    ((ENNReal.ofReal_lt_ofReal_iff hη).2 (by linarith))
  · simp; positivity
  · have : t = a := le_antisymm ht.2 ht.1
    subst this; exact hn.le

lemma restrict (B a b : ℝ) (hab : a ≤ b) (ha0 : 0 ≤ a) (hbB : b ≤ B) (ws : ℕ → ℝ → ℝ)
    (w : ℝ → ℝ) (hws : ∀ n, IsCadlagOn (Icc 0 B) (ws n)) (hw : IsCadlagOn (Icc 0 B) w)
    (h : J1TendstoOn 0 B ws w) (ha : a = 0 ∨ a = B ∨ ContinuousAt w a)
    (hb : b = 0 ∨ b = B ∨ ContinuousAt w b) : J1TendstoOn a b ws w := by
  have hB : 0 ≤ B := ha0.trans (hab.trans hbB)
  rcases eq_or_lt_of_le hab with hab' | hab'
  · subst hab'
    exact j1_point a ws w (pointwise_of_j1 B hB ws w h a ⟨ha0, hbB⟩ ha)
  have ha' : a = 0 ∨ ContinuousAt w a := by
    rcases ha with ha | ha | ha
    · exact Or.inl ha
    · exact absurd (ha ▸ hbB) (not_le.2 hab')
    · exact Or.inr ha
  have hb' : b = B ∨ ContinuousAt w b := by
    rcases hb with hb | hb | hb
    · exact absurd (hb ▸ hab') (not_lt.2 ha0)
    · exact Or.inl hb
    · exact Or.inr hb
  -- convergence on `[a, B]`
  have haB : J1TendstoOn a B ws w := by
    rcases ha' with ha' | ha'
    · subst ha'; exact h
    · rcases eq_or_lt_of_le ha0 with h0a | h0a
      · subst h0a; exact h
      · exact ((lemma_2_2 0 a B h0a (lt_of_lt_of_le hab' hbB) ws w hws hw ha').1 h).2
  rcases hb' with hb' | hb'
  · subst hb'; exact haB
  · rcases eq_or_lt_of_le hbB with hbB' | hbB'
    · subst hbB'; exact haB
    · exact ((lemma_2_2 a b B hab' hbB' ws w
        (fun n => cadlag_mono (hws n) (Icc_subset_Icc ha0 le_rfl))
        (cadlag_mono hw (Icc_subset_Icc ha0 le_rfl)) hb').1 haB).1

lemma j1Tendsto_of_initial (T : Set ℝ) (hT : T.OrdConnected) (h0 : IsLeast T 0)
    (ws : ℕ → ℝ → ℝ) (w : ℝ → ℝ) (hws : ∀ n, IsCadlagOn T (ws n)) (hw : IsCadlagOn T w)
    (hinit : ∀ b ∈ T, ∃ B ∈ T, b ≤ B ∧ J1TendstoOn 0 B ws w) : J1Tendsto T ws w := by
  refine ⟨hws, hw, fun a b hab hsub ha hb => ?_⟩
  have haT : a ∈ T := hsub ⟨le_rfl, hab⟩
  have hbT : b ∈ T := hsub ⟨hab, le_rfl⟩
  have ha0 : 0 ≤ a := h0.2 haT
  obtain ⟨B, hBT, hbB, hJ⟩ := hinit b hbT
  have hsB : Icc 0 B ⊆ T := hT.out h0.1 hBT
  have hint : ∀ s, 0 < s → s < B → T ∈ 𝓝 s := fun s h1 h2 =>
    mem_of_superset (Ioo_mem_nhds h1 h2) (Ioo_subset_Icc_self.trans hsB)
  have conv : ∀ s ∈ T, (ContinuousWithinAt w T s ∨ IsEndpoint T s) → s ≤ B →
      s = 0 ∨ s = B ∨ ContinuousAt w s := by
    intro s hsT hs hsB'
    rcases hs with hs | hs | hs
    · rcases eq_or_lt_of_le (h0.2 hsT) with h1 | h1
      · exact Or.inl h1.symm
      rcases eq_or_lt_of_le hsB' with h2 | h2
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (hs.continuousAt (hint s h1 h2)))
    · exact Or.inl (le_antisymm (hs.2 h0.1) (h0.2 hsT))
    · exact Or.inr (Or.inl (le_antisymm hsB' (hs.2 hBT)))
  exact restrict B a b hab ha0 hbB ws w (fun n => cadlag_mono (hws n) hsB) (cadlag_mono hw hsB) hJ
    (conv a haT ha (hab.trans hbB)) (conv b hbT hb hbB)


lemma cadlag_of_centered (T : Set ℝ) (u : ℝ → ℝ) (k : ℝ)
    (h : IsCadlagOn T (fun t => u t - k * t)) : IsCadlagOn T u := by
  have := cadlag_add h (cadlag_of_continuous (u := fun t => k * t) (by fun_prop))
  simpa using this

/-! ### Theorem 6.2 -/

lemma runSup_j1_initial (B : ℝ) (hB : 0 ≤ B) (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ)
    (hxs : ∀ n, IsCadlagOn (Icc 0 B) (xs n)) (hx : IsCadlagOn (Icc 0 B) x)
    (h : J1TendstoOn 0 B xs x) : J1TendstoOn 0 B (fun n => runSup (xs n)) (runSup x) := by
  unfold J1TendstoOn at *
  rw [tendsto_zero_iff_real] at h ⊢
  intro η hη
  filter_upwards [h (η / 2) (by positivity)] with n hn
  obtain ⟨l, hl, hlb⟩ := exists_of_j1Dist_lt 0 B _ x _ hn
  obtain ⟨Mn, -, hMn⟩ := cadlag_bdd 0 B hB (xs n) (hxs n)
  obtain ⟨Mx, -, hMx⟩ := cadlag_bdd 0 B hB x hx
  have hd : ∀ s ∈ Icc 0 B, |xs n s - x (l s)| ≤ η / 2 := fun s hs => by
    have := (hlb s hs).2; rw [Real.dist_eq] at this; exact this.le
  have hsup := runSup_tc B hB l hl (xs n) x Mn Mx (η / 2) hMn hMx hd
  refine lt_of_le_of_lt (j1Dist_le_of 0 B _ _ l hl (η / 2) fun t ht => ⟨?_, ?_⟩)
    ((ENNReal.ofReal_lt_ofReal_iff hη).2 (by linarith))
  · linarith [(hlb t ht).1]
  · rw [Real.dist_eq]; exact hsup t ht

lemma add_linear_j1 (T : Set ℝ) (ys : ℕ → ℝ → ℝ) (x : ℝ → ℝ) (c : ℕ → ℝ) (c₀ : ℝ)
    (h : J1Tendsto T ys x) (hc : Tendsto c atTop (𝓝 c₀)) :
    J1Tendsto T (fun n t => ys n t + c n * t) (fun t => x t + c₀ * t) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun n => cadlag_add (h1 n) (cadlag_of_continuous (u := fun t => c n * t) (by fun_prop)),
    cadlag_add h2 (cadlag_of_continuous (u := fun t => c₀ * t) (by fun_prop)),
    fun a b hab hsub ha hb => ?_⟩
  have hlin : Continuous fun t : ℝ => c₀ * t := by fun_prop
  have conv : ∀ s, (ContinuousWithinAt (fun t => x t + c₀ * t) T s ∨ IsEndpoint T s) →
      (ContinuousWithinAt x T s ∨ IsEndpoint T s) := by
    intro s hs
    rcases hs with hs | hs
    · left
      have := hs.sub hlin.continuousWithinAt
      convert this using 1
      funext t; simp
    · exact Or.inr hs
  have hz := h3 a b hab hsub (conv a ha) (conv b hb)
  unfold J1TendstoOn at *
  rw [tendsto_zero_iff_real] at hz ⊢
  intro η hη
  set K := |a| + |b| + 1 with hK
  have hKpos : 0 < K := by positivity
  set ρ := min (η / 8) (η / (8 * (|c₀| + 1))) with hρ
  have hρpos : 0 < ρ := lt_min (by positivity) (by positivity)
  have hev : ∀ᶠ n in atTop, dist (c n) c₀ < η / 8 / K :=
    (Metric.tendsto_nhds.1 hc) _ (by positivity)
  filter_upwards [hz ρ hρpos, hev] with n hn hcn
  obtain ⟨l, hl, hlb⟩ := exists_of_j1Dist_lt a b _ x ρ hn
  refine lt_of_le_of_lt (j1Dist_le_of a b _ _ l hl (η / 2) fun t ht => ⟨?_, ?_⟩)
    ((ENNReal.ofReal_lt_ofReal_iff hη).2 (by linarith))
  · linarith [(hlb t ht).1, min_le_left (η / 8) (η / (8 * (|c₀| + 1)))]
  · have e1 := (hlb t ht).1
    have e2 := (hlb t ht).2
    rw [Real.dist_eq] at e1 e2 hcn ⊢
    have htK : |t| ≤ K := by
      rw [abs_le]; constructor
      · linarith [ht.1, neg_abs_le a, abs_nonneg b]
      · linarith [ht.2, le_abs_self b, abs_nonneg a]
    have i1 : |(c n - c₀) * t| ≤ η / 8 := by
      rw [abs_mul]
      calc |c n - c₀| * |t| ≤ (η / 8 / K) * K := by gcongr
        _ = η / 8 := by field_simp
    have i2 : |c₀ * (t - l t)| ≤ η / 8 := by
      rw [abs_mul]
      have hρ2 : ρ ≤ η / (8 * (|c₀| + 1)) := min_le_right _ _
      have : |t - l t| ≤ η / (8 * (|c₀| + 1)) := by
        rw [abs_sub_comm]; linarith
      calc |c₀| * |t - l t| ≤ (|c₀| + 1) * (η / (8 * (|c₀| + 1))) := by
            gcongr; linarith
        _ = η / 8 := by field_simp
    have hρ1 : ρ ≤ η / 8 := min_le_left _ _
    calc |ys n t + c n * t - (x (l t) + c₀ * l t)|
        = |(ys n t - x (l t)) + ((c n - c₀) * t + c₀ * (t - l t))| := by ring_nf
      _ ≤ |ys n t - x (l t)| + (|(c n - c₀) * t| + |c₀ * (t - l t)|) :=
          (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
      _ ≤ η / 2 := by linarith

lemma part_i (T : Set ℝ) (hT : T.OrdConnected) (h0 : IsLeast T 0)
    (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ) (c : ℕ → ℝ)
    (hconv : J1Tendsto T (fun n t => xs n t - c n * t) x) (c₀ : ℝ)
    (hc : Tendsto c atTop (𝓝 c₀)) :
    J1Tendsto T (fun n => runSup (xs n)) (runSup (fun t => x t + c₀ * t)) := by
  have hsum := add_linear_j1 T _ x c c₀ hconv hc
  have e : (fun n t => xs n t - c n * t + c n * t) = xs := by funext n t; ring
  rw [e] at hsum
  refine j1Tendsto_of_initial T hT h0 _ _ (fun n => runSup_cadlag T hT h0 _ (hsum.1 n))
    (runSup_cadlag T hT h0 _ hsum.2.1) fun b hbT => ?_
  obtain ⟨B, hBT, hbB, hBc⟩ := upper3 T _ hsum.2.1 hT b hbT
  have hsB : Icc 0 B ⊆ T := hT.out h0.1 hBT
  exact ⟨B, hBT, hbB, runSup_j1_initial B (h0.2 hBT) xs _
    (fun n => cadlag_mono (hsum.1 n) hsB) (cadlag_mono hsum.2.1 hsB)
    (hsum.2.2 0 B (h0.2 hBT) hsB (Or.inr (Or.inl h0)) hBc)⟩

lemma leftLim_neg_of_cadlag (B : ℝ) (x : ℝ → ℝ) (hx : IsCadlagOn (Icc 0 B) x) (t : ℝ)
    (ht : t ∈ Icc 0 B) (ht0 : 0 < t) :
    Function.leftLim (fun s => -x s) t = -Function.leftLim x t := by
  obtain ⟨-, l, hl⟩ := hx t ht
  have hmem : Icc 0 B ∈ 𝓝[<] t :=
    mem_of_superset (Ioo_mem_nhdsLT ht0) (fun s hs => ⟨hs.1.le, hs.2.le.trans ht.2⟩)
  rw [nhdsWithin_inter_of_mem hmem] at hl
  rw [leftLim_eq_of_tendsto hl, leftLim_eq_of_tendsto hl.neg]

lemma part_ii (T : Set ℝ) (hT : T.OrdConnected) (h0 : IsLeast T 0)
    (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ) (c : ℕ → ℝ)
    (hconv : J1Tendsto T (fun n t => xs n t - c n * t) x)
    (hc : Tendsto c atTop atTop) (hj : NoNegJump T x) :
    J1Tendsto T (fun n t => runSup (xs n) t - c n * t) x := by
  have hxs : ∀ n, IsCadlagOn T (xs n) := fun n => cadlag_of_centered T _ _ (hconv.1 n)
  refine j1Tendsto_of_initial T hT h0 _ _ (fun n => ?_) hconv.2.1 fun b hbT => ?_
  · have := cadlag_add (runSup_cadlag T hT h0 _ (hxs n))
      (cadlag_of_continuous (u := fun t => -(c n * t)) (by fun_prop))
    simpa [sub_eq_add_neg] using this
  obtain ⟨B, hBT, hbB, hBc⟩ := upper3 T x hconv.2.1 hT b hbT
  have hB0 : 0 ≤ B := h0.2 hBT
  have hsB : Icc 0 B ⊆ T := hT.out h0.1 hBT
  refine ⟨B, hBT, hbB, ?_⟩
  have hJ := hconv.2.2 0 B hB0 hsB (Or.inr (Or.inl h0)) hBc
  have hxc : IsCadlagOn (Icc 0 B) x := cadlag_mono hconv.2.1 hsB
  obtain ⟨M, hM0, hM⟩ := cadlag_bdd 0 B hB0 x hxc
  unfold J1TendstoOn at hJ ⊢
  rw [tendsto_zero_iff_real] at hJ ⊢
  intro ε hε
  -- lower modulus of `x`, i.e. upper modulus of `-x`
  obtain ⟨δ, hδ, hδ'⟩ := upper_modulus B (fun s => -x s) (cadlag_neg hxc)
    (fun t ht ht0 => by
      rw [leftLim_neg_of_cadlag B x hxc t ht ht0, neg_le_neg_iff]
      exact hj t (hsB ht) ht0) (ε / 4) (by positivity)
  set ρ := min (δ / 4) (ε / 8) with hρ
  have hρpos : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρ1 : ρ ≤ δ / 4 := min_le_left _ _
  have hρ2 : ρ ≤ ε / 8 := min_le_right _ _
  have hcb : ∀ᶠ n in atTop, 2 * (2 * M + ε) / δ ≤ c n := hc.eventually (eventually_ge_atTop _)
  filter_upwards [hJ ρ hρpos, hcb] with n hn hcn
  obtain ⟨l, hl, hlb⟩ := exists_of_j1Dist_lt 0 B _ x ρ hn
  have hlmem : ∀ t ∈ Icc 0 B, l t ∈ Icc 0 B := fun t ht => hl.2.2 ▸ mem_image_of_mem l ht
  have hKpos : 0 < 2 * (2 * M + ε) / δ := by positivity
  have key : ∀ s t, s ∈ Icc 0 B → t ∈ Icc 0 B → s ≤ t →
      xs n s - c n * t ≤ x (l t) + ε / 2 := by
    intro s t hs ht hst
    have e1 := (hlb s hs)
    rw [Real.dist_eq, Real.dist_eq, abs_lt, abs_lt] at e1
    have hdecomp : xs n s - c n * t = (xs n s - c n * s) - c n * (t - s) := by ring
    by_cases hd : t - s < δ / 2
    · have hlst : l s ≤ l t := hl.1.monotoneOn hs ht hst
      have hmod := hδ' (l s) (l t) (hlmem s hs) (hlmem t ht) hlst (by
        linarith [(hlb t ht).1, abs_lt.1 (show |l t - t| < ρ by rw [← Real.dist_eq]; exact (hlb t ht).1)])
      have hpos : 0 ≤ c n * (t - s) := mul_nonneg (by linarith) (by linarith)
      linarith
    · push_neg at hd
      have h1 := hM (l t) (hlmem t ht)
      have h2 := hM (l s) (hlmem s hs)
      rw [abs_le] at h1 h2
      have hge : 2 * (2 * M + ε) / δ * (δ / 2) ≤ c n * (t - s) := by
        have : c n * (δ / 2) ≤ c n * (t - s) := mul_le_mul_of_nonneg_left hd (by linarith)
        refine le_trans ?_ this
        exact mul_le_mul_of_nonneg_right hcn (by positivity)
      have hcalc : 2 * (2 * M + ε) / δ * (δ / 2) = 2 * M + ε := by field_simp
      linarith
  refine lt_of_le_of_lt (j1Dist_le_of 0 B _ _ l hl (ε / 2) fun t ht => ⟨?_, ?_⟩)
    ((ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith))
  · linarith [(hlb t ht).1]
  have hI : Icc 0 t ⊆ Icc 0 B := Icc_subset_Icc le_rfl ht.2
  have hne : (xs n '' Icc 0 t).Nonempty := ⟨xs n t, mem_image_of_mem _ ⟨ht.1, le_rfl⟩⟩
  have hup : ∀ y ∈ xs n '' Icc 0 t, y ≤ x (l t) + ε / 2 + c n * t := by
    rintro _ ⟨s, hs, rfl⟩
    have := key s t (hI hs) ht hs.2
    linarith
  have hbdd : BddAbove (xs n '' Icc 0 t) := ⟨_, hup⟩
  have i1 : xs n t ≤ runSup (xs n) t := le_csSup hbdd (mem_image_of_mem _ ⟨ht.1, le_rfl⟩)
  have i2 : runSup (xs n) t ≤ x (l t) + ε / 2 + c n * t := csSup_le hne hup
  have e2 := (hlb t ht).2
  rw [Real.dist_eq, abs_lt] at e2
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [e2.1, e2.2]

lemma part_iii (T : Set ℝ) (hT : T.OrdConnected) (h0 : IsLeast T 0)
    (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ) (c : ℕ → ℝ)
    (hconv : J1Tendsto T (fun n t => xs n t - c n * t) x)
    (hc : Tendsto c atTop atBot) :
    UTendsto T (fun n => runSup (xs n)) (fun _ => x 0) := by
  intro a b hab
  by_cases hle : a ≤ b
  swap
  · simp only [supDist, Icc_eq_empty hle, mem_empty_iff_false, iSup_false, iSup_const]
    exact tendsto_const_nhds
  have hbT : b ∈ T := hab ⟨hle, le_rfl⟩
  have ha0 : 0 ≤ a := h0.2 (hab ⟨le_rfl, hle⟩)
  obtain ⟨B, hBT, hbB, hBc⟩ := upper3 T x hconv.2.1 hT b hbT
  have hB0 : 0 ≤ B := h0.2 hBT
  have hsub : Icc 0 B ⊆ T := hT.out h0.1 hBT
  have hJ := hconv.2.2 0 B hB0 hsub (Or.inr (Or.inl h0)) hBc
  have hxc : IsCadlagOn (Icc 0 B) x := cadlag_mono hconv.2.1 hsub
  obtain ⟨M, hM0, hM⟩ := cadlag_bdd 0 B hB0 x hxc
  unfold J1TendstoOn at hJ
  rw [tendsto_zero_iff_real] at hJ ⊢
  intro ε hε
  obtain ⟨t₀, ht₀, ht₀'⟩ := Metric.continuousWithinAt_iff.1 (hconv.2.1 0 h0.1).1 (ε / 4)
    (by positivity)
  set ρ := min (t₀ / 2) (ε / 4) with hρ
  have hρpos : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρ1 : ρ ≤ t₀ / 2 := min_le_left _ _
  have hρ2 : ρ ≤ ε / 4 := min_le_right _ _
  have hcb : ∀ᶠ n in atTop, c n ≤ -(2 * (M + |x 0|) / t₀) :=
    hc.eventually (eventually_le_atBot _)
  filter_upwards [hJ ρ hρpos, hcb] with n hn hcn
  obtain ⟨l, hl, hlb⟩ := exists_of_j1Dist_lt 0 B _ x ρ hn
  have hlmem : ∀ t ∈ Icc 0 B, l t ∈ Icc 0 B := fun t ht => hl.2.2 ▸ mem_image_of_mem l ht
  have hl0 : l 0 = 0 := (tc_ends B hB0 l hl).1
  have hKpos : 0 ≤ 2 * (M + |x 0|) / t₀ := by positivity
  have key : ∀ s ∈ Icc 0 B, xs n s ≤ x 0 + ε / 2 := by
    intro s hs
    have e1 := (hlb s hs)
    rw [Real.dist_eq, Real.dist_eq, abs_lt, abs_lt] at e1
    by_cases hd : s < t₀ / 2
    · have hls : dist (l s) 0 < t₀ := by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [(hlmem s hs).1]
      have := ht₀' ⟨hsub (hlmem s hs), (hlmem s hs).1⟩ hls
      rw [Real.dist_eq, abs_lt] at this
      have hneg : c n * s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hs.1
      linarith [this.2]
    · push_neg at hd
      have h1 := hM (l s) (hlmem s hs)
      rw [abs_le] at h1
      have hle' : c n * s ≤ -(2 * (M + |x 0|) / t₀) * (t₀ / 2) := by
        have : c n * s ≤ c n * (t₀ / 2) := mul_le_mul_of_nonpos_left hd (by linarith)
        exact this.trans (mul_le_mul_of_nonneg_right hcn (by positivity))
      have hcalc : -(2 * (M + |x 0|) / t₀) * (t₀ / 2) = -(M + |x 0|) := by field_simp
      linarith [neg_abs_le (x 0)]
  have h0B : (0:ℝ) ∈ Icc 0 B := ⟨le_rfl, hB0⟩
  have hx0n : x 0 - ε / 4 < xs n 0 := by
    have e := (hlb 0 h0B).2
    rw [hl0, Real.dist_eq, abs_lt] at e
    linarith [e.1]
  refine lt_of_le_of_lt (supDist_le_of a b _ _ (ε / 2) fun t ht => ?_)
    ((ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith))
  have htB : t ∈ Icc 0 B := ⟨ha0.trans ht.1, ht.2.trans hbB⟩
  have hne : (xs n '' Icc 0 t).Nonempty := ⟨xs n t, mem_image_of_mem _ ⟨htB.1, le_rfl⟩⟩
  have hup : ∀ y ∈ xs n '' Icc 0 t, y ≤ x 0 + ε / 2 := by
    rintro _ ⟨s, hs, rfl⟩
    exact key s ⟨hs.1, hs.2.trans htB.2⟩
  have hbdd : BddAbove (xs n '' Icc 0 t) := ⟨_, hup⟩
  have i1 : xs n 0 ≤ runSup (xs n) t := le_csSup hbdd (mem_image_of_mem _ ⟨le_rfl, htB.1⟩)
  have i2 : runSup (xs n) t ≤ x 0 + ε / 2 := csSup_le hne hup
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

end W64c

open W64c in
theorem solution (T : Set ℝ) (hT : T.OrdConnected) (h0 : IsLeast T 0)
    (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ) (c : ℕ → ℝ)
    (hconv : WhittFLT.Composition.J1Tendsto T (fun n t => xs n t - c n * t) x) :
    (∀ c₀ : ℝ, Tendsto c atTop (𝓝 c₀) →
      WhittFLT.Composition.J1Tendsto T (fun n => runSup (xs n)) (runSup (fun t => x t + c₀ * t))) ∧
    (Tendsto c atTop atTop → NoNegJump T x →
      WhittFLT.Composition.J1Tendsto T (fun n t => runSup (xs n) t - c n * t) x) ∧
    (Tendsto c atTop atBot →
      WhittFLT.Composition.UTendsto T (fun n => runSup (xs n)) (fun _ => x 0)) :=
  ⟨part_i T hT h0 xs x c hconv, part_ii T hT h0 xs x c hconv, part_iii T hT h0 xs x c hconv⟩
