-- Prove2me | solution 2 for WhittFLT.Reflection.theorem_6_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T05:05:41.142802+00:00
-- url     : https://prove2.me/submissions/242ae95b-4a08-456a-8443-4c46992a18f4

import Mathlib
import Definitions.Def_WhittFLT_Composition_SkorohodD
import Definitions.Def_WhittFLT_Reflection_Supremum
import Theorems.Thm_WhittFLT_Reflection_billingsley_lemma_1
import Theorems.Thm_WhittFLT_Reflection_theorem_6_2
import Theorems.Thm_WhittFLT_Reflection_barrier_continuous

open WhittFLT.Composition WhittFLT.Reflection
open Set Filter Topology Metric
open scoped ENNReal

namespace W64

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

/-! ### The three parts -/

lemma hadd_real : ∀ s₁ s₂ s₃ s₄ : ℝ, dist (s₁ + s₂) (s₃ + s₄) ≤ dist s₁ s₃ + dist s₂ s₄ := by
  intro s₁ s₂ s₃ s₄
  simp only [Real.dist_eq]
  rw [show s₁ + s₂ - (s₃ + s₄) = (s₁ - s₃) + (s₂ - s₄) by ring]
  exact abs_add_le _ _

lemma linear_j1 (T : Set ℝ) (c : ℕ → ℝ) (c₀ : ℝ) (hc : Tendsto c atTop (𝓝 c₀)) :
    J1Tendsto T (fun n t => c n * t) (fun t => c₀ * t) := by
  refine ⟨fun n => cadlag_of_continuous (by fun_prop), cadlag_of_continuous (by fun_prop),
    fun a b _ _ _ _ => ?_⟩
  unfold J1TendstoOn
  rw [tendsto_zero_iff_real]
  intro η hη
  set K := |a| + |b| + 1 with hK
  have hKpos : 0 < K := by positivity
  have hev : ∀ᶠ n in atTop, dist (c n) c₀ < η / 2 / K :=
    (Metric.tendsto_nhds.1 hc) _ (by positivity)
  filter_upwards [hev] with n hn
  refine lt_of_le_of_lt (j1Dist_le_of a b _ _ id (tc_id a b) (η / 2) fun t ht => ⟨?_, ?_⟩)
    ((ENNReal.ofReal_lt_ofReal_iff hη).2 (by linarith))
  · simp; positivity
  · simp only [id, Real.dist_eq] at hn ⊢
    have htK : |t| ≤ K := by
      rw [abs_le]; constructor
      · linarith [ht.1, neg_abs_le a, abs_nonneg b]
      · linarith [ht.2, le_abs_self b, abs_nonneg a]
    rw [← sub_mul, abs_mul]
    calc |c n - c₀| * |t| ≤ (η / 2 / K) * K := by
          gcongr
      _ = η / 2 := by field_simp

lemma cadlag_of_centered (T : Set ℝ) (u : ℝ → ℝ) (k : ℝ)
    (h : IsCadlagOn T (fun t => u t - k * t)) : IsCadlagOn T u := by
  have := cadlag_add h (cadlag_of_continuous (u := fun t => k * t) (by fun_prop))
  simpa using this

lemma barrier_cadlag (T : Set ℝ) (hT : T.OrdConnected) (h0 : IsLeast T 0) (u : ℝ → ℝ)
    (hu : IsCadlagOn T u) : IsCadlagOn T (barrier u) := by
  have hc : J1Tendsto T (fun _ => u) u := by
    refine ⟨fun _ => hu, hu, fun a b _ _ _ _ => ?_⟩
    unfold J1TendstoOn
    rw [tendsto_zero_iff_real]
    intro η hη
    refine Eventually.of_forall fun _ => lt_of_le_of_lt
      (j1Dist_le_of a b u u id (tc_id a b) 0 fun t _ => ⟨by simp, by simp⟩)
      (by simpa using hη)
  exact (barrier_continuous T hT h0 (fun _ => u) u hc).2.1

lemma runSup_neg (u : ℝ → ℝ) (t : ℝ) : runSup (fun s => -u s) t = -runInf u t := by
  unfold runSup runInf
  rw [show (fun s => -u s) '' Icc 0 t = -(u '' Icc 0 t) by
    rw [← Set.image_neg_eq_neg, Set.image_image]]
  exact Real.sSup_neg _

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

lemma part2 (T : Set ℝ) (hT : T.OrdConnected) (h0 : IsLeast T 0)
    (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ) (c : ℕ → ℝ)
    (hconv : J1Tendsto T (fun n t => xs n t - c n * t) x) (hx0 : x 0 = 0)
    (hc : Tendsto c atTop atTop) :
    J1Tendsto T (fun n t => barrier (xs n) t - c n * t) x := by
  have hneg := j1Tendsto_neg hconv
  have hneg' : J1Tendsto T (fun n t => (fun s => -xs n s) t - (-c n) * t) (fun t => -x t) := by
    convert hneg using 3; ring
  have hU := (theorem_6_2 T hT h0 (fun n s => -xs n s) (fun t => -x t) (fun n => -c n)
    hneg').2.2 (tendsto_neg_atTop_atBot.comp hc)
  simp only [hx0, neg_zero] at hU
  have hxs : ∀ n, IsCadlagOn T (xs n) := fun n => cadlag_of_centered T _ _ (hconv.1 n)
  have hwc : ∀ n, IsCadlagOn T (runSup (fun s => -xs n s)) := by
    intro n
    have := cadlag_add (barrier_cadlag T hT h0 _ (hxs n)) (cadlag_neg (hxs n))
    convert this using 1
    funext t
    rw [runSup_neg]; unfold barrier; ring
  have := j1Tendsto_add_u hconv _ hU hwc
  convert this using 2
  funext t
  rw [runSup_neg]; unfold barrier; ring

lemma part3 (T : Set ℝ) (hT : T.OrdConnected) (h0 : IsLeast T 0)
    (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ) (c : ℕ → ℝ)
    (hconv : J1Tendsto T (fun n t => xs n t - c n * t) x)
    (hc : Tendsto c atTop atBot) (hj : NoPosJump T x) :
    UTendsto T (fun n => barrier (xs n)) (fun _ => 0) := by
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
  obtain ⟨δ, hδ, hδ'⟩ := upper_modulus B x hxc (fun t ht ht0 => hj t (hsub ht) ht0) (ε / 4)
    (by positivity)
  set ρ := min (δ / 4) (ε / 8) with hρ
  have hρpos : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρ1 : ρ ≤ δ / 4 := min_le_left _ _
  have hρ2 : ρ ≤ ε / 8 := min_le_right _ _
  have hcb : ∀ᶠ n in atTop, c n ≤ -(2 * (2 * M + ε) / δ) :=
    hc.eventually (eventually_le_atBot _)
  filter_upwards [hJ ρ hρpos, hcb] with n hn hcn
  obtain ⟨l, hl, hlb⟩ := exists_of_j1Dist_lt 0 B _ x ρ hn
  have hlmem : ∀ t ∈ Icc 0 B, l t ∈ Icc 0 B := fun t ht => hl.2.2 ▸ mem_image_of_mem l ht
  have hKpos : 0 < 2 * (2 * M + ε) / δ := by positivity
  -- the key increment bound
  have key : ∀ s t, s ∈ Icc 0 B → t ∈ Icc 0 B → s ≤ t → xs n t - xs n s ≤ ε / 2 := by
    intro s t hs ht hst
    have e1 := (hlb t ht)
    have e2 := (hlb s hs)
    rw [Real.dist_eq, Real.dist_eq, abs_lt, abs_lt] at e1 e2
    have hdecomp : xs n t - xs n s = ((xs n t - c n * t) - (xs n s - c n * s)) + c n * (t - s) := by
      ring
    by_cases hd : t - s < δ / 2
    · have hlst : l s ≤ l t := hl.1.monotoneOn hs ht hst
      have hmod := hδ' (l s) (l t) (hlmem s hs) (hlmem t ht) hlst (by linarith)
      have hneg : c n * (t - s) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      linarith
    · push_neg at hd
      have h1 := hM (l t) (hlmem t ht)
      have h2 := hM (l s) (hlmem s hs)
      rw [abs_le] at h1 h2
      have hneg : c n * (t - s) ≤ -(2 * (2 * M + ε) / δ) * (δ / 2) := by
        have : c n * (t - s) ≤ c n * (δ / 2) :=
          mul_le_mul_of_nonpos_left hd (by linarith)
        refine this.trans ?_
        exact mul_le_mul_of_nonneg_right hcn (by positivity)
      have hcalc : -(2 * (2 * M + ε) / δ) * (δ / 2) = -(2 * M + ε) := by
        field_simp
      linarith
  refine lt_of_le_of_lt (supDist_le_of a b _ _ (ε / 2) fun t ht => ?_)
    ((ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith))
  have htB : t ∈ Icc 0 B := ⟨ha0.trans ht.1, ht.2.trans hbB⟩
  have hne : (xs n '' Icc 0 t).Nonempty := ⟨xs n t, mem_image_of_mem _ ⟨htB.1, le_rfl⟩⟩
  have hlow : ∀ y ∈ xs n '' Icc 0 t, xs n t - ε / 2 ≤ y := by
    rintro _ ⟨s, hs, rfl⟩
    have := key s t ⟨hs.1, hs.2.trans htB.2⟩ htB hs.2
    linarith
  have hbdd : BddBelow (xs n '' Icc 0 t) := ⟨_, hlow⟩
  have i1 : runInf (xs n) t ≤ xs n t := csInf_le hbdd (mem_image_of_mem _ ⟨htB.1, le_rfl⟩)
  have i2 : xs n t - ε / 2 ≤ runInf (xs n) t := le_csInf hne hlow
  rw [Real.dist_eq, sub_zero, abs_le]
  unfold barrier
  constructor <;> linarith

end W64

open W64 in
theorem solution (T : Set ℝ) (hT : T.OrdConnected) (h0 : IsLeast T 0)
    (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ) (c : ℕ → ℝ)
    (hconv : WhittFLT.Composition.J1Tendsto T (fun n t => xs n t - c n * t) x) (hx0 : x 0 = 0) :
    (∀ c₀ : ℝ, Tendsto c atTop (𝓝 c₀) →
      WhittFLT.Composition.J1Tendsto T (fun n => barrier (xs n)) (barrier (fun t => x t + c₀ * t))) ∧
    (Tendsto c atTop atTop →
      WhittFLT.Composition.J1Tendsto T (fun n t => barrier (xs n) t - c n * t) x) ∧
    (Tendsto c atTop atBot → NoPosJump T x →
      WhittFLT.Composition.UTendsto T (fun n => barrier (xs n)) (fun _ => 0)) := by
  refine ⟨fun c₀ hc => ?_, part2 T hT h0 xs x c hconv hx0, part3 T hT h0 xs x c hconv⟩
  have hsum := add_linear_j1 T _ x c c₀ hconv hc
  have e : (fun n t => xs n t - c n * t + c n * t) = xs := by
    funext n t; ring
  rw [e] at hsum
  exact barrier_continuous T hT h0 xs _ hsum
