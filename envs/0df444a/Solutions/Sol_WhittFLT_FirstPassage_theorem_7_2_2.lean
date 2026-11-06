-- Prove2me | solution 2 for WhittFLT.FirstPassage.theorem_7_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T02:42:43.664862+00:00
-- url     : https://prove2.me/submissions/08b0088c-f181-4093-8763-26acfdd5858c

import Mathlib
import Definitions.Def_WhittFLT_FirstPassage_FirstPassage
import Theorems.Thm_WhittFLT_FirstPassage_firstPassage_continuous
import Theorems.Thm_WhittFLT_FirstPassage_firstPassage_mem

open WhittFLT.FirstPassage WhittFLT.Composition
open Set Filter Topology

lemma fp72_le {y : ℝ → ℝ} {t s : ℝ} (hs : 0 ≤ s) (h : t < y s) : firstPassage y t ≤ s :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨hs, h⟩

lemma fp72_nonempty {y : ℝ → ℝ} (hy : ¬ BddAbove (y '' Ici 0)) (t : ℝ) :
    {s | 0 ≤ s ∧ t < y s}.Nonempty := by
  by_contra h
  apply hy
  refine ⟨t, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  by_contra h'
  exact h ⟨s, hs, lt_of_not_ge h'⟩

lemma fp72_ge {y : ℝ → ℝ} (hy : ¬ BddAbove (y '' Ici 0)) {t c : ℝ}
    (h : ∀ s, 0 ≤ s → t < y s → c ≤ s) : c ≤ firstPassage y t :=
  le_csInf (fp72_nonempty hy t) (fun s hs => h s hs.1 hs.2)

lemma fp72_approx {y : ℝ → ℝ} (hy : ¬ BddAbove (y '' Ici 0)) (t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s, 0 ≤ s ∧ t < y s ∧ s < firstPassage y t + δ := by
  obtain ⟨s, ⟨hs0, hs1⟩, hs2⟩ :=
    exists_lt_of_csInf_lt (fp72_nonempty hy t) (lt_add_of_pos_right (firstPassage y t) hδ)
  exact ⟨s, hs0, hs1, hs2⟩

lemma fp72_U (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ)
    (hxs : ∀ n, InE (xs n)) (hx : InE x) (hmono : StrictMonoOn x (Ici 0))
    (hconv : J1Tendsto (Ici 0) xs x) :
    UTendsto (Ici 0) (fun n => firstPassage (xs n)) (firstPassage x) := by
  obtain ⟨hgc, hg0⟩ := firstPassage_continuous x hx hmono
  have hgm : MonotoneOn (firstPassage x) (Ici 0) := (firstPassage_mem x hx).2.1
  set g := firstPassage x with hg
  intro a b hab
  set T : ℝ := max b 0 with hT
  have hT0 : 0 ≤ T := le_max_right _ _
  have hcount := hmono.monotoneOn.countable_not_continuousWithinAt
  set c : ℝ := max (g (T + 1)) 0 + 1 with hc
  obtain ⟨B, hBc, hB1, hB2⟩ :=
    (hcount.dense_compl ℝ).exists_between (show c < c + 1 by linarith)
  have hc1 : g (T + 1) + 1 ≤ c := by
    have := le_max_left (g (T + 1)) 0; linarith
  have hc0 : 1 ≤ c := by
    have := le_max_right (g (T + 1)) 0; linarith
  have hBpos : 0 < B := by linarith
  have hBcont : ContinuousWithinAt x (Ici 0) B := by
    by_contra hh; exact hBc ⟨le_of_lt hBpos, hh⟩
  have hJ := hconv.2.2 0 B hBpos.le (Icc_subset_Ici_self)
    (Or.inr (Or.inl isLeast_Ici)) (Or.inl hBcont)
  have hUC := isCompact_Icc.uniformContinuousOn_of_continuous
    (hgc.mono (Icc_subset_Ici_self : Icc 0 (T + 1) ⊆ Ici 0))
  rw [Metric.uniformContinuousOn_iff] at hUC
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  obtain ⟨δ, hδpos, hδe⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ e := by
    rcases eq_or_ne e ⊤ with rfl | hne
    · exact ⟨1, one_pos, le_top⟩
    · refine ⟨e.toReal, ENNReal.toReal_pos he.ne' hne, ?_⟩
      rw [ENNReal.ofReal_toReal hne]
  obtain ⟨η, hηpos, hη⟩ := hUC (δ / 2) (by linarith)
  set ε : ℝ := min (min (η / 2) (δ / 2)) (1 / 2) with hε
  have hεη : ε < η := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith)
  have hεδ : ε ≤ δ / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hε2 : ε ≤ 1 / 2 := min_le_right _ _
  have hεpos : 0 < ε := lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
  filter_upwards [(tendsto_order.1 hJ).2 _ (ENNReal.ofReal_pos.2 hεpos)] with n hn
  unfold j1Dist at hn
  obtain ⟨l, hn⟩ := iInf_lt_iff.1 hn
  obtain ⟨hl, hn⟩ := iInf_lt_iff.1 hn
  rw [max_lt_iff] at hn
  obtain ⟨hn1, hn2⟩ := hn
  have hl1 : ∀ s ∈ Icc 0 B, |l s - s| < ε := by
    intro s hs
    have : edist (l s) (id s) < ENNReal.ofReal ε :=
      lt_of_le_of_lt (le_iSup₂ (f := fun t (_ : t ∈ Icc 0 B) => edist (l t) (id t)) s hs) hn1
    rw [edist_lt_ofReal, Real.dist_eq] at this
    exact this
  have hl2 : ∀ s ∈ Icc 0 B, |xs n s - x (l s)| < ε := by
    intro s hs
    have : edist (xs n s) ((x ∘ l) s) < ENNReal.ofReal ε :=
      lt_of_le_of_lt
        (le_iSup₂ (f := fun t (_ : t ∈ Icc 0 B) => edist (xs n t) ((x ∘ l) t)) s hs) hn2
    rw [edist_lt_ofReal, Real.dist_eq] at this
    exact this
  have hlmaps : ∀ s ∈ Icc 0 B, l s ∈ Icc 0 B := by
    intro s hs; rw [← hl.2.2]; exact ⟨s, hs, rfl⟩
  have hgT : ∀ u, 0 ≤ u → u ≤ T + 1 → g u ≤ g (T + 1) := by
    intro u hu1 hu2
    exact hgm hu1 (show (0:ℝ) ≤ T + 1 by linarith) hu2
  refine le_trans ?_ hδe
  unfold supDist
  refine iSup₂_le fun t ht => ?_
  have ht0 : 0 ≤ t := hab ht
  have htT : t ≤ T := le_trans ht.2 (le_max_left _ _)
  -- upper bound
  have hup : firstPassage (xs n) t ≤ g (t + ε) + ε := by
    apply le_of_forall_pos_lt_add
    intro δ' hδ'
    set δ'' := min δ' (1 / 2) with hδ''
    have hδ''pos : 0 < δ'' := lt_min hδ' (by norm_num)
    have hδ''le : δ'' ≤ δ' := min_le_left _ _
    have hδ''2 : δ'' ≤ 1 / 2 := min_le_right _ _
    obtain ⟨s, hs0, hs1, hs2⟩ := fp72_approx hx.2.1 (t + ε) hδ''pos
    have hgtε : g (t + ε) ≤ g (T + 1) := hgT _ (by linarith) (by linarith)
    have hsB : s ∈ Icc 0 B := ⟨hs0, by linarith⟩
    rw [← hl.2.2] at hsB
    obtain ⟨s', hs', hls'⟩ := hsB
    have h1 := hl1 s' hs'
    have h2 := hl2 s' hs'
    rw [hls'] at h1 h2
    have hlt : t < xs n s' := by
      have := (abs_lt.1 h2).1; linarith
    have hfp := fp72_le hs'.1 hlt
    have := (abs_lt.1 h1).1
    linarith
  -- lower bound
  have hlow : g (max (t - ε) 0) - ε ≤ firstPassage (xs n) t := by
    apply fp72_ge (hxs n).2.1
    intro s hs0 hs1
    have hm0 : 0 ≤ max (t - ε) 0 := le_max_right _ _
    have hmT : max (t - ε) 0 ≤ T + 1 := max_le (by linarith) (by linarith)
    have hgm' := hgT _ hm0 hmT
    by_cases hsB : s ≤ B
    · have hs : s ∈ Icc 0 B := ⟨hs0, hsB⟩
      have h1 := hl1 s hs
      have h2 := hl2 s hs
      have hls := hlmaps s hs
      have hlt := (abs_lt.1 h1).2
      rcases le_or_gt 0 (t - ε) with hte | hte
      · rw [max_eq_left hte]
        have : t - ε < x (l s) := by
          have := (abs_lt.1 h2).2; linarith
        have := fp72_le hls.1 this
        linarith
      · rw [max_eq_right hte.le, hg0]
        linarith
    · rw [not_le] at hsB
      linarith
  have hd1 : g (t + ε) - g t < δ / 2 := by
    have := hη (t + ε) ⟨by linarith, by linarith⟩ t ⟨ht0, by linarith⟩
      (by rw [Real.dist_eq]; rw [show t + ε - t = ε by ring, abs_of_pos hεpos]; linarith)
    rw [Real.dist_eq] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  have hd2 : g t - g (max (t - ε) 0) < δ / 2 := by
    have hm0 : 0 ≤ max (t - ε) 0 := le_max_right _ _
    have hmt : max (t - ε) 0 ≤ t := max_le (by linarith) ht0
    have hmt2 : t - ε ≤ max (t - ε) 0 := le_max_left _ _
    have := hη t ⟨ht0, by linarith⟩ (max (t - ε) 0) ⟨hm0, by linarith⟩
      (by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith)
    rw [Real.dist_eq] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  rw [edist_dist, Real.dist_eq]
  apply ENNReal.ofReal_le_ofReal
  rw [abs_le]
  constructor <;> linarith

theorem solution (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ)
    (hxs : ∀ n, InE (xs n)) (hx : InE x) (hmono : StrictMonoOn x (Ici 0))
    (hconv : WhittFLT.Composition.J1Tendsto (Ici 0) xs x) :
    WhittFLT.Composition.J1Tendsto (Ici 0) (fun n => firstPassage (xs n)) (firstPassage x) := by
  have h := fp72_U xs x hxs hx hmono hconv
  refine ⟨fun n => (firstPassage_mem (xs n) (hxs n)).1.1, (firstPassage_mem x hx).1.1,
    fun a b _ hab _ _ => ?_⟩
  have hid : IsTimeChange a b id :=
    ⟨strictMono_id.strictMonoOn _, continuousOn_id, image_id _⟩
  have h0 : supDist a b (id : ℝ → ℝ) id = 0 := by
    simp [supDist]
  have hle : ∀ n, j1Dist a b (firstPassage (xs n)) (firstPassage x) ≤
      supDist a b (firstPassage (xs n)) (firstPassage x) := by
    intro n
    refine (iInf₂_le (id : ℝ → ℝ) hid).trans ?_
    rw [h0]
    simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h a b hab)
    (fun n => zero_le) hle
