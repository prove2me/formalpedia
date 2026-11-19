-- Prove2me | solution 1 for Plasticity.Ell1.exists_closed_code_set
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-11-18T20:10:12.960022+00:00
-- url     : https://prove2.me/submissions/c4ebb931-c384-486f-a4be-34a301c8d43f

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Logic.Encodable.Basic

namespace Sol_Plasticity_Ell1_exists_closed_code_set
open PiNat Filter Topology

section
variable {Y : Type*} [MetricSpace Y] (C : Set (ℕ → ℕ)) (φ : (ℕ → ℕ) → Y)

noncomputable def D (b : ℕ → ℕ) (k : ℕ) : ENNReal :=
  Metric.ediam (φ '' (C ∩ cylinder b k))

noncomputable def T (b : ℕ → ℕ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else (min 1 (2 * D C φ b k)).toReal

theorem T_nonneg (b k) : 0 ≤ T C φ b k := by
  unfold T; split_ifs <;> simp

theorem T_le_one (b k) : T C φ b k ≤ 1 := by
  unfold T; split_ifs
  · exact le_rfl
  · have : min 1 (2 * D C φ b k) ≤ 1 := min_le_left _ _
    simpa using ENNReal.toReal_mono (by simp) this

theorem cyl_congr {b b' : ℕ → ℕ} {k : ℕ} (h : ∀ i < k, b i = b' i) :
    cylinder b k = cylinder b' k := by
  ext c
  simp only [mem_cylinder_iff]
  exact ⟨fun hc i hi => (hc i hi).trans (h i hi), fun hc i hi => (hc i hi).trans (h i hi).symm⟩

theorem T_congr {b b' : ℕ → ℕ} {k : ℕ} (h : ∀ i < k, b i = b' i) :
    T C φ b k = T C φ b' k := by
  unfold T D; rw [cyl_congr h]

theorem T_succ_le (b k) : T C φ b (k+1) ≤ T C φ b k := by
  by_cases hk : k = 0
  · subst hk; simpa [T] using T_le_one C φ b 1
  · simp only [T, if_neg hk, if_neg (Nat.succ_ne_zero k)]
    have hd : D C φ b (k+1) ≤ D C φ b k :=
      Metric.ediam_mono (Set.image_mono (Set.inter_subset_inter_right _ (cylinder_anti b (Nat.le_succ k))))
    have : min 1 (2 * D C φ b (k+1)) ≤ min 1 (2 * D C φ b k) := min_le_min le_rfl (by gcongr)
    exact ENNReal.toReal_mono (by simp) this

theorem T_dist {b b' : ℕ → ℕ} {k : ℕ} (hb : b ∈ C) (hb' : b' ∈ C) (hc : b' ∈ cylinder b k)
    (hT : T C φ b k < 1) : dist (φ b) (φ b') ≤ T C φ b k / 2 := by
  have hk : k ≠ 0 := by rintro rfl; simp [T] at hT
  simp only [T, if_neg hk] at hT ⊢
  have hm : min 1 (2 * D C φ b k) < 1 := by
    by_contra h
    have : min 1 (2 * D C φ b k) = 1 := le_antisymm (min_le_left _ _) (not_lt.1 h)
    rw [this] at hT; simp at hT
  have h2 : 2 * D C φ b k < 1 := by
    rcases min_lt_iff.1 hm with h | h
    · exact absurd h (lt_irrefl _)
    · exact h
  rw [min_eq_right h2.le] at hT ⊢
  have hDt : D C φ b k ≠ ⊤ := by
    intro h; rw [h] at h2; simp at h2
  have hed : edist (φ b) (φ b') ≤ D C φ b k :=
    Metric.edist_le_ediam_of_mem (Set.mem_image_of_mem φ ⟨hb, by simp [mem_cylinder_iff]⟩)
      (Set.mem_image_of_mem φ ⟨hb', hc⟩)
  have : dist (φ b) (φ b') ≤ (D C φ b k).toReal := by
    rw [dist_edist]; exact ENNReal.toReal_mono hDt hed
  rw [ENNReal.toReal_mul]
  simp only [ENNReal.toReal_ofNat]
  linarith

theorem exists_cyl {b : ℕ → ℕ} {u : Set (ℕ → ℕ)} (hu : IsOpen u) (hb : b ∈ u) :
    ∃ k, cylinder b k ⊆ u := by
  obtain ⟨v, ⟨x, n, rfl⟩, hbv, hvu⟩ :=
    (isTopologicalBasis_cylinders (fun _ : ℕ => ℕ)).exists_subset_of_mem_open hb hu
  refine ⟨n, fun c hc => hvu ?_⟩
  rw [mem_cylinder_iff] at hbv hc ⊢
  exact fun i hi => (hc i hi).trans (hbv i hi)

theorem T_tendsto (hφ : ContinuousOn φ C) {b : ℕ → ℕ} (hb : b ∈ C) :
    Tendsto (T C φ b) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h1 : (fun c => φ c) ⁻¹' Metric.ball (φ b) (ε/8) ∈ 𝓝[C] b :=
    (hφ b hb).tendsto (Metric.ball_mem_nhds _ (by positivity))
  obtain ⟨u, hu, hbu, hsub⟩ := mem_nhdsWithin.1 h1
  obtain ⟨k, hk⟩ := exists_cyl hu hbu
  refine ⟨k + 1, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hball : ∀ c ∈ C ∩ cylinder b n, dist (φ c) (φ b) < ε / 8 := fun c hc =>
    hsub ⟨hk (cylinder_anti b (by omega : k ≤ n) hc.2), hc.1⟩
  have hD : D C φ b n ≤ ENNReal.ofReal (ε / 4) := by
    unfold D
    apply Metric.ediam_le
    rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have := hball c hc; have := hball c' hc'
    rw [dist_comm (φ c') ] at *
    linarith [dist_triangle (φ c) (φ b) (φ c')]
  have h2 : min 1 (2 * D C φ b n) ≤ ENNReal.ofReal (ε / 2) := by
    refine (min_le_right _ _).trans ?_
    calc 2 * D C φ b n ≤ 2 * ENNReal.ofReal (ε / 4) := by gcongr
      _ = ENNReal.ofReal (ε / 2) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
  have h3 : T C φ b n ≤ ε / 2 := by
    simp only [T, if_neg hn0]
    exact (ENNReal.toReal_mono (by simp) h2).trans (by rw [ENNReal.toReal_ofReal (by positivity)])
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (T_nonneg C φ b n)]
  linarith

theorem T_antitone (b) : Antitone (T C φ b) := antitone_nat_of_succ_le (T_succ_le C φ b)

/-! Codes -/
def pre (b : ℕ → ℕ) (k : ℕ) : List ℕ := List.ofFn (fun i : Fin k => b i)

theorem pre_length (b k) : (pre b k).length = k := List.length_ofFn

theorem pre_ne_nil (b k) : pre b (k + 1) ≠ [] := by
  intro h; have := congrArg List.length h; simp [pre_length] at this

theorem pre_eq_iff {b b' : ℕ → ℕ} {k : ℕ} : pre b k = pre b' k ↔ ∀ i < k, b i = b' i := by
  simp only [pre, List.ofFn_inj, funext_iff, Fin.forall_iff]

noncomputable def wt (b : ℕ → ℕ) (j : ℕ) : ℝ := T C φ b j - T C φ b (j + 1)

theorem wt_nonneg (b j) : 0 ≤ wt C φ b j := sub_nonneg.2 (T_succ_le C φ b j)

theorem wt_congr {b b' : ℕ → ℕ} {j : ℕ} (h : ∀ i < j + 1, b i = b' i) : wt C φ b j = wt C φ b' j := by
  unfold wt
  rw [T_congr C φ h, T_congr C φ (fun i hi => h i (by omega))]

noncomputable def coord (b : ℕ → ℕ) (m : ℕ) : ℝ :=
  match Encodable.decode₂ (List ℕ) m with
  | none => 0
  | some l => if l ≠ [] ∧ pre b l.length = l then wt C φ b (l.length - 1) else 0

def kap (b : ℕ → ℕ) (j : ℕ) : ℕ := Encodable.encode (pre b (j + 1))

theorem kap_inj (b) : Function.Injective (kap b) := by
  intro j j' h
  have := Encodable.encode_injective h
  have := congrArg List.length this
  simp [pre] at this; exact this

theorem coord_kap (b j) : coord C φ b (kap b j) = wt C φ b j := by
  simp [coord, kap, Encodable.decode₂_encode, pre_length, pre_ne_nil]

theorem coord_nonneg (b m) : 0 ≤ coord C φ b m := by
  unfold coord; split <;> [exact le_rfl; (split_ifs <;> [exact wt_nonneg _ _ _ _; exact le_rfl])]

theorem coord_off (b m) (h : m ∉ Set.range (kap b)) : coord C φ b m = 0 := by
  unfold coord
  split
  · rfl
  · rename_i l hl
    split_ifs with hc
    · exfalso; apply h
      refine ⟨l.length - 1, ?_⟩
      have hm : Encodable.encode l = m := Encodable.decode₂_eq_some.1 hl
      have hl1 : l.length - 1 + 1 = l.length := by
        have : l.length ≠ 0 := fun h0 => hc.1 (List.length_eq_zero_iff.1 h0)
        omega
      unfold kap; rw [hl1, hc.2, hm]
    · rfl

theorem coord_eventually {b b' : ℕ → ℕ} {n : ℕ} (m : ℕ)
    (h : ∀ i < n, b i = b' i) (hn : ∀ l : List ℕ, Encodable.decode₂ (List ℕ) m = some l → l.length ≤ n) :
    coord C φ b m = coord C φ b' m := by
  unfold coord
  split
  · rfl
  · rename_i l hl
    have hln := hn l hl
    have hh : ∀ i < l.length, b i = b' i := fun i hi => h i (lt_of_lt_of_le hi hln)
    have h1 : pre b l.length = l ↔ pre b' l.length = l := by rw [pre_eq_iff.2 hh]
    by_cases hl0 : l = []
    · simp [hl0]
    have hpos : l.length ≠ 0 := fun h0 => hl0 (List.length_eq_zero_iff.1 h0)
    have h2 : wt C φ b (l.length - 1) = wt C φ b' (l.length - 1) := by
      apply wt_congr
      intro i hi
      exact h i (by omega)
    simp only [h1, h2]

theorem sum_wt (b n) : ∑ j ∈ Finset.range n, wt C φ b j = T C φ b 0 - T C φ b n := by
  simpa [wt] using Finset.sum_range_sub' (fun j => T C φ b j) n

theorem T_zero (b) : T C φ b 0 = 1 := by simp [T]

theorem coord_summable (b) : Summable (coord C φ b) := by
  rw [← (kap_inj b).summable_iff (fun m hm => coord_off C φ b m hm)]
  refine summable_of_sum_range_le (c := 1) (fun j => ?_) (fun n => ?_)
  · simpa [Function.comp, coord_kap] using wt_nonneg C φ b j
  · have := sum_wt C φ b n
    have h0 := T_nonneg C φ b n
    simp only [Function.comp, coord_kap]
    rw [this, T_zero]; linarith

theorem coord_mem (b) : Memℓp (coord C φ b) 1 := by
  rw [memℓp_gen_iff (by simp)]
  simpa [abs_of_nonneg (coord_nonneg C φ b _)] using coord_summable C φ b

noncomputable def code (b : ℕ → ℕ) : lp (fun _ : ℕ => ℝ) 1 := ⟨coord C φ b, coord_mem C φ b⟩

theorem code_apply (b m) : code C φ b m = coord C φ b m := rfl

theorem hasSum_abs (f : lp (fun _ : ℕ => ℝ) 1) : HasSum (fun i => |f i|) ‖f‖ := by
  simpa using lp.hasSum_norm (p := 1) (by simp) f

theorem code_norm (hφ : ContinuousOn φ C) {b} (hb : b ∈ C) : ‖code C φ b‖ = 1 := by
  have h1 := hasSum_abs (code C φ b)
  simp only [code_apply, abs_of_nonneg (coord_nonneg C φ b _)] at h1
  rw [← (kap_inj b).hasSum_iff (fun m hm => coord_off C φ b m hm)] at h1
  have h2 : HasSum (fun j => wt C φ b j) 1 := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (wt_nonneg C φ b)]
    simp only [sum_wt, T_zero]
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub (T_tendsto C φ hφ hb)
  have h1' : HasSum (fun j => wt C φ b j) ‖code C φ b‖ := by
    simpa [Function.comp_def, coord_kap] using h1
  exact h1'.unique h2

theorem coord_enc_zero (b : ℕ → ℕ) (l : List ℕ) (hl : pre b l.length ≠ l) :
    coord C φ b (Encodable.encode l) = 0 := by
  simp [coord, Encodable.decode₂_encode, hl]

theorem sum_wt_shift (b k n) :
    ∑ j ∈ Finset.range n, wt C φ b (k + j) = T C φ b k - T C φ b (k + n) := by
  have h := Finset.sum_range_sub' (fun j => T C φ b (k + j)) n
  simp only [Nat.add_zero] at h
  exact h

theorem code_lower (hφ : ContinuousOn φ C) {b b' : ℕ → ℕ} (hb : b ∈ C) (hb' : b' ∈ C) {k : ℕ}
    (h : ∀ i < k, b i = b' i) (hne : b k ≠ b' k) :
    2 * T C φ b k ≤ ‖code C φ b - code C φ b'‖ := by
  have hdisj : ∀ b b' : ℕ → ℕ, (∀ i < k, b i = b' i) → b k ≠ b' k → ∀ n,
      Disjoint ((Finset.range n).image (fun j => kap b (k+j)))
        ((Finset.range n).image (fun j => kap b' (k+j))) := by
    intro b b' h hne n
    rw [Finset.disjoint_left]
    intro m hm hm'
    simp only [Finset.mem_image, Finset.mem_range] at hm hm'
    obtain ⟨j, hj, rfl⟩ := hm
    obtain ⟨j', hj', hjj⟩ := hm'
    have h1 := Encodable.encode_injective hjj
    have hl := congrArg List.length h1
    simp only [pre_length] at hl
    have : j' = j := by omega
    subst this
    exact hne ((pre_eq_iff.1 h1 k (by omega)).symm)
  have hfin : ∀ n, (T C φ b k - T C φ b (k+n)) + (T C φ b' k - T C φ b' (k+n)) ≤
      ‖code C φ b - code C φ b'‖ := by
    intro n
    have hs := hasSum_abs (code C φ b - code C φ b')
    have hle := sum_le_hasSum ((Finset.range n).image (fun j => kap b (k+j)) ∪
        (Finset.range n).image (fun j => kap b' (k+j))) (fun i _ => abs_nonneg _) hs
    rw [Finset.sum_union (hdisj b b' h hne n)] at hle
    have hinj : ∀ b'' : ℕ → ℕ, Set.InjOn (fun j => kap b'' (k+j)) (Finset.range n : Set ℕ) :=
      fun b'' x _ y _ hxy => by simpa using kap_inj b'' hxy
    rw [Finset.sum_image (hinj b), Finset.sum_image (hinj b')] at hle
    have e1 : ∀ j, |(code C φ b - code C φ b') (kap b (k+j))| = wt C φ b (k+j) := by
      intro j
      have : coord C φ b' (kap b (k+j)) = 0 := by
        apply coord_enc_zero
        simp only [pre_length]
        intro hh
        have := pre_eq_iff.1 hh k (by omega)
        exact hne this.symm
      simp [code_apply, this, coord_kap, abs_of_nonneg (wt_nonneg C φ b _)]
    have e2 : ∀ j, |(code C φ b - code C φ b') (kap b' (k+j))| = wt C φ b' (k+j) := by
      intro j
      have : coord C φ b (kap b' (k+j)) = 0 := by
        apply coord_enc_zero
        simp only [pre_length]
        intro hh
        have := pre_eq_iff.1 hh k (by omega)
        exact hne this
      simp [code_apply, this, coord_kap, abs_of_nonneg (wt_nonneg C φ b' _)]
    simp only [e1, e2, sum_wt_shift] at hle
    exact hle
  have hlim : Tendsto (fun n => (T C φ b k - T C φ b (k+n)) + (T C φ b' k - T C φ b' (k+n)))
      atTop (𝓝 ((T C φ b k - 0) + (T C φ b' k - 0))) := by
    have hk : Tendsto (fun n => k + n) atTop atTop := tendsto_atTop_mono (fun n => Nat.le_add_left n k) tendsto_id
    exact (tendsto_const_nhds.sub ((T_tendsto C φ hφ hb).comp hk)).add
      (tendsto_const_nhds.sub ((T_tendsto C φ hφ hb').comp hk))
  have := le_of_tendsto hlim (Eventually.of_forall hfin)
  rw [T_congr C φ (b' := b') h] at this ⊢
  linarith

theorem code_quarter (hφ : ContinuousOn φ C) {b b' : ℕ → ℕ} (hb : b ∈ C) (hb' : b' ∈ C)
    (h : ‖code C φ b - code C φ b'‖ < 2) :
    dist (φ b) (φ b') ≤ ‖code C φ b - code C φ b'‖ / 4 := by
  by_cases hbb : b = b'
  · subst hbb; simp
  have hk := mem_cylinder_firstDiff b b'
  have hne := apply_firstDiff_ne hbb
  have hagree : ∀ i < firstDiff b b', b i = b' i := mem_cylinder_iff.1 hk
  have hlow := code_lower C φ hφ hb hb' hagree hne
  have hT : T C φ b (firstDiff b b') < 1 := by linarith
  have hc : b' ∈ cylinder b (firstDiff b b') := by
    rw [mem_cylinder_iff]; exact fun i hi => (hagree i hi).symm
  have := T_dist C φ hb hb' hc hT
  linarith

theorem code_injOn (hφ : ContinuousOn φ C) (hinj : Set.InjOn φ C) : Set.InjOn (code C φ) C := by
  intro b hb b' hb' h
  by_contra hne
  have := code_quarter C φ hφ hb hb' (by rw [h]; simp)
  rw [h] at this
  simp at this
  exact hne (hinj hb hb' this)

theorem code_image_closed (hC : IsClosed C) (hφ : ContinuousOn φ C) (hinj : Set.InjOn φ C) :
    IsClosed (code C φ '' C) := by
  rw [← isSeqClosed_iff_isClosed]
  intro x x0 hxmem hx
  choose b hbC hbx using hxmem
  have hcauchy : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, ‖code C φ (b n) - code C φ (b m)‖ < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hx (ε / 2) (by positivity)
    refine ⟨N, fun n hn m hm => ?_⟩
    have h1 := hN n hn
    have h2 := hN m hm
    rw [← hbx n, ← hbx m, dist_eq_norm] at *
    calc ‖code C φ (b n) - code C φ (b m)‖
        = ‖(code C φ (b n) - x0) - (code C φ (b m) - x0)‖ := by congr 1; abel
      _ ≤ ‖code C φ (b n) - x0‖ + ‖code C φ (b m) - x0‖ := norm_sub_le _ _
      _ < ε := by linarith
  have P : ∀ k, ∃ c : ℕ → ℕ, ∀ᶠ n in atTop, ∀ i < k, b n i = c i := by
    intro k
    induction k with
    | zero => exact ⟨b 0, Eventually.of_forall fun n i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      obtain ⟨c, hc⟩ := ih
      obtain ⟨N, hN⟩ := eventually_atTop.1 hc
      have hTeq : ∀ n ≥ N, T C φ (b n) k = T C φ (b N) k := fun n hn =>
        T_congr C φ (fun i hi => (hN n hn i hi).trans (hN N le_rfl i hi).symm)
      rcases (T_nonneg C φ (b N) k).eq_or_lt with h0 | hpos
      · refine ⟨b N, eventually_atTop.2 ⟨N, fun n hn i hi => ?_⟩⟩
        have hd : dist (φ (b N)) (φ (b n)) ≤ T C φ (b N) k / 2 := by
          apply T_dist C φ (hbC N) (hbC n)
          · rw [mem_cylinder_iff]; exact fun i hi => (hN n hn i hi).trans (hN N le_rfl i hi).symm
          · rw [← h0]; norm_num
        rw [← h0] at hd
        have : b N = b n := hinj (hbC N) (hbC n) (dist_le_zero.1 (by simpa using hd))
        rw [this]
      · obtain ⟨N', hN'⟩ := hcauchy (2 * T C φ (b N) k) (by linarith)
        refine ⟨b (max N N'), eventually_atTop.2 ⟨max N N', fun n hn i hi => ?_⟩⟩
        have hnN : N ≤ n := le_trans (le_max_left _ _) hn
        have hMN : N ≤ max N N' := le_max_left _ _
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hik | hik
        · exact (hN n hnN i hik).trans (hN _ hMN i hik).symm
        · subst hik
          by_contra hne
          have hlow := code_lower C φ hφ (hbC n) (hbC (max N N'))
            (k := i) (fun j hj => (hN n hnN j hj).trans (hN _ hMN j hj).symm) hne
          have := hN' n (le_trans (le_max_right _ _) hn) (max N N') (le_max_right _ _)
          rw [hTeq n hnN] at hlow
          linarith
  choose c hc using P
  set bt : ℕ → ℕ := fun i => c (i + 1) i with hbt
  have hev : ∀ i, ∀ᶠ n in atTop, b n i = bt i := fun i => (hc (i + 1)).mono fun n hn => hn i (by omega)
  have hevk : ∀ k, ∀ᶠ n in atTop, ∀ i < k, b n i = bt i := by
    intro k
    have := (Finset.range k).eventually_all.2 (fun i _ => hev i)
    exact this.mono fun n hn i hi => hn i (Finset.mem_range.2 hi)
  have htend : Tendsto b atTop (𝓝 bt) := by
    rw [tendsto_pi_nhds]
    intro i
    exact tendsto_const_nhds.congr' ((hev i).mono fun n hn => hn.symm)
  have hbtC : bt ∈ C := hC.mem_of_tendsto htend (Eventually.of_forall hbC)
  refine ⟨bt, hbtC, ?_⟩
  apply lp.ext
  funext m
  have hcoord : ∀ᶠ n in atTop, x n m = code C φ bt m := by
    set n0 := (Encodable.decode₂ (List ℕ) m).elim 0 List.length
    refine (hevk n0).mono fun n hn => ?_
    rw [← hbx n, code_apply, code_apply]
    exact coord_eventually C φ m hn (fun l hl => by simp [n0, hl])
  have h1 : Tendsto (fun n => x n m) atTop (𝓝 (x0 m)) := by
    rw [Metric.tendsto_atTop] at hx ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hx ε hε
    refine ⟨N, fun n hn => ?_⟩
    have := hN n hn
    rw [dist_eq_norm] at this ⊢
    calc ‖x n m - x0 m‖ = ‖(x n - x0) m‖ := rfl
      _ ≤ ‖x n - x0‖ := lp.norm_apply_le_norm (by simp) _ _
      _ < ε := this
  have h2 : Tendsto (fun n => x n m) atTop (𝓝 (code C φ bt m)) :=
    tendsto_const_nhds.congr' (hcoord.mono fun n hn => hn.symm)
  exact tendsto_nhds_unique h2 h1

end
end Sol_Plasticity_Ell1_exists_closed_code_set

theorem solution {Y : Type*} [MetricSpace Y] (M : Set Y)
    (C : Set (ℕ → ℕ)) (hC : IsClosed C)
    (φ : (ℕ → ℕ) → Y) (hφ : ContinuousOn φ C) (hbij : Set.BijOn φ C M) :
    ∃ E : Set (lp (fun _ : ℕ => ℝ) 1), IsClosed E ∧ (∀ e ∈ E, ‖e‖ = 1 ∧ ∀ j, 0 ≤ e j) ∧
      ∃ lab : lp (fun _ : ℕ => ℝ) 1 → Y, Set.BijOn lab E M ∧
        ∀ e ∈ E, ∀ e' ∈ E, ‖e - e'‖ < 2 → dist (lab e) (lab e') ≤ ‖e - e'‖ / 4 := by
  open Sol_Plasticity_Ell1_exists_closed_code_set in
  classical
  have hinj := hbij.injOn
  have hci := code_injOn C φ hφ hinj
  let lab : lp (fun _ : ℕ => ℝ) 1 → Y := fun e =>
    if h : ∃ b ∈ C, code C φ b = e then φ h.choose else φ (fun _ => 0)
  have hlab : ∀ b ∈ C, lab (code C φ b) = φ b := by
    intro b hb
    have h : ∃ b' ∈ C, code C φ b' = code C φ b := ⟨b, hb, rfl⟩
    simp only [lab, dif_pos h]
    rw [hci h.choose_spec.1 hb h.choose_spec.2]
  refine ⟨code C φ '' C, code_image_closed C φ hC hφ hinj, ?_, lab, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact ⟨code_norm C φ hφ hb, fun j => by rw [code_apply]; exact coord_nonneg C φ b j⟩
  · refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩
      rw [hlab b hb]; exact hbij.mapsTo hb
    · rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩ h
      rw [hlab b hb, hlab b' hb'] at h
      rw [hinj hb hb' h]
    · intro y hy
      obtain ⟨b, hb, rfl⟩ := hbij.surjOn hy
      exact ⟨code C φ b, ⟨b, hb, rfl⟩, hlab b hb⟩
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩ h
    rw [hlab b hb, hlab b' hb']
    exact code_quarter C φ hφ hb hb' h
