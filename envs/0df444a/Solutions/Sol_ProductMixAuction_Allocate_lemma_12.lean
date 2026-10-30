-- Prove2me | solution 1 for ProductMixAuction.Allocate.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T16:26:54.976801+00:00
-- url     : https://prove2.me/submissions/eefdf760-9021-4925-9397-a1e2b9293d00

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Algorithm

open ProductMixAuction.Allocate

set_option linter.unusedSectionVars false

namespace PMAL12

variable {n : ℕ}

lemma ext_add_smul (q d : Fin n → ℝ) (s : ℝ) (m : Fin (n + 1)) :
    ext (q + s • d) m = ext q m + s * ext d m := by
  cases m using Fin.cases <;> simp [ext]

lemma surplusMax_eq_of (b : Bid n) (q : Fin n → ℝ) (g : Fin (n + 1))
    (h : ∀ m, b.v m - ext q m ≤ b.v g - ext q g) : surplusMax b q = b.v g - ext q g :=
  le_antisymm (Finset.sup'_le _ _ fun m _ => h m)
    (Finset.le_sup' (fun i => b.v i - ext q i) (Finset.mem_univ g))

lemma le_surplusMax (b : Bid n) (q : Fin n → ℝ) (m : Fin (n + 1)) :
    b.v m - ext q m ≤ surplusMax b q :=
  Finset.le_sup' (fun i => b.v i - ext q i) (Finset.mem_univ m)

lemma near0 (b : Bid n) (q d : Fin n → ℝ) (hb : (demGoods b q).card = 1) :
    ∀ᶠ s in nhds (0 : ℝ), surplusMax b (q + s • d) =
      surplusMax b q - s * ∑ i ∈ demGoods b q, ext d i := by
  obtain ⟨g, hg⟩ := Finset.card_eq_one.mp hb
  have hgm : g ∈ demGoods b q := by rw [hg]; exact Finset.mem_singleton_self g
  have hgv : b.v g - ext q g = surplusMax b q := by
    simpa [demGoods] using hgm
  have hall : ∀ᶠ s in nhds (0 : ℝ), ∀ m, b.v m - (ext q m + s * ext d m) ≤
      b.v g - (ext q g + s * ext d g) := by
    rw [Filter.eventually_all]
    intro m
    by_cases hm : m = g
    · subst hm; exact Filter.Eventually.of_forall fun _ => le_rfl
    · have hlt : b.v m - ext q m < b.v g - ext q g := by
        rcases (le_surplusMax b q m).lt_or_eq with h | h
        · rwa [hgv]
        · exfalso
          have : m ∈ demGoods b q := by simp [demGoods, h]
          rw [hg] at this; exact hm (Finset.mem_singleton.mp this)
      have hc : ContinuousAt (fun s : ℝ => b.v m - (ext q m + s * ext d m)) 0 := by fun_prop
      have hc' : ContinuousAt (fun s : ℝ => b.v g - (ext q g + s * ext d g)) 0 := by fun_prop
      exact (hc.eventually_lt hc' (by simpa using hlt)).mono fun _ h => h.le
  filter_upwards [hall] with s hs
  rw [surplusMax_eq_of b _ g (fun m => by simpa only [ext_add_smul] using hs m), hg,
    Finset.sum_singleton, ext_add_smul, ← hgv]
  ring

lemma lsum1 (B : List (Bid n)) (x y : Bid n → ℝ) (s : ℝ) :
    (B.map fun b => (b.w : ℝ) * (x b - s * y b)).sum =
      (B.map fun b => (b.w : ℝ) * x b).sum - s * (B.map fun b => (b.w : ℝ) * y b).sum := by
  induction B with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma lsum2 (B : List (Bid n)) (M : Bid n → ℝ) (c s : ℝ) :
    (B.map fun b => (b.w : ℝ) * (c * s + M b)).sum =
      c * s * (B.map fun b => (b.w : ℝ)).sum + (B.map fun b => (b.w : ℝ) * M b).sum := by
  induction B with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma dG_nonempty (b : Bid n) (q : Fin n → ℝ) : (demGoods b q).Nonempty := by
  obtain ⟨m, -, hm⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin (n + 1)))
    (fun i => b.v i - ext q i)
  exact ⟨m, by simp only [demGoods, Finset.mem_filter, Finset.mem_univ, true_and]; exact hm.symm⟩

lemma dG_other (b : Bid n) (q : Fin n → ℝ) (k : Fin (n + 1)) (h : demGoods b q ≠ {k}) :
    ∃ g ∈ demGoods b q, g ≠ k := by
  by_contra H
  push Not at H
  apply h
  obtain ⟨g, hg⟩ := dG_nonempty b q
  rw [Finset.eq_singleton_iff_unique_mem]
  exact ⟨H g hg ▸ hg, H⟩

lemma dG_val (b : Bid n) (q : Fin n → ℝ) (g : Fin (n + 1)) (hg : g ∈ demGoods b q) :
    b.v g - ext q g = surplusMax b q := by
  simpa [demGoods] using hg

lemma nearS_succ (b : Bid n) (q : Fin n → ℝ) (i : Fin n) :
    ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      surplusMax b (q + s • Pi.single i (1 : ℝ)) =
        surplusMax b q - s * (if demGoods b q = {i.succ} then 1 else 0) := by
  have hed : ∀ m, ext (Pi.single i (1 : ℝ)) m = if m = i.succ then 1 else 0 := by
    intro m; cases m using Fin.cases <;> simp [ext, Pi.single_apply, (Fin.succ_ne_zero _).symm]
  by_cases h : demGoods b q = {i.succ}
  · have hc : (demGoods b q).card = 1 := by rw [h]; rfl
    refine (Filter.Eventually.filter_mono nhdsWithin_le_nhds (near0 b q (Pi.single i (1 : ℝ)) hc)).mono fun s hs => ?_
    rw [hs, h, if_pos rfl, Finset.sum_singleton, hed, if_pos rfl]
  · rw [if_neg h]
    obtain ⟨g, hg, hgk⟩ := dG_other b q _ h
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs : (0 : ℝ) < s := hs
    have hgv := dG_val b q g hg
    rw [surplusMax_eq_of b _ g, ext_add_smul, hed, if_neg hgk]
    · rw [← hgv]; ring
    · intro m
      rw [ext_add_smul, ext_add_smul, hed, hed, if_neg hgk]
      have := le_surplusMax b q m
      split_ifs <;> nlinarith

lemma nearS_zero (b : Bid n) (q : Fin n → ℝ) :
    ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      surplusMax b (q + s • (fun _ => (-1 : ℝ))) =
        surplusMax b q - s * (if demGoods b q = {0} then 0 else -1) := by
  have hed : ∀ m : Fin (n + 1), ext (n := n) (fun _ => (-1 : ℝ)) m = if m = 0 then 0 else -1 := by
    intro m; cases m using Fin.cases <;> simp [ext, Fin.succ_ne_zero]
  by_cases h : demGoods b q = {0}
  · have hc : (demGoods b q).card = 1 := by rw [h]; rfl
    refine (Filter.Eventually.filter_mono nhdsWithin_le_nhds (near0 b q (fun _ => (-1 : ℝ)) hc)).mono fun s hs => ?_
    rw [hs, h, if_pos rfl, Finset.sum_singleton, hed, if_pos rfl]
  · rw [if_neg h]
    obtain ⟨g, hg, hgk⟩ := dG_other b q _ h
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs : (0 : ℝ) < s := hs
    have hgv := dG_val b q g hg
    rw [surplusMax_eq_of b _ g, ext_add_smul, hed, if_neg hgk]
    · rw [← hgv]; ring
    · intro m
      rw [ext_add_smul, ext_add_smul, hed, hed, if_neg hgk]
      have := le_surplusMax b q m
      split_ifs <;> nlinarith


lemma conv_line (f : (Fin n → ℝ) → ℝ) (p : Fin n → ℝ) (R : ℝ) (hconv : ConvexOn ℝ (Metric.ball p R) f)
    (x d : Fin n → ℝ) (S2 : ℝ) (hmem : ∀ s ∈ Set.Icc 0 S2, x + s • d ∈ Metric.ball p R) :
    ConvexOn ℝ (Set.Icc 0 S2) (fun s => f (x + s • d)) := by
  refine ⟨convex_Icc 0 S2, fun s hs t ht α β hα hβ hαβ => ?_⟩
  have h := hconv.2 (hmem s hs) (hmem t ht) hα hβ hαβ
  have e : α • (x + s • d) + β • (x + t • d) = x + (α • s + β • t) • d := by
    funext m; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (x m) * hαβ
  simp only [smul_eq_mul] at h ⊢
  rw [e] at h; simpa using h

lemma slope_local (L : List (Bid n)) (x d : Fin n → ℝ) (S1 S2 : ℝ) (h0 : 0 < S1) (h12 : S1 < S2)
    (hconv : ConvexOn ℝ (Set.Icc 0 S2) (fun s => fB L (x + s • d))) (τ : Bid n → ℝ)
    (hτ : ∀ b ∈ L, ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      surplusMax b (x + s • d) = surplusMax b x - s * τ b)
    (c : ℝ) (M : Bid n → ℝ)
    (hfar : ∀ b ∈ L, ∀ s ∈ Set.Icc S1 S2, surplusMax b (x + s • d) = c * s + M b) :
    -(L.map fun b => (b.w : ℝ) * τ b).sum ≤ c * (L.map fun b => (b.w : ℝ)).sum := by
  classical
  set a := (L.map fun b => (b.w : ℝ) * τ b).sum
  set W := (L.map fun b => (b.w : ℝ)).sum
  set φ : ℝ → ℝ := fun s => fB L (x + s • d)
  have hnear : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), φ s = fB L x - s * a := by
    have : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ b ∈ L.toFinset, surplusMax b (x + s • d) =
        surplusMax b x - s * τ b := by
      rw [Filter.eventually_all_finset]
      intro b hb
      exact hτ b (List.mem_toFinset.mp hb)
    filter_upwards [this] with s hs
    simp only [φ, fB]
    rw [List.map_congr_left (fun b hb => by rw [hs b (List.mem_toFinset.mpr hb)]), lsum1]
  have hlt : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), s < S1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds h0)
  obtain ⟨s0, ⟨hφ0, hs0S1⟩, hs0⟩ := ((hnear.and hlt).and self_mem_nhdsWithin).exists
  have hs0 : 0 < s0 := hs0
  have hφz : φ 0 = fB L x := by simp [φ]
  have hfarφ : ∀ s ∈ Set.Icc S1 S2, φ s = c * s * W + (L.map fun b => (b.w : ℝ) * M b).sum := by
    intro s hs
    simp only [φ, fB]
    rw [List.map_congr_left (fun b hb => by rw [hfar b hb s hs]), lsum2]
  have h1 := hfarφ S1 ⟨le_rfl, h12.le⟩
  have h2 := hfarφ S2 ⟨h12.le, le_rfl⟩
  have mem : ∀ s, 0 ≤ s → s ≤ S2 → s ∈ Set.Icc 0 S2 := fun s a b => ⟨a, b⟩
  have m1 := hconv.slope_mono_adjacent (mem 0 le_rfl (by linarith)) (mem S1 h0.le h12.le) hs0 hs0S1
  have m2 := hconv.slope_mono_adjacent (mem s0 hs0.le (by linarith)) (mem S2 (by linarith) le_rfl)
    hs0S1 h12
  change (φ s0 - φ 0) / (s0 - 0) ≤ (φ S1 - φ s0) / (S1 - s0) at m1
  change (φ S1 - φ s0) / (S1 - s0) ≤ (φ S2 - φ S1) / (S2 - S1) at m2
  rw [hφ0, hφz, h1] at m1
  rw [hφ0, h1, h2] at m2
  have e1 : (fB L x - s0 * a - fB L x) / (s0 - 0) = -a := by
    rw [sub_zero, div_eq_iff hs0.ne']; ring
  have e2 : (c * S2 * W + (L.map fun b => (b.w : ℝ) * M b).sum -
      (c * S1 * W + (L.map fun b => (b.w : ℝ) * M b).sum)) / (S2 - S1) = c * W := by
    rw [div_eq_iff (by linarith)]; ring
  rw [e1] at m1; rw [e2] at m2
  linarith


lemma ext_diff_le (x p : Fin n → ℝ) (m : Fin (n + 1)) : |ext x m - ext p m| ≤ dist x p := by
  cases m using Fin.cases with
  | zero => simp [ext]
  | succ i => simpa [ext, Real.dist_eq] using dist_le_pi_dist x p i

/-- Local slope lemma: for a locally convex list all of whose bids are marginal at `p`, the bids
uniquely demanding a good `k` at a price `x` close to `p` have non-negative total weight. -/
lemma LS (L : List (Bid n)) (p : Fin n → ℝ) (R : ℝ) (hR : 0 < R)
    (hconv : ConvexOn ℝ (Metric.ball p R) (fB L)) (hmarg : ∀ b ∈ L, IsMarginalBid b p)
    (hstab : ∀ b ∈ L, ∀ x' ∈ Metric.ball p R, demGoods b x' ⊆ demGoods b p)
    (x : Fin n → ℝ) (hx : dist x p < R / 2) (k : Fin (n + 1)) :
    0 ≤ (L.map fun b => (b.w : ℝ) * (if demGoods b x = {k} then 1 else 0)).sum := by
  set η := dist x p with hη
  have hη0 : 0 ≤ η := dist_nonneg
  cases k using Fin.cases with
  | succ i =>
    set d : Fin n → ℝ := Pi.single i (1 : ℝ)
    have hed : ∀ m, ext d m = if m = i.succ then 1 else 0 := by
      intro m; cases m using Fin.cases <;> simp [d, ext, Pi.single_apply, (Fin.succ_ne_zero _).symm]
    set a := x i - p i
    have ha : |a| ≤ η := by simpa [a, Real.dist_eq] using dist_le_pi_dist x p i
    have ha' := abs_le.mp ha
    set S1 := η + (R - η) / 3 - a
    set S2 := η + 2 * (R - η) / 3 - a
    have hS1 : 0 < S1 := by simp only [S1]; linarith
    have hS12 : S1 < S2 := by simp only [S1, S2]; linarith
    have hmem : ∀ s ∈ Set.Icc 0 S2, x + s • d ∈ Metric.ball p R := by
      intro s hs
      rw [Metric.mem_ball, dist_pi_lt_iff hR]
      intro m
      rw [Real.dist_eq]
      by_cases hm : m = i
      · subst hm
        simp only [Pi.add_apply, Pi.smul_apply, d, Pi.single_eq_same, smul_eq_mul, mul_one]
        rw [abs_lt]; constructor <;> [linarith [hs.1]; (simp only [S2] at hs; linarith [hs.2])]
      · simp only [Pi.add_apply, Pi.smul_apply, d, Pi.single_eq_of_ne hm, smul_eq_mul, mul_zero,
          add_zero]
        have := dist_le_pi_dist x p m
        rw [Real.dist_eq] at this
        linarith
    have h0mem : (0 : Fin (n + 1)) ∈ (Finset.univ : Finset (Fin (n + 1))).erase i.succ :=
      Finset.mem_erase.mpr ⟨(Fin.succ_ne_zero i).symm, Finset.mem_univ _⟩
    let M : Bid n → ℝ := fun b => ((Finset.univ : Finset (Fin (n + 1))).erase i.succ).sup' ⟨0, h0mem⟩
      (fun m => b.v m - ext x m)
    have hfar : ∀ b ∈ L, ∀ s ∈ Set.Icc S1 S2, surplusMax b (x + s • d) = 0 * s + M b := by
      intro b hb s hs
      have hsm := hmem s ⟨by linarith [hs.1], hs.2⟩
      have hk : i.succ ∉ demGoods b (x + s • d) := by
        by_cases hkp : i.succ ∈ demGoods b p
        · obtain ⟨g, hg, hgk⟩ := Finset.exists_mem_ne (hmarg b hb) i.succ
          intro hkx
          have e1 := dG_val b p _ hkp
          have e2 := dG_val b p g hg
          have e3 := dG_val b _ _ hkx
          have e4 := le_surplusMax b (x + s • d) g
          rw [ext_add_smul, hed, if_pos rfl] at e3
          rw [ext_add_smul, hed, if_neg hgk] at e4
          have e5 := abs_le.mp (ext_diff_le x p g)
          have e6 : ext x i.succ = ext p i.succ + a := by simp [ext, a]
          simp only [S1] at hs
          linarith [hs.1]
        · exact fun h => hkp (hstab b hb _ hsm h)
      obtain ⟨m, hm⟩ := dG_nonempty b (x + s • d)
      have hmk : m ≠ i.succ := fun h => hk (h ▸ hm)
      have hval := dG_val b _ m hm
      rw [ext_add_smul, hed, if_neg hmk, mul_zero, add_zero] at hval
      rw [zero_mul, zero_add]
      apply le_antisymm
      · rw [← hval]
        exact Finset.le_sup' (fun m => b.v m - ext x m) (Finset.mem_erase.mpr ⟨hmk, Finset.mem_univ _⟩)
      · apply Finset.sup'_le
        intro m' hm'
        have := le_surplusMax b (x + s • d) m'
        rw [ext_add_smul, hed, if_neg (Finset.mem_erase.mp hm').1, mul_zero, add_zero] at this
        exact this
    have := slope_local L x d S1 S2 hS1 hS12 (conv_line _ p R hconv x d S2 hmem) _
      (fun b _ => nearS_succ b x i) 0 M hfar
    simp only [zero_mul] at this
    linarith
  | zero =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have : L = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro b hb
        have h1 := hmarg b hb
        unfold IsMarginalBid at h1
        have h2 := Finset.card_le_univ (demGoods b p)
        simp at h2
        omega
      simp [this]
    set d : Fin n → ℝ := fun _ => -1
    have hed : ∀ m : Fin (n + 1), ext d m = if m = 0 then 0 else -1 := by
      intro m; cases m using Fin.cases <;> simp [d, ext, Fin.succ_ne_zero]
    set S1 := η + (R - 2 * η) / 3
    set S2 := η + 2 * (R - 2 * η) / 3
    have hS1 : 0 < S1 := by simp only [S1]; linarith
    have hS12 : S1 < S2 := by simp only [S1, S2]; linarith
    have hmem : ∀ s ∈ Set.Icc 0 S2, x + s • d ∈ Metric.ball p R := by
      intro s hs
      rw [Metric.mem_ball, dist_pi_lt_iff hR]
      intro m
      rw [Real.dist_eq]
      simp only [Pi.add_apply, Pi.smul_apply, d, smul_eq_mul]
      have := dist_le_pi_dist x p m
      rw [Real.dist_eq] at this
      have h1 := abs_le.mp this
      rw [abs_lt]; constructor
      · simp only [S2] at hs; nlinarith [hs.1, hs.2]
      · linarith [hs.1]
    set g1 : Fin (n + 1) := (⟨0, hn⟩ : Fin n).succ
    have h1mem : g1 ∈ (Finset.univ : Finset (Fin (n + 1))).erase 0 :=
      Finset.mem_erase.mpr ⟨Fin.succ_ne_zero _, Finset.mem_univ _⟩
    let M : Bid n → ℝ := fun b => ((Finset.univ : Finset (Fin (n + 1))).erase 0).sup' ⟨g1, h1mem⟩
      (fun m => b.v m - ext x m)
    have hfar : ∀ b ∈ L, ∀ s ∈ Set.Icc S1 S2, surplusMax b (x + s • d) = 1 * s + M b := by
      intro b hb s hs
      have hsm := hmem s ⟨by linarith [hs.1], hs.2⟩
      have hk : (0 : Fin (n + 1)) ∉ demGoods b (x + s • d) := by
        by_cases hkp : (0 : Fin (n + 1)) ∈ demGoods b p
        · obtain ⟨g, hg, hgk⟩ := Finset.exists_mem_ne (hmarg b hb) 0
          intro hkx
          have e1 := dG_val b p _ hkp
          have e2 := dG_val b p g hg
          have e3 := dG_val b _ _ hkx
          have e4 := le_surplusMax b (x + s • d) g
          rw [ext_add_smul, hed, if_pos rfl] at e3
          rw [ext_add_smul, hed, if_neg hgk] at e4
          have e5 := abs_le.mp (ext_diff_le x p g)
          have e6 : ext x 0 = 0 := by simp [ext]
          have e7 : ext p 0 = 0 := by simp [ext]
          simp only [S1] at hs
          linarith [hs.1]
        · exact fun h => hkp (hstab b hb _ hsm h)
      obtain ⟨m, hm⟩ := dG_nonempty b (x + s • d)
      have hmk : m ≠ 0 := fun h => hk (h ▸ hm)
      have hval := dG_val b _ m hm
      rw [ext_add_smul, hed, if_neg hmk] at hval
      apply le_antisymm
      · rw [← hval]
        have := Finset.le_sup' (fun m => b.v m - ext x m)
          (Finset.mem_erase.mpr ⟨hmk, Finset.mem_univ m⟩)
        simp only [M]
        linarith
      · have : M b ≤ surplusMax b (x + s • d) - s := by
          apply Finset.sup'_le
          intro m' hm'
          have := le_surplusMax b (x + s • d) m'
          rw [ext_add_smul, hed, if_neg (Finset.mem_erase.mp hm').1] at this
          linarith
        linarith
    have := slope_local L x d S1 S2 hS1 hS12 (conv_line _ p R hconv x d S2 hmem) _
      (fun b _ => nearS_zero b x) 1 M hfar
    have e : ∀ b ∈ L, (if demGoods b x = {0} then (0 : ℝ) else -1) =
        (if demGoods b x = {0} then 1 else 0) - 1 * 1 := by
      intro b _; split_ifs <;> ring
    rw [List.map_congr_left (fun b hb => by rw [e b hb]), lsum1] at this
    simp only [mul_one, one_mul] at this
    linarith


lemma mem_dG (b : Bid n) (q : Fin n → ℝ) (g : Fin (n + 1)) :
    g ∈ demGoods b q ↔ b.v g - ext q g = surplusMax b q := by
  simp [demGoods]

lemma eventually_sub (B : List (Bid n)) (p : Fin n → ℝ) :
    ∀ᶠ q in nhds p, ∀ b ∈ B, demGoods b q ⊆ demGoods b p := by
  classical
  have : ∀ᶠ q in nhds p, ∀ b ∈ B.toFinset, demGoods b q ⊆ demGoods b p := by
    rw [Filter.eventually_all_finset]
    intro b _
    obtain ⟨g, hg⟩ := dG_nonempty b p
    have hall : ∀ᶠ q in nhds p, ∀ m : Fin (n + 1), m ∉ demGoods b p →
        b.v m - ext q m < b.v g - ext q g := by
      rw [Filter.eventually_all]
      intro m
      by_cases hm : m ∈ demGoods b p
      · exact Filter.Eventually.of_forall fun _ h => absurd hm h
      · have hlt : b.v m - ext p m < b.v g - ext p g := by
          rw [dG_val b p g hg]
          rcases (le_surplusMax b p m).lt_or_eq with h | h
          · exact h
          · exact absurd ((mem_dG b p m).mpr h) hm
        have hc : Continuous (fun q : Fin n → ℝ => b.v m - ext q m) := by
          cases m using Fin.cases with
          | zero => simp only [ext, Fin.cons_zero]; fun_prop
          | succ i => simp only [ext, Fin.cons_succ]; fun_prop
        have hc' : Continuous (fun q : Fin n → ℝ => b.v g - ext q g) := by
          cases g using Fin.cases with
          | zero => simp only [ext, Fin.cons_zero]; fun_prop
          | succ i => simp only [ext, Fin.cons_succ]; fun_prop
        exact (hc.continuousAt.eventually_lt hc'.continuousAt hlt).mono fun q hq _ => hq
    filter_upwards [hall] with q hq
    intro m hm
    by_contra hmp
    have h1 := hq m hmp
    have h2 := le_surplusMax b q g
    have h3 := dG_val b q m hm
    linarith
  filter_upwards [this] with q hq b hb
  exact hq b (List.mem_toFinset.mpr hb)

open scoped Classical in
lemma sum_split {X : Type*} [AddCommMonoid X] (B : List (Bid n)) (Q : Bid n → Prop)
    (f : Bid n → X) :
    (B.map f).sum = ((B.filter fun b => Q b).map f).sum + ((B.filter fun b => ¬ Q b).map f).sum := by
  induction B with
  | nil => simp
  | cons b L ih =>
    by_cases hb : Q b <;> simp [List.filter_cons, hb, ih, add_assoc, add_left_comm]

open scoped Classical in
lemma fB_split (B : List (Bid n)) (Q : Bid n → Prop) (q : Fin n → ℝ) :
    fB B q = fB (B.filter fun b => Q b) q + fB (B.filter fun b => ¬ Q b) q :=
  sum_split B Q _

open scoped Classical in
lemma nm_split (B : List (Bid n)) (Q : Bid n → Prop) (q : Fin n → ℝ) :
    nmBundle B q = nmBundle (B.filter fun b => Q b) q + nmBundle (B.filter fun b => ¬ Q b) q :=
  sum_split B Q _

lemma list_apply_cast (B : List (Bid n)) (f : Bid n → Fin (n + 1) → ℤ) (k : Fin (n + 1)) :
    (((B.map f).sum k : ℤ) : ℝ) = (B.map fun b => ((f b k : ℤ) : ℝ)).sum := by
  induction B with
  | nil => simp
  | cons a L ih => simp [List.map_cons, List.sum_cons, ih]

lemma nm_cast_NM (L : List (Bid n)) (x : Fin n → ℝ) (hx : NonMarginalAt L x) (k : Fin (n + 1)) :
    ((nmBundle L x k : ℤ) : ℝ) =
      (L.map fun b => (b.w : ℝ) * (if demGoods b x = {k} then 1 else 0)).sum := by
  unfold nmBundle
  rw [list_apply_cast]
  congr 1
  apply List.map_congr_left
  intro b hb
  obtain ⟨g, hg⟩ := Finset.card_eq_one.mp (hx b hb)
  simp [hg, Pi.single_apply, eq_comm]

def castZ {m : ℕ} (y : Fin m → ℤ) : Fin m → ℝ := fun k => (y k : ℝ)

lemma demand_sub (B : List (Bid n)) (p : Fin n → ℝ) (S : Set (Fin (n + 1) → ℝ))
    (hS : Convex ℝ S) (h : ∀ y ∈ nearBundles B p, castZ y ∈ S) :
    ∀ x ∈ demand B p, castZ x ∈ S := by
  intro x hx
  unfold demand at hx
  refine convexHull_min ?_ hS hx
  rintro _ ⟨y, hy, rfl⟩
  exact h y hy


lemma lsum_aff (B : List (Bid n)) (X Y : Bid n → ℝ) (α β : ℝ) :
    (B.map fun b => (b.w : ℝ) * (α * X b + β * Y b)).sum =
      α * (B.map fun b => (b.w : ℝ) * X b).sum + β * (B.map fun b => (b.w : ℝ) * Y b).sum := by
  induction B with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma ext_comb (x y : Fin n → ℝ) (α β : ℝ) (hαβ : α + β = 1) (m : Fin (n + 1)) :
    ext (α • x + β • y) m = α * ext x m + β * ext y m := by
  cases m using Fin.cases <;> simp [ext]

end PMAL12

namespace PMAL12

variable {n : ℕ}

lemma list_sum_coord {α : Type*} (L : List α) (f : α → Fin (n + 1) → ℤ) :
    ∑ k, (L.map f).sum k = (L.map fun a => ∑ k, f a k).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

lemma nm_total (B : List (Bid n)) (q : Fin n → ℝ) (h : NonMarginalAt B q) :
    ∑ k, nmBundle B q k = (B.map Bid.w).sum := by
  unfold nmBundle
  rw [list_sum_coord]
  congr 1
  apply List.map_congr_left
  intro b hb
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, Finset.sum_apply]
  rw [Finset.sum_comm]
  simp [Pi.single_apply, h b hb]

lemma demand_total (B : List (Bid n)) (p : Fin n → ℝ) (x : Fin (n + 1) → ℤ)
    (hx : x ∈ demand B p) : ∑ k, x k = (B.map Bid.w).sum := by
  have hS : Convex ℝ {z : Fin (n + 1) → ℝ | ∑ k, z k = (((B.map Bid.w).sum : ℤ) : ℝ)} := by
    apply convex_hyperplane
    exact ⟨fun a b => by simp [Finset.sum_add_distrib],
      fun c a => by simp [Finset.mul_sum]⟩
  have := demand_sub B p _ hS (by
    intro y hy
    obtain ⟨q, -, hq, rfl⟩ := hy 1 one_pos
    simp only [Set.mem_ofPred_eq, castZ]
    exact_mod_cast nm_total B q hq) x hx
  simp only [Set.mem_ofPred_eq, castZ] at this
  exact_mod_cast this


/-- all-marginal locally valid lists demand only non-negative bundles -/
lemma AM_nonneg (L : List (Bid n)) (p : Fin n → ℝ) (R ρ : ℝ) (hR : 0 < R) (hRρ : R ≤ ρ)
    (hV : EpsValid L p R) (hmarg : ∀ b ∈ L, IsMarginalBid b p)
    (hstab : ∀ b ∈ L, ∀ x ∈ Metric.ball p ρ, demGoods b x ⊆ demGoods b p) :
    ∀ x ∈ demand L p, ∀ k, 0 ≤ x k := by
  intro x hx k
  have hS : Convex ℝ {z : Fin (n + 1) → ℝ | (0 : ℝ) ≤ z k} := by
    apply convex_halfSpace_ge
    exact ⟨fun a b => by simp, fun c a => by simp⟩
  have := demand_sub L p _ hS (by
    intro y hy
    obtain ⟨q, hq, hnm, rfl⟩ := hy (R / 2) (by positivity)
    simp only [Set.mem_ofPred_eq, castZ]
    rw [nm_cast_NM _ q hnm k]
    refine LS _ p R hR hV hmarg ?_ q hq k
    intro b hb x' hx'
    exact hstab b hb x' (Metric.ball_subset_ball hRρ hx')) x hx
  simp only [Set.mem_ofPred_eq, castZ] at this
  exact_mod_cast this

end PMAL12

namespace PMAL12

variable {n : ℕ}

lemma dG_eq_on (b : Bid n) (p : Fin n → ℝ) (ρ : ℝ) (S : Finset (Fin (n + 1)))
    (hS : demGoods b p ⊆ S) (hstab : ∀ x ∈ Metric.ball p ρ, demGoods b x ⊆ demGoods b p)
    (x y : Fin n → ℝ) (hx : x ∈ Metric.ball p ρ) (hy : y ∈ Metric.ball p ρ)
    (hxy : ∀ m ∈ S, ext x m = ext y m) :
    surplusMax b x = surplusMax b y ∧ demGoods b x = demGoods b y := by
  have hsm : surplusMax b x = surplusMax b y := by
    obtain ⟨g, hg⟩ := dG_nonempty b x
    obtain ⟨g', hg'⟩ := dG_nonempty b y
    have hgS := hS (hstab x hx hg)
    have hgS' := hS (hstab y hy hg')
    apply le_antisymm
    · rw [← dG_val b x g hg, hxy g hgS]; exact le_surplusMax b y g
    · rw [← dG_val b y g' hg', ← hxy g' hgS']; exact le_surplusMax b x g'
  refine ⟨hsm, ?_⟩
  ext m
  constructor
  · intro hm
    have hmS := hS (hstab x hx hm)
    rw [mem_dG, ← hsm, ← hxy m hmS]; exact (mem_dG b x m).mp hm
  · intro hm
    have hmS := hS (hstab y hy hm)
    rw [mem_dG, hsm, hxy m hmS]; exact (mem_dG b y m).mp hm

open scoped Classical in
/-- keep the prices of the goods in `I`, take those of `p` elsewhere -/
noncomputable def keep (I : Finset (Fin (n + 1))) (p x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if i.succ ∈ I then x i else p i

lemma ext_keep_in (I : Finset (Fin (n + 1))) (p x : Fin n → ℝ) (m : Fin (n + 1)) (hm : m ∈ I) :
    ext (keep I p x) m = ext x m := by
  classical
  cases m using Fin.cases with
  | zero => simp [ext]
  | succ i => simp [ext, keep, hm]

lemma ext_keep_out (I : Finset (Fin (n + 1))) (p x : Fin n → ℝ) (m : Fin (n + 1)) (hm : m ∉ I) :
    ext (keep I p x) m = ext p m := by
  classical
  cases m using Fin.cases with
  | zero => simp [ext]
  | succ i => simp [ext, keep, hm]

lemma dist_keep (I : Finset (Fin (n + 1))) (p x : Fin n → ℝ) : dist (keep I p x) p ≤ dist x p := by
  classical
  rw [dist_pi_le_iff dist_nonneg]
  intro i
  unfold keep
  split_ifs
  · exact dist_le_pi_dist x p i
  · simp

lemma keep_comb (I : Finset (Fin (n + 1))) (p x y : Fin n → ℝ) (α β : ℝ) (hαβ : α + β = 1) :
    keep I p (α • x + β • y) = α • keep I p x + β • keep I p y := by
  classical
  funext i
  simp only [keep, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs
  · rfl
  · linear_combination (p i) * hαβ.symm

open scoped Classical in
noncomputable def mix (I : Finset (Fin (n + 1))) (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if i.succ ∈ I then x i else y i

lemma ext_mix_in (I : Finset (Fin (n + 1))) (x y : Fin n → ℝ) (m : Fin (n + 1)) (hm : m ∈ I) :
    ext (mix I x y) m = ext x m := by
  classical
  cases m using Fin.cases with
  | zero => simp [ext]
  | succ i => simp [ext, mix, hm]

lemma ext_mix_out (I : Finset (Fin (n + 1))) (x y : Fin n → ℝ) (m : Fin (n + 1)) (hm : m ∉ I) :
    ext (mix I x y) m = ext y m := by
  classical
  cases m using Fin.cases with
  | zero => simp [ext]
  | succ i => simp [ext, mix, hm]

lemma dist_mix (I : Finset (Fin (n + 1))) (p x y : Fin n → ℝ) (r : ℝ)
    (hx : dist x p < r) (hy : dist y p < r) : dist (mix I x y) p < r := by
  classical
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg hx
  rw [dist_pi_lt_iff hr]
  intro i
  unfold mix
  split_ifs
  · exact lt_of_le_of_lt (dist_le_pi_dist x p i) hx
  · exact lt_of_le_of_lt (dist_le_pi_dist y p i) hy

open scoped Classical in
noncomputable def resI (I : Finset (Fin (n + 1))) (x : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ :=
  fun k => if k ∈ I then x k else 0

open scoped Classical in
noncomputable def resO (I : Finset (Fin (n + 1))) (x : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ :=
  fun k => if k ∈ I then 0 else x k

lemma res_add (I : Finset (Fin (n + 1))) (x : Fin (n + 1) → ℤ) : resI I x + resO I x = x := by
  classical
  funext k; simp only [resI, resO, Pi.add_apply]; split_ifs <;> simp

end PMAL12

namespace PMAL12

variable {n : ℕ}

open scoped Classical in
noncomputable def LI (L : List (Bid n)) (p : Fin n → ℝ) (I : Finset (Fin (n + 1))) : List (Bid n) :=
  L.filter fun b => ∃ i ∈ I, i ∈ demGoods b p

open scoped Classical in
noncomputable def LR (L : List (Bid n)) (p : Fin n → ℝ) (I : Finset (Fin (n + 1))) : List (Bid n) :=
  L.filter fun b => ¬ ∃ i ∈ I, i ∈ demGoods b p

lemma sum_split_LI {X : Type*} [AddCommMonoid X] (L : List (Bid n)) (p : Fin n → ℝ)
    (I : Finset (Fin (n + 1))) (f : Bid n → X) :
    (L.map f).sum = ((LI L p I).map f).sum + ((LR L p I).map f).sum := by
  classical
  induction L with
  | nil => simp [LI, LR]
  | cons b L ih =>
    unfold LI LR at ih ⊢
    by_cases hb : ∃ i ∈ I, i ∈ demGoods b p
    · rw [List.filter_cons, List.filter_cons, if_pos (by simpa using hb),
        if_neg (by simpa using hb)]
      simp only [List.map_cons, List.sum_cons, ih, add_assoc]
    · rw [List.filter_cons, List.filter_cons, if_neg (by simpa using hb),
        if_pos (by simpa using hb)]
      simp only [List.map_cons, List.sum_cons, ih]
      exact add_left_comm _ _ _

lemma list_apply (B : List (Bid n)) (f : Bid n → Fin (n + 1) → ℤ) (k : Fin (n + 1)) :
    (B.map f).sum k = (B.map fun b => f b k).sum := by
  induction B with
  | nil => simp
  | cons a L ih => simp [List.map_cons, List.sum_cons, ih]

section split

open scoped Classical Pointwise

variable (L : List (Bid n)) (p : Fin n → ℝ) (ρ : ℝ) (I : Finset (Fin (n + 1)))
  (hstab : ∀ b ∈ L, ∀ x ∈ Metric.ball p ρ, demGoods b x ⊆ demGoods b p)
  (hsplit : ∀ b ∈ L, (∃ i ∈ I, i ∈ demGoods b p) → demGoods b p ⊆ I)
include hstab hsplit

lemma mem_LI {b : Bid n} (hb : b ∈ LI L p I) : b ∈ L ∧ demGoods b p ⊆ I := by
  have := List.mem_filter.mp hb
  exact ⟨this.1, hsplit b this.1 (by simpa using this.2)⟩

lemma mem_LR {b : Bid n} (hb : b ∈ LR L p I) : b ∈ L ∧ demGoods b p ⊆ Finset.univ \ I := by
  have := List.mem_filter.mp hb
  refine ⟨this.1, fun m hm => ?_⟩
  have h2 : ¬ ∃ i ∈ I, i ∈ demGoods b p := by simpa using this.2
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact fun hmI => h2 ⟨m, hmI, hm⟩

lemma fB_LI_const (x : Fin n → ℝ) (hx : x ∈ Metric.ball p ρ) (hρ : 0 < ρ) :
    fB (LI L p I) (keep (Finset.univ \ I) p x) = fB (LI L p I) p := by
  have hk : keep (Finset.univ \ I) p x ∈ Metric.ball p ρ :=
    Metric.mem_ball.mpr (lt_of_le_of_lt (dist_keep _ p x) hx)
  unfold fB
  congr 1
  apply List.map_congr_left
  intro b hb
  obtain ⟨hbL, hbI⟩ := mem_LI L p ρ I hstab hsplit hb
  rw [(dG_eq_on b p ρ I hbI (hstab b hbL) _ p hk (Metric.mem_ball_self hρ)
    (fun m hm => ext_keep_out _ p x m (by simp [hm]))).1]

lemma fB_LR_eq (x : Fin n → ℝ) (hx : x ∈ Metric.ball p ρ) :
    fB (LR L p I) (keep (Finset.univ \ I) p x) = fB (LR L p I) x := by
  have hk : keep (Finset.univ \ I) p x ∈ Metric.ball p ρ :=
    Metric.mem_ball.mpr (lt_of_le_of_lt (dist_keep _ p x) hx)
  unfold fB
  congr 1
  apply List.map_congr_left
  intro b hb
  obtain ⟨hbL, hbI⟩ := mem_LR L p ρ I hstab hsplit hb
  rw [(dG_eq_on b p ρ _ hbI (hstab b hbL) _ x hk hx (fun m hm => ext_keep_in _ p x m hm)).1]

lemma fB_LI_eq (x : Fin n → ℝ) (hx : x ∈ Metric.ball p ρ) :
    fB (LI L p I) (keep I p x) = fB (LI L p I) x := by
  have hk : keep I p x ∈ Metric.ball p ρ :=
    Metric.mem_ball.mpr (lt_of_le_of_lt (dist_keep _ p x) hx)
  unfold fB
  congr 1
  apply List.map_congr_left
  intro b hb
  obtain ⟨hbL, hbI⟩ := mem_LI L p ρ I hstab hsplit hb
  rw [(dG_eq_on b p ρ _ hbI (hstab b hbL) _ x hk hx (fun m hm => ext_keep_in _ p x m hm)).1]

lemma fB_LR_const (x : Fin n → ℝ) (hx : x ∈ Metric.ball p ρ) (hρ : 0 < ρ) :
    fB (LR L p I) (keep I p x) = fB (LR L p I) p := by
  have hk : keep I p x ∈ Metric.ball p ρ :=
    Metric.mem_ball.mpr (lt_of_le_of_lt (dist_keep _ p x) hx)
  unfold fB
  congr 1
  apply List.map_congr_left
  intro b hb
  obtain ⟨hbL, hbI⟩ := mem_LR L p ρ I hstab hsplit hb
  rw [(dG_eq_on b p ρ _ hbI (hstab b hbL) _ p hk (Metric.mem_ball_self hρ)
    (fun m hm => ext_keep_out _ p x m (by simpa using hm))).1]

lemma conv_keep (S : Finset (Fin (n + 1))) (δ : ℝ) (hL : EpsValid L p δ) :
    ConvexOn ℝ (Metric.ball p (min δ ρ)) (fun x => fB L (keep S p x)) := by
  refine ⟨convex_ball _ _, fun x hx y hy α β hα hβ hαβ => ?_⟩
  have hsub : ∀ z ∈ Metric.ball p (min δ ρ), keep S p z ∈ Metric.ball p δ := fun z hz =>
    Metric.mem_ball.mpr (lt_of_le_of_lt (dist_keep _ p z)
      (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_left _ _)))
  have h := hL.2 (hsub x hx) (hsub y hy) hα hβ hαβ
  simp only [smul_eq_mul] at h ⊢
  rw [keep_comb S p x y α β hαβ]
  exact h

lemma LV_LR (hρ : 0 < ρ) (δ : ℝ) (hL : EpsValid L p δ) : EpsValid (LR L p I) p (min δ ρ) := by
  have h := (conv_keep L p ρ I hstab hsplit (Finset.univ \ I) δ hL).sub
    (concaveOn_const (fB (LI L p I) p) (convex_ball p (min δ ρ)))
  refine h.congr ?_
  intro x hx
  have hxρ : x ∈ Metric.ball p ρ := Metric.ball_subset_ball (min_le_right _ _) hx
  have : fB L (keep (Finset.univ \ I) p x) = fB (LI L p I) (keep (Finset.univ \ I) p x) + fB (LR L p I) (keep (Finset.univ \ I) p x) :=
    sum_split_LI L p I _
  simp only [Pi.sub_apply]
  change fB L (keep (Finset.univ \ I) p x) - fB (LI L p I) p = fB (LR L p I) x
  rw [this]
  rw [fB_LI_const L p ρ I hstab hsplit x hxρ hρ, fB_LR_eq L p ρ I hstab hsplit x hxρ]
  ring

lemma LV_LI (hρ : 0 < ρ) (δ : ℝ) (hL : EpsValid L p δ) : EpsValid (LI L p I) p (min δ ρ) := by
  have h := (conv_keep L p ρ I hstab hsplit I δ hL).sub
    (concaveOn_const (fB (LR L p I) p) (convex_ball p (min δ ρ)))
  refine h.congr ?_
  intro x hx
  have hxρ : x ∈ Metric.ball p ρ := Metric.ball_subset_ball (min_le_right _ _) hx
  have : fB L (keep I p x) = fB (LI L p I) (keep I p x) + fB (LR L p I) (keep I p x) :=
    sum_split_LI L p I _
  simp only [Pi.sub_apply]
  change fB L (keep I p x) - fB (LR L p I) p = fB (LI L p I) x
  rw [this]
  rw [fB_LR_const L p ρ I hstab hsplit x hxρ hρ, fB_LI_eq L p ρ I hstab hsplit x hxρ]
  ring

omit hsplit in
lemma nm_zero_of (L' : List (Bid n)) (S : Finset (Fin (n + 1))) (hL' : ∀ b ∈ L', b ∈ L)
    (hS : ∀ b ∈ L', demGoods b p ⊆ S) (q : Fin n → ℝ) (hq : q ∈ Metric.ball p ρ)
    (k : Fin (n + 1)) (hk : k ∉ S) : nmBundle L' q k = 0 := by
  unfold nmBundle
  rw [list_apply]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  have : k ∉ demGoods b q := fun h => hk (hS b hb (hstab b (hL' b hb) q hq h))
  simp [Finset.sum_apply, Pi.single_apply, this]

lemma nm_LI_out (q : Fin n → ℝ) (hq : q ∈ Metric.ball p ρ) (k : Fin (n + 1)) (hk : k ∉ I) :
    nmBundle (LI L p I) q k = 0 :=
  nm_zero_of L p ρ hstab _ I (fun b hb => (mem_LI L p ρ I hstab hsplit hb).1)
    (fun b hb => (mem_LI L p ρ I hstab hsplit hb).2) q hq k hk

lemma nm_LR_in (q : Fin n → ℝ) (hq : q ∈ Metric.ball p ρ) (k : Fin (n + 1)) (hk : k ∈ I) :
    nmBundle (LR L p I) q k = 0 :=
  nm_zero_of L p ρ hstab _ (Finset.univ \ I) (fun b hb => (mem_LR L p ρ I hstab hsplit hb).1)
    (fun b hb => (mem_LR L p ρ I hstab hsplit hb).2) q hq k (by simp [hk])

lemma resI_nm (q : Fin n → ℝ) (hq : q ∈ Metric.ball p ρ) :
    resI I (nmBundle L q) = nmBundle (LI L p I) q ∧ resO I (nmBundle L q) = nmBundle (LR L p I) q := by
  have hs : nmBundle L q = nmBundle (LI L p I) q + nmBundle (LR L p I) q := sum_split_LI L p I _
  constructor
  · funext k; simp only [resI, hs, Pi.add_apply]
    split_ifs with hk
    · rw [nm_LR_in L p ρ I hstab hsplit q hq k hk, add_zero]
    · rw [nm_LI_out L p ρ I hstab hsplit q hq k hk]
  · funext k; simp only [resO, hs, Pi.add_apply]
    split_ifs with hk
    · rw [nm_LR_in L p ρ I hstab hsplit q hq k hk]
    · rw [nm_LI_out L p ρ I hstab hsplit q hq k hk, zero_add]

lemma NM_dec (q : Fin n → ℝ) :
    NonMarginalAt L q ↔ NonMarginalAt (LI L p I) q ∧ NonMarginalAt (LR L p I) q := by
  constructor
  · intro h
    exact ⟨fun b hb => h b (List.mem_filter.mp hb).1, fun b hb => h b (List.mem_filter.mp hb).1⟩
  · rintro ⟨h1, h2⟩ b hb
    by_cases hbi : ∃ i ∈ I, i ∈ demGoods b p
    · exact h1 b (List.mem_filter.mpr ⟨hb, by simpa using hbi⟩)
    · exact h2 b (List.mem_filter.mpr ⟨hb, by simpa using hbi⟩)

lemma nb_dec (hρ : 0 < ρ) (y : Fin (n + 1) → ℤ) :
    y ∈ nearBundles L p ↔ resI I y ∈ nearBundles (LI L p I) p ∧
      resO I y ∈ nearBundles (LR L p I) p := by
  constructor
  · intro h
    constructor
    · intro δ hδ
      obtain ⟨q, hq, hnm, rfl⟩ := h (min δ ρ) (lt_min hδ hρ)
      have hqb : q ∈ Metric.ball p ρ := lt_of_lt_of_le hq (min_le_right _ _)
      exact ⟨q, lt_of_lt_of_le hq (min_le_left _ _), ((NM_dec L p ρ I hstab hsplit q).mp hnm).1,
        (resI_nm L p ρ I hstab hsplit q hqb).1.symm⟩
    · intro δ hδ
      obtain ⟨q, hq, hnm, rfl⟩ := h (min δ ρ) (lt_min hδ hρ)
      have hqb : q ∈ Metric.ball p ρ := lt_of_lt_of_le hq (min_le_right _ _)
      exact ⟨q, lt_of_lt_of_le hq (min_le_left _ _), ((NM_dec L p ρ I hstab hsplit q).mp hnm).2,
        (resI_nm L p ρ I hstab hsplit q hqb).2.symm⟩
  · rintro ⟨h1, h2⟩ δ hδ
    obtain ⟨q1, hq1, hnm1, he1⟩ := h1 (min δ ρ) (lt_min hδ hρ)
    obtain ⟨q2, hq2, hnm2, he2⟩ := h2 (min δ ρ) (lt_min hδ hρ)
    set q := mix I q1 q2
    have hq : dist q p < min δ ρ := dist_mix I p q1 q2 _ hq1 hq2
    have hqb : q ∈ Metric.ball p ρ := lt_of_lt_of_le hq (min_le_right _ _)
    have hq1b : q1 ∈ Metric.ball p ρ := lt_of_lt_of_le hq1 (min_le_right _ _)
    have hq2b : q2 ∈ Metric.ball p ρ := lt_of_lt_of_le hq2 (min_le_right _ _)
    have dI : ∀ b ∈ LI L p I, demGoods b q = demGoods b q1 := by
      intro b hb
      obtain ⟨hbL, hbI⟩ := mem_LI L p ρ I hstab hsplit hb
      exact (dG_eq_on b p ρ I hbI (hstab b hbL) q q1 hqb hq1b (fun m hm => ext_mix_in I q1 q2 m hm)).2
    have dR : ∀ b ∈ LR L p I, demGoods b q = demGoods b q2 := by
      intro b hb
      obtain ⟨hbL, hbI⟩ := mem_LR L p ρ I hstab hsplit hb
      exact (dG_eq_on b p ρ _ hbI (hstab b hbL) q q2 hqb hq2b
        (fun m hm => ext_mix_out I q1 q2 m (by simpa using hm))).2
    have nI : nmBundle (LI L p I) q = nmBundle (LI L p I) q1 := by
      unfold nmBundle; congr 1; apply List.map_congr_left; intro b hb; rw [dI b hb]
    have nR : nmBundle (LR L p I) q = nmBundle (LR L p I) q2 := by
      unfold nmBundle; congr 1; apply List.map_congr_left; intro b hb; rw [dR b hb]
    refine ⟨q, lt_of_lt_of_le hq (min_le_left _ _), ?_, ?_⟩
    · rw [NM_dec L p ρ I hstab hsplit q]
      exact ⟨fun b hb => by rw [dI b hb]; exact hnm1 b hb, fun b hb => by rw [dR b hb]; exact hnm2 b hb⟩
    · rw [show nmBundle L q = nmBundle (LI L p I) q + nmBundle (LR L p I) q from sum_split_LI L p I _,
        nI, nR, he1, he2, res_add]

lemma supp_LI (hρ : 0 < ρ) (y : Fin (n + 1) → ℤ) (hy : y ∈ nearBundles (LI L p I) p) :
    ∀ k ∉ I, y k = 0 := by
  obtain ⟨q, hq, -, rfl⟩ := hy ρ hρ
  exact fun k hk => nm_LI_out L p ρ I hstab hsplit q hq k hk

lemma supp_LR (hρ : 0 < ρ) (y : Fin (n + 1) → ℤ) (hy : y ∈ nearBundles (LR L p I) p) :
    ∀ k ∈ I, y k = 0 := by
  obtain ⟨q, hq, -, rfl⟩ := hy ρ hρ
  exact fun k hk => nm_LR_in L p ρ I hstab hsplit q hq k hk

lemma demand_dec (hρ : 0 < ρ) (x : Fin (n + 1) → ℤ) :
    x ∈ demand L p ↔ resI I x ∈ demand (LI L p I) p ∧ resO I x ∈ demand (LR L p I) p := by
  have hS : castZ '' nearBundles L p =
      castZ '' nearBundles (LI L p I) p + castZ '' nearBundles (LR L p I) p := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h := (nb_dec L p ρ I hstab hsplit hρ y).mp hy
      refine Set.mem_add.mpr ⟨castZ (resI I y), ⟨_, h.1, rfl⟩, castZ (resO I y), ⟨_, h.2, rfl⟩, ?_⟩
      funext k; simp only [castZ, Pi.add_apply]; rw [← Int.cast_add, ← Pi.add_apply, res_add]
    · intro hz
      obtain ⟨_, ⟨y1, hy1, rfl⟩, _, ⟨y2, hy2, rfl⟩, rfl⟩ := Set.mem_add.mp hz
      have s1 := supp_LI L p ρ I hstab hsplit hρ y1 hy1
      have s2 := supp_LR L p ρ I hstab hsplit hρ y2 hy2
      have r1 : resI I (y1 + y2) = y1 := by
        funext k; simp only [resI, Pi.add_apply]; split_ifs with hk
        · rw [s2 k hk, add_zero]
        · rw [s1 k hk]
      have r2 : resO I (y1 + y2) = y2 := by
        funext k; simp only [resO, Pi.add_apply]; split_ifs with hk
        · rw [s2 k hk]
        · rw [s1 k hk, zero_add]
      refine ⟨y1 + y2, (nb_dec L p ρ I hstab hsplit hρ _).mpr ⟨by rw [r1]; exact hy1,
        by rw [r2]; exact hy2⟩, ?_⟩
      funext k; simp [castZ]
  have hc1 : convexHull ℝ (castZ '' nearBundles (LI L p I) p) ⊆ {z | ∀ k ∉ I, z k = 0} := by
    apply convexHull_min
    · rintro _ ⟨y, hy, rfl⟩ k hk; simp [castZ, supp_LI L p ρ I hstab hsplit hρ y hy k hk]
    · intro a ha b hb α β _ _ _ k hk
      simp [ha k hk, hb k hk]
  have hc2 : convexHull ℝ (castZ '' nearBundles (LR L p I) p) ⊆ {z | ∀ k ∈ I, z k = 0} := by
    apply convexHull_min
    · rintro _ ⟨y, hy, rfl⟩ k hk; simp [castZ, supp_LR L p ρ I hstab hsplit hρ y hy k hk]
    · intro a ha b hb α β _ _ _ k hk
      simp [ha k hk, hb k hk]
  change castZ x ∈ convexHull ℝ (castZ '' nearBundles L p) ↔
    castZ (resI I x) ∈ convexHull ℝ (castZ '' nearBundles (LI L p I) p) ∧
    castZ (resO I x) ∈ convexHull ℝ (castZ '' nearBundles (LR L p I) p)
  rw [hS, convexHull_add]
  constructor
  · intro hx
    obtain ⟨u, hu, w, hw, huw⟩ := Set.mem_add.mp hx
    have hu0 := hc1 hu
    have hw0 := hc2 hw
    have e1 : castZ (resI I x) = u := by
      funext k
      have := congrFun huw k
      simp only [castZ, resI, Pi.add_apply] at this ⊢
      split_ifs with hk
      · rw [← this, hw0 k hk, add_zero]
      · rw [hu0 k hk]; simp
    have e2 : castZ (resO I x) = w := by
      funext k
      have := congrFun huw k
      simp only [castZ, resO, Pi.add_apply] at this ⊢
      split_ifs with hk
      · rw [hw0 k hk]; simp
      · rw [← this, hu0 k hk, zero_add]
    exact ⟨e1 ▸ hu, e2 ▸ hw⟩
  · rintro ⟨h1, h2⟩
    refine Set.mem_add.mpr ⟨_, h1, _, h2, ?_⟩
    funext k; simp only [castZ, Pi.add_apply]; rw [← Int.cast_add, ← Pi.add_apply, res_add]

end split

end PMAL12

namespace PMAL12

lemma sum_update {J : Type*} [Fintype J] [DecidableEq J] {X : Type*} [AddCommGroup X]
    (f : J → X) (j : J) (v : X) : ∑ x, Function.update f j v x = ∑ x, f x - f j + v := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ j), ← Finset.add_sum_erase _ f (Finset.mem_univ j),
    Finset.sdiff_singleton_eq_erase]
  abel

/-- coordinates no bid demands vanish on the whole demand set -/
lemma demand_coord_zero {n : ℕ} (L : List (Bid n)) (p : Fin n → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hstab : ∀ b ∈ L, ∀ x ∈ Metric.ball p ρ, demGoods b x ⊆ demGoods b p)
    (i : Fin (n + 1)) (hi : ∀ b ∈ L, i ∉ demGoods b p) : ∀ x ∈ demand L p, x i = 0 := by
  intro x hx
  have hS : Convex ℝ {z : Fin (n + 1) → ℝ | z i = 0} := by
    intro a ha b hb α β _ _ _; simp only [Set.mem_ofPred_eq] at ha hb ⊢; simp [ha, hb]
  have := demand_sub L p _ hS (by
    intro y hy
    obtain ⟨q, hq, -, rfl⟩ := hy ρ hρ
    simp only [Set.mem_ofPred_eq, castZ]
    have : nmBundle L q i = 0 := by
      unfold nmBundle
      rw [list_apply]
      apply List.sum_eq_zero
      intro z hz
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
      have : i ∉ demGoods b q := fun h => hi b hb (hstab b hb q hq h)
      simp [Finset.sum_apply, Pi.single_apply, this]
    simp [this]) x hx
  simp only [Set.mem_ofPred_eq, castZ] at this
  exact_mod_cast this

end PMAL12

open PMAL12 in
theorem solution {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J] (A : AllocProblem n J)
    (hA : IsAllocProblem A) (hmarg : ∀ j, ∀ b ∈ A.B j, IsMarginalBid b A.p)
    (I : Finset (Fin (n + 1))) (j : J) (hI : IsCluster A I j)
    (hlink : {i | i ∈ I ∧ IsLink A i}.Subsingleton) :
    IsReduction (unambiguousMarginals A I j) A ∧
      (edges (unambiguousMarginals A I j)).card < (edges A).card := by
  classical
  set p := A.p with hp
  -- stability radius
  have hev : ∀ᶠ q in nhds p, ∀ j, ∀ b ∈ A.B j, demGoods b q ⊆ demGoods b p :=
    Filter.eventually_all.2 (fun j => eventually_sub (A.B j) p)
  obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff.mp hev
  have hstab : ∀ j, ∀ b ∈ A.B j, ∀ x ∈ Metric.ball p ρ, demGoods b x ⊆ demGoods b p :=
    fun j b hb x hx => hρs (Metric.mem_ball.mp hx) j b hb
  -- cluster facts
  obtain ⟨i0, ⟨i', hadj⟩, hmemI⟩ := hI
  have hi0 : i0 ∈ I := (hmemI i0).mpr Relation.ReflTransGen.refl
  have hedgeJ : ∀ g g' : Fin (n + 1), g ≠ g' → ∀ b ∈ A.B j, g ∈ demGoods b p → g' ∈ demGoods b p →
      adj A j g g' := by
    intro g g' hne b hb hg hg'
    simp only [adj, edges, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨by simpa using hne, b, hb, fun x hx => ?_⟩
    rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption
  have hclosed : ∀ g ∈ I, ∀ g', adj A j g g' → g' ∈ I := fun g hg g' ha =>
    (hmemI g').mpr (((hmemI g).mp hg).tail ha)
  have hsplitj : ∀ b ∈ A.B j, (∃ i ∈ I, i ∈ demGoods b p) → demGoods b p ⊆ I := by
    rintro b hb ⟨i, hiI, hib⟩ g hg
    by_cases hgi : g = i
    · exact hgi ▸ hiI
    · exact hclosed i hiI g (hedgeJ i g (Ne.symm hgi) b hb hib hg)
  have hjedge : ∀ i ∈ I, ∃ x, (s(i, x), j) ∈ edges A := by
    intro i hi
    rcases Relation.ReflTransGen.cases_tail ((hmemI i).mp hi) with h | ⟨x, -, hx⟩
    · exact ⟨i', h ▸ hadj⟩
    · exact ⟨x, by have : (s(x, i), j) ∈ edges A := hx; rwa [Sym2.eq_swap] at this⟩
  have hother : ∀ j', j' ≠ j → ∀ b ∈ A.B j', ∀ i ∈ I, i ∈ demGoods b p → IsLink A i := by
    intro j' hj' b hb i hiI hib
    obtain ⟨g, hg, hgi⟩ := Finset.exists_mem_ne (hmarg j' b hb) i
    obtain ⟨x, hx⟩ := hjedge i hiI
    refine ⟨_, hx, (s(i, g), j'), ?_, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _, Ne.symm hj'⟩
    simp only [edges, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨by simpa using (Ne.symm hgi), b, hb, fun y hy => ?_⟩
    rcases Sym2.mem_iff.mp hy with rfl | rfl <;> assumption
  -- the lists
  set LIj := LI (A.B j) p I
  set LRj := LR (A.B j) p I
  have hXB : (unambiguousMarginals A I j).B j = LRj := by
    simp only [unambiguousMarginals, Function.update_self, LRj, LR]
    apply List.filter_congr
    intro b hb
    have hm : IsMarginalBid b A.p := hmarg j b hb
    simp [hm, hp]
  have hXB' : ∀ j', j' ≠ j → (unambiguousMarginals A I j).B j' = A.B j' := fun j' h => by
    simp only [unambiguousMarginals, Function.update_of_ne h]
  have hMO : marginalOn A I j = LIj := by
    simp only [marginalOn, LIj, LI]
    apply List.filter_congr
    intro b hb
    have hm : IsMarginalBid b A.p := hmarg j b hb
    simp [hm, hp]
  -- validity and non-negativity
  obtain ⟨δ, hδ, hval⟩ := hA.2.1 j
  have hVR : EpsValid LRj p (min δ ρ) := LV_LR (A.B j) p ρ I (hstab j) hsplitj hρ δ hval
  have hVI : EpsValid LIj p (min δ ρ) := LV_LI (A.B j) p ρ I (hstab j) hsplitj hρ δ hval
  have nnI : ∀ x ∈ demand LIj p, ∀ k, 0 ≤ x k :=
    AM_nonneg LIj p (min δ ρ) ρ (lt_min hδ hρ) (min_le_right _ _) hVI
      (fun b hb => hmarg j b (List.mem_filter.mp hb).1)
      (fun b hb => hstab j b (List.mem_filter.mp hb).1)
  have nnR : ∀ x ∈ demand LRj p, ∀ k, 0 ≤ x k :=
    AM_nonneg LRj p (min δ ρ) ρ (lt_min hδ hρ) (min_le_right _ _) hVR
      (fun b hb => hmarg j b (List.mem_filter.mp hb).1)
      (fun b hb => hstab j b (List.mem_filter.mp hb).1)
  have nnAll : ∀ j', ∀ x ∈ demand (A.B j') p, ∀ k, 0 ≤ x k := by
    intro j'
    obtain ⟨δ', hδ', hval'⟩ := hA.2.1 j'
    exact AM_nonneg (A.B j') p (min δ' ρ) ρ (lt_min hδ' hρ) (min_le_right _ _)
      (hval'.subset (Metric.ball_subset_ball (min_le_left _ _)) (convex_ball _ _))
      (hmarg j') (hstab j')
  -- a solution of A
  obtain ⟨t0, rr, hrr, hsum, -⟩ := hA.2.2.2.2
  have hdec := (demand_dec (A.B j) p ρ I (hstab j) hsplitj hρ (rr j)).mp (hrr j)
  have hnonlink : ∀ i ∈ I, ¬ IsLink A i → A.r i = resI I (rr j) i := by
    intro i hiI hnl
    have h1 : A.r i = ∑ j', rr j' i := by rw [← hsum, Finset.sum_apply]
    rw [h1, Finset.sum_eq_single j]
    · simp [resI, hiI]
    · intro j' _ hj'
      refine demand_coord_zero (A.B j') p ρ hρ (hstab j') i ?_ (rr j') (hrr j')
      intro b hb hib
      exact hnl (hother j' hj' b hb i hiI hib)
    · intro h; exact absurd (Finset.mem_univ j) h
  have hresIsum : ∑ k, resI I (rr j) k = ∑ k ∈ I, resI I (rr j) k := by
    rw [← Finset.sum_subset (Finset.subset_univ I)]
    intro k _ hk; simp [resI, hk]
  have htotal : ∑ k, resI I (rr j) k = (LIj.map Bid.w).sum := demand_total LIj p _ hdec.1
  have hT : unambiguousTransfer A I j = resI I (rr j) := by
    funext i
    unfold unambiguousTransfer
    by_cases h : ∃ i ∈ I, IsLink A i
    · rw [dif_pos h]
      have hs := h.choose_spec
      by_cases hi : i = h.choose
      · rw [if_pos hi]
        have herase : ∑ i' ∈ I.erase h.choose, A.r i' =
            ∑ i' ∈ I.erase h.choose, resI I (rr j) i' := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkI := Finset.mem_of_mem_erase hk
          refine hnonlink k hkI (fun hkl => (Finset.ne_of_mem_erase hk) ?_)
          exact hlink ⟨hkI, hkl⟩ ⟨hs.1, hs.2⟩
        rw [hMO, ← htotal, herase, hresIsum, ← Finset.add_sum_erase _ _ hs.1, hi]
        ring
      · rw [if_neg hi]
        by_cases hi2 : i ∈ I
        · rw [if_pos hi2]
          exact hnonlink i hi2 (fun hl => hi (hlink ⟨hi2, hl⟩ hs))
        · rw [if_neg hi2]; simp [resI, hi2]
    · rw [dif_neg h]
      by_cases hi3 : i ∈ I
      · rw [if_pos hi3]; exact hnonlink i hi3 (fun hl => h ⟨i, hi3, hl⟩)
      · rw [if_neg hi3]; simp [resI, hi3]
  -- the new problem
  set X := unambiguousMarginals A I j with hXdef
  have hXp : X.p = p := rfl
  have hXm : X.m = Function.update A.m j (A.m j + resI I (rr j)) := by
    simp only [X, unambiguousMarginals, hT]
  have hXr : X.r = A.r - resI I (rr j) := by
    simp only [X, unambiguousMarginals, hT]
  have hLRmem : ∀ b ∈ LRj, b ∈ A.B j := fun b hb => (List.mem_filter.mp hb).1
  have hXmem : ∀ j', ∀ b ∈ X.B j', b ∈ A.B j' := by
    intro j' b hb
    by_cases hj : j' = j
    · subst hj; rw [hXB] at hb; exact hLRmem b hb
    · rw [hXB' j' hj] at hb; exact hb
  have hXnn : ∀ j', ∀ x ∈ demand (X.B j') X.p, ∀ k, 0 ≤ x k := by
    intro j'
    by_cases hj : j' = j
    · subst hj; rw [hXB]; exact nnR
    · rw [hXB' j' hj]; exact nnAll j'
  -- the LR-demand vanishes on I
  have hLRzero : ∀ x ∈ demand LRj p, ∀ k ∈ I, x k = 0 := by
    intro x hx k hk
    refine demand_coord_zero LRj p ρ hρ (fun b hb => hstab j b (hLRmem b hb)) k ?_ x hx
    intro b hb hkb
    have := (mem_LR (A.B j) p ρ I (hstab j) hsplitj hb).2 hkb
    simp [hk] at this
  -- solution of X
  set rr' := Function.update rr j (resO I (rr j)) with hrr'def
  have hrr' : ∀ j', rr' j' ∈ demand (X.B j') X.p := by
    intro j'
    by_cases hj : j' = j
    · subst hj; rw [hXB, hrr'def, Function.update_self]; exact hdec.2
    · rw [hXB' j' hj, hrr'def, Function.update_of_ne hj]; exact hrr j'
  have hsum' : ∑ j', rr' j' = X.r := by
    rw [hrr'def, sum_update, hsum, hXr]
    have := res_add I (rr j)
    set a := resI I (rr j)
    set b := resO I (rr j)
    rw [← this]; abel
  have hallocX : IsAllocProblem X := by
    refine ⟨fun j' b hb => hA.1 j' b (hXmem j' b hb), ?_, ?_, ?_,
      ⟨_, rr', hrr', hsum', fun _ => rfl⟩⟩
    · intro j'
      by_cases hj : j' = j
      · subst hj; rw [hXB]; exact ⟨_, lt_min hδ hρ, hVR⟩
      · rw [hXB' j' hj]; exact hA.2.1 j'
    · intro j' k
      rw [hXm]
      by_cases hj : j' = j
      · subst hj; rw [Function.update_self, Pi.add_apply]
        exact add_nonneg (hA.2.2.1 _ k) (nnI _ hdec.1 k)
      · rw [Function.update_of_ne hj]; exact hA.2.2.1 j' k
    · intro k
      rw [← hsum', Finset.sum_apply]
      exact Finset.sum_nonneg fun j' _ => hXnn j' _ (hrr' j') k
  have hred : ∀ t, IsSolution X t → IsSolution A t := by
    rintro t ⟨r2, hr2, hs2, ht2⟩
    refine ⟨Function.update r2 j (r2 j + resI I (rr j)), fun j' => ?_, ?_, fun j' => ?_⟩
    · by_cases hj : j' = j
      · subst hj
        rw [Function.update_self]
        have h2 : r2 j' ∈ demand LRj p := by have := hr2 j'; rwa [hXB] at this
        have hz := hLRzero _ h2
        refine (demand_dec (A.B j') p ρ I (hstab j') hsplitj hρ _).mpr ⟨?_, ?_⟩
        · have : resI I (r2 j' + resI I (rr j')) = resI I (rr j') := by
            funext k; simp only [resI, Pi.add_apply]; split_ifs with hk
            · rw [hz k hk, zero_add]
            · rfl
          rw [this]; exact hdec.1
        · have : resO I (r2 j' + resI I (rr j')) = r2 j' := by
            funext k; simp only [resO, resI, Pi.add_apply]; split_ifs with hk
            · rw [hz k hk]
            · simp
          rw [this]; exact h2
      · rw [Function.update_of_ne hj]
        have := hr2 j'; rwa [hXB' j' hj] at this
    · rw [sum_update, hs2, hXr]; abel
    · by_cases hj : j' = j
      · subst hj
        rw [ht2, Function.update_self, hXm, Function.update_self]; abel
      · rw [ht2, Function.update_of_ne hj, hXm, Function.update_of_ne hj]
  refine ⟨⟨hallocX, hred⟩, ?_⟩
  -- edges
  have hsubE : edges X ⊆ edges A := by
    intro e he
    simp only [edges, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    obtain ⟨hd, b, hb, hbe⟩ := he
    exact ⟨hd, b, hXmem _ b hb, hbe⟩
  have hnot : (s(i0, i'), j) ∉ edges X := by
    intro hx
    simp only [edges, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨-, b, hb, hbe⟩ := hx
    rw [hXB] at hb
    have := (mem_LR (A.B j) p ρ I (hstab j) hsplitj hb).2 (hbe i0 (Sym2.mem_mk_left _ _))
    simp [hi0] at this
  apply Finset.card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hsubE, fun h => hnot (h ▸ hadj)⟩
