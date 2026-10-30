-- Prove2me | solution 1 for ProductMixAuction.Allocate.lemma_11_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T16:02:06.657056+00:00
-- url     : https://prove2.me/submissions/90e1006c-0b3d-48ef-8df6-00145f7e7609

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Algorithm

open ProductMixAuction.Allocate

set_option linter.unusedSectionVars false

namespace PMAL11N

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

section decomp

open scoped Classical Pointwise

variable (L : List (Bid n)) (p : Fin n → ℝ) (ρ : ℝ)
  (hstab : ∀ b ∈ L, ∀ x ∈ Metric.ball p ρ, demGoods b x ⊆ demGoods b p)
include hstab

lemma N_dG (b : Bid n) (hb : b ∈ L) (hnm : ¬ IsMarginalBid b p) (x : Fin n → ℝ)
    (hx : x ∈ Metric.ball p ρ) : demGoods b x = demGoods b p ∧ (demGoods b p).card = 1 := by
  have hc : (demGoods b p).card = 1 := by
    unfold IsMarginalBid at hnm
    have := (dG_nonempty b p).card_pos
    omega
  refine ⟨Finset.eq_of_subset_of_card_le (hstab b hb x hx) ?_, hc⟩
  rw [hc]; exact (dG_nonempty b x).card_pos

lemma NM_iff (x : Fin n → ℝ) (hx : x ∈ Metric.ball p ρ) :
    NonMarginalAt L x ↔ NonMarginalAt (L.filter fun b => IsMarginalBid b p) x := by
  constructor
  · intro h b hb
    exact h b (List.mem_filter.mp hb).1
  · intro h b hb
    by_cases hm : IsMarginalBid b p
    · exact h b (List.mem_filter.mpr ⟨hb, by simpa using hm⟩)
    · rw [(N_dG L p ρ hstab b hb hm x hx).1]
      exact (N_dG L p ρ hstab b hb hm x hx).2

lemma nm_dec (x : Fin n → ℝ) (hx : x ∈ Metric.ball p ρ) :
    nmBundle L x = nmBundle (L.filter fun b => IsMarginalBid b p) x +
      nmBundle (L.filter fun b => ¬ IsMarginalBid b p) p := by
  rw [nm_split L (fun b => IsMarginalBid b p) x]
  congr 1
  unfold nmBundle
  congr 1
  apply List.map_congr_left
  intro b hb
  have hb' := List.mem_filter.mp hb
  rw [(N_dG L p ρ hstab b hb'.1 (by simpa using hb'.2) x hx).1]

lemma nb_iff (hρ : 0 < ρ) (y : Fin (n + 1) → ℤ) :
    y ∈ nearBundles L p ↔
      y - nmBundle (L.filter fun b => ¬ IsMarginalBid b p) p ∈
        nearBundles (L.filter fun b => IsMarginalBid b p) p := by
  constructor
  · intro h δ hδ
    obtain ⟨q, hq, hnm, hy⟩ := h (min δ ρ) (lt_min hδ hρ)
    have hqb : q ∈ Metric.ball p ρ := lt_of_lt_of_le hq (min_le_right _ _)
    refine ⟨q, lt_of_lt_of_le hq (min_le_left _ _), (NM_iff L p ρ hstab q hqb).mp hnm, ?_⟩
    rw [← hy, nm_dec L p ρ hstab q hqb]; abel
  · intro h δ hδ
    obtain ⟨q, hq, hnm, hy⟩ := h (min δ ρ) (lt_min hδ hρ)
    have hqb : q ∈ Metric.ball p ρ := lt_of_lt_of_le hq (min_le_right _ _)
    refine ⟨q, lt_of_lt_of_le hq (min_le_left _ _), (NM_iff L p ρ hstab q hqb).mpr hnm, ?_⟩
    rw [nm_dec L p ρ hstab q hqb, hy]; abel

lemma demand_iff (hρ : 0 < ρ) (x : Fin (n + 1) → ℤ) :
    x ∈ demand L p ↔
      x - nmBundle (L.filter fun b => ¬ IsMarginalBid b p) p ∈
        demand (L.filter fun b => IsMarginalBid b p) p := by
  set c := nmBundle (L.filter fun b => ¬ IsMarginalBid b p) p
  have hS : castZ '' nearBundles L p =
      ({castZ c} : Set (Fin (n + 1) → ℝ)) +
        castZ '' nearBundles (L.filter fun b => IsMarginalBid b p) p := by
    ext z
    rw [Set.singleton_add]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨castZ (y - c), ⟨y - c, (nb_iff L p ρ hstab hρ y).mp hy, rfl⟩, ?_⟩
      funext k; simp [castZ]
    · rintro ⟨_, ⟨y', hy', rfl⟩, rfl⟩
      refine ⟨y' + c, (nb_iff L p ρ hstab hρ _).mpr (by rw [add_sub_cancel_right]; exact hy'), ?_⟩
      funext k; simp [castZ]; ring
  unfold demand
  simp only [Set.mem_ofPred_eq]
  change castZ x ∈ convexHull ℝ (castZ '' nearBundles L p) ↔
    castZ (x - c) ∈ convexHull ℝ (castZ '' nearBundles (L.filter fun b => IsMarginalBid b p) p)
  rw [hS, convexHull_add, convexHull_singleton, Set.singleton_add]
  constructor
  · rintro ⟨z, hz, hzx⟩
    have : castZ (x - c) = z := by
      funext k; have := congrFun hzx k; simp [castZ] at this ⊢; linarith
    rwa [this]
  · intro h
    exact ⟨_, h, by funext k; simp [castZ]⟩

lemma LV_M (hρ : 0 < ρ) (δ : ℝ) (hL : EpsValid L p δ) :
    EpsValid (L.filter fun b => IsMarginalBid b p) p (min δ ρ) := by
  unfold EpsValid at hL ⊢
  set NL := L.filter fun b => ¬ IsMarginalBid b p
  have hball : Metric.ball p (min δ ρ) ⊆ Metric.ball p ρ :=
    Metric.ball_subset_ball (min_le_right _ _)
  have hconc : ConcaveOn ℝ (Metric.ball p ρ) (fB NL) := by
    refine ⟨convex_ball _ _, fun x hx y hy α β hα hβ hαβ => le_of_eq ?_⟩
    have hz := (convex_ball p ρ) hx hy hα hβ hαβ
    have per : ∀ b ∈ NL, surplusMax b (α • x + β • y) =
        α * surplusMax b x + β * surplusMax b y := by
      intro b hb
      have hb' := List.mem_filter.mp hb
      have hnm : ¬ IsMarginalBid b p := by simpa using hb'.2
      obtain ⟨g, hg⟩ := Finset.card_eq_one.mp
        (N_dG L p ρ hstab b hb'.1 hnm p (Metric.mem_ball_self hρ)).2
      have hgz : ∀ z ∈ Metric.ball p ρ, surplusMax b z = b.v g - ext z g := by
        intro z hzb
        have := (N_dG L p ρ hstab b hb'.1 hnm z hzb).1
        rw [hg] at this
        exact (dG_val b z g (by rw [this]; exact Finset.mem_singleton_self g)).symm
      rw [hgz _ hz, hgz x hx, hgz y hy, ext_comb x y α β hαβ]
      linear_combination (b.v g) * hαβ.symm
    simp only [fB, smul_eq_mul]
    have e : (NL.map fun b => (b.w : ℝ) * surplusMax b (α • x + β • y)) =
        NL.map fun b => (b.w : ℝ) * (α * surplusMax b x + β * surplusMax b y) :=
      List.map_congr_left (fun b hb => by rw [per b hb])
    rw [e, lsum_aff]
  have h := (hL.subset (Metric.ball_subset_ball (min_le_left _ _)) (convex_ball _ _)).sub
    (hconc.subset hball (convex_ball _ _))
  refine h.congr ?_
  intro x _
  have := fB_split L (fun b => IsMarginalBid b p) x
  simp only [Pi.sub_apply]
  linarith

lemma demand_M_nonneg (R : ℝ) (hR : 0 < R) (hRρ : R ≤ ρ)
    (hV : EpsValid (L.filter fun b => IsMarginalBid b p) p R) :
    ∀ x ∈ demand (L.filter fun b => IsMarginalBid b p) p, ∀ k, 0 ≤ x k := by
  intro x hx k
  have hS : Convex ℝ {z : Fin (n + 1) → ℝ | (0 : ℝ) ≤ z k} := by
    apply convex_halfSpace_ge
    exact ⟨fun a b => by simp, fun c a => by simp⟩
  have := demand_sub _ p _ hS (by
    intro y hy
    obtain ⟨q, hq, hnm, rfl⟩ := hy (R / 2) (by positivity)
    simp only [Set.mem_ofPred_eq, castZ]
    rw [nm_cast_NM _ q hnm k]
    refine LS _ p R hR hV (fun b hb => by simpa using (List.mem_filter.mp hb).2) ?_ q hq k
    intro b hb x' hx'
    exact hstab b (List.mem_filter.mp hb).1 x' (Metric.ball_subset_ball hRρ hx')) x hx
  simp only [Set.mem_ofPred_eq, castZ] at this
  exact_mod_cast this

end decomp

end PMAL11N

open PMAL11N in
theorem solution {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J] (A : AllocProblem n J)
    (hA : IsAllocProblem A) (hm : ∀ j k, 0 ≤ (nonMarginals A).m j k) :
    IsReduction (nonMarginals A) A ∧ edges (nonMarginals A) = edges A := by
  classical
  have hev : ∀ᶠ q in nhds A.p, ∀ j, ∀ b ∈ A.B j, demGoods b q ⊆ demGoods b A.p :=
    Filter.eventually_all.2 (fun j => eventually_sub (A.B j) A.p)
  obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff.mp hev
  have hstab : ∀ j, ∀ b ∈ A.B j, ∀ x ∈ Metric.ball A.p ρ, demGoods b x ⊆ demGoods b A.p :=
    fun j b hb x hx => hρs (Metric.mem_ball.mp hx) j b hb
  choose δ hδ hval using hA.2.1
  have hMval : ∀ j, EpsValid ((A.B j).filter fun b => IsMarginalBid b A.p) A.p (min (δ j) ρ) :=
    fun j => LV_M (A.B j) A.p ρ (hstab j) hρ (δ j) (hval j)
  have hdem : ∀ j x, x ∈ demand (A.B j) A.p ↔
      x - nmBundle ((A.B j).filter fun b => ¬ IsMarginalBid b A.p) A.p ∈
        demand ((A.B j).filter fun b => IsMarginalBid b A.p) A.p :=
    fun j x => demand_iff (A.B j) A.p ρ (hstab j) hρ x
  have hnn : ∀ j, ∀ x ∈ demand ((A.B j).filter fun b => IsMarginalBid b A.p) A.p, ∀ k, 0 ≤ x k :=
    fun j => demand_M_nonneg (A.B j) A.p ρ (hstab j) _ (lt_min (hδ j) hρ) (min_le_right _ _)
      (hMval j)
  set c : J → Fin (n + 1) → ℤ := fun j =>
    nmBundle ((A.B j).filter fun b => ¬ IsMarginalBid b A.p) A.p with hc
  have hB' : ∀ j, (nonMarginals A).B j = (A.B j).filter fun b => IsMarginalBid b A.p :=
    fun j => rfl
  have hm' : ∀ j, (nonMarginals A).m j = A.m j + c j := fun j => rfl
  have hr' : (nonMarginals A).r = A.r - ∑ j, c j := rfl
  have hp' : (nonMarginals A).p = A.p := rfl
  have hsol : ∀ t, IsSolution (nonMarginals A) t → IsSolution A t := by
    rintro t ⟨rr, hrr, hsum, ht⟩
    refine ⟨fun j => rr j + c j, fun j => ?_, ?_, fun j => ?_⟩
    · rw [hdem]
      show rr j + c j - c j ∈ _
      rw [add_sub_cancel_right]
      exact hrr j
    · rw [Finset.sum_add_distrib, hsum, hr']; abel
    · rw [ht j, hm']
      show rr j + (A.m j + c j) = rr j + c j + A.m j
      abel
  refine ⟨⟨⟨?_, ?_, hm, ?_, ?_⟩, hsol⟩, ?_⟩
  · intro j b hb
    rw [hB'] at hb
    exact hA.1 j b (List.mem_filter.mp hb).1
  · intro j
    rw [hB', hp']
    exact ⟨_, lt_min (hδ j) hρ, hMval j⟩
  · obtain ⟨t, rr, hrr, hsum, -⟩ := hA.2.2.2.2
    intro k
    rw [hr', ← hsum, ← Finset.sum_sub_distrib, Finset.sum_apply]
    exact Finset.sum_nonneg fun j _ => hnn j _ ((hdem j (rr j)).mp (hrr j)) k
  · obtain ⟨t, rr, hrr, hsum, -⟩ := hA.2.2.2.2
    refine ⟨fun j => (rr j - c j) + (nonMarginals A).m j, fun j => rr j - c j,
      fun j => ?_, ?_, fun j => rfl⟩
    · rw [hB', hp']; exact (hdem j (rr j)).mp (hrr j)
    · rw [Finset.sum_sub_distrib, hsum, hr']
  · ext ⟨e, j⟩
    simp only [edges, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hB', hp']
    constructor
    · rintro ⟨hd, b, hb, hbe⟩
      exact ⟨hd, b, (List.mem_filter.mp hb).1, hbe⟩
    · rintro ⟨hd, b, hb, hbe⟩
      refine ⟨hd, b, List.mem_filter.mpr ⟨hb, ?_⟩, hbe⟩
      induction e using Sym2.ind with
      | _ i i' =>
        have hii : i ≠ i' := by simpa using hd
        simp only [decide_eq_true_eq]
        exact Finset.one_lt_card.mpr ⟨i, hbe i (Sym2.mem_mk_left _ _), i',
          hbe i' (Sym2.mem_mk_right _ _), hii⟩
