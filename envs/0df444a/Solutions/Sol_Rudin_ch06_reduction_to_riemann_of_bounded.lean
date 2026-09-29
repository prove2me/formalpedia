-- Prove2me | solution 1 for Rudin.ch06_reduction_to_riemann_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-18T15:38:34.618774+00:00
-- url     : https://prove2.me/submissions/6f8cc922-a0f9-4a04-9ed8-02549e21323e

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes
import Theorems.Thm_Rudin_ch06_refinement
import Theorems.Thm_Rudin_ch06_riemann_criterion

open Filter Topology

namespace RudinRed

open Rudin

/-! ### Partition plumbing -/

/-- The division points of a partition increase. -/
lemma px_mono {a b : ℝ} (P : Partition a b) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ P.n) :
    P.x i ≤ P.x j := by
  induction j with
  | zero =>
    have : i = 0 := Nat.le_zero.mp hij
    simp [this]
  | succ m ih =>
    rcases Nat.lt_or_ge i (m + 1) with h | h
    · have him : i ≤ m := Nat.lt_succ_iff.mp h
      exact le_trans (ih him (by omega)) (P.mono m (by omega))
    · have : i = m + 1 := le_antisymm hij h
      simp [this]

lemma px_mem {a b : ℝ} (P : Partition a b) {i : ℕ} (hi : i ≤ P.n) : P.x i ∈ Set.Icc a b := by
  constructor
  · have := px_mono P (Nat.zero_le i) hi
    rwa [P.first] at this
  · have := px_mono P hi (le_refl P.n)
    rwa [P.last] at this

/-- The trivial partition `{a, b}`. -/
def trivialPartition {a b : ℝ} (hab : a ≤ b) : Partition a b where
  n := 1
  x := fun i => if i = 0 then a else b
  first := by norm_num
  last := by norm_num
  mono := by
    intro i hi
    have : i = 0 := by omega
    subst this
    norm_num
    exact hab

/-- Every partition has a refinement having `c` among its division points. -/
lemma exists_refinement_with_point {a b : ℝ} (P : Partition a b) (c : ℝ) (hc : c ∈ Set.Icc a b) :
    ∃ P' : Partition a b, Refines P' P ∧ ∃ k, ∃ _ : k ≤ P'.n, P'.x k = c := by
  classical
  have hex : ∃ j, c ≤ P.x j := ⟨P.n, by rw [P.last]; exact hc.2⟩
  set k := Nat.find hex with hkdef
  have hkspec : c ≤ P.x k := Nat.find_spec hex
  have hkmin : ∀ j, j < k → P.x j < c := fun j hj => lt_of_not_ge (Nat.find_min hex hj)
  have hkn : k ≤ P.n := Nat.find_min' hex (by rw [P.last]; exact hc.2)
  refine ⟨⟨P.n + 1, fun j => if j < k then P.x j else if j = k then c else P.x (j - 1), ?_, ?_, ?_⟩,
    ?_, k, ?_, ?_⟩
  · by_cases h : 0 < k
    · rw [if_pos h]
      exact P.first
    · have hk0 : k = 0 := by omega
      have hca : c ≤ a := by rw [← P.first, ← hk0]; exact hkspec
      rw [if_neg (by omega), if_pos (show 0 = k by omega)]
      exact le_antisymm hca hc.1
  · have h1 : ¬ (P.n + 1 < k) := by omega
    have h2 : ¬ (P.n + 1 = k) := by omega
    rw [if_neg h1, if_neg h2, Nat.add_sub_cancel]
    exact P.last
  · intro j hj
    rcases lt_trichotomy j k with h | h | h
    · rcases Nat.lt_or_ge (j + 1) k with h' | h'
      · have hjn : j < P.n := by omega
        rw [if_pos h, if_pos h']
        exact P.mono j hjn
      · have hjk : j + 1 = k := by omega
        have h2 : ¬ (j + 1 < k) := by omega
        rw [if_pos h, if_neg h2, if_pos hjk]
        exact le_of_lt (hkmin j h)
    · have h1 : ¬ (j < k) := by omega
      have h2 : ¬ (j + 1 < k) := by omega
      have h3 : ¬ (j + 1 = k) := by omega
      rw [if_neg h1, if_pos h, if_neg h2, if_neg h3, show j + 1 - 1 = k by omega]
      exact hkspec
    · have h1 : ¬ (j < k) := by omega
      have h1' : ¬ (j = k) := by omega
      have h2 : ¬ (j + 1 < k) := by omega
      have h3 : ¬ (j + 1 = k) := by omega
      rw [if_neg h1, if_neg h1', if_neg h2, if_neg h3, show j + 1 - 1 = j by omega]
      have hjn : j - 1 < P.n := by omega
      have := P.mono (j - 1) hjn
      have heq2 : j - 1 + 1 = j := by omega
      rwa [heq2] at this
  · intro i hi
    by_cases h : i < k
    · refine ⟨i, ?_, ?_⟩
      · show i ≤ P.n + 1
        omega
      · show (if i < k then P.x i else if i = k then c else P.x (i - 1)) = P.x i
        rw [if_pos h]
    · refine ⟨i + 1, ?_, ?_⟩
      · show i + 1 ≤ P.n + 1
        omega
      · show (if i + 1 < k then P.x (i + 1) else if i + 1 = k then c else P.x (i + 1 - 1)) = P.x i
        rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
  · show k ≤ P.n + 1
    omega
  · show (if k < k then P.x k else if k = k then c else P.x (k - 1)) = c
    rw [if_neg (by omega), if_pos rfl]

/-- `Refines` is reflexive. -/
lemma Refines_refl {a b : ℝ} (P : Partition a b) : Refines P P :=
  fun i hi => ⟨i, hi, rfl⟩

/-- `Refines` is transitive. -/
lemma Refines_trans {a b : ℝ} {Q P' P : Partition a b} (h1 : Refines Q P') (h2 : Refines P' P) :
    Refines Q P := by
  intro i hi
  obtain ⟨j, hj, hxj⟩ := h2 i hi
  obtain ⟨k, hk, hxk⟩ := h1 j hj
  exact ⟨k, hk, by rw [hxk, hxj]⟩

/-- Any two partitions of `[a, b]` have a common refinement. -/
lemma exists_common_refinement {a b : ℝ} (P₁ P₂ : Partition a b) :
    ∃ Q : Partition a b, Refines Q P₁ ∧ Refines Q P₂ := by
  have key : ∀ k, k ≤ P₂.n + 1 →
      ∃ Q : Partition a b, Refines Q P₁ ∧ ∀ i < k, ∃ j ≤ Q.n, Q.x j = P₂.x i := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨P₁, Refines_refl P₁, by omega⟩
    | succ m ih =>
      intro hm
      obtain ⟨Q, hQ1, hQ2⟩ := ih (by omega)
      have hmem : P₂.x m ∈ Set.Icc a b := px_mem P₂ (by omega)
      obtain ⟨Q', hQ'ref, j₀, hj₀, hxj₀⟩ := exists_refinement_with_point Q (P₂.x m) hmem
      refine ⟨Q', Refines_trans hQ'ref hQ1, ?_⟩
      intro i hi
      rcases Nat.lt_or_ge i m with h | h
      · obtain ⟨j, hj, hxj⟩ := hQ2 i h
        obtain ⟨j', hj', hxj'⟩ := hQ'ref j hj
        exact ⟨j', hj', by rw [hxj', hxj]⟩
      · have : i = m := by omega
        subst this
        exact ⟨j₀, hj₀, hxj₀⟩
  obtain ⟨Q, hQ1, hQ2⟩ := key (P₂.n + 1) (le_refl _)
  exact ⟨Q, hQ1, fun i hi => hQ2 i (by omega)⟩

/-- The increments of `α` over the subintervals of a partition telescope. -/
lemma sum_delta {a b : ℝ} (α : ℝ → ℝ) (P : Partition a b) :
    ∑ i ∈ Finset.range P.n, (α (P.x (i + 1)) - α (P.x i)) = α b - α a := by
  rw [Finset.sum_range_sub (fun i => α (P.x i)) P.n, P.first, P.last]

/-! ### The sets of upper and lower sums are bounded -/

lemma upperSum_ge {a b M : ℝ} {f α : ℝ → ℝ} (hα : MonotoneOn α (Set.Icc a b))
    (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M) (P : Partition a b) :
    -(M * (α b - α a)) ≤ upperSum f α P := by
  have key : ∀ i ∈ Finset.range P.n,
      -(M * (α (P.x (i + 1)) - α (P.x i)))
        ≤ sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) * (α (P.x (i + 1)) - α (P.x i)) := by
    intro i hi
    have hi' : i < P.n := Finset.mem_range.mp hi
    have h1 : P.x i ∈ Set.Icc a b := px_mem P (le_of_lt hi')
    have h2 : P.x (i + 1) ∈ Set.Icc a b := px_mem P hi'
    have hle : P.x i ≤ P.x (i + 1) := P.mono i hi'
    have hsub : Set.Icc (P.x i) (P.x (i + 1)) ⊆ Set.Icc a b := Set.Icc_subset_Icc h1.1 h2.2
    have hbdd : BddAbove (f '' Set.Icc (P.x i) (P.x (i + 1))) :=
      ⟨M, by rintro _ ⟨y, hy, rfl⟩; exact (abs_le.mp (hM y (hsub hy))).2⟩
    have hmem : f (P.x i) ∈ f '' Set.Icc (P.x i) (P.x (i + 1)) := ⟨P.x i, ⟨le_refl _, hle⟩, rfl⟩
    have hge : -M ≤ sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) :=
      le_trans (abs_le.mp (hM (P.x i) h1)).1 (le_csSup hbdd hmem)
    have hΔ : 0 ≤ α (P.x (i + 1)) - α (P.x i) := by
      have := hα h1 h2 hle
      linarith
    nlinarith
  have := Finset.sum_le_sum key
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, sum_delta α P] at this
  exact this

lemma lowerSum_le {a b M : ℝ} {f α : ℝ → ℝ} (hα : MonotoneOn α (Set.Icc a b))
    (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M) (P : Partition a b) :
    lowerSum f α P ≤ M * (α b - α a) := by
  have key : ∀ i ∈ Finset.range P.n,
      sInf (f '' Set.Icc (P.x i) (P.x (i + 1))) * (α (P.x (i + 1)) - α (P.x i))
        ≤ M * (α (P.x (i + 1)) - α (P.x i)) := by
    intro i hi
    have hi' : i < P.n := Finset.mem_range.mp hi
    have h1 : P.x i ∈ Set.Icc a b := px_mem P (le_of_lt hi')
    have h2 : P.x (i + 1) ∈ Set.Icc a b := px_mem P hi'
    have hle : P.x i ≤ P.x (i + 1) := P.mono i hi'
    have hsub : Set.Icc (P.x i) (P.x (i + 1)) ⊆ Set.Icc a b := Set.Icc_subset_Icc h1.1 h2.2
    have hbdd : BddBelow (f '' Set.Icc (P.x i) (P.x (i + 1))) :=
      ⟨-M, by rintro _ ⟨y, hy, rfl⟩; exact (abs_le.mp (hM y (hsub hy))).1⟩
    have hmem : f (P.x i) ∈ f '' Set.Icc (P.x i) (P.x (i + 1)) := ⟨P.x i, ⟨le_refl _, hle⟩, rfl⟩
    have hle' : sInf (f '' Set.Icc (P.x i) (P.x (i + 1))) ≤ M :=
      le_trans (csInf_le hbdd hmem) (abs_le.mp (hM (P.x i) h1)).2
    have hΔ : 0 ≤ α (P.x (i + 1)) - α (P.x i) := by
      have := hα h1 h2 hle
      linarith
    nlinarith
  have := Finset.sum_le_sum key
  rw [← Finset.mul_sum, sum_delta α P] at this
  exact this

lemma bddBelow_upperSums {a b M : ℝ} {f α : ℝ → ℝ}
    (hα : MonotoneOn α (Set.Icc a b)) (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M) :
    BddBelow {y : ℝ | ∃ P : Partition a b, y = upperSum f α P} := by
  refine ⟨-(M * (α b - α a)), ?_⟩
  rintro _ ⟨P, rfl⟩
  exact upperSum_ge hα hM P

lemma bddAbove_lowerSums {a b M : ℝ} {f α : ℝ → ℝ}
    (hα : MonotoneOn α (Set.Icc a b)) (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M) :
    BddAbove {y : ℝ | ∃ P : Partition a b, y = lowerSum f α P} := by
  refine ⟨M * (α b - α a), ?_⟩
  rintro _ ⟨P, rfl⟩
  exact lowerSum_le hα hM P

lemma upperSums_nonempty {a b : ℝ} (f α : ℝ → ℝ) (hab : a ≤ b) :
    {y : ℝ | ∃ P : Partition a b, y = upperSum f α P}.Nonempty :=
  ⟨upperSum f α (trivialPartition hab), trivialPartition hab, rfl⟩

lemma lowerSums_nonempty {a b : ℝ} (f α : ℝ → ℝ) (hab : a ≤ b) :
    {y : ℝ | ∃ P : Partition a b, y = lowerSum f α P}.Nonempty :=
  ⟨lowerSum f α (trivialPartition hab), trivialPartition hab, rfl⟩

/-! ### The key comparison on one subinterval -/

/-- On a subinterval `[u, v]` of `[a, b]`, the contribution of `f` against `dα` and the
contribution of `f α'` against `dx` differ by at most `M` times the oscillation of `α'`. -/
lemma term_compare {a b u v M K : ℝ} {f α g : ℝ → ℝ}
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
    (hmono : MonotoneOn α (Set.Icc a b))
    (hαd : ∀ x ∈ Set.Icc a b, HasDerivAt α (g x) x)
    (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M) (hK : ∀ x ∈ Set.Icc a b, |g x| ≤ K) :
    (sSup (f '' Set.Icc u v) * (α v - α u)
        ≤ sSup ((fun x => f x * g x) '' Set.Icc u v) * (v - u)
          + M * ((sSup (g '' Set.Icc u v) - sInf (g '' Set.Icc u v)) * (v - u)))
      ∧ (sSup ((fun x => f x * g x) '' Set.Icc u v) * (v - u)
        ≤ sSup (f '' Set.Icc u v) * (α v - α u)
          + M * ((sSup (g '' Set.Icc u v) - sInf (g '' Set.Icc u v)) * (v - u)))
      ∧ (sInf ((fun x => f x * g x) '' Set.Icc u v) * (v - u)
          - M * ((sSup (g '' Set.Icc u v) - sInf (g '' Set.Icc u v)) * (v - u))
        ≤ sInf (f '' Set.Icc u v) * (α v - α u))
      ∧ (sInf (f '' Set.Icc u v) * (α v - α u)
          - M * ((sSup (g '' Set.Icc u v) - sInf (g '' Set.Icc u v)) * (v - u))
        ≤ sInf ((fun x => f x * g x) '' Set.Icc u v) * (v - u)) := by
  rcases eq_or_lt_of_le huv with heq | hlt
  · subst heq
    simp
  have hsub : Set.Icc u v ⊆ Set.Icc a b := Set.Icc_subset_Icc hau hvb
  have hne : (Set.Icc u v).Nonempty := ⟨u, le_refl u, huv⟩
  have humem : u ∈ Set.Icc u v := ⟨le_refl u, huv⟩
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM u (hsub humem))
  have hnef : (f '' Set.Icc u v).Nonempty := hne.image f
  have hneg : (g '' Set.Icc u v).Nonempty := hne.image g
  have hnefg : ((fun x => f x * g x) '' Set.Icc u v).Nonempty := hne.image _
  have hbddf : BddAbove (f '' Set.Icc u v) :=
    ⟨M, by rintro _ ⟨y, hy, rfl⟩; exact (abs_le.mp (hM y (hsub hy))).2⟩
  have hbddf' : BddBelow (f '' Set.Icc u v) :=
    ⟨-M, by rintro _ ⟨y, hy, rfl⟩; exact (abs_le.mp (hM y (hsub hy))).1⟩
  have hbddg : BddAbove (g '' Set.Icc u v) :=
    ⟨K, by rintro _ ⟨y, hy, rfl⟩; exact (abs_le.mp (hK y (hsub hy))).2⟩
  have hbddg' : BddBelow (g '' Set.Icc u v) :=
    ⟨-K, by rintro _ ⟨y, hy, rfl⟩; exact (abs_le.mp (hK y (hsub hy))).1⟩
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK u (hsub humem))
  have hbddfg : BddAbove ((fun x => f x * g x) '' Set.Icc u v) :=
    ⟨M * K, by
      rintro _ ⟨y, hy, rfl⟩
      have h1 : |f y * g y| ≤ M * K := by
        rw [abs_mul]
        exact mul_le_mul (hM y (hsub hy)) (hK y (hsub hy)) (abs_nonneg _) hM0
      exact (abs_le.mp h1).2⟩
  have hbddfg' : BddBelow ((fun x => f x * g x) '' Set.Icc u v) :=
    ⟨-(M * K), by
      rintro _ ⟨y, hy, rfl⟩
      have h1 : |f y * g y| ≤ M * K := by
        rw [abs_mul]
        exact mul_le_mul (hM y (hsub hy)) (hK y (hsub hy)) (abs_nonneg _) hM0
      exact (abs_le.mp h1).1⟩
  set Sf := sSup (f '' Set.Icc u v) with hSf
  set If := sInf (f '' Set.Icc u v) with hIf
  set Sg := sSup (g '' Set.Icc u v) with hSg
  set Ig := sInf (g '' Set.Icc u v) with hIg
  set Sfg := sSup ((fun x => f x * g x) '' Set.Icc u v) with hSfg
  set Ifg := sInf ((fun x => f x * g x) '' Set.Icc u v) with hIfg
  have hgbounds : ∀ s ∈ Set.Icc u v, Ig ≤ g s ∧ g s ≤ Sg := fun s hs =>
    ⟨csInf_le hbddg' ⟨s, hs, rfl⟩, le_csSup hbddg ⟨s, hs, rfl⟩⟩
  have hosc0 : 0 ≤ Sg - Ig := by
    have h1 := (hgbounds u humem).1
    have h2 := (hgbounds u humem).2
    linarith
  -- the mean value theorem on `[u, v]`
  have hcont : ContinuousOn α (Set.Icc u v) := fun x hx =>
    ((hαd x (hsub hx)).continuousAt).continuousWithinAt
  obtain ⟨t, ht, hslope⟩ :=
    exists_hasDerivAt_eq_slope α g hlt hcont
      (fun x hx => hαd x (hsub (Set.Ioo_subset_Icc_self hx)))
  have htmem : t ∈ Set.Icc u v := Set.Ioo_subset_Icc_self ht
  have hvu : (0:ℝ) < v - u := sub_pos.mpr hlt
  have hvu0 : (0:ℝ) ≤ v - u := le_of_lt hvu
  have hΔ : α v - α u = g t * (v - u) := by
    field_simp at hslope
    linarith [hslope]
  have hc0 : 0 ≤ g t := by
    have hmv : α u ≤ α v := hmono (hsub humem) (hsub ⟨huv, le_refl v⟩) huv
    nlinarith
  -- pointwise estimates
  have hswap : ∀ s ∈ Set.Icc u v, |f s * (g t - g s)| ≤ M * (Sg - Ig) := by
    intro s hs
    have h1 := hgbounds s hs
    have h2 := hgbounds t htmem
    have habs : |g t - g s| ≤ Sg - Ig := by
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    calc |f s * (g t - g s)| = |f s| * |g t - g s| := abs_mul _ _
      _ ≤ M * (Sg - Ig) := mul_le_mul (hM s (hsub hs)) habs (abs_nonneg _) hM0
  have hswap' : ∀ s ∈ Set.Icc u v, |f s * (g s - g t)| ≤ M * (Sg - Ig) := by
    intro s hs
    have := hswap s hs
    rwa [show f s * (g s - g t) = -(f s * (g t - g s)) by ring, abs_neg]
  have pointA : ∀ s ∈ Set.Icc u v, f s * g t ≤ Sfg + M * (Sg - Ig) := by
    intro s hs
    have h1 : f s * g s ≤ Sfg := le_csSup hbddfg ⟨s, hs, rfl⟩
    have h2 : f s * (g t - g s) ≤ M * (Sg - Ig) :=
      le_trans (le_abs_self _) (hswap s hs)
    nlinarith
  have pointB : ∀ s ∈ Set.Icc u v, f s * g s ≤ Sf * g t + M * (Sg - Ig) := by
    intro s hs
    have h1 : f s ≤ Sf := le_csSup hbddf ⟨s, hs, rfl⟩
    have h1' : f s * g t ≤ Sf * g t := mul_le_mul_of_nonneg_right h1 hc0
    have h2 : f s * (g s - g t) ≤ M * (Sg - Ig) :=
      le_trans (le_abs_self _) (hswap' s hs)
    nlinarith
  have pointC : ∀ s ∈ Set.Icc u v, Ifg - M * (Sg - Ig) ≤ f s * g t := by
    intro s hs
    have h1 : Ifg ≤ f s * g s := csInf_le hbddfg' ⟨s, hs, rfl⟩
    have h2 : -(M * (Sg - Ig)) ≤ f s * (g t - g s) :=
      neg_le_of_abs_le (hswap s hs)
    nlinarith
  have pointD : ∀ s ∈ Set.Icc u v, If * g t - M * (Sg - Ig) ≤ f s * g s := by
    intro s hs
    have h1 : If ≤ f s := csInf_le hbddf' ⟨s, hs, rfl⟩
    have h1' : If * g t ≤ f s * g t := mul_le_mul_of_nonneg_right h1 hc0
    have h2 : -(M * (Sg - Ig)) ≤ f s * (g s - g t) :=
      neg_le_of_abs_le (hswap' s hs)
    nlinarith
  -- from the pointwise estimates to the suprema and infima
  have hA : Sf * g t ≤ Sfg + M * (Sg - Ig) := by
    rcases eq_or_lt_of_le hc0 with hzero | hpos
    · rw [← hzero, mul_zero]
      have := pointA u humem
      rwa [← hzero, mul_zero] at this
    · have hle : Sf ≤ (Sfg + M * (Sg - Ig)) / g t := by
        refine csSup_le hnef ?_
        rintro _ ⟨s, hs, rfl⟩
        rw [le_div_iff₀ hpos]
        exact pointA s hs
      exact (le_div_iff₀ hpos).mp hle
  have hB : Sfg ≤ Sf * g t + M * (Sg - Ig) := by
    refine csSup_le hnefg ?_
    rintro _ ⟨s, hs, rfl⟩
    exact pointB s hs
  have hC : Ifg - M * (Sg - Ig) ≤ If * g t := by
    rcases eq_or_lt_of_le hc0 with hzero | hpos
    · rw [← hzero, mul_zero]
      have := pointC u humem
      rwa [← hzero, mul_zero] at this
    · have hle : (Ifg - M * (Sg - Ig)) / g t ≤ If := by
        refine le_csInf hnef ?_
        rintro _ ⟨s, hs, rfl⟩
        rw [div_le_iff₀ hpos]
        exact pointC s hs
      exact (div_le_iff₀ hpos).mp hle
  have hD : If * g t - M * (Sg - Ig) ≤ Ifg := by
    refine le_csInf hnefg ?_
    rintro _ ⟨s, hs, rfl⟩
    exact pointD s hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hΔ]
    have := mul_le_mul_of_nonneg_right hA hvu0
    nlinarith
  · rw [hΔ]
    have := mul_le_mul_of_nonneg_right hB hvu0
    nlinarith
  · rw [hΔ]
    have := mul_le_mul_of_nonneg_right hC hvu0
    nlinarith
  · rw [hΔ]
    have := mul_le_mul_of_nonneg_right hD hvu0
    nlinarith

/-! ### The comparison for whole partitions -/

lemma sum_compare {a b M K : ℝ} {f α g : ℝ → ℝ}
    (hmono : MonotoneOn α (Set.Icc a b))
    (hαd : ∀ x ∈ Set.Icc a b, HasDerivAt α (g x) x)
    (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M) (hK : ∀ x ∈ Set.Icc a b, |g x| ≤ K)
    (P : Partition a b) :
    (upperSum f α P ≤ upperSum (fun x => f x * g x) id P
        + M * (upperSum g id P - lowerSum g id P))
      ∧ (upperSum (fun x => f x * g x) id P
        ≤ upperSum f α P + M * (upperSum g id P - lowerSum g id P))
      ∧ (lowerSum (fun x => f x * g x) id P - M * (upperSum g id P - lowerSum g id P)
        ≤ lowerSum f α P)
      ∧ (lowerSum f α P - M * (upperSum g id P - lowerSum g id P)
        ≤ lowerSum (fun x => f x * g x) id P) := by
  have hosc : upperSum g id P - lowerSum g id P
      = ∑ i ∈ Finset.range P.n,
        (sSup (g '' Set.Icc (P.x i) (P.x (i + 1))) - sInf (g '' Set.Icc (P.x i) (P.x (i + 1))))
          * (P.x (i + 1) - P.x i) := by
    rw [upperSum, lowerSum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [id_eq]; ring
  have hterms := fun (i : ℕ) (hi : i ∈ Finset.range P.n) => by
    have hi' : i < P.n := Finset.mem_range.mp hi
    exact term_compare (a := a) (b := b) (f := f) (α := α) (g := g) (M := M) (K := K)
      (px_mem P (le_of_lt hi')).1 (P.mono i hi') (px_mem P hi').2 hmono hαd hM hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hosc, upperSum, upperSum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i hi => ?_
    simpa only [id_eq] using (hterms i hi).1
  · rw [hosc, upperSum, upperSum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i hi => ?_
    simpa only [id_eq] using (hterms i hi).2.1
  · rw [hosc, lowerSum, lowerSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun i hi => ?_
    simpa only [id_eq] using (hterms i hi).2.2.1
  · rw [hosc, lowerSum, lowerSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun i hi => ?_
    simpa only [id_eq] using (hterms i hi).2.2.2

end RudinRed

open Rudin RudinRed in
/-- Rudin, Theorem 6.17, with the boundedness hypotheses of Chapter 6: let `α` increase
monotonically with `α'` bounded and Riemann-integrable on `[a, b]`, and let `f` be bounded.
Then `f ∈ ℛ(α)` if and only if `f α' ∈ ℛ`, and in that case `∫ f dα = ∫ f α' dx`. -/
theorem solution (a b : ℝ) (hab : a ≤ b) (f α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b))
    (hαd : ∀ x ∈ Set.Icc a b, HasDerivAt α (deriv α x) x)
    (hα' : RiemannIntegrable a b (deriv α))
    (hα'b : ∃ K, ∀ x ∈ Set.Icc a b, |deriv α x| ≤ K)
    (hf : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) :
    (RSIntegrable a b f α ↔ RiemannIntegrable a b (fun x => f x * deriv α x)) ∧
    (RSIntegrable a b f α →
      RSIntegral a b f α = RiemannIntegral a b (fun x => f x * deriv α x)) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨K, hK⟩ := hα'b
  set g : ℝ → ℝ := deriv α with hg
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM a ⟨le_refl a, hab⟩)
  have hidmono : MonotoneOn id (Set.Icc a b) := fun x _ y _ hxy => hxy
  have hfgb : ∃ C, ∀ x ∈ Set.Icc a b, |f x * g x| ≤ C := by
    refine ⟨M * K, fun x hx => ?_⟩
    rw [abs_mul]
    exact mul_le_mul (hM x hx) (hK x hx) (abs_nonneg _) hM0
  obtain ⟨C, hC⟩ := hfgb
  -- the oscillation of `g` can be made small, and stays small under refinement
  have hsmall : ∀ ε : ℝ, 0 < ε → ∃ P₀ : Partition a b, ∀ P : Partition a b, Refines P P₀ →
      upperSum g id P - lowerSum g id P < ε := by
    intro ε hε
    obtain ⟨P₀, hP₀⟩ :=
      (ch06_riemann_criterion a b hab g id hidmono ⟨K, hK⟩).mp hα' ε hε
    refine ⟨P₀, fun P hP => ?_⟩
    have := ch06_refinement a b hab g id hidmono ⟨K, hK⟩ P₀ P hP
    linarith [this.1, this.2]
  -- the four comparisons at the level of the upper and lower integrals
  have hupper : upperIntegral a b f α = upperIntegral a b (fun x => f x * g x) id := by
    have key : ∀ ε : ℝ, 0 < ε →
        upperIntegral a b f α ≤ upperIntegral a b (fun x => f x * g x) id + M * ε ∧
        upperIntegral a b (fun x => f x * g x) id ≤ upperIntegral a b f α + M * ε := by
      intro ε hε
      obtain ⟨P₀, hP₀⟩ := hsmall ε hε
      constructor
      · have hle : upperIntegral a b f α - M * ε
            ≤ upperIntegral a b (fun x => f x * g x) id := by
          refine le_csInf (upperSums_nonempty (fun x => f x * g x) id hab) ?_
          rintro _ ⟨Q, rfl⟩
          obtain ⟨R, hR1, hR2⟩ := exists_common_refinement Q P₀
          have hoscR : upperSum g id R - lowerSum g id R < ε := hP₀ R hR2
          have hcmp := (sum_compare hα hαd hM hK R).1
          have h1 : upperIntegral a b f α ≤ upperSum f α R :=
            csInf_le (bddBelow_upperSums hα hM) ⟨R, rfl⟩
          have h2 : upperSum (fun x => f x * g x) id R ≤ upperSum (fun x => f x * g x) id Q :=
            (ch06_refinement a b hab (fun x => f x * g x) id hidmono ⟨C, hC⟩ Q R hR1).2
          nlinarith
        linarith
      · have hle : upperIntegral a b (fun x => f x * g x) id - M * ε
            ≤ upperIntegral a b f α := by
          refine le_csInf (upperSums_nonempty f α hab) ?_
          rintro _ ⟨Q, rfl⟩
          obtain ⟨R, hR1, hR2⟩ := exists_common_refinement Q P₀
          have hoscR : upperSum g id R - lowerSum g id R < ε := hP₀ R hR2
          have hcmp := (sum_compare hα hαd hM hK R).2.1
          have h1 : upperIntegral a b (fun x => f x * g x) id
              ≤ upperSum (fun x => f x * g x) id R :=
            csInf_le (bddBelow_upperSums hidmono hC) ⟨R, rfl⟩
          have h2 : upperSum f α R ≤ upperSum f α Q :=
            (ch06_refinement a b hab f α hα ⟨M, hM⟩ Q R hR1).2
          nlinarith
        linarith
    refine le_antisymm ?_ ?_
    · refine le_of_forall_pos_le_add ?_
      intro ε hε
      have hpos : 0 < ε / (M + 1) := by positivity
      have := (key (ε / (M + 1)) hpos).1
      have hMle : M * (ε / (M + 1)) ≤ ε := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by linarith : (0:ℝ) < M + 1)]
        nlinarith
      linarith
    · refine le_of_forall_pos_le_add ?_
      intro ε hε
      have hpos : 0 < ε / (M + 1) := by positivity
      have := (key (ε / (M + 1)) hpos).2
      have hMle : M * (ε / (M + 1)) ≤ ε := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by linarith : (0:ℝ) < M + 1)]
        nlinarith
      linarith
  have hlower : lowerIntegral a b f α = lowerIntegral a b (fun x => f x * g x) id := by
    have key : ∀ ε : ℝ, 0 < ε →
        lowerIntegral a b (fun x => f x * g x) id ≤ lowerIntegral a b f α + M * ε ∧
        lowerIntegral a b f α ≤ lowerIntegral a b (fun x => f x * g x) id + M * ε := by
      intro ε hε
      obtain ⟨P₀, hP₀⟩ := hsmall ε hε
      constructor
      · refine csSup_le (lowerSums_nonempty (fun x => f x * g x) id hab) ?_
        rintro _ ⟨Q, rfl⟩
        obtain ⟨R, hR1, hR2⟩ := exists_common_refinement Q P₀
        have hoscR : upperSum g id R - lowerSum g id R < ε := hP₀ R hR2
        have hcmp := (sum_compare hα hαd hM hK R).2.2.1
        have h1 : lowerSum f α R ≤ lowerIntegral a b f α :=
          le_csSup (bddAbove_lowerSums hα hM) ⟨R, rfl⟩
        have h2 : lowerSum (fun x => f x * g x) id Q ≤ lowerSum (fun x => f x * g x) id R :=
          (ch06_refinement a b hab (fun x => f x * g x) id hidmono ⟨C, hC⟩ Q R hR1).1
        nlinarith
      · refine csSup_le (lowerSums_nonempty f α hab) ?_
        rintro _ ⟨Q, rfl⟩
        obtain ⟨R, hR1, hR2⟩ := exists_common_refinement Q P₀
        have hoscR : upperSum g id R - lowerSum g id R < ε := hP₀ R hR2
        have hcmp := (sum_compare hα hαd hM hK R).2.2.2
        have h1 : lowerSum (fun x => f x * g x) id R
            ≤ lowerIntegral a b (fun x => f x * g x) id :=
          le_csSup (bddAbove_lowerSums hidmono hC) ⟨R, rfl⟩
        have h2 : lowerSum f α Q ≤ lowerSum f α R :=
          (ch06_refinement a b hab f α hα ⟨M, hM⟩ Q R hR1).1
        nlinarith
    refine le_antisymm ?_ ?_
    · refine le_of_forall_pos_le_add ?_
      intro ε hε
      have hpos : 0 < ε / (M + 1) := by positivity
      have := (key (ε / (M + 1)) hpos).2
      have hMle : M * (ε / (M + 1)) ≤ ε := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by linarith : (0:ℝ) < M + 1)]
        nlinarith
      linarith
    · refine le_of_forall_pos_le_add ?_
      intro ε hε
      have hpos : 0 < ε / (M + 1) := by positivity
      have := (key (ε / (M + 1)) hpos).1
      have hMle : M * (ε / (M + 1)) ≤ ε := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by linarith : (0:ℝ) < M + 1)]
        nlinarith
      linarith
  constructor
  · constructor
    · intro h
      have h' : upperIntegral a b f α = lowerIntegral a b f α := h
      show upperIntegral a b (fun x => f x * g x) id = lowerIntegral a b (fun x => f x * g x) id
      rw [← hupper, ← hlower]
      exact h'
    · intro h
      have h' : upperIntegral a b (fun x => f x * g x) id
          = lowerIntegral a b (fun x => f x * g x) id := h
      show upperIntegral a b f α = lowerIntegral a b f α
      rw [hupper, hlower]
      exact h'
  · intro _
    exact hupper
