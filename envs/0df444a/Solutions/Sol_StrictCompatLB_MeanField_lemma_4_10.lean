-- Prove2me | solution 1 for StrictCompatLB.MeanField.lemma_4_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T15:06:30.178987+00:00
-- url     : https://prove2.me/submissions/34e54004-2276-4ba6-8f75-6572e21babeb

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

open Filter Topology MeasureTheory Finset
open scoped ENNReal

namespace StrictCompatLB.MeanField.L410

open StrictCompatLB.MeanField

abbrev L1 := lp (fun _ : ℕ => ℝ) 1

lemma norm_L1 (f : L1) : ‖f‖ = ∑' i, |f i| := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp

lemma summable_L1 (f : L1) : Summable (fun i => |f i|) := by
  have := (memℓp_gen_iff (p := 1) (by norm_num)).mp f.2
  simpa using this

lemma mk_L1 (a : ℕ → ℝ) (ha : Summable (fun i => |a i|)) : Memℓp a 1 :=
  (memℓp_gen_iff (by norm_num)).mpr (by simpa using ha)

/-- The compact sets used for tightness in `ℓ₁`: coordinatewise bounds and uniformly small
tails. -/
def boxK (B : ℕ → ℝ) (J : ℕ → ℕ) : Set L1 :=
  {f | (∀ i, |f i| ≤ B i) ∧ ∀ m : ℕ, ∑' i, (if J m ≤ i then |f i| else 0) ≤ 1 / ((m : ℝ) + 1)}

lemma ite_summable (g : ℕ → ℝ) (hg : Summable g) (hg0 : ∀ i, 0 ≤ g i) (J : ℕ) :
    Summable (fun i => if J ≤ i then g i else 0) :=
  Summable.of_nonneg_of_le (fun i => by split_ifs; exact hg0 i; exact le_refl _)
    (fun i => by split_ifs; exact le_refl _; exact hg0 i) hg

lemma isCompact_boxK (B : ℕ → ℝ) (J : ℕ → ℕ) : IsCompact (boxK B J) := by
  apply IsSeqCompact.isCompact
  intro y hy
  have hcpt : IsCompact (Set.pi Set.univ (fun i : ℕ => Set.Icc (-B i) (B i))) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨a, ha, φ, hφ, hlim⟩ := hcpt.tendsto_subseq (x := fun n => ⇑(y n)) (fun n => by
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
    intro i; exact abs_le.mp ((hy n).1 i))
  have hpt : ∀ i, Tendsto (fun n => y (φ n) i) atTop (𝓝 (a i)) := by
    intro i; exact (tendsto_pi_nhds.mp hlim) i
  have habs : ∀ i, |a i| ≤ B i := by
    intro i
    exact le_of_tendsto' ((hpt i).abs) (fun n => (hy (φ n)).1 i)
  have htail : ∀ m (F : Finset ℕ), ∑ i ∈ F, (if J m ≤ i then |a i| else 0) ≤ 1 / ((m : ℝ) + 1) := by
    intro m F
    have hT : Tendsto (fun n => ∑ i ∈ F, (if J m ≤ i then |y (φ n) i| else 0)) atTop
        (𝓝 (∑ i ∈ F, (if J m ≤ i then |a i| else 0))) := by
      apply tendsto_finsetSum F
      intro i _
      split_ifs
      · exact (hpt i).abs
      · exact tendsto_const_nhds
    apply le_of_tendsto' hT
    intro n
    calc _ ≤ ∑' i, (if J m ≤ i then |y (φ n) i| else 0) :=
          (ite_summable _ (summable_L1 _) (fun _ => abs_nonneg _) _).sum_le_tsum F
            (fun i _ => by split_ifs; exact abs_nonneg _; exact le_refl _)
      _ ≤ _ := (hy (φ n)).2 m
  have hasum : Summable (fun i => |a i|) := by
    apply summable_of_sum_le (c := ∑ i ∈ range (J 0), B i + 1) (fun i => abs_nonneg _)
    intro F
    have h1 : ∀ i, |a i| ≤ (if J 0 ≤ i then |a i| else 0) + (if i ∈ range (J 0) then B i else 0) := by
      intro i
      by_cases h : J 0 ≤ i
      · rw [if_pos h, if_neg (by simp; omega)]; simp
      · rw [if_neg h, if_pos (by simp; omega)]; simpa using habs i
    calc ∑ i ∈ F, |a i| ≤ ∑ i ∈ F, ((if J 0 ≤ i then |a i| else 0) +
          (if i ∈ range (J 0) then B i else 0)) := Finset.sum_le_sum (fun i _ => h1 i)
      _ = ∑ i ∈ F, (if J 0 ≤ i then |a i| else 0) + ∑ i ∈ F ∩ range (J 0), B i := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_mem]
      _ ≤ 1 + ∑ i ∈ range (J 0), B i := by
          have := htail 0 F
          simp only [Nat.cast_zero, zero_add, div_one] at this
          have : ∑ i ∈ F ∩ range (J 0), B i ≤ ∑ i ∈ range (J 0), B i :=
            Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
              (fun i _ _ => le_trans (abs_nonneg _) (habs i))
          linarith
      _ = _ := by ring
  set aL : L1 := ⟨a, mk_L1 a hasum⟩ with haL
  have haLc : ∀ i, aL i = a i := fun i => rfl
  refine ⟨aL, ⟨fun i => by rw [haLc]; exact habs i, fun m => ?_⟩, φ, hφ, ?_⟩
  · simp only [haLc]
    exact (ite_summable _ hasum (fun _ => abs_nonneg _) _).tsum_le_of_sum_le (htail m)
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < ε / 4 by linarith)
    have hfin : Tendsto (fun n => ∑ i ∈ range (J m), |y (φ n) i - a i|) atTop
        (𝓝 (∑ i ∈ range (J m), |a i - a i|)) :=
      tendsto_finsetSum _ (fun i _ => ((hpt i).sub tendsto_const_nhds).abs)
    simp only [sub_self, abs_zero, Finset.sum_const_zero] at hfin
    obtain ⟨n₀, hn₀⟩ := (Metric.tendsto_atTop.mp hfin) (ε / 2) (by linarith)
    refine ⟨n₀, fun n hn => ?_⟩
    have h1 := hn₀ n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))] at h1
    rw [dist_eq_norm, norm_L1]
    have hsy := summable_L1 (y (φ n))
    have hterm : ∀ i, |(y (φ n) - aL) i| ≤ (if i ∈ range (J m) then |y (φ n) i - a i| else 0) +
        ((if J m ≤ i then |y (φ n) i| else 0) + (if J m ≤ i then |a i| else 0)) := by
      intro i
      rw [lp.coeFn_sub, Pi.sub_apply, haLc]
      by_cases h : J m ≤ i
      · rw [if_neg (by simp; omega), if_pos h, if_pos h, zero_add]
        exact abs_sub _ _
      · rw [if_pos (by simp; omega), if_neg h, if_neg h]; simp
    have hs1 : Summable (fun i => if i ∈ range (J m) then |y (φ n) i - a i| else 0) :=
      summable_of_ne_finset_zero (s := range (J m)) (fun i hi => by rw [if_neg hi])
    have hs2 := ite_summable _ hsy (fun _ => abs_nonneg _) (J m)
    have hs3 := ite_summable _ hasum (fun _ => abs_nonneg _) (J m)
    have hsub : Summable (fun i => |(y (φ n) - aL) i|) := summable_L1 _
    calc ∑' i, |(y (φ n) - aL) i| ≤ ∑' i, ((if i ∈ range (J m) then |y (φ n) i - a i| else 0) +
          ((if J m ≤ i then |y (φ n) i| else 0) + (if J m ≤ i then |a i| else 0))) :=
          Summable.tsum_le_tsum hterm hsub (hs1.add (hs2.add hs3))
      _ = ∑ i ∈ range (J m), |y (φ n) i - a i| + (∑' i, (if J m ≤ i then |y (φ n) i| else 0) +
            ∑' i, (if J m ≤ i then |a i| else 0)) := by
          rw [Summable.tsum_add hs1 (hs2.add hs3), Summable.tsum_add hs2 hs3]
          congr 1
          rw [tsum_eq_sum (s := range (J m)) (fun i hi => by rw [if_neg hi])]
          exact Finset.sum_congr rfl (fun i hi => by rw [if_pos hi])
      _ < ε / 2 + (ε / 4 + ε / 4) := by
          have a1 := (hy (φ n)).2 m
          have a2 : ∑' i, (if J m ≤ i then |a i| else 0) ≤ 1 / ((m : ℝ) + 1) :=
            hs3.tsum_le_of_sum_le (htail m)
          linarith
      _ = ε := by ring

/-! Probability facts for laws given by probability vectors. -/

section prob
variable {S : Type*}

lemma probOf_mono (π : S → ℝ) (hπ : IsProbVec π) {A B : Set S} (h : A ⊆ B) :
    probOf π A ≤ probOf π B := by
  unfold probOf
  apply Summable.tsum_le_tsum
  · intro z; exact Set.indicator_le_indicator_of_subset h hπ.1 z
  · exact Summable.of_nonneg_of_le (fun z => Set.indicator_nonneg (fun z _ => hπ.1 z) z)
      (fun z => Set.indicator_le_self' (fun z _ => hπ.1 z) z) hπ.2.summable
  · exact Summable.of_nonneg_of_le (fun z => Set.indicator_nonneg (fun z _ => hπ.1 z) z)
      (fun z => Set.indicator_le_self' (fun z _ => hπ.1 z) z) hπ.2.summable

lemma indicator_summable (π : S → ℝ) (hπ : IsProbVec π) (A : Set S) :
    Summable (fun z => A.indicator π z) :=
  Summable.of_nonneg_of_le (fun z => Set.indicator_nonneg (fun z _ => hπ.1 z) z)
    (fun z => Set.indicator_le_self' (fun z _ => hπ.1 z) z) hπ.2.summable

lemma probOf_compl_small (π : S → ℝ) (hπ : IsProbVec π) (δ : ℝ) (hδ : 0 < δ) :
    ∃ F : Finset S, probOf π {z | z ∉ F} ≤ δ := by
  classical
  have ht : Filter.Tendsto (fun s : Finset S => ∑ b ∈ s, π b) Filter.atTop (nhds 1) := hπ.2
  obtain ⟨F, hF⟩ := (ht.eventually (lt_mem_nhds (show 1 - δ < 1 by linarith))).exists
  refine ⟨F, ?_⟩
  have hsplit : ∀ z, {z | z ∉ F}.indicator π z = π z - (if z ∈ F then π z else 0) := by
    intro z; by_cases hz : z ∈ F <;> simp [Set.indicator, hz]
  unfold probOf
  simp_rw [hsplit]
  have hs : Summable (fun z => if z ∈ F then π z else 0) :=
    summable_of_ne_finset_zero (s := F) (fun z hz => by rw [if_neg hz])
  rw [Summable.tsum_sub hπ.2.summable hs, hπ.2.tsum_eq,
    tsum_eq_sum (s := F) (fun z hz => by rw [if_neg hz])]
  rw [Finset.sum_ite_mem, Finset.inter_self]
  linarith

/-- Countable subadditivity of `probOf`. -/
lemma probOf_iUnion_le (π : S → ℝ) (hπ : IsProbVec π) (E : ℕ → Set S) (c : ℕ → ℝ)
    (hE : ∀ m, probOf π (E m) ≤ c m) (hc : Summable c) :
    probOf π (⋃ m, E m) ≤ ∑' m, c m := by
  classical
  unfold probOf
  apply (indicator_summable π hπ _).tsum_le_of_sum_le
  intro F
  -- choose for each `z ∈ F` in the union an index
  have hidx : ∀ z ∈ F, ∃ M : ℕ, ((⋃ m, E m).indicator π z ≤ ∑ m ∈ range M, (E m).indicator π z) := by
    intro z _
    by_cases hz : z ∈ ⋃ m, E m
    · obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hz
      refine ⟨m + 1, ?_⟩
      rw [Set.indicator_of_mem hz]
      calc π z = (E m).indicator π z := by rw [Set.indicator_of_mem hm]
        _ ≤ _ := Finset.single_le_sum (f := fun m => (E m).indicator π z)
            (fun i _ => Set.indicator_nonneg (fun z _ => hπ.1 z) z) (by simp)
    · exact ⟨0, by rw [Set.indicator_of_notMem hz]; simp⟩
  choose Mf hMf using hidx
  set M := F.attach.sup (fun z => Mf z.1 z.2)
  have hc0 : ∀ m, 0 ≤ c m := fun m => le_trans (tsum_nonneg (fun z =>
    Set.indicator_nonneg (fun z _ => hπ.1 z) z)) (hE m)
  calc ∑ z ∈ F, (⋃ m, E m).indicator π z ≤ ∑ z ∈ F, ∑ m ∈ range M, (E m).indicator π z := by
        apply Finset.sum_le_sum
        intro z hz
        calc _ ≤ ∑ m ∈ range (Mf z hz), (E m).indicator π z := hMf z hz
          _ ≤ _ := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro m hm
                simp only [mem_range] at hm ⊢
                have : Mf z hz ≤ M := Finset.le_sup (f := fun z : F => Mf z.1 z.2) (mem_attach F ⟨z, hz⟩)
                omega
              · intro i _ _; exact Set.indicator_nonneg (fun z _ => hπ.1 z) z
    _ = ∑ m ∈ range M, ∑ z ∈ F, (E m).indicator π z := Finset.sum_comm
    _ ≤ ∑ m ∈ range M, c m := by
        apply Finset.sum_le_sum
        intro m _
        calc _ ≤ ∑' z, (E m).indicator π z :=
              (indicator_summable π hπ _).sum_le_tsum F
                (fun z _ => Set.indicator_nonneg (fun z _ => hπ.1 z) z)
          _ ≤ c m := hE m
    _ ≤ ∑' m, c m := hc.sum_le_tsum _ (fun m _ => hc0 m)

end prob

lemma weightedTail_anti (ω : ℕ → ℝ) (hω : ∀ i, 1 ≤ i → 0 < ω i) {N : ℕ} (z : Fin N → ℕ)
    {j j' : ℕ} (hj : 1 ≤ j) (hjj : j ≤ j') : weightedTail ω j' z ≤ weightedTail ω j z := by
  unfold weightedTail
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi; simp only [mem_Ico] at hi ⊢; omega
  · intro i hi _
    simp only [mem_Ico] at hi
    exact mul_nonneg (hω i (by omega)).le (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

lemma weightedTail_zero (ω : ℕ → ℝ) {N : ℕ} (z : Fin N → ℕ) {j : ℕ} (hj : maxLen z < j) :
    weightedTail ω j z = 0 := by
  unfold weightedTail
  rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]

lemma occ_nonneg {N : ℕ} (z : Fin N → ℕ) (i : ℕ) : 0 ≤ occ z i :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma occ_le_one {N : ℕ} (z : Fin N → ℕ) (i : ℕ) : occ z i ≤ 1 := by
  unfold occ
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · rw [div_le_one (by exact_mod_cast h)]
    have : Qcount z i ≤ N := by
      unfold Qcount
      calc _ ≤ (univ : Finset (Fin N)).card := Finset.card_filter_le _ _
        _ = N := by simp
    exact_mod_cast this

lemma occ_zero_of {N : ℕ} (z : Fin N → ℕ) (i : ℕ) (hi : maxLen z < i) : occ z i = 0 := by
  have : Qcount z i = 0 := by
    unfold Qcount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro u _ hu
    have : z u ≤ maxLen z := Finset.le_sup (f := z) (mem_univ u)
    omega
  simp [occ, this]

/-- The uniform-in-`N` choice of a tail index. -/
lemma uniform_index (ω : ℕ → ℝ) (hω : ∀ i, 1 ≤ i → 0 < ω i) (N₀ : ℕ)
    (π : (N : ℕ) → (Fin N → ℕ) → ℝ) (hπ : ∀ N ≥ N₀, IsProbVec (π N))
    (h419 : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∃ N₁ : ℕ, ∀ N ≥ max N₀ N₁,
      probOf (π N) {z | ε < weightedTail ω j z} ≤ η)
    (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ N ≥ N₀, probOf (π N) {z | ε < weightedTail ω J z} ≤ η := by
  obtain ⟨j₀, hj₀⟩ := h419 ε hε η hη
  set j₁ := max j₀ 1
  obtain ⟨N₁, hN₁⟩ := hj₀ j₁ (le_max_left _ _)
  have hsmall : ∀ N, ∃ jN : ℕ, N₀ ≤ N → ∀ j ≥ jN,
      probOf (π N) {z | ε < weightedTail ω j z} ≤ η := by
    intro N
    by_cases hN : N₀ ≤ N
    · obtain ⟨F, hF⟩ := probOf_compl_small (π N) (hπ N hN) η hη
      refine ⟨F.sup (fun z => maxLen z + 1), fun _ j hj => ?_⟩
      refine le_trans (probOf_mono (π N) (hπ N hN) ?_) hF
      intro z hz
      simp only [Set.mem_setOf_eq] at hz ⊢
      intro hzF
      have : maxLen z + 1 ≤ F.sup (fun z => maxLen z + 1) :=
        Finset.le_sup (f := fun z => maxLen z + 1) hzF
      rw [weightedTail_zero ω z (by omega)] at hz
      linarith
    · exact ⟨0, fun h => absurd h hN⟩
  choose jf hjf using hsmall
  refine ⟨max j₁ ((range N₁).sup jf), le_trans (le_max_right _ _) (le_max_left _ _), ?_⟩
  intro N hN
  by_cases hNN : N₁ ≤ N
  · refine le_trans (probOf_mono (π N) (hπ N hN) ?_) (hN₁ N (max_le hN hNN))
    intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    exact lt_of_lt_of_le hz (weightedTail_anti ω hω z (le_max_right _ _) (le_max_left _ _))
  · apply hjf N hN
    have : jf N ≤ (range N₁).sup jf := Finset.le_sup (f := jf) (by simp; omega)
    exact le_trans this (le_max_right _ _)

end StrictCompatLB.MeanField.L410

open StrictCompatLB.MeanField StrictCompatLB.MeanField.L410 in
theorem solution (ω : ℕ → ℝ) (hω : ∀ i, 1 ≤ i → 0 < ω i) (N₀ : ℕ)
    (π : (N : ℕ) → (Fin N → ℕ) → ℝ) (hπ : ∀ N ≥ N₀, IsProbVec (π N))
    (htight : ∀ i : ℕ, 1 ≤ i → ∀ η : ℝ, 0 < η → ∃ R : ℝ, ∀ N ≥ N₀,
      probOf (π N) {z | R < |occ z i|} ≤ η)
    (h419 : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∃ N₁ : ℕ, ∀ N ≥ max N₀ N₁,
      probOf (π N) {z | ε < weightedTail ω j z} ≤ η) :
    IsTightWeighted ω N₀ π := by
  intro η hη
  have hJ : ∀ m : ℕ, ∃ J : ℕ, 1 ≤ J ∧ ∀ N ≥ N₀,
      probOf (π N) {z | 1 / ((m : ℝ) + 1) < weightedTail ω J z} ≤ η / 2 ^ (m + 1) :=
    fun m => uniform_index ω hω N₀ π hπ h419 _ (by positivity) _ (by positivity)
  choose J hJ1 hJb using hJ
  refine ⟨boxK (fun i => ω (i + 1)) (fun m => J m - 1), isCompact_boxK _ _, ?_⟩
  intro N hN
  set E : ℕ → Set (Fin N → ℕ) := fun m => {z | 1 / ((m : ℝ) + 1) < weightedTail ω (J m) z}
  have hsub : {z : Fin N → ℕ | ¬ ∃ y ∈ boxK (fun i => ω (i + 1)) (fun m => J m - 1),
      ∀ i : ℕ, (y : ℕ → ℝ) i = ω (i + 1) * occ z (i + 1)} ⊆ ⋃ m, E m := by
    intro z hz
    by_contra hcon
    apply hz
    have hgood : ∀ m, weightedTail ω (J m) z ≤ 1 / ((m : ℝ) + 1) := by
      intro m
      by_contra h
      exact hcon (Set.mem_iUnion.mpr ⟨m, by simp only [E, Set.mem_setOf_eq]; push Not at h; exact h⟩)
    set a : ℕ → ℝ := fun i => ω (i + 1) * occ z (i + 1) with ha
    have hsupp : ∀ i ∉ range (maxLen z), a i = 0 := by
      intro i hi
      simp only [mem_range, not_lt] at hi
      simp only [ha, occ_zero_of z (i + 1) (by omega), mul_zero]
    have hasum : Summable (fun i => |a i|) :=
      summable_of_ne_finset_zero (s := range (maxLen z)) (fun i hi => by rw [hsupp i hi, abs_zero])
    refine ⟨⟨a, mk_L1 a hasum⟩, ⟨fun i => ?_, fun m => ?_⟩, fun i => rfl⟩
    · show |a i| ≤ ω (i + 1)
      rw [abs_of_nonneg (mul_nonneg (hω _ (by omega)).le (occ_nonneg _ _))]
      calc a i ≤ ω (i + 1) * 1 :=
            mul_le_mul_of_nonneg_left (occ_le_one _ _) (hω _ (by omega)).le
        _ = _ := mul_one _
    · show ∑' i, (if J m - 1 ≤ i then |a i| else 0) ≤ 1 / ((m : ℝ) + 1)
      have e : ∑' i, (if J m - 1 ≤ i then |a i| else 0) = weightedTail ω (J m) z := by
        rw [tsum_eq_sum (s := Ico (J m - 1) (maxLen z)) (fun i hi => by
          simp only [mem_Ico, not_and_or, not_le, not_lt] at hi
          rcases hi with h | h
          · rw [if_neg (by omega)]
          · split_ifs
            · rw [hsupp i (by simp; omega), abs_zero]
            · rfl)]
        unfold weightedTail
        have h1 := Finset.sum_Ico_add' (fun i => ω i * occ z i) (J m - 1) (maxLen z) 1
        have hJ1' : J m - 1 + 1 = J m := by have := hJ1 m; omega
        rw [hJ1'] at h1
        rw [← h1]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [mem_Ico] at hi
        rw [if_pos hi.1, abs_of_nonneg (mul_nonneg (hω _ (by omega)).le (occ_nonneg _ _))]
      rw [e]; exact hgood m
  calc _ ≤ probOf (π N) (⋃ m, E m) := probOf_mono (π N) (hπ N hN) hsub
    _ ≤ ∑' m : ℕ, η / 2 ^ (m + 1) := probOf_iUnion_le (π N) (hπ N hN) E _ (fun m => hJb m N hN)
        (by
          refine (summable_geometric_two' η).congr (fun m => ?_)
          rw [pow_succ', div_div])
    _ = ∑' m : ℕ, η / 2 / 2 ^ m := by
        congr 1; funext m; rw [pow_succ', div_div]
    _ = η := tsum_geometric_two' η
