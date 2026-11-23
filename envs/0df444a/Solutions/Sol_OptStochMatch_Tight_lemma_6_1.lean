-- Prove2me | solution 1 for OptStochMatch.Tight.lemma_6_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:40:28.028632+00:00
-- url     : https://prove2.me/submissions/c1f57bcf-9992-4d7f-984d-d29de750e3f8

import Definitions.Def_OptStochMatch_Tight_Basic
import Definitions.Def_OptStochMatch_Tight_Matching
import Definitions.Def_OptStochMatch_Tight_Algorithms
import Theorems.Thm_OptStochMatch_Tight_lemma_2_3

namespace AuxLemma61

open scoped NNReal BigOperators
open OptStochMatch.Tight

lemma weighted_flow_sum {m : ℕ} (A : Finset (Fin m)) (u s : Fin m → ℝ)
    (F : Fin m → Ty m → ℝ)
    (hsum : ∀ i, ∑ S ∈ (Finset.univ.filter fun S : Ty m => i ∈ S), F i S = s i) :
    ∑ i ∈ A, u i * s i =
      ∑ S ∈ (Finset.univ.filter fun S : Ty m => (S ∩ A).Nonempty),
        ∑ i ∈ S ∩ A, u i * F i S := by
  have h1 : ∑ i ∈ A, u i * s i =
      ∑ i ∈ A, ∑ S ∈ (Finset.univ.filter fun S : Ty m => i ∈ S), u i * F i S := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hsum i, Finset.mul_sum]
  rw [h1]
  trans ∑ i ∈ A, ∑ S : Ty m, if i ∈ S then u i * F i S else 0
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  trans ∑ S : Ty m, if (S ∩ A).Nonempty then ∑ i ∈ S ∩ A, u i * F i S else 0
  · refine Finset.sum_congr rfl fun S _ => ?_
    by_cases hne : (S ∩ A).Nonempty
    · rw [if_pos hne]
      have hfilt : A.filter (fun i => i ∈ S) = S ∩ A := by
        ext i; simp [and_comm]
      rw [← Finset.sum_filter, hfilt]
    · rw [if_neg hne]
      refine Finset.sum_eq_zero fun i hiA => ?_
      have hiS : i ∉ S := fun hiS => hne ⟨i, Finset.mem_inter.mpr ⟨hiS, hiA⟩⟩
      simp [hiS]
  · rw [Finset.sum_filter]

lemma balanced_flow_saturates {m : ℕ} (lam : Ty m → ℝ≥0) (A : Finset (Fin m))
    (s : Fin m → ℝ) (hs : BalancedFeasible lam A s) (F : Fin m → Ty m → ℝ)
    (hF_nn : ∀ i S, 0 ≤ F i S)
    (hF_cap : ∀ S : Ty m, ∑ i ∈ S, F i S ≤ (lam S : ℝ))
    (hF_sum : ∀ i, ∑ S ∈ (Finset.univ.filter fun S : Ty m => i ∈ S), F i S = s i) :
    ∀ S ∈ (Finset.univ.filter fun S : Ty m => (S ∩ A).Nonempty),
      ∑ i ∈ S ∩ A, F i S = (lam S : ℝ) := by
  have hle : ∀ S ∈ (Finset.univ.filter fun S : Ty m => (S ∩ A).Nonempty),
      ∑ i ∈ S ∩ A, F i S ≤ (lam S : ℝ) := by
    intro S _
    exact (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
      (fun i _ _ => hF_nn i S)).trans (hF_cap S)
  have htot : ∑ S ∈ (Finset.univ.filter fun S : Ty m => (S ∩ A).Nonempty),
      ∑ i ∈ S ∩ A, F i S =
      ∑ S ∈ (Finset.univ.filter fun S : Ty m => (S ∩ A).Nonempty), (lam S : ℝ) := by
    have hw := weighted_flow_sum A (fun _ => 1) s F hF_sum
    simp only [one_mul] at hw
    rw [← hw, hs.2.2]
    rfl
  exact (Finset.sum_eq_sum_iff_of_le hle).mp htot

lemma balanced_flow_min_rate {m : ℕ} (lam : Ty m → ℝ≥0) (A : Finset (Fin m))
    (s : Fin m → ℝ) (hs : IsBalanced lam A s) (F : Fin m → Ty m → ℝ)
    (hF_nn : ∀ i S, 0 ≤ F i S)
    (hF_cap : ∀ S : Ty m, ∑ i ∈ S, F i S ≤ (lam S : ℝ))
    (hF_sum : ∀ i, ∑ S ∈ (Finset.univ.filter fun S : Ty m => i ∈ S), F i S = s i)
    (S : Ty m) {i j : Fin m} (hi : i ∈ S ∩ A) (hj : j ∈ S ∩ A) (hpos : 0 < F i S) :
    s i ≤ s j := by
  by_contra hlt
  have hlt' : s j < s i := lt_of_not_ge hlt
  have hij : i ≠ j := fun heq => (ne_of_lt hlt') (heq ▸ rfl)
  obtain ⟨hiS, hiA⟩ := Finset.mem_inter.mp hi
  obtain ⟨hjS, hjA⟩ := Finset.mem_inter.mp hj
  let ε : ℝ := min (F i S) ((s i - s j) / 2)
  have hε_pos : 0 < ε := lt_min hpos (by linarith)
  have hε_le_F : ε ≤ F i S := min_le_left _ _
  have hε_le_diff : ε ≤ (s i - s j) / 2 := min_le_right _ _
  let F' : Fin m → Ty m → ℝ := fun k T =>
    if T = S then (if k = i then F i S - ε else if k = j then F j S + ε else F k S) else F k T
  let s' : Fin m → ℝ := Function.update (Function.update s i (s i - ε)) j (s j + ε)
  have hs'_i : s' i = s i - ε := by simp [s', hij]
  have hs'_j : s' j = s j + ε := by simp [s']
  have hs'_other : ∀ k, k ≠ i → k ≠ j → s' k = s k := by
    intro k hki hkj; simp [s', hki, hkj]
  have hs'_nn : ∀ k, 0 ≤ s' k := by
    intro k
    by_cases hki : k = i
    · rw [hki, hs'_i]; linarith [hs.1.1.1 i, hs.1.1.1 j]
    · by_cases hkj : k = j
      · rw [hkj, hs'_j]; linarith [hs.1.1.1 j]
      · rw [hs'_other k hki hkj]; exact hs.1.1.1 k
  have hF'_nn : ∀ k T, 0 ≤ F' k T := by
    intro k T
    dsimp [F']
    split_ifs <;> linarith [hF_nn k T, hF_nn k S, hF_nn j S]
  have hF'_cap : ∀ T : Ty m, ∑ k ∈ T, F' k T ≤ (lam T : ℝ) := by
    intro T
    by_cases hTS : T = S
    · subst T
      have hpair : ({i, j} : Finset (Fin m)) ⊆ S := by
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk'
        · exact hiS
        · rw [Finset.mem_singleton.mp hk']; exact hjS
      have hsum_eq : ∑ k ∈ S, F' k S = ∑ k ∈ S, F k S := by
        rw [← Finset.sum_sdiff hpair, ← Finset.sum_sdiff hpair]
        have hp1 : ∑ k ∈ ({i, j} : Finset (Fin m)), F' k S = (F i S - ε) + (F j S + ε) := by
          rw [Finset.sum_pair hij]
          simp [F', hij.symm]
        have hp2 : ∑ k ∈ ({i, j} : Finset (Fin m)), F k S = F i S + F j S :=
          Finset.sum_pair hij
        have hrest : ∑ k ∈ S \ {i, j}, F' k S = ∑ k ∈ S \ {i, j}, F k S := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk' := (Finset.mem_sdiff.mp hk).2
          have hki : k ≠ i := fun h => hk' (by simp [h])
          have hkj : k ≠ j := fun h => hk' (by simp [h])
          simp [F', hki, hkj]
        linarith
      rw [hsum_eq]
      exact hF_cap S
    · have hsum_eq : ∑ k ∈ T, F' k T = ∑ k ∈ T, F k T :=
        Finset.sum_congr rfl fun k _ => by simp [F', hTS]
      rw [hsum_eq]
      exact hF_cap T
  have hF'_sum : ∀ k, ∑ T ∈ (Finset.univ.filter fun T : Ty m => k ∈ T), F' k T = s' k := by
    intro k
    by_cases hki : k = i
    · rw [hki]
      have hmem : S ∈ (Finset.univ.filter fun T : Ty m => i ∈ T) := by simp [hiS]
      rw [← Finset.add_sum_erase _ _ hmem]
      have herase : ∑ T ∈ (Finset.univ.filter fun T : Ty m => i ∈ T).erase S, F' i T =
          ∑ T ∈ (Finset.univ.filter fun T : Ty m => i ∈ T).erase S, F i T :=
        Finset.sum_congr rfl fun T hT => by simp [F', (Finset.mem_erase.mp hT).1]
      have horig := Finset.add_sum_erase (Finset.univ.filter fun T : Ty m => i ∈ T) (fun T => F i T) hmem
      rw [hF_sum i] at horig
      have hFiS : F' i S = F i S - ε := by simp [F']
      rw [hs'_i, hFiS, herase]
      linarith
    · by_cases hkj : k = j
      · rw [hkj]
        have hmem : S ∈ (Finset.univ.filter fun T : Ty m => j ∈ T) := by simp [hjS]
        rw [← Finset.add_sum_erase _ _ hmem]
        have herase : ∑ T ∈ (Finset.univ.filter fun T : Ty m => j ∈ T).erase S, F' j T =
            ∑ T ∈ (Finset.univ.filter fun T : Ty m => j ∈ T).erase S, F j T :=
          Finset.sum_congr rfl fun T hT => by simp [F', (Finset.mem_erase.mp hT).1]
        have horig := Finset.add_sum_erase (Finset.univ.filter fun T : Ty m => j ∈ T) (fun T => F j T) hmem
        rw [hF_sum j] at horig
        have hFjS : F' j S = F j S + ε := by simp [F', hij.symm]
        rw [hs'_j, hFjS, herase]
        linarith
      · rw [hs'_other k hki hkj, ← hF_sum k]
        refine Finset.sum_congr rfl fun T _ => ?_
        by_cases hTS : T = S
        · subst hTS; simp [F', hki, hkj]
        · simp [F', hTS]
  have hs'_plam : s' ∈ Plam lam :=
    (lemma_2_3 lam s' hs'_nn).mpr ⟨F', hF'_nn, hF'_cap, hF'_sum⟩
  have hpairA : ({i, j} : Finset (Fin m)) ⊆ A := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk'
    · exact hiA
    · rw [Finset.mem_singleton.mp hk']; exact hjA
  have hs'_feas : BalancedFeasible lam A s' := by
    refine ⟨hs'_plam, ?_, ?_⟩
    · intro k hkA
      have hki : k ≠ i := fun h => hkA (h ▸ hiA)
      have hkj : k ≠ j := fun h => hkA (h ▸ hjA)
      rw [hs'_other k hki hkj]
      exact hs.1.2.1 k hkA
    · rw [← hs.1.2.2, ← Finset.sum_sdiff hpairA, ← Finset.sum_sdiff hpairA]
      have hp1 : ∑ k ∈ ({i, j} : Finset (Fin m)), s' k = (s i - ε) + (s j + ε) := by
        rw [Finset.sum_pair hij, hs'_i, hs'_j]
      have hp2 : ∑ k ∈ ({i, j} : Finset (Fin m)), s k = s i + s j := Finset.sum_pair hij
      have hrest : ∑ k ∈ A \ {i, j}, s' k = ∑ k ∈ A \ {i, j}, s k := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' := (Finset.mem_sdiff.mp hk).2
        exact hs'_other k (fun h => hk' (by simp [h])) (fun h => hk' (by simp [h]))
      linarith
  have hmin_sq := hs.2 s' hs'_feas
  have hsq_diff : ∑ k ∈ A, s' k ^ 2 - ∑ k ∈ A, s k ^ 2 = 2 * ε * (s j - s i + ε) := by
    rw [← Finset.sum_sdiff hpairA (f := fun k => s' k ^ 2),
      ← Finset.sum_sdiff hpairA (f := fun k => s k ^ 2)]
    have hp1 : ∑ k ∈ ({i, j} : Finset (Fin m)), s' k ^ 2 = (s i - ε) ^ 2 + (s j + ε) ^ 2 := by
      rw [Finset.sum_pair hij, hs'_i, hs'_j]
    have hp2 : ∑ k ∈ ({i, j} : Finset (Fin m)), s k ^ 2 = s i ^ 2 + s j ^ 2 := Finset.sum_pair hij
    have hrest : ∑ k ∈ A \ {i, j}, s' k ^ 2 = ∑ k ∈ A \ {i, j}, s k ^ 2 := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := (Finset.mem_sdiff.mp hk).2
      rw [hs'_other k (fun h => hk' (by simp [h])) (fun h => hk' (by simp [h]))]
    linarith [show (s i - ε) ^ 2 + (s j + ε) ^ 2 - (s i ^ 2 + s j ^ 2) = 2 * ε * (s j - s i + ε) by ring]
  have hneg : 2 * ε * (s j - s i + ε) < 0 := by
    nlinarith
  linarith

end AuxLemma61

open scoped NNReal BigOperators
open OptStochMatch.Tight AuxLemma61

theorem solution {m : ℕ} (lam : Ty m → ℝ≥0) (A : Finset (Fin m)) (s : Fin m → ℝ)
    (hs : IsBalanced lam A s) (x : Fin m → ℝ) (hx : ∀ i, 0 ≤ x i) (c : ℝ) (hc : 0 ≤ c)
    (y : Fin m → ℝ) (hy : y ∈ Plam lam) (hyA : ∀ i, i ∉ A → y i = 0)
    (hyx : ∀ i, y i ≤ x i + c) (w : ℝ → ℝ) (hw_anti : AntitoneOn w (Set.Ici 0))
    (hw_range : ∀ z, 0 ≤ z → 0 ≤ w z ∧ w z ≤ 1) (hw0 : w 0 = 1) :
    ∑ i ∈ A, y i ≤ ∑ i ∈ A, (w (x i) * s i + (1 - w (x i)) * (x i + c)) := by
  have _ := hc
  have _ := hyA
  obtain ⟨Fs, hFs_nn, hFs_cap, hFs_sum⟩ := (lemma_2_3 lam s hs.1.1.1).mp hs.1.1
  obtain ⟨Fy, hFy_nn, hFy_cap, hFy_sum⟩ := (lemma_2_3 lam y hy.1).mp hy
  let a : Fin m → ℝ := fun i => w (max (s i - c) 0)
  have ha_range : ∀ i, 0 ≤ a i ∧ a i ≤ 1 := fun i => hw_range _ (le_max_right _ _)
  have ha_anti : ∀ i j, s i ≤ s j → a j ≤ a i := by
    intro i j hij
    exact hw_anti (Set.mem_Ici.mpr (le_max_right _ _)) (Set.mem_Ici.mpr (le_max_right _ _))
      (max_le_max_right 0 (sub_le_sub_right hij c))
  have hsat := balanced_flow_saturates lam A s hs.1 Fs hFs_nn hFs_cap hFs_sum
  have hw_cmp : ∑ i ∈ A, a i * y i ≤ ∑ i ∈ A, a i * s i := by
    rw [weighted_flow_sum A a y Fy hFy_sum, weighted_flow_sum A a s Fs hFs_sum]
    refine Finset.sum_le_sum fun S hS => ?_
    have hne : (S ∩ A).Nonempty := (Finset.mem_filter.mp hS).2
    let M : ℝ := (S ∩ A).sup' hne a
    have hM_nn : 0 ≤ M := by
      obtain ⟨j₀, hj₀⟩ := hne
      exact (ha_range j₀).1.trans (Finset.le_sup' a hj₀)
    have h1 : ∑ i ∈ S ∩ A, a i * Fy i S ≤ M * (lam S : ℝ) := by
      calc
        ∑ i ∈ S ∩ A, a i * Fy i S ≤ ∑ i ∈ S ∩ A, M * Fy i S :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (Finset.le_sup' a hi) (hFy_nn i S)
        _ = M * ∑ i ∈ S ∩ A, Fy i S := by rw [← Finset.mul_sum]
        _ ≤ M * (lam S : ℝ) := mul_le_mul_of_nonneg_left
          ((Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
            (fun i _ _ => hFy_nn i S)).trans (hFy_cap S)) hM_nn
    have h2 : ∑ i ∈ S ∩ A, a i * Fs i S = M * (lam S : ℝ) := by
      rw [← hsat S hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rcases eq_or_lt_of_le (hFs_nn i S) with hzero | hpos
      · simp [← hzero]
      · have hmax : M = a i := by
          apply le_antisymm
          · exact Finset.sup'_le hne a fun j hj =>
              ha_anti i j (balanced_flow_min_rate lam A s hs Fs hFs_nn hFs_cap hFs_sum S hi hj hpos)
          · exact Finset.le_sup' a hi
        rw [hmax]
    linarith
  have hpt : ∀ i ∈ A, a i * s i + (1 - a i) * (x i + c) ≤
      w (x i) * s i + (1 - w (x i)) * (x i + c) := by
    intro i _
    suffices hprod : 0 ≤ (w (x i) - a i) * (s i - x i - c) by linarith
    by_cases hsc : c ≤ s i
    · have ha_eq : a i = w (s i - c) := by
        dsimp [a]
        rw [max_eq_left (by linarith)]
      rw [ha_eq]
      by_cases hxs : x i ≤ s i - c
      · have hw_ge : w (s i - c) ≤ w (x i) :=
          hw_anti (Set.mem_Ici.mpr (hx i)) (Set.mem_Ici.mpr (by linarith)) hxs
        exact mul_nonneg (by linarith) (by linarith)
      · have hxs' : s i - c < x i := lt_of_not_ge hxs
        have hw_le : w (x i) ≤ w (s i - c) :=
          hw_anti (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (hx i)) (le_of_lt hxs')
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · have hsc' : s i < c := lt_of_not_ge hsc
      have ha_eq : a i = 1 := by
        dsimp [a]
        rw [max_eq_right (by linarith), hw0]
      rw [ha_eq]
      have hw_le1 : w (x i) ≤ 1 := (hw_range (x i) (hx i)).2
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [hx i])
  calc
    ∑ i ∈ A, y i = ∑ i ∈ A, (a i * y i + (1 - a i) * y i) :=
      Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ i ∈ A, (a i * y i + (1 - a i) * (x i + c)) :=
      Finset.sum_le_sum fun i _ => add_le_add_right
        (mul_le_mul_of_nonneg_left (hyx i) (by linarith [(ha_range i).2])) _
    _ = (∑ i ∈ A, a i * y i) + ∑ i ∈ A, (1 - a i) * (x i + c) := Finset.sum_add_distrib
    _ ≤ (∑ i ∈ A, a i * s i) + ∑ i ∈ A, (1 - a i) * (x i + c) := add_le_add_left hw_cmp _
    _ = ∑ i ∈ A, (a i * s i + (1 - a i) * (x i + c)) := Finset.sum_add_distrib.symm
    _ ≤ ∑ i ∈ A, (w (x i) * s i + (1 - w (x i)) * (x i + c)) := Finset.sum_le_sum hpt
