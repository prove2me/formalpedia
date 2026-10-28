-- Prove2me | solution 2 for RetailVariety.Structure.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T10:24:17.249899+00:00
-- url     : https://prove2.me/submissions/6f22df94-6675-45bb-b574-4350de6e8434

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Theorems.Thm_RetailVariety_Structure_h_endpoints
import Theorems.Thm_RetailVariety_Structure_lemma_1

-- carved verbatim out of submission 98c36c84-53e9-49c4-baa4-19f5aec60b15, lines 366-396

section
open RetailVariety.Structure

private lemma den_pos {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ j, 0 < v j)
    (hv0 : 0 < v0) (S : Finset (Fin n)) : 0 < ∑ j ∈ S, v j + v0 := by
  exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun j _ => (hv j).le) hv0

end

section
open RetailVariety.Structure
set_option autoImplicit false

private def rank {n : ℕ} (S : Finset (Fin n)) : ℕ := ∑ j ∈ S, (j.val+1)

private lemma rank_erase {n : ℕ} (S : Finset (Fin n)) (k : Fin n) (hk : k ∈ S) :
    rank (S.erase k) < rank S := by
  have he := Finset.sum_erase_add S (fun j : Fin n => j.val+1) hk
  unfold rank
  omega

private lemma prefix_dom {n : ℕ} (F : Finset (Fin n) → ℝ)
    (hgap : ∀ S (j k : Fin n), j < k → j ∉ S → k ∈ S →
      F S ≤ max (F (S.erase k)) (F (insert j (S.erase k)))) (S : Finset (Fin n)) :
    ∃ i : ℕ, i ≤ n ∧ F S ≤ F (popularSet n i) := by
  classical
  suffices hh : ∀ r S, rank S = r → ∃ i, i ≤ n ∧ F S ≤ F (popularSet n i) from hh _ S rfl
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro S hr
    by_cases hg : ∃ j k : Fin n, j < k ∧ j ∉ S ∧ k ∈ S
    · obtain ⟨j,k,hjk,hj,hk⟩ := hg
      have hT := rank_erase S k hk
      have hjT : j ∉ S.erase k := fun h => hj (Finset.mem_of_mem_erase h)
      have hU : rank (insert j (S.erase k)) < rank S := by
        unfold rank
        rw [Finset.sum_insert hjT]
        have he := Finset.sum_erase_add S (fun j : Fin n => j.val+1) hk
        have hjk' : j.val < k.val := hjk
        omega
      have hh := hgap S j k hjk hj hk
      rcases le_max_iff.mp hh with hh | hh
      · obtain ⟨i,hi,hf⟩ := ih _ (by omega) (S.erase k) rfl
        exact ⟨i,hi,hh.trans hf⟩
      · obtain ⟨i,hi,hf⟩ := ih _ (by omega) (insert j (S.erase k)) rfl
        exact ⟨i,hi,hh.trans hf⟩
    · by_cases hS : S.Nonempty
      · let k := S.max' hS
        have hk : k ∈ S := Finset.max'_mem _ _
        have hkn : k.val+1 ≤ n := by have := k.isLt; omega
        have he : S = popularSet n (k.val+1) := by
          ext j
          simp only [popularSet, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hj
            have := Finset.le_max' S j hj
            change j.val ≤ k.val at this
            omega
          · intro hj
            by_cases he : j = k
            · simpa [he] using hk
            · by_contra hn
              have hjk : j < k := by have := Fin.ext_iff.not.mp he; change j.val < k.val; omega
              exact hg ⟨j,k,hjk,hn,hk⟩
        exact ⟨k.val+1,hkn,by rw [← he]⟩
      · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
        exact ⟨0,Nat.zero_le _,by simp [he, popularSet]⟩

private lemma prefix_max {n : ℕ} (F : Finset (Fin n) → ℝ)
    (hgap : ∀ S (j k : Fin n), j < k → j ∉ S → k ∈ S →
      F S ≤ max (F (S.erase k)) (F (insert j (S.erase k)))) :
    ∃ i : ℕ, i ≤ n ∧ ∀ S, F S ≤ F (popularSet n i) := by
  classical
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup' (s := Finset.range (n+1))
    (by simp : (Finset.range (n+1)).Nonempty) (fun i => F (popularSet n i))
  refine ⟨i,by simpa using Finset.mem_range.mp hi,?_⟩
  intro S
  obtain ⟨j,hj,hh⟩ := prefix_dom F hgap S
  apply hh.trans
  rw [← he]
  exact Finset.le_sup' (fun i => F (popularSet n i)) (by simp; omega)

private lemma qc_between (M : ℝ) (hM : 0 < M) (f : ℝ → ℝ)
    (hf : QuasiconvexOn ℝ (Set.Icc 0 M) f) (u w : ℝ)
    (hu : 0 ≤ u) (huw : u ≤ w) (hw : w ≤ M) (hw0 : 0 < w) :
    f u ≤ max (f 0) (f w) := by
  have hb : 0 ≤ u/w := div_nonneg hu hw0.le
  have hb1 : u/w ≤ 1 := (div_le_one hw0).mpr huw
  have hh := (quasiconvexOn_iff_le_max.mp hf).2
    (show 0 ∈ Set.Icc 0 M by constructor; rfl; exact hM.le)
    (show w ∈ Set.Icc 0 M from ⟨hw0.le,hw⟩)
    (sub_nonneg.mpr hb1) hb (by ring : 1-u/w+u/w=1)
  have he : (1-u/w)*0+u/w*w = u := by field_simp; ring
  simpa only [smul_eq_mul, he] using hh

private lemma gap_pos (n : ℕ) (hn : 0 < n) (v : Fin n → ℝ) (v0 : ℝ)
    (hv : ∀ j, 0 < v j) (hv0 : 0 < v0) (hanti : Antitone v)
    (p c lam σ β : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hβ : 0 < β)
    (S : Finset (Fin n)) (j k : Fin n) (hjk : j < k) (hj : j ∉ S) (hk : k ∈ S) :
    profitI p c lam σ β v v0 S ≤
      max (profitI p c lam σ β v v0 (S.erase k))
        (profitI p c lam σ β v v0 (insert j (S.erase k))) ∧
    profitT p c lam v v0 S ≤
      max (profitT p c lam v v0 (S.erase k))
        (profitT p c lam v v0 (insert j (S.erase k))) := by
  have hq := RetailVariety.Structure.lemma_1 n hn v v0 hv hv0 hanti p c lam σ β hc hcp hlam hσ hβ0 hβ1 (S.erase k)
  have hep := RetailVariety.Structure.h_endpoints v v0 hv hv0 p c lam σ β hc hcp hlam hσ hβ0 hβ1 (S.erase k)
  have hkj : v k ≤ v j := hanti hjk.le
  have hjM : v j ≤ v ⟨0,hn⟩ := hanti (by change 0 ≤ j.val; omega)
  have hi := qc_between _ (hv _) _ hq.1 (v k) (v j) (hv k).le hkj hjM (hv j)
  have ht := qc_between _ (hv _) _ hq.2 (v k) (v j) (hv k).le hkj hjM (hv j)
  have hj' : j ∉ S.erase k := fun h => hj (Finset.mem_of_mem_erase h)
  rw [hep.1 k (by simp), Finset.insert_erase hk,
    hep.2.2.2 hβ, hep.1 j hj'] at hi
  rw [hep.2.1 k (by simp), Finset.insert_erase hk,
    hep.2.2.1, hep.2.1 j hj'] at ht
  exact ⟨hi,ht⟩

private lemma gap_zero {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ j, 0 < v j)
    (hv0 : 0 < v0) (hanti : Antitone v) (p c lam σ : ℝ)
    (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (S : Finset (Fin n)) (j k : Fin n) (hjk : j < k) (hj : j ∉ S) (hk : k ∈ S) :
    profitI p c lam σ 0 v v0 S ≤ profitI p c lam σ 0 v v0 (insert j (S.erase k)) := by
  classical
  let T := insert j (S.erase k)
  have hj' : j ∉ S.erase k := fun h => hj (Finset.mem_of_mem_erase h)
  have hsum : ∑ i ∈ S, v i ≤ ∑ i ∈ T, v i := by
    dsimp [T]
    rw [Finset.sum_insert hj']
    have he := Finset.sum_erase_add S v hk
    have hh := hanti hjk.le
    linarith
  have hcard : T.card = S.card := by
    dsimp [T]
    simp only [Finset.card_insert_of_notMem hj', Finset.card_erase_of_mem hk]
    have := Finset.card_pos.mpr ⟨k,hk⟩
    omega
  have hshare : (∑ i ∈ S, v i)/(∑ i ∈ S, v i+v0) ≤
      (∑ i ∈ T, v i)/(∑ i ∈ T, v i+v0) := by
    apply (div_le_div_iff₀ (den_pos v v0 hv hv0 S) (den_pos v v0 hv hv0 T)).mpr
    nlinarith
  have hnS : ∀ i ∈ S, share v v0 S i ≠ 0 := by
    intro i hi; exact ne_of_gt (div_pos (hv i) (den_pos v v0 hv hv0 S))
  change profitI p c lam σ 0 v v0 S ≤ profitI p c lam σ 0 v v0 T
  unfold profitI
  simp only [Real.rpow_zero, Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
  simp only [share, ← Finset.sum_div]
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left hshare (by positivity : 0 ≤ (p-c)*lam)) _

theorem solution (n : ℕ) (hn : 0 < n) (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ j, 0 < v j)
    (hv0 : 0 < v0) (hanti : Antitone v) (p c lam σ β : ℝ) (hc : 0 < c) (hcp : c < p)
    (hlam : 0 < lam) (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (∃ i : ℕ, i ≤ n ∧ ∀ S : Finset (Fin n),
        profitI p c lam σ β v v0 S ≤ profitI p c lam σ β v v0 (popularSet n i)) ∧
      (∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧ ∀ S : Finset (Fin n),
        profitT p c lam v v0 S ≤ profitT p c lam v v0 (popularSet n i))  := by
  classical
  constructor
  · apply prefix_max
    intro S j k hjk hj hk
    by_cases hb : β = 0
    · subst β
      exact (gap_zero v v0 hv hv0 hanti p c lam σ hc hcp hlam S j k hjk hj hk).trans (le_max_right _ _)
    · exact (gap_pos n hn v v0 hv hv0 hanti p c lam σ β hc hcp hlam hσ hβ0 hβ1
        (lt_of_le_of_ne hβ0 (Ne.symm hb)) S j k hjk hj hk).1
  · obtain ⟨i,hi,hF⟩ := prefix_max (profitT p c lam v v0) (by
      intro S j k hjk hj hk
      exact (gap_pos n hn v v0 hv hv0 hanti p c lam σ (1/2) hc hcp hlam hσ
        (by norm_num) (by norm_num) (by norm_num) S j k hjk hj hk).2)
    by_cases hi0 : i = 0
    · subst i
      refine ⟨1,le_rfl,hn,?_⟩
      intro S
      have hh := hF S
      have hz : profitT p c lam v v0 (popularSet n 0) = 0 := by simp [popularSet, profitT]
      rw [hz] at hh
      exact hh.trans (Finset.sum_nonneg (fun j hj => mul_nonneg (le_max_right _ _) hlam.le))
    · exact ⟨i,by omega,hi,hF⟩

end
