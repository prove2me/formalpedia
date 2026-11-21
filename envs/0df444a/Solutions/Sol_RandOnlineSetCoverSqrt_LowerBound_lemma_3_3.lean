-- Prove2me | solution 1 for RandOnlineSetCoverSqrt.LowerBound.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:46:56.405228+00:00
-- url     : https://prove2.me/submissions/4f153afa-72a7-4d21-9b1c-145c4461f001

import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Candidates

section
namespace RandOnlineSetCoverSqrt.Dev.L33
open RandOnlineSetCoverSqrt.LowerBound

theorem card_sup {α : Type*} [DecidableEq α] (K Q : Finset α) (M : ℕ) (hQ : Q ⊆ K)
    (hqM : Q.card ≤ M) :
    ((Finset.powersetCard M K).filter (fun F => Q ⊆ F)).card = (K.card - Q.card).choose (M - Q.card) := by
  rw [← Finset.card_sdiff_of_subset hQ, ← Finset.card_powersetCard (M - Q.card) (K \ Q)]
  refine Finset.card_nbij' (fun F => F \ Q) (fun S => S ∪ Q) ?_ ?_ ?_ ?_
  · intro F hF
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powersetCard] at hF
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨Finset.sdiff_subset_sdiff hF.1.1 le_rfl, ?_⟩
    rw [Finset.card_sdiff_of_subset hF.2, hF.1.2]
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hS
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powersetCard]
    have hd : Disjoint S Q := by
      rw [Finset.disjoint_left]; intro x hx hxQ
      exact (Finset.mem_sdiff.mp (hS.1 hx)).2 hxQ
    refine ⟨⟨Finset.union_subset (hS.1.trans Finset.sdiff_subset) hQ, ?_⟩, Finset.subset_union_right⟩
    rw [Finset.card_union_of_disjoint hd, hS.2]; omega
  · intro F hF
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powersetCard] at hF
    simp only [Finset.sdiff_union_of_subset hF.2]
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hS
    have hd : Disjoint S Q := by
      rw [Finset.disjoint_left]; intro x hx hxQ
      exact (Finset.mem_sdiff.mp (hS.1 hx)).2 hxQ
    simp only [Finset.union_sdiff_right, hd.sdiff_eq_left]

theorem desc_ratio (a N : ℕ) (h : a ≤ N) (q : ℕ) :
    a.descFactorial q * N ^ q ≤ a ^ q * N.descFactorial q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
    have h2 : (a - q) * N ≤ a * (N - q) := by
      rcases le_or_gt a q with hq | hq
      · simp [Nat.sub_eq_zero_of_le hq]
      · have : q ≤ N := by omega
        zify [hq.le, this]
        nlinarith
    calc (a - q) * a.descFactorial q * (N ^ q * N) = ((a - q) * N) * (a.descFactorial q * N ^ q) := by ring
      _ ≤ (a * (N - q)) * (a ^ q * N.descFactorial q) := Nat.mul_le_mul h2 ih
      _ = a ^ q * a * ((N - q) * N.descFactorial q) := by ring

theorem choose_ratio (a N q : ℕ) (h : a ≤ N) :
    a.choose q * N ^ q ≤ a ^ q * N.choose q := by
  have := desc_ratio a N h q
  have e1 := Nat.descFactorial_eq_factorial_mul_choose a q
  have e2 := Nat.descFactorial_eq_factorial_mul_choose N q
  rw [e1, e2] at this
  have hp := Nat.factorial_pos q
  nlinarith [this]

end RandOnlineSetCoverSqrt.Dev.L33

namespace RandOnlineSetCoverSqrt.LowerBound
open RandOnlineSetCoverSqrt.Dev.L33

theorem chk_lemma_3_3 (m k q r M : ℕ)
    (hk : 1 ≤ k) (hkr : k ≤ r) (hrm : r ≤ m) (hq : 2 ≤ q)
    (hM : M ≤ Nat.choose m k)
    (hfirst : (Nat.choose M q : ℝ) * (Nat.choose m r : ℝ) *
      ((Nat.choose r k : ℝ) / (Nat.choose m k : ℝ)) ^ q < 1) :
    ∃ C : Family m, C.card = M ∧ UnionExpanding k q r C := by
  classical
  set K : Finset (Finset (Fin m)) := Finset.powersetCard k Finset.univ with hK
  have hN : K.card = Nat.choose m k := by simp [hK, Finset.card_powersetCard]
  have hKk : ∀ W ∈ K, W.card = k := by
    intro W hW; exact (Finset.mem_powersetCard.mp hW).2
  have hbase : 1 ≤ k ∧ k ≤ r ∧ r ≤ m ∧ 2 ≤ q := ⟨hk, hkr, hrm, hq⟩
  by_cases hMq : M < q
  · obtain ⟨F, hF⟩ := (Finset.powersetCard_nonempty (s := K) (n := M)).mpr (by omega)
    rw [Finset.mem_powersetCard] at hF
    refine ⟨F, hF.2, hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2, fun W hW => hKk W (hF.1 hW), ?_⟩
    intro Q hQ hQc
    have := Finset.card_le_card hQ
    omega
  push Not at hMq
  set a := Nat.choose r k with ha
  set N := Nat.choose m k with hNdef
  have haN : a ≤ N := Nat.choose_le_choose k hrm
  set bad : Finset (Finset (Finset (Fin m))) :=
    (Finset.powersetCard r (Finset.univ : Finset (Fin m))).biUnion fun R =>
      (Finset.powersetCard q (Finset.powersetCard k R)).biUnion fun Q =>
        (Finset.powersetCard M K).filter (fun F => Q ⊆ F) with hbad
  have hcard : bad.card ≤ Nat.choose m r * (Nat.choose a q * (N - q).choose (M - q)) := by
    calc bad.card ≤ ∑ R ∈ Finset.powersetCard r (Finset.univ : Finset (Fin m)),
          ((Finset.powersetCard q (Finset.powersetCard k R)).biUnion fun Q =>
            (Finset.powersetCard M K).filter (fun F => Q ⊆ F)).card := Finset.card_biUnion_le
      _ ≤ ∑ R ∈ Finset.powersetCard r (Finset.univ : Finset (Fin m)),
          Nat.choose a q * (N - q).choose (M - q) := by
        apply Finset.sum_le_sum
        intro R hR
        have hRc : R.card = r := (Finset.mem_powersetCard.mp hR).2
        refine Finset.card_biUnion_le.trans ?_
        have : ∀ Q ∈ Finset.powersetCard q (Finset.powersetCard k R),
            ((Finset.powersetCard M K).filter (fun F => Q ⊆ F)).card = (N - q).choose (M - q) := by
          intro Q hQ
          rw [Finset.mem_powersetCard] at hQ
          have hQK : Q ⊆ K := by
            intro W hW
            have := Finset.mem_powersetCard.mp (hQ.1 hW)
            exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, this.2⟩
          rw [card_sup K Q M hQK (by omega), hQ.2, hN]
        rw [Finset.sum_congr rfl this]
        simp [Finset.card_powersetCard, hRc, ha]
      _ = Nat.choose m r * (Nat.choose a q * (N - q).choose (M - q)) := by
        simp [Finset.card_powersetCard]
  have hqN : q ≤ N := hMq.trans hM
  have hNq : 0 < N.choose q := Nat.choose_pos hqN
  have hNpos : (0:ℝ) < (N:ℝ) ^ q := by
    have : 0 < N := by omega
    positivity
  have h1 : (Nat.choose M q : ℝ) * Nat.choose m r * (a:ℝ) ^ q < (N:ℝ) ^ q := by
    rw [div_pow, ← mul_div_assoc, div_lt_one hNpos] at hfirst
    exact hfirst
  have h2 : Nat.choose M q * Nat.choose m r * a ^ q < N ^ q := by exact_mod_cast h1
  have h3 : Nat.choose M q * Nat.choose m r * Nat.choose a q < N.choose q := by
    have hlt : (Nat.choose M q * Nat.choose m r * Nat.choose a q) * N ^ q < N.choose q * N ^ q := by
      calc (Nat.choose M q * Nat.choose m r * Nat.choose a q) * N ^ q
          = Nat.choose M q * Nat.choose m r * (Nat.choose a q * N ^ q) := by ring
        _ ≤ Nat.choose M q * Nat.choose m r * (a ^ q * N.choose q) :=
            Nat.mul_le_mul_left _ (choose_ratio a N q haN)
        _ = (Nat.choose M q * Nat.choose m r * a ^ q) * N.choose q := by ring
        _ < N ^ q * N.choose q := Nat.mul_lt_mul_of_pos_right h2 hNq
        _ = N.choose q * N ^ q := by ring
    exact Nat.lt_of_mul_lt_mul_right hlt
  have hid : N.choose M * M.choose q = N.choose q * (N - q).choose (M - q) := Nat.choose_mul hMq
  have hlt : bad.card < (Finset.powersetCard M K).card := by
    rw [Finset.card_powersetCard, hN]
    have hNM : 0 < N.choose M := Nat.choose_pos hM
    have : bad.card * N.choose q < N.choose M * N.choose q := by
      calc bad.card * N.choose q ≤ Nat.choose m r * (Nat.choose a q * (N - q).choose (M - q)) * N.choose q :=
            Nat.mul_le_mul_right _ hcard
        _ = Nat.choose m r * Nat.choose a q * (N.choose q * (N - q).choose (M - q)) := by ring
        _ = Nat.choose m r * Nat.choose a q * (N.choose M * Nat.choose M q) := by rw [← hid]
        _ = (Nat.choose M q * Nat.choose m r * Nat.choose a q) * N.choose M := by ring
        _ < N.choose q * N.choose M := Nat.mul_lt_mul_of_pos_right h3 hNM
        _ = N.choose M * N.choose q := by ring
    exact Nat.lt_of_mul_lt_mul_right this
  obtain ⟨F, hF, hFbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hFm := Finset.mem_powersetCard.mp hF
  refine ⟨F, hFm.2, hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2, fun W hW => hKk W (hFm.1 hW), ?_⟩
  intro Q hQF hQc
  by_contra hle
  push Not at hle
  obtain ⟨R, hUR, hRc⟩ := Finset.exists_superset_card_eq (s := Q.biUnion id) (n := r) hle
    (by simpa using hrm)
  apply hFbad
  rw [hbad, Finset.mem_biUnion]
  refine ⟨R, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hRc⟩, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨Q, ?_, ?_⟩
  · rw [Finset.mem_powersetCard]
    refine ⟨?_, hQc⟩
    intro W hW
    rw [Finset.mem_powersetCard]
    exact ⟨(Finset.subset_biUnion_of_mem id hW).trans hUR, hKk W (hFm.1 (hQF hW))⟩
  · rw [Finset.mem_filter]; exact ⟨hF, hQF⟩

end RandOnlineSetCoverSqrt.LowerBound
end

theorem solution : type_of% @RandOnlineSetCoverSqrt.LowerBound.chk_lemma_3_3 := @RandOnlineSetCoverSqrt.LowerBound.chk_lemma_3_3
