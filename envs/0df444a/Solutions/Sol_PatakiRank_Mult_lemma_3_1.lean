-- Prove2me | solution 1 for PatakiRank.Mult.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:55:55.208571+00:00
-- url     : https://prove2.me/submissions/62ea8a0f-e362-4bed-a0bc-95c9115da704

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet
import Definitions.Def_PatakiRank_Mult_Setting
open Matrix BurerMonteiro.RankIncrease ProjLikeRetr.Spectral

namespace Aux_PR31
open PatakiRank.Mult

lemma gap {n k : ℕ} (lam : Fin n → ℝ) (hkn : k < n) (p : ℝ × (Fin n → ℝ) × (Fin n → ℝ))
    (hp : lpFeas lam p) :
    lpObj k p - ∑ i : Fin n with i.val < k, lam i =
      ∑ i : Fin n with i.val < k, p.2.2 i + ∑ i : Fin n with ¬ i.val < k, p.2.1 i := by
  obtain ⟨-, -, heq⟩ := hp
  have hpt : ∀ i, lam i = p.1 + p.2.1 i - p.2.2 i := by
    intro i
    have := congrFun heq i
    simp only [Pi.add_apply, Pi.sub_apply] at this
    linarith
  have hcard : (Finset.univ.filter (fun i : Fin n => i.val < k)).card = k := by
    rw [Fin.card_filter_val_lt, min_eq_right hkn.le]
  unfold lpObj
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => i.val < k) p.2.1]
  simp only [hpt]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul]
  ring

end Aux_PR31

open PatakiRank.Mult in
theorem solution {n k : ℕ} (lam : Fin n → ℝ) (hlam : Antitone lam) (hk : 1 ≤ k) (hkn : k < n) :
    IsLeast (lpObj k '' {p | lpFeas lam p}) (∑ i : Fin n with i.val < k, lam i) ∧
    ∀ p : ℝ × (Fin n → ℝ) × (Fin n → ℝ), IsOptimal (lpFeas lam) (lpObj k) p ↔
      ((lam ⟨k, hkn⟩ ≤ p.1 ∧ p.1 ≤ lam ⟨k - 1, by omega⟩) ∧
        p.2.1 = vStar k lam p.1 ∧ p.2.2 = wStar k lam p.1) := by
  set S := ∑ i : Fin n with i.val < k, lam i with hS
  -- lower bound for feasible points
  have hlb : ∀ p, lpFeas lam p → S ≤ lpObj k p := by
    intro p hp
    have h := Aux_PR31.gap lam hkn p hp
    have h1 : 0 ≤ ∑ i : Fin n with i.val < k, p.2.2 i :=
      Finset.sum_nonneg (fun i _ => hp.2.1 i)
    have h2 : 0 ≤ ∑ i : Fin n with ¬ i.val < k, p.2.1 i :=
      Finset.sum_nonneg (fun i _ => hp.1 i)
    linarith
  -- feasibility and value of the candidate points
  have hcand : ∀ z, lam ⟨k, hkn⟩ ≤ z → z ≤ lam ⟨k - 1, by omega⟩ →
      lpFeas lam (z, vStar k lam z, wStar k lam z) ∧ lpObj k (z, vStar k lam z, wStar k lam z) = S := by
    intro z hz1 hz2
    have hfeas : lpFeas lam (z, vStar k lam z, wStar k lam z) := by
      refine ⟨fun i => ?_, fun i => ?_, ?_⟩
      · simp only [vStar, Pi.zero_apply]
        split_ifs with hi
        · have : lam ⟨k - 1, by omega⟩ ≤ lam i := hlam (Fin.le_iff_val_le_val.mpr (by simp; omega))
          linarith
        · exact le_rfl
      · simp only [wStar, Pi.zero_apply]
        split_ifs with hi
        · exact le_rfl
        · have : lam i ≤ lam ⟨k, hkn⟩ := hlam (Fin.le_iff_val_le_val.mpr (by simp; omega))
          linarith
      · funext i
        simp only [Pi.add_apply, Pi.sub_apply, vStar, wStar]
        split_ifs <;> ring
    refine ⟨hfeas, ?_⟩
    have h := Aux_PR31.gap lam hkn _ hfeas
    have h1 : ∑ i : Fin n with i.val < k, wStar k lam z i = 0 :=
      Finset.sum_eq_zero (fun i hi => by
        simp only [wStar, if_pos (Finset.mem_filter.mp hi).2])
    have h2 : ∑ i : Fin n with ¬ i.val < k, vStar k lam z i = 0 :=
      Finset.sum_eq_zero (fun i hi => by
        simp only [vStar, if_neg (Finset.mem_filter.mp hi).2])
    simp only at h
    rw [h1, h2] at h
    linarith
  obtain ⟨hf0, hv0⟩ := hcand (lam ⟨k - 1, by omega⟩)
    (hlam (Fin.le_iff_val_le_val.mpr (by simp))) le_rfl
  refine ⟨⟨⟨_, hf0, hv0⟩, ?_⟩, fun p => ⟨fun hopt => ?_, fun hcond => ?_⟩⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact hlb q hq
  · obtain ⟨hp, hmin⟩ := hopt
    have hle := hmin _ hf0
    rw [hv0] at hle
    have hEq : lpObj k p = S := le_antisymm hle (hlb p hp)
    have h := Aux_PR31.gap lam hkn p hp
    rw [hEq, sub_self] at h
    have h1 : 0 ≤ ∑ i : Fin n with i.val < k, p.2.2 i :=
      Finset.sum_nonneg (fun i _ => hp.2.1 i)
    have h2 : 0 ≤ ∑ i : Fin n with ¬ i.val < k, p.2.1 i :=
      Finset.sum_nonneg (fun i _ => hp.1 i)
    have hw0 : ∀ i : Fin n, i.val < k → p.2.2 i = 0 := by
      intro i hi
      have hz : ∑ i : Fin n with i.val < k, p.2.2 i = 0 := by linarith
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hp.2.1 j)).mp hz i
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    have hv0' : ∀ i : Fin n, ¬ i.val < k → p.2.1 i = 0 := by
      intro i hi
      have hz : ∑ i : Fin n with ¬ i.val < k, p.2.1 i = 0 := by linarith
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hp.1 j)).mp hz i
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    have hpt : ∀ i, lam i = p.1 + p.2.1 i - p.2.2 i := by
      intro i
      have := congrFun hp.2.2 i
      simp only [Pi.add_apply, Pi.sub_apply] at this
      linarith
    have hvv : p.2.1 = vStar k lam p.1 := by
      funext i
      simp only [vStar]
      split_ifs with hi
      · have := hpt i; rw [hw0 i hi] at this; linarith
      · exact hv0' i hi
    have hww : p.2.2 = wStar k lam p.1 := by
      funext i
      simp only [wStar]
      split_ifs with hi
      · exact hw0 i hi
      · have := hpt i; rw [hv0' i hi] at this; linarith
    refine ⟨⟨?_, ?_⟩, hvv, hww⟩
    · have h3 := hp.2.1 ⟨k, hkn⟩
      rw [hww] at h3
      simp only [wStar, lt_irrefl, if_false, Pi.zero_apply] at h3
      linarith
    · have h3 := hp.1 ⟨k - 1, by omega⟩
      rw [hvv] at h3
      simp only [vStar, Pi.zero_apply] at h3
      rw [if_pos (by simp; omega)] at h3
      linarith
  · obtain ⟨⟨hz1, hz2⟩, hvv, hww⟩ := hcond
    obtain ⟨hf, hval⟩ := hcand p.1 hz1 hz2
    have hp : p = (p.1, vStar k lam p.1, wStar k lam p.1) := by
      ext
      · rfl
      · rw [hvv]
      · rw [hww]
    rw [hp]
    refine ⟨hf, fun q hq => ?_⟩
    rw [hval]
    exact hlb q hq
