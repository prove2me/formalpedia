-- Prove2me | solution 1 for RevenueOrdered.UDPmin.reduction_isRegular
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T04:07:20.26709+00:00
-- url     : https://prove2.me/submissions/cc4169a4-6429-48e2-8294-e64d7f898dfb

import Mathlib
import Definitions.Def_RevenueOrdered_UDPmin_Reduction

open RevenueOrdered.UDPmin
local notation "IsRegular" => RevenueOrdered.UDPmin.IsRegular

private theorem Q_nonempty_iff {X M : Type*} [Fintype X] [DecidableEq X] [Fintype M]
    (I : Instance X M) (i : M) (S : Finset (RedProd I)) :
    (Q I i S).Nonempty ↔ ∃ y ∈ S, y.1 ∈ I.B i ∧ (y.2 : ℝ) ≤ I.v i := by
  classical
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨hyS,hyB,hyv,hmin⟩ := Finset.mem_filter.mp hy
    exact ⟨y,hyS,hyB,hyv⟩
  · rintro ⟨y,hyS,hyB,hyv⟩
    have hne : (S.filter (fun z => z.1 ∈ I.B i)).Nonempty := ⟨y,by simp [hyS,hyB]⟩
    obtain ⟨z,hz,hmin⟩ := (S.filter (fun z => z.1 ∈ I.B i)).exists_min_image
      (fun z => (z.2 : ℝ)) hne
    refine ⟨z,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2,?_,?_⟩⟩
    · exact (hmin y (by simp [hyS,hyB])).trans hyv
    · intro w hw hwB
      exact hmin w (by simp [hw,hwB])

private theorem pcons_sum {X M : Type*} [Fintype X] [DecidableEq X] [Fintype M]
    (I : Instance X M) (i : M) (S : Finset (RedProd I)) :
    ∑ y ∈ S, Pcons I i y S = if (Q I i S).Nonempty then 1 else 0 := by
  classical
  simp only [Pcons]
  rw [← Finset.sum_filter]
  have hf : S.filter (fun y => y ∈ Q I i S) = Q I i S := by
    ext y
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨(Finset.mem_filter.mp h).1,h⟩⟩
  rw [hf,Finset.sum_const,nsmul_eq_mul]
  split_ifs with h
  · have hcard : ((Q I i S).card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr h).ne'
    field_simp
  · rw [Finset.not_nonempty_iff_eq_empty.mp h]
    simp

private theorem total_mass {X M : Type*} [Fintype X] [DecidableEq X] [Fintype M]
    (I : Instance X M) (S : Finset (RedProd I)) :
    ∑ y ∈ S, redP I y S = (1 / (Fintype.card M : ℝ)) * ∑ i, if (Q I i S).Nonempty then 1 else 0 := by
  classical
  simp only [redP]
  rw [← Finset.mul_sum,Finset.sum_comm]
  simp_rw [pcons_sum]

private theorem pcons_antitone {X M : Type*} [Fintype X] [DecidableEq X] [Fintype M]
    (I : Instance X M) (i : M) (S T : Finset (RedProd I)) (hST : S ⊆ T)
    (y : RedProd I) (hy : y ∈ S) : Pcons I i y T ≤ Pcons I i y S := by
  classical
  by_cases hyT : y ∈ Q I i T
  · obtain ⟨hyT',hyB,hyv,hymin⟩ := Finset.mem_filter.mp hyT
    have hyS : y ∈ Q I i S :=
      Finset.mem_filter.mpr ⟨hy,hyB,hyv,fun z hz hzB => hymin z (hST hz) hzB⟩
    have hQ : Q I i S ⊆ Q I i T := by
      intro z hz
      obtain ⟨hzS,hzB,hzv,hzmin⟩ := Finset.mem_filter.mp hz
      refine Finset.mem_filter.mpr ⟨hST hzS,hzB,hzv,?_⟩
      intro w hw hwB
      exact (hzmin y hy hyB).trans (hymin w hw hwB)
    simp only [Pcons,if_pos hyT,if_pos hyS]
    apply one_div_le_one_div_of_le
    · exact_mod_cast Finset.card_pos.mpr ⟨y,hyS⟩
    · exact_mod_cast Finset.card_le_card hQ
  · simp only [Pcons,if_neg hyT]
    split_ifs <;> positivity

theorem solution {X M : Type*} [Fintype X] [DecidableEq X] [Fintype M] [Nonempty M]
    (I : Instance X M) : IsRegular (redP I) := by
  classical
  have hcard : 0 < (Fintype.card M : ℝ) := by exact_mod_cast Fintype.card_pos
  have hn (y : RedProd I) (S : Finset (RedProd I)) : 0 ≤ redP I y S := by
    unfold redP
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro i hi
    unfold Pcons
    split_ifs <;> positivity
  have hsum (S : Finset (RedProd I)) : ∑ y ∈ S,redP I y S ≤ 1 := by
    rw [total_mass]
    have h : (∑ i : M,if (Q I i S).Nonempty then (1:ℝ) else 0) ≤ Fintype.card M := by
      simpa using (Finset.sum_le_sum (s:=Finset.univ)
        (f:=fun i : M => if (Q I i S).Nonempty then (1:ℝ) else 0) (g:=fun _ => (1:ℝ))
        (fun i hi => by split_ifs <;> norm_num))
    calc _ ≤ (1 / (Fintype.card M : ℝ)) * Fintype.card M := mul_le_mul_of_nonneg_left h (by positivity)
      _ = 1 := by field_simp
  refine ⟨hn,?_,?_,hsum,?_,?_⟩
  · intro S
    exact sub_nonneg.mpr (hsum S)
  · intro y S hy
    unfold redP
    have h : ∑ i,Pcons I i y S = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact if_neg (fun hyQ => hy (Finset.mem_filter.mp hyQ).1)
    rw [h,mul_zero]
  · intro S T y hST hy
    apply mul_le_mul_of_nonneg_left
    · exact Finset.sum_le_sum (fun i hi => pcons_antitone I i S T hST y hy)
    · positivity
  · intro S T hST
    unfold RevenueOrdered.Ratio.noPurchase
    apply sub_le_sub_left
    rw [total_mass,total_mass]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro i hi
    by_cases hS : (Q I i S).Nonempty
    · obtain ⟨y,hy,hyB,hyv⟩ := (Q_nonempty_iff I i S).mp hS
      have hT := (Q_nonempty_iff I i T).mpr ⟨y,hST hy,hyB,hyv⟩
      simp [hS,hT]
    · simp only [if_neg hS]
      split_ifs <;> norm_num
