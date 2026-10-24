-- Prove2me | solution 1 for SaturatedNet.Uniqueness.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T10:07:46.050243+00:00
-- url     : https://prove2.me/submissions/a49b9ba4-2315-4b6d-b6d9-1130c78ce7dc

import Mathlib
import Definitions.Def_SaturatedNet_Uniqueness_Model
import Theorems.Thm_SaturatedNet_Uniqueness_proposition_3
open Matrix

-- Complete local proof: Scalar.lean

namespace SaturatedNet.Uniqueness.PartitionProof

lemma sat_contract (w a b : ℝ) : |sat w a-sat w b| ≤ |a-b| := by
  calc
    _ ≤ |max a 0-max b 0| := by
      simpa only [sat,sub_self,abs_zero,max_eq_left (abs_nonneg (max a 0-max b 0))] using
        abs_min_sub_min_le_max (max a 0) w (max b 0) w
    _ ≤ _ := abs_max_sub_max_le_abs a b 0

lemma sat_surplus_imp (w a b : ℝ) (hw : 0 ≤ w)
    (he : |sat w a-sat w b|=|a-b|) (ha : w<a) : w<b := by
  by_contra hb
  have hb' : b ≤ w := le_of_not_gt hb
  have hsa : sat w a=w := by
    unfold sat
    rw [max_eq_left (by linarith),min_eq_right ha.le]
  have hsb : sat w b=max b 0 := min_eq_left (max_le hb' hw)
  rw [hsa,hsb,abs_of_nonneg (sub_nonneg.mpr (max_le hb' hw)),
    abs_of_nonneg (show 0 ≤ a-b by linarith)] at he
  linarith [le_max_left b 0]

lemma sat_deficit_imp (w a b : ℝ) (hw : 0 ≤ w)
    (he : |sat w a-sat w b|=|a-b|) (ha : a<0) : b<0 := by
  by_contra hb
  have hb' : 0 ≤ b := le_of_not_gt hb
  have hsa : sat w a=0 := by simp [sat,max_eq_right ha.le,min_eq_left hw]
  have hsb : sat w b=min b w := by simp [sat,max_eq_left hb']
  rw [hsa,hsb,abs_of_nonpos (show 0-min b w ≤ 0 by linarith [le_min hb' hw]),
    abs_of_nonpos (show a-b ≤ 0 by linarith)] at he
  linarith [min_le_left b w]

lemma sat_regions (w a b : ℝ) (hw : 0 ≤ w)
    (he : |sat w a-sat w b|=|a-b|) :
    (w<a ↔ w<b) ∧ ((0≤a ∧ a≤w) ↔ (0≤b ∧ b≤w)) ∧ (a<0 ↔ b<0) := by
  have he' : |sat w b-sat w a|=|b-a| := by simpa only [abs_sub_comm] using he
  have hs : w<a ↔ w<b := ⟨sat_surplus_imp w a b hw he,sat_surplus_imp w b a hw he'⟩
  have hd : a<0 ↔ b<0 := ⟨sat_deficit_imp w a b hw he,sat_deficit_imp w b a hw he'⟩
  refine ⟨hs,?_,hd⟩
  simp only [← not_lt,hd,hs]

end SaturatedNet.Uniqueness.PartitionProof

-- Complete local proof: Weighted.lean

namespace SaturatedNet.Uniqueness.PartitionProof
open Matrix

lemma inflow_difference {n : Type*} [Fintype n] (P : Matrix n n ℝ) (c x y : n → ℝ) (i : n) :
    inflow P c x i-inflow P c y i=∑ j,(x j-y j)*P j i := by
  unfold inflow
  rw [add_sub_add_right_eq_sub,← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun j _ => (sub_mul _ _ _).symm)

lemma weighted_inflow_contract {n : Type*} [Fintype n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (v : n → ℝ)
    (hv : ∀ i,0<v i) (hPv : P *ᵥ v ≤ v) (c x y : n → ℝ) :
    (∑ i,v i*|inflow P c x i-inflow P c y i|) ≤ ∑ i,v i*|x i-y i| := by
  have hi (i : n) : |inflow P c x i-inflow P c y i| ≤ ∑ j,|x j-y j| * P j i := by
    rw [inflow_difference]
    calc
      _ ≤ ∑ j,|(x j-y j)*P j i| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := Finset.sum_congr rfl (fun j _ => by rw [abs_mul,abs_of_nonneg (hP j i)])
  calc
    _ ≤ ∑ i,v i*(∑ j,|x j-y j| * P j i) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hi i) (hv i).le)
    _ = ∑ j,(∑ i,P j i*v i)*|x j-y j| := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    _ ≤ _ := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hPv j) (abs_nonneg _))

lemma equilibrium_absolute_eq {n : Type*} [Fintype n]
    (P : Matrix n n ℝ) (hP : ∀ i j,0≤P i j) (v : n → ℝ)
    (hv : ∀ i,0<v i) (hPv : P *ᵥ v ≤ v) (w c x y : n → ℝ)
    (hx : IsEquilibrium P w c x) (hy : IsEquilibrium P w c y) (i : n) :
    |x i-y i|=|inflow P c x i-inflow P c y i| := by
  have hi (j : n) : |x j-y j| ≤ |inflow P c x j-inflow P c y j| := by
    rw [hx j,hy j]
    exact sat_contract _ _ _
  have hw (j : n) : v j*|x j-y j| ≤ v j*|inflow P c x j-inflow P c y j| :=
    mul_le_mul_of_nonneg_left (hi j) (hv j).le
  have hs : (∑ j,v j*|x j-y j|) = ∑ j,v j*|inflow P c x j-inflow P c y j| :=
    le_antisymm (Finset.sum_le_sum (fun j _ => hw j)) (weighted_inflow_contract P hP v hv hPv c x y)
  have he := (Finset.sum_eq_sum_iff_of_le (fun j (_ : j ∈ Finset.univ) => hw j)).mp hs i (Finset.mem_univ i)
  exact mul_left_cancel₀ (ne_of_gt (hv i)) he

lemma partition_of_subinvariant {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j,0≤P i j) (v : n → ℝ)
    (hv : ∀ i,0<v i) (hPv : P *ᵥ v ≤ v) (w : n → ℝ) (hw : 0≤w) (c : n → ℝ)
    (x y : n → ℝ) (hx : IsEquilibrium P w c x) (hy : IsEquilibrium P w c y) :
    surplus P w c x=surplus P w c y ∧ exposed P w c x=exposed P w c y ∧ deficit P c x=deficit P c y := by
  classical
  have hi (i : n) := equilibrium_absolute_eq P hP v hv hPv w c x y hx hy i
  have hr (i : n) :
      (w i< inflow P c x i ↔ w i< inflow P c y i) ∧
      ((0≤ inflow P c x i ∧ inflow P c x i≤w i) ↔ (0≤ inflow P c y i ∧ inflow P c y i≤w i)) ∧
      (inflow P c x i<0 ↔ inflow P c y i<0) := by
    apply sat_regions _ _ _ (hw i)
    rw [← hx i,← hy i]
    exact hi i
  refine ⟨?_,?_,?_⟩
  · ext i
    simpa only [surplus,Finset.mem_filter,Finset.mem_univ,true_and] using (hr i).1
  · ext i
    simpa only [exposed,Finset.mem_filter,Finset.mem_univ,true_and] using (hr i).2.1
  · ext i
    simpa only [deficit,Finset.mem_filter,Finset.mem_univ,true_and] using (hr i).2.2

end SaturatedNet.Uniqueness.PartitionProof

-- Complete local proof: ConditionalAssembly.lean

open Matrix SaturatedNet.Uniqueness SaturatedNet.Uniqueness.PartitionProof
universe u

def PositiveCertificateStatement : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j),
    (∃ v : n → ℝ, (∀ i, 0 < v i) ∧ P *ᵥ v ≤ v) ↔
      (specRad P < 1 ∨
        (specRad P = 1 ∧ ∀ V : Finset n, IsClass P V → IsBasic P V → IsFinal P V))

theorem conditional_solution (hcertificate : PositiveCertificateStatement.{u}) {n : Type u} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (w : n → ℝ) (hw : 0 ≤ w) (c : n → ℝ) (hne : IsNonExpansive P) :
    ∀ x ∈ equilibria P w c, ∀ y ∈ equilibria P w c,
      surplus P w c x = surplus P w c y ∧ exposed P w c x = exposed P w c y ∧
        deficit P c x = deficit P c y := by
  obtain ⟨v,hv,hPv⟩ := (hcertificate P hP).mpr hne
  intro x hx y hy
  exact partition_of_subinvariant P hP v hv hPv w hw c x y hx hy


theorem solution {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (w : n → ℝ) (hw : 0 ≤ w) (c : n → ℝ) (hne : IsNonExpansive P) :
    ∀ x ∈ equilibria P w c, ∀ y ∈ equilibria P w c,
      surplus P w c x = surplus P w c y ∧ exposed P w c x = exposed P w c y ∧
        deficit P c x = deficit P c y := by
  exact conditional_solution (@SaturatedNet.Uniqueness.proposition_3) P hP w hw c hne
