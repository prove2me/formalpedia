-- Prove2me | solution 1 for ScenarioReduction.Redistribution.dual_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T16:11:13.620359+00:00
-- url     : https://prove2.me/submissions/390073ba-6ed8-4f5e-886b-d14aaa7da9e6

import Definitions.Def_ScenarioReduction_Redistribution_transportValue
import Mathlib.Tactic

open Finset
namespace ScenarioProof
open ScenarioReduction.Redistribution

lemma cost_nonneg {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω)
    (hc : ∀ a b, 0 ≤ c a b) (p : Fin N → ℝ) (J : Finset (Fin N)) (q η)
    (hη : IsTransportPlan p J q η) : 0 ≤ transportCost c ω J η := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j hj =>
    mul_nonneg (hc _ _) (hη.1 i j (Finset.mem_compl.mp hj))))

lemma plan_exists {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i,p i=1)
    (J : Finset (Fin N)) (q) (hq : IsReducedWeight J q) :
    ∃ η, IsTransportPlan p J q η := by
  refine ⟨fun i j => p i*q j,?_,?_,?_⟩
  · exact fun i j hj => mul_nonneg (hp i) (hq.1 j hj)
  · intro i
    rw [←Finset.mul_sum,hq.2,mul_one]
  · intro j hj
    rw [←Finset.sum_mul,hp1,one_mul]

lemma values_nonempty {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω)
    (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i,p i=1)
    (J : Finset (Fin N)) (q) (hq : IsReducedWeight J q) :
    {z : ℝ | ∃ η, IsTransportPlan p J q η ∧ z=transportCost c ω J η}.Nonempty := by
  obtain ⟨η,hη⟩ := plan_exists p hp hp1 J q hq
  exact ⟨_,η,hη,rfl⟩

lemma value_le_cost {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω)
    (hc : ∀ a b, 0 ≤ c a b) (p : Fin N → ℝ) (J : Finset (Fin N)) (q η)
    (hη : IsTransportPlan p J q η) : transportValue c ω p J q ≤ transportCost c ω J η := by
  apply csInf_le
  · refine ⟨0,?_⟩
    rintro z ⟨η,hη,rfl⟩
    exact cost_nonneg c ω hc p J q η hη
  · exact ⟨η,hη,rfl⟩

lemma min_le {N : ℕ} (S : Finset (Fin N)) (hS : S.Nonempty) (f : Fin N → ℝ)
    (j : Fin N) (hj : j∈S) : minOver S f ≤ f j := by
  rw [minOver,dif_pos hS]
  exact Finset.inf'_le f hj

lemma min_nonneg {N : ℕ} (S : Finset (Fin N)) (f : Fin N → ℝ) (hf : ∀ i∈S,0≤f i) :
    0 ≤ minOver S f := by
  unfold minOver
  split_ifs with hS
  · exact Finset.le_inf' hS f hf
  · rfl

lemma min_eq {N : ℕ} (S : Finset (Fin N)) (hS : S.Nonempty) (f : Fin N → ℝ)
    (j : Fin N) (hj : j∈S) (hm : ∀ i∈S,f j≤f i) : minOver S f=f j := by
  apply le_antisymm (min_le S hS f j hj)
  rw [minOver,dif_pos hS]
  exact Finset.le_inf' hS f hm

lemma cost_lower {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω)
    (hc : ∀ a b,0≤c a b) (p : Fin N → ℝ) (J : Finset (Fin N)) (hJ : Jᶜ.Nonempty)
    (q η) (hη : IsTransportPlan p J q η) :
    ∑ i∈J,p i*minOver Jᶜ (fun j=>c (ω i) (ω j)) ≤ transportCost c ω J η := by
  have hrow (i : Fin N) : p i*minOver Jᶜ (fun j=>c (ω i) (ω j)) ≤
      ∑ j∈Jᶜ,c (ω i) (ω j)*η i j := by
    rw [←hη.2.1 i,Finset.sum_mul]
    exact Finset.sum_le_sum (fun j hj => by
      have hh := mul_le_mul_of_nonneg_right (min_le Jᶜ hJ (fun k => c (ω i) (ω k)) j hj) (hη.1 i j (Finset.mem_compl.mp hj))
      nlinarith)
  calc
    _ ≤ ∑ i∈J,∑ j∈Jᶜ,c (ω i) (ω j)*η i j := Finset.sum_le_sum (fun i _=>hrow i)
    _ ≤ transportCost c ω J η := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
      (fun i _ _ => Finset.sum_nonneg (fun j hj=>mul_nonneg (hc _ _) (hη.1 i j (Finset.mem_compl.mp hj))))

lemma lower {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω)
    (hc : ∀ a b,0≤c a b) (p : Fin N → ℝ) (hp : ∀ i,0≤p i) (hp1 : ∑ i,p i=1)
    (J : Finset (Fin N)) (hJ : Jᶜ.Nonempty) (q) (hq : IsReducedWeight J q) :
    ∑ i∈J,p i*minOver Jᶜ (fun j=>c (ω i) (ω j)) ≤ transportValue c ω p J q := by
  apply le_csInf (values_nonempty c ω p hp hp1 J q hq)
  rintro z ⟨η,hη,rfl⟩
  exact cost_lower c ω hc p J hJ q η hη

lemma weak_dual {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω)
    (p : Fin N → ℝ) (J : Finset (Fin N)) (q η) (hη : IsTransportPlan p J q η)
    (u v : Fin N → ℝ) (huv : IsDualFeasible c ω J u v) :
    dualObjective p J q u v ≤ transportCost c ω J η := by
  have heq : dualObjective p J q u v = ∑ i,∑ j∈Jᶜ,(u i+v j)*η i j := by
    simp only [dualObjective,add_mul,Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [←Finset.mul_sum,hη.2.1 i,mul_comm]
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [←Finset.mul_sum,hη.2.2 j (Finset.mem_compl.mp hj),mul_comm]
  rw [heq]
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j hj =>
    mul_le_mul_of_nonneg_right (huv i j (Finset.mem_compl.mp hj)) (hη.1 i j (Finset.mem_compl.mp hj))))

end ScenarioProof

namespace ScenarioReduction.Redistribution

theorem _root_.solution {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω) (p : Fin N → ℝ)
    (hc : ∀ a b : Ω, 0 ≤ c a b) (hc1 : ∀ a b : Ω, c a b = 0 ↔ a = b)
    (hc2 : ∀ a b : Ω, c a b = c b a)
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1)
    (J : Finset (Fin N)) (hJ : Jᶜ.Nonempty) (q : Fin N → ℝ) (hq : IsReducedWeight J q) :
    ∑ i ∈ J, p i * minOver Jᶜ (fun k => c (ω i) (ω k)) ≤ transportValue c ω p J q := by
  exact ScenarioProof.lower c ω hc p (fun i=>(hp i).le) hp1 J hJ q hq

end ScenarioReduction.Redistribution
