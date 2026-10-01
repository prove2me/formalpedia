-- Prove2me | solution 1 for ScenarioReduction.Redistribution.bounds
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T16:26:49.26251+00:00
-- url     : https://prove2.me/submissions/e9855708-10de-4b0d-a885-18c0ab149d2b

import Definitions.Def_ScenarioReduction_Redistribution_transportValue
import Mathlib.Tactic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

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

namespace ScenarioProof
open Finset ScenarioReduction.Redistribution

noncomputable def assigned {N : ℕ} (p : Fin N → ℝ) (r : Fin N → Fin N) : Fin N → ℝ :=
  fun j => ∑ i, if r i=j then p i else 0

lemma assigned_reduced {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i,0≤p i) (hp1 : ∑ i,p i=1)
    (J : Finset (Fin N)) (r : Fin N → Fin N) (hr : ∀ i,r i∉J) : IsReducedWeight J (assigned p r) := by
  constructor
  · intro j hj
    exact Finset.sum_nonneg (fun i _=>by split_ifs <;> first | exact hp i | rfl)
  · dsimp [assigned]
    rw [Finset.sum_comm]
    simpa [hr] using hp1

lemma assigned_plan {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i,0≤p i)
    (J : Finset (Fin N)) (r : Fin N → Fin N) (hr : ∀ i,r i∉J) :
    IsTransportPlan p J (assigned p r) (fun i j=>if r i=j then p i else 0) := by
  refine ⟨fun i j hj=>?_,fun i=>?_,fun j hj=>rfl⟩
  · dsimp only
    split_ifs <;> first | exact hp i | rfl
  · simp [hr]

lemma assigned_cost {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω)
    (p : Fin N → ℝ) (J : Finset (Fin N)) (r : Fin N → Fin N) (hr : ∀ i,r i∉J) :
    transportCost c ω J (fun i j=>if r i=j then p i else 0) = ∑ i,p i*c (ω i) (ω (r i)) := by
  simp [transportCost,mul_ite,hr,mul_comm]

def selector {N : ℕ} (J : Finset (Fin N)) (jsel : Fin N → Fin N) : Fin N → Fin N :=
  fun i => if i∈J then jsel i else i

lemma selector_kept {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω)
    (J : Finset (Fin N)) (jsel : Fin N → Fin N) (hs : IsArgminSelector c ω J jsel) :
    ∀ i,selector J jsel i∉J := by
  intro i
  by_cases hi : i∈J
  · simpa [selector,hi] using (hs i hi).1
  · simpa [selector,hi] using hi

lemma assigned_eq_qbar {N : ℕ} (p : Fin N → ℝ) (J : Finset (Fin N))
    (jsel : Fin N → Fin N) (j : Fin N) (hj : j∉J) :
    assigned p (selector J jsel) j=qbar p J jsel j := by
  unfold assigned qbar
  rw [←Finset.sum_add_sum_compl J]
  have h1 : ∑ i∈J,(if selector J jsel i=j then p i else 0) = ∑ i∈J with jsel i=j,p i := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun i hi=>by simp [selector,hi])
  have h2 : ∑ i∈Jᶜ,(if selector J jsel i=j then p i else 0) = p j := by
    calc
      _ = ∑ i∈Jᶜ,if i=j then p i else 0 := Finset.sum_congr rfl (fun i hi=>by
        simp [selector,Finset.mem_compl.mp hi])
      _ = _ := by simp [hj]
  rw [h1,h2,add_comm]

lemma qbar_result {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω)
    (p : Fin N → ℝ) (hc : ∀ a b,0≤c a b) (hc0 : ∀ a,c a a=0)
    (hp : ∀ i,0≤p i) (hp1 : ∑ i,p i=1) (J : Finset (Fin N)) (hJ : Jᶜ.Nonempty)
    (jsel : Fin N → Fin N) (hs : IsArgminSelector c ω J jsel) :
    IsReducedWeight J (qbar p J jsel) ∧
      transportValue c ω p J (qbar p J jsel) ≤ ∑ i∈J,p i*minOver Jᶜ (fun j=>c (ω i) (ω j)) := by
  let r := selector J jsel
  have hr := selector_kept c ω J jsel hs
  have heq := assigned_eq_qbar p J jsel
  have hqr := assigned_reduced p hp hp1 J r hr
  have hpr := assigned_plan p hp J r hr
  have hq : IsReducedWeight J (qbar p J jsel) := by
    refine ⟨fun j hj=>?_,?_⟩
    · rw [←heq j hj]
      exact hqr.1 j hj
    · rw [←hqr.2]
      exact Finset.sum_congr rfl (fun j hj=>(heq j (Finset.mem_compl.mp hj)).symm)
  have hplan : IsTransportPlan p J (qbar p J jsel) (fun i j=>if r i=j then p i else 0) := by
    refine ⟨hpr.1,hpr.2.1,fun j hj=>?_⟩
    exact (hpr.2.2 j hj).trans (heq j hj)
  refine ⟨hq,(value_le_cost c ω hc p J _ _ hplan).trans_eq ?_⟩
  rw [assigned_cost c ω p J r hr,←Finset.sum_add_sum_compl J]
  have hzero : ∑ i∈Jᶜ,p i*c (ω i) (ω (r i))=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [r,selector,Finset.mem_compl.mp hi,hc0]
  rw [hzero,add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show r i=jsel i by simp [r,selector,hi]]
  rw [min_eq Jᶜ hJ _ (jsel i) (Finset.mem_compl.mpr (hs i hi).1)
    (fun j hj=>(hs i hi).2 j (Finset.mem_compl.mp hj))]

end ScenarioProof

open Finset
namespace CScenario

theorem greedy_injective {ι : Type*} {k : ℕ} (l : Fin k → ι)
    (hfresh : ∀ i j : Fin k,j < i → l i ≠ l j) : Function.Injective l := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with h|h
  · exact hfresh j i h hij.symm
  · exact hfresh i j h hij

theorem greedy_sum_le {ι : Type*} [DecidableEq ι] (a : ι → ℝ) (S : Finset ι)
    {k : ℕ} (l : Fin k → ι) (hmem : ∀ i,l i∈S)
    (hfresh : ∀ i j : Fin k,j < i → l i ≠ l j)
    (hmin : ∀ i : Fin k,∀ m∈S,(∀ j : Fin k,j < i → l j ≠ m) → a (l i) ≤ a m)
    (J : Finset ι) (hJ : J⊆S) (hcard : J.card=k) : (∑ i,a (l i)) ≤ ∑ j∈J,a j := by
  induction k generalizing S J with
  | zero =>
    have he : J=∅ := Finset.card_eq_zero.mp hcard
    simp [he]
  | succ k ih =>
    have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨m,hm,hfirst⟩ : ∃ m∈J,l 0∈J → m=l 0 := by
      by_cases h : l 0∈J
      · exact ⟨l 0,h,fun _=>rfl⟩
      · obtain ⟨m,hm⟩ := hJne
        exact ⟨m,hm,fun h'=>False.elim (h h')⟩
    let l' : Fin k → ι := fun i=>l i.succ
    let S' := S.erase (l 0)
    have hmem' : ∀ i,l' i∈S' := by
      intro i
      exact Finset.mem_erase.mpr ⟨hfresh i.succ 0 (Fin.succ_pos i),hmem i.succ⟩
    have hfresh' : ∀ i j : Fin k,j < i → l' i ≠ l' j := by
      intro i j hji
      exact hfresh i.succ j.succ (by simpa using hji)
    have hmin' : ∀ i : Fin k,∀ m∈S',(∀ j : Fin k,j < i → l' j ≠ m) → a (l' i) ≤ a m := by
      intro i m hm hp
      apply hmin i.succ m (Finset.mem_of_mem_erase hm)
      intro j hj
      refine Fin.cases ?_ (fun j=>?_) j hj
      · intro _
        exact (Finset.ne_of_mem_erase hm).symm
      · intro hj
        exact hp j (by simpa using hj)
    have hsub : J.erase m⊆S' := by
      intro j hj
      apply Finset.mem_erase.mpr
      constructor
      · intro he
        subst j
        have hmm := hfirst (Finset.mem_of_mem_erase hj)
        exact (Finset.ne_of_mem_erase hj) hmm.symm
      · exact hJ (Finset.mem_of_mem_erase hj)
    have hcard' : (J.erase m).card=k := by rw [Finset.card_erase_of_mem hm,hcard];omega
    have htail := ih S' l' hmem' hfresh' hmin' (J.erase m) hsub hcard'
    have hhead : a (l 0) ≤ a m := hmin 0 m (hJ hm) (fun j hj=>False.elim (Fin.not_lt_zero j hj))
    rw [Fin.sum_univ_succ,←Finset.add_sum_erase J a hm]
    exact add_le_add hhead htail

theorem greedy_smallest {N k : ℕ} (a : Fin N → ℝ) (l : Fin k → Fin N)
    (hfresh : ∀ i j : Fin k,j < i → l i ≠ l j)
    (hmin : ∀ i : Fin k,∀ m : Fin N,(∀ j : Fin k,j < i → l j ≠ m) → a (l i) ≤ a m) :
    Function.Injective l ∧ (Finset.univ.image l).card=k ∧
      ∀ J : Finset (Fin N),J.card=k → (∑ i,a (l i)) ≤ ∑ j∈J,a j := by
  have hinj := greedy_injective l hfresh
  refine ⟨hinj,?_,?_⟩
  · rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_fin]
  · intro J hJ
    exact greedy_sum_le a Finset.univ l (fun _=>Finset.mem_univ _) hfresh
      (fun i m _=>hmin i m) J (Finset.subset_univ _) hJ

end CScenario
namespace ScenarioProof
open Finset ScenarioReduction.Redistribution

lemma weights_formula {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω)
    (p : Fin N → ℝ) (hc : ∀ a b,0≤c a b) (hc0 : ∀ a,c a a=0)
    (hp : ∀ i,0≤p i) (hp1 : ∑ i,p i=1) (J : Finset (Fin N)) (hJ : Jᶜ.Nonempty) :
    optWeightsValue c ω p J=∑ i∈J,p i*minOver Jᶜ (fun j=>c (ω i) (ω j)) := by
  classical
  have hs : ∀ i:Fin N,∃ j∈Jᶜ,∀ j'∈Jᶜ,c (ω i) (ω j)≤c (ω i) (ω j') :=
    fun i=>Finset.exists_min_image Jᶜ (fun j=>c (ω i) (ω j)) hJ
  choose r hr hm using hs
  have hsel : IsArgminSelector c ω J r := fun i _=>
    ⟨Finset.mem_compl.mp (hr i),fun j hj=>hm i j (Finset.mem_compl.mpr hj)⟩
  obtain ⟨hq,hupper⟩ := qbar_result c ω p hc hc0 hp hp1 J hJ r hsel
  have hne : {z:ℝ | ∃ q,IsReducedWeight J q ∧ z=transportValue c ω p J q}.Nonempty :=
    ⟨_,qbar p J r,hq,rfl⟩
  have hb : BddBelow {z:ℝ | ∃ q,IsReducedWeight J q ∧ z=transportValue c ω p J q} := by
    refine ⟨∑ i∈J,p i*minOver Jᶜ (fun j=>c (ω i) (ω j)),?_⟩
    rintro z ⟨q,hq,rfl⟩
    exact lower c ω hc p hp hp1 J hJ q hq
  apply le_antisymm
  · exact (csInf_le hb ⟨qbar p J r,hq,rfl⟩).trans hupper
  · apply le_csInf hne
    rintro z ⟨q,hq,rfl⟩
    exact lower c ω hc p hp hp1 J hJ q hq

lemma compl_nonempty {N k : ℕ} (J : Finset (Fin N)) (hJ : J.card=k) (hk : k<N) : Jᶜ.Nonempty := by
  apply Finset.card_pos.mp
  rw [Finset.card_compl,Fintype.card_fin,hJ]
  omega

lemma individual_lower {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω)
    (p : Fin N → ℝ) (hc : ∀ a b,0≤c a b) (hc0 : ∀ a,c a a=0)
    (hp : ∀ i,0≤p i) (hp1 : ∑ i,p i=1) (J : Finset (Fin N)) (hJ : Jᶜ.Nonempty) :
    (∑ i∈J,p i*minOver {i}ᶜ (fun j=>c (ω i) (ω j)))≤optWeightsValue c ω p J := by
  rw [weights_formula c ω p hc hc0 hp hp1 J hJ]
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (hp i)
  have hsub : Jᶜ⊆({i}:Finset (Fin N))ᶜ := by
    intro j hj
    simp only [Finset.mem_compl,Finset.mem_singleton]
    intro he
    subst j
    exact (Finset.mem_compl.mp hj) hi
  have hne := hJ.mono hsub
  conv_rhs => rw [minOver,dif_pos hJ]
  apply Finset.le_inf' hJ
  intro j hj
  exact min_le {i}ᶜ hne _ j (hsub hj)

end ScenarioProof
namespace ScenarioReduction.Redistribution

theorem _root_.solution {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω) (p : Fin N → ℝ)
    (hc : ∀ a b : Ω, 0 ≤ c a b) (hc1 : ∀ a b : Ω, c a b = 0 ↔ a = b)
    (hc2 : ∀ a b : Ω, c a b = c b a)
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1)
    (k : ℕ) (hk1 : 1 ≤ k) (hkN : k < N)
    (l : Fin k → Fin N)
    (hl : ∀ i : Fin k, l i ∉ (univ.filter (fun i' => i' < i)).image l ∧
      ∀ m ∉ (univ.filter (fun i' => i' < i)).image l,
        p (l i) * minOver {l i}ᶜ (fun j => c (ω (l i)) (ω j)) ≤ p m * minOver {m}ᶜ (fun j => c (ω m) (ω j)))
    (u : Fin (N - k) → Fin N)
    (hu : ∀ j : Fin (N - k), u j ∉ (univ.filter (fun j' => j' < j)).image u ∧
      ∀ m ∉ (univ.filter (fun j' => j' < j)).image u,
        ∑ i ∈ (insert (u j) ((univ.filter (fun j' => j' < j)).image u))ᶜ,
            p i * minOver (insert (u j) ((univ.filter (fun j' => j' < j)).image u)) (fun l' => c (ω l') (ω i))
          ≤ ∑ i ∈ (insert m ((univ.filter (fun j' => j' < j)).image u))ᶜ,
            p i * minOver (insert m ((univ.filter (fun j' => j' < j)).image u)) (fun l' => c (ω l') (ω i))) :
    ∑ i : Fin k, p (l i) * minOver {l i}ᶜ (fun j => c (ω (l i)) (ω j)) ≤ optimalDeletionValue c ω p k ∧
      optimalDeletionValue c ω p k ≤
        ∑ i ∈ (univ.image u)ᶜ, p i * minOver (univ.image u) (fun j => c (ω i) (ω j)) ∧
      ((∀ i : Fin k, ∃ j : Fin N, j ≠ l i ∧ (∀ i' : Fin k, i' ≠ i → j ≠ l i') ∧
          ∀ j' : Fin N, j' ≠ l i → c (ω (l i)) (ω j) ≤ c (ω (l i)) (ω j')) →
        (univ.image l).card = k ∧ optWeightsValue c ω p (univ.image l) = optimalDeletionValue c ω p k) := by
  classical
  let a : Fin N → ℝ := fun i=>p i*minOver {i}ᶜ (fun j=>c (ω i) (ω j))
  have hp0 : ∀ i,0≤p i := fun i=>(hp i).le
  have hc0 : ∀ b,c b b=0 := fun b=>(hc1 b b).mpr rfl
  have hfresh : ∀ i j:Fin k,j < i → l i≠l j := by
    intro i j hji he
    apply (hl i).1
    exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ j,hji⟩,he.symm⟩
  have hmin : ∀ i:Fin k,∀ m:Fin N,(∀ j:Fin k,j < i → l j≠m) → a (l i)≤a m := by
    intro i m hm
    apply (hl i).2
    rintro hh
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hh
    exact hm j (Finset.mem_filter.mp hj).2 he
  obtain ⟨hinj,hcard,hgreedy⟩ := CScenario.greedy_smallest a l hfresh hmin
  have hufresh : ∀ i j:Fin (N-k),j < i → u i≠u j := by
    intro i j hji he
    apply (hu i).1
    exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ j,hji⟩,he.symm⟩
  have huinj := CScenario.greedy_injective u hufresh
  have hucard : (univ.image u).card=N-k := by
    rw [Finset.card_image_of_injective _ huinj,Finset.card_univ,Fintype.card_fin]
  have hJu : ((univ.image u)ᶜ).card=k := by
    rw [Finset.card_compl,Fintype.card_fin,hucard]
    omega
  have hne : {z:ℝ | ∃ J:Finset (Fin N),J.card=k ∧ z=optWeightsValue c ω p J}.Nonempty :=
    ⟨_,univ.image l,hcard,rfl⟩
  have hlowerJ : ∀ J:Finset (Fin N),J.card=k → (∑ i,a (l i))≤optWeightsValue c ω p J := by
    intro J hJ
    exact (hgreedy J hJ).trans (ScenarioProof.individual_lower c ω p hc hc0 hp0 hp1 J
      (ScenarioProof.compl_nonempty J hJ hkN))
  have hlower : (∑ i,a (l i))≤optimalDeletionValue c ω p k := by
    apply le_csInf hne
    rintro z ⟨J,hJ,rfl⟩
    exact hlowerJ J hJ
  have hb : BddBelow {z:ℝ | ∃ J:Finset (Fin N),J.card=k ∧ z=optWeightsValue c ω p J} := by
    refine ⟨∑ i,a (l i),?_⟩
    rintro z ⟨J,hJ,rfl⟩
    exact hlowerJ J hJ
  have hupperJ : ∀ J:Finset (Fin N),J.card=k → optimalDeletionValue c ω p k≤optWeightsValue c ω p J := by
    intro J hJ
    exact csInf_le hb ⟨J,hJ,rfl⟩
  refine ⟨hlower,?_,?_⟩
  · have hh := hupperJ (univ.image u)ᶜ hJu
    rw [ScenarioProof.weights_formula c ω p hc hc0 hp0 hp1 _
      (ScenarioProof.compl_nonempty _ hJu hkN),compl_compl] at hh
    exact hh
  · intro hnear
    refine ⟨hcard,le_antisymm ?_ (hupperJ _ hcard)⟩
    apply le_trans _ hlower
    rw [ScenarioProof.weights_formula c ω p hc hc0 hp0 hp1 _
      (ScenarioProof.compl_nonempty _ hcard hkN)]
    rw [Finset.sum_image (fun i _ j _ he=>hinj he)]
    apply Finset.sum_le_sum
    intro i _
    obtain ⟨j,hji,hjother,hjm⟩ := hnear i
    have hj : j∉univ.image l := by
      rintro hh
      obtain ⟨i',_,he⟩ := Finset.mem_image.mp hh
      by_cases hi' : i'=i
      · subst i'
        exact hji he.symm
      · exact hjother i' hi' he.symm
    have hjc := Finset.mem_compl.mpr hj
    have hjone : j∈({l i}:Finset (Fin N))ᶜ := by simpa using hji
    have hm1 := ScenarioProof.min_eq (univ.image l)ᶜ ⟨j,hjc⟩
      (fun j'=>c (ω (l i)) (ω j')) j hjc (fun j' hj'=>hjm j' (by
        intro he;subst j'
        exact (Finset.mem_compl.mp hj') (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)))
    have hm2 := ScenarioProof.min_eq {l i}ᶜ ⟨j,hjone⟩
      (fun j'=>c (ω (l i)) (ω j')) j hjone (fun j' hj'=>hjm j' (by simpa using hj'))
    change p (l i)*minOver (univ.image l)ᶜ (fun j'=>c (ω (l i)) (ω j'))≤
      p (l i)*minOver {l i}ᶜ (fun j'=>c (ω (l i)) (ω j'))
    rw [hm1,hm2]


end ScenarioReduction.Redistribution