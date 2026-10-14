-- Prove2me | solution 1 for UnrelatedSched.ThreeHalves.matching_gives_makespan_two
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:59:00.322492+00:00
-- url     : https://prove2.me/submissions/5de6d979-9fb9-4b00-b7b3-a867f2f76f95

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_ThreeHalves_ThreeDimMatching
import Definitions.Def_UnrelatedSched_ThreeHalves_Theorem5Instance

open MatousekLP.Scheduling


namespace UnrelatedSched.ThreeHalves

lemma sum_typeCount {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) :
    ∑ j : Fin n, typeCount T j = m := by
  unfold typeCount
  rw [← Finset.card_eq_sum_card_fiberwise (f := fun i : Fin m => (T i).1) (s := Finset.univ)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  simp

lemma sum_succ_eq {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) :
    ∑ j : Fin n, (typeCount T j - 1 + 1) = (∑ j : Fin n, (typeCount T j - 1)) + n := by
  simp [Finset.sum_add_distrib]

lemma m_le {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) :
    m ≤ (∑ j : Fin n, (typeCount T j - 1)) + n := by
  calc m = ∑ j : Fin n, typeCount T j := (sum_typeCount T).symm
    _ ≤ ∑ j : Fin n, (typeCount T j - 1 + 1) := Finset.sum_le_sum (fun j _ => by omega)
    _ = _ := sum_succ_eq T

lemma m_lt {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (j0 : Fin n) (h : typeCount T j0 = 0) :
    m < (∑ j : Fin n, (typeCount T j - 1)) + n := by
  calc m = ∑ j : Fin n, typeCount T j := (sum_typeCount T).symm
    _ < ∑ j : Fin n, (typeCount T j - 1 + 1) :=
        Finset.sum_lt_sum (fun j _ => by omega) ⟨j0, Finset.mem_univ _, by omega⟩
    _ = _ := sum_succ_eq T

theorem dummy_count_core {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n)
    (hT : ∀ j : Fin n, 1 ≤ typeCount T j) :
    (∑ j : Fin n, (typeCount T j - 1)) + n = m := by
  calc _ = ∑ j : Fin n, (typeCount T j - 1 + 1) := (sum_succ_eq T).symm
    _ = ∑ j : Fin n, typeCount T j := Finset.sum_congr rfl (fun j _ => by have := hT j; omega)
    _ = m := sum_typeCount T

lemma load_eq {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (σ' : Job T → Fin m) (i : Fin m) :
    load (fun i r => (P T i r : ℝ)) (fun r => σ' ((jobEnum T).symm r)) i
      = ∑ x ∈ Finset.univ.filter (fun x => σ' x = i), (procTime T i x : ℝ) := by
  unfold load
  refine Finset.sum_equiv (jobEnum T).symm ?_ ?_
  · intro r; simp
  · intro r hr; simp [P]

lemma makespan_le_iff {m k : ℕ} (d : Matrix (Fin m) (Fin k) ℝ) (σ : Fin k → Fin m) :
    makespan d σ ≤ 2 ↔ ∀ i, load d σ i ≤ 2 := by
  unfold makespan
  constructor
  · intro h i; exact le_trans (le_ciSup (f := fun i => load d σ i) (Set.finite_range _).bddAbove i) h
  · intro h; exact Real.iSup_le h (by norm_num)

lemma makespan_iff_job {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (σ : Fin (numJobs T) → Fin m) :
    makespan (fun i r => (P T i r : ℝ)) σ ≤ 2 ↔
      ∀ i, ∑ x ∈ Finset.univ.filter (fun x => (σ (jobEnum T x)) = i), (procTime T i x : ℝ) ≤ 2 := by
  refine Iff.trans (makespan_le_iff (fun i r => (P T i r : ℝ)) σ) ?_
  have : ∀ i, load (fun i r => (P T i r : ℝ)) σ i
      = ∑ x ∈ Finset.univ.filter (fun x => (σ (jobEnum T x)) = i), (procTime T i x : ℝ) := by
    intro i
    have h := load_eq T (fun x => σ (jobEnum T x)) i
    simpa using h
  simp only [this]

lemma exists_sched {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (σ' : Job T → Fin m)
    (hs : ∀ i, ∑ x ∈ Finset.univ.filter (fun x => σ' x = i), (procTime T i x : ℝ) ≤ 2) :
    ∃ σ : Fin (numJobs T) → Fin m, makespan (fun i r => (P T i r : ℝ)) σ ≤ 2 := by
  refine ⟨fun r => σ' ((jobEnum T).symm r), ?_⟩
  refine (makespan_le_iff (fun i r => (P T i r : ℝ)) _).2 ?_
  intro i
  rw [load_eq]
  exact hs i

lemma procTime_pos {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (i : Fin m) (x : Job T) :
    1 ≤ procTime T i x := by
  rcases x with k | l | ⟨j, r⟩ <;> simp only [procTime] <;> split_ifs <;> omega

lemma procTime_dummy {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (i : Fin m)
    (y : Σ j : Fin n, Fin (typeCount T j - 1)) :
    2 ≤ procTime T i (Sum.inr (Sum.inr y)) := by
  obtain ⟨j, r⟩ := y
  simp only [procTime]; split_ifs <;> omega

lemma matching_core {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (hT : HasMatching T) :
    ∃ σ' : Job T → Fin m, ∀ i,
      ∑ x ∈ Finset.univ.filter (fun x => σ' x = i), (procTime T i x : ℝ) ≤ 2 := by
  obtain ⟨F', hcard, ha, hb, hc⟩ := hT
  have hinj : Set.InjOn (fun i => (T i).1) (F' : Set (Fin m)) := by
    rw [← Finset.card_image_iff]
    have : F'.image (fun i => (T i).1) = Finset.univ := by
      ext j; simp only [Finset.mem_image, Finset.mem_univ, iff_true]
      obtain ⟨i, hi, hij⟩ := ha j
      exact ⟨i, hi, hij⟩
    rw [this]; simp [hcard]
  choose fa hfaF hfa using ha
  choose fb hfbF hfb using hb
  choose fc hfcF hfc using hc
  have hE : ∀ j : Fin n, ∃ e : Fin (typeCount T j - 1) → Fin m, Function.Injective e ∧
      ∀ r, (T (e r)).1 = j ∧ e r ∉ F' := by
    intro j
    set S := (Finset.univ.filter (fun i : Fin m => (T i).1 = j)).erase (fa j) with hS
    have hcS : S.card = typeCount T j - 1 := by
      rw [hS, Finset.card_erase_of_mem (by simp [hfa])]; rfl
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
      (α := Fin (typeCount T j - 1)) (β := S) (by simp [hcS])
    refine ⟨fun r => (f r).1, ?_, ?_⟩
    · intro a b hab; exact f.injective (Subtype.ext hab)
    · intro r
      have hm : (f r).1 ∈ (Finset.univ.filter (fun i : Fin m => (T i).1 = j)).erase (fa j) := (f r).2
      rw [Finset.mem_erase, Finset.mem_filter] at hm
      refine ⟨hm.2.2, fun hF => hm.1 ?_⟩
      exact hinj hF (hfaF j) (by simp [hm.2.2, hfa])
  choose e he1 he2 using hE
  refine ⟨fun x => Sum.elim fb (Sum.elim fc (fun y => e y.1 y.2)) x, ?_⟩
  intro i
  by_cases hi : i ∈ F'
  · have hsub : Finset.univ.filter (fun x : Job T =>
        Sum.elim fb (Sum.elim fc (fun y => e y.1 y.2)) x = i)
        ⊆ {Sum.inl (T i).2.1, Sum.inr (Sum.inl (T i).2.2)} := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rcases x with k | l | ⟨j, r⟩
      · have := hfb k; simp only [Sum.elim_inl] at hx
        rw [hx.2] at this; simp [this]
      · have := hfc l; simp only [Sum.elim_inr, Sum.elim_inl] at hx
        rw [hx.2] at this; simp [this]
      · simp only [Sum.elim_inr] at hx
        exact absurd (hx.2 ▸ hi) ((he2 j r).2)
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)) ?_
    rw [Finset.sum_pair (by simp)]
    simp [procTime]
    norm_num
  · by_cases hex : ∃ x : Job T, Sum.elim fb (Sum.elim fc (fun y => e y.1 y.2)) x = i
    · obtain ⟨x0, hx0⟩ := hex
      rcases x0 with k | l | ⟨j0, r0⟩
      · exact absurd (by simpa using hx0 ▸ hfbF k) hi
      · exact absurd (by simpa using hx0 ▸ hfcF l) hi
      · simp only [Sum.elim_inr] at hx0
        have hj0 : (T i).1 = j0 := hx0 ▸ (he2 j0 r0).1
        have hsub : Finset.univ.filter (fun x : Job T =>
            Sum.elim fb (Sum.elim fc (fun y => e y.1 y.2)) x = i)
            ⊆ {Sum.inr (Sum.inr ⟨j0, r0⟩)} := by
          intro x hx
          rw [Finset.mem_filter] at hx
          rcases x with k | l | ⟨j, r⟩
          · exact absurd (by simpa using hx.2 ▸ hfbF k) hi
          · exact absurd (by simpa using hx.2 ▸ hfcF l) hi
          · simp only [Sum.elim_inr] at hx
            have hj : (T i).1 = j := hx.2 ▸ (he2 j r).1
            obtain rfl : j = j0 := hj.symm.trans hj0
            have : r = r0 := (he1 j) (hx.2.trans hx0.symm)
            subst this; simp
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)) ?_
        simp [procTime, hj0]
    · have : Finset.univ.filter (fun x : Job T =>
          Sum.elim fb (Sum.elim fc (fun y => e y.1 y.2)) x = i) = ∅ := by
        ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        exact fun h => hex ⟨x, h⟩
      rw [this]; simp

theorem matching_gives_makespan_two_core {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n)
    (hT : HasMatching T) :
    ∃ σ : Fin (numJobs T) → Fin m, makespan (fun i r => (P T i r : ℝ)) σ ≤ 2 := by
  obtain ⟨σ', h⟩ := matching_core T hT
  exact exists_sched T σ' h

end UnrelatedSched.ThreeHalves

open UnrelatedSched.ThreeHalves


theorem solution {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n)
    (hT : HasMatching T) :
    ∃ σ : Fin (numJobs T) → Fin m, makespan (fun i r => (P T i r : ℝ)) σ ≤ 2 := by
  exact matching_gives_makespan_two_core T hT
