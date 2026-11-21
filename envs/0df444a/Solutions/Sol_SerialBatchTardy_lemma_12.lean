-- Prove2me | solution 1 for SerialBatchTardy.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:04:28.051605+00:00
-- url     : https://prove2.me/submissions/94b689e8-f0c9-4eac-b628-0d9628cd65ac

import Definitions.Def_SerialBatchTardy_Construction
set_option autoImplicit false

namespace Aux_SerialBatchTardy_lemma_12

open SerialBatchTardy

theorem rev_len (I : Instance) : (reverseInstance I).jobs.length = I.jobs.length := by
  simp [reverseInstance]

theorem rev_job (I : Instance) (j : Fin (reverseInstance I).jobs.length) :
    (reverseInstance I).job j =
      { p := (I.job (Fin.cast (rev_len I) j)).p, w := (I.job (Fin.cast (rev_len I) j)).w,
        r := -(I.job (Fin.cast (rev_len I) j)).d, d := -(I.job (Fin.cast (rev_len I) j)).r } := by
  simp only [Instance.job, List.get_eq_getElem]
  simp [reverseInstance]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem rev_rev (I : Instance) : reverseInstance (reverseInstance I) = I := by
  rcases I with ⟨s, jobs⟩
  simp only [reverseInstance, List.map_map]
  congr 1
  conv_rhs => rw [← List.map_id jobs]
  apply List.map_congr_left
  intro j _
  cases j
  simp

theorem toFinset_map_eq {α β : Type} [DecidableEq β] (l : List α) (f : α → β) [DecidableEq α] :
    (l.map f).toFinset = l.toFinset.image f := by
  ext b
  simp

theorem forward (I : Instance) (W : ℕ)
    (h : ∃ σ : Schedule I, σ.Feasible ∧ σ.tardyWeight ≤ W) :
    ∃ σ' : Schedule (reverseInstance I), σ'.Feasible ∧ σ'.tardyWeight ≤ W := by
  obtain ⟨σ, ⟨hrel, hov⟩, hW⟩ := h
  let e : Fin (reverseInstance I).jobs.length ≃ Fin I.jobs.length := finCongr (rev_len I)
  have hje : ∀ j, (reverseInstance I).job j =
      { p := (I.job (e j)).p, w := (I.job (e j)).w, r := -(I.job (e j)).d,
        d := -(I.job (e j)).r } := fun j => rev_job I j
  have hjp : ∀ j, ((reverseInstance I).job j).p = (I.job (e j)).p := fun j => by rw [hje]
  have hjw : ∀ j, ((reverseInstance I).job j).w = (I.job (e j)).w := fun j => by rw [hje]
  have hjr : ∀ j, ((reverseInstance I).job j).r = -(I.job (e j)).d := fun j => by rw [hje]
  have hjd : ∀ j, ((reverseInstance I).job j).d = -(I.job (e j)).r := fun j => by rw [hje]
  obtain ⟨B, hB⟩ : ∃ B, B = Finset.univ.sup σ.batch + 1 := ⟨_, rfl⟩
  have hBlt : ∀ j, σ.batch j < B := fun j => by
    rw [hB]; exact Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ j))
  have hBne : ∀ j, σ.batch j ≠ B := fun j => Nat.ne_of_lt (hBlt j)
  obtain ⟨T, hT⟩ : ∃ T : ℤ, T = ∑ j, (|(I.job j).d| + |σ.start (σ.batch j)|) := ⟨_, rfl⟩
  have hTsingle : ∀ j, |(I.job j).d| + |σ.start (σ.batch j)| ≤ T := by
    intro j
    rw [hT]
    exact Finset.single_le_sum (f := fun j => |(I.job j).d| + |σ.start (σ.batch j)|)
      (fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ j)
  have hTd : ∀ j, -(I.job j).d ≤ T := by
    intro j
    have h1 := hTsingle j
    have h2 := neg_le_abs ((I.job j).d)
    have h3 := abs_nonneg (σ.start (σ.batch j))
    linarith
  have hTs : ∀ j, -σ.start (σ.batch j) ≤ T := by
    intro j
    have h1 := hTsingle j
    have h2 := neg_le_abs (σ.start (σ.batch j))
    have h3 := abs_nonneg ((I.job j).d)
    linarith
  let σ' : Schedule (reverseInstance I) :=
    ⟨fun j => if σ.IsTardy (e j) then B else σ.batch (e j),
     fun b => if b = B then T else -σ.comp b⟩
  have hb' : ∀ j, σ'.batch j = if σ.IsTardy (e j) then B else σ.batch (e j) := fun j => rfl
  have hs' : ∀ b, σ'.start b = if b = B then T else -σ.comp b := fun b => rfl
  have hbatch_ne : ∀ j b, b ≠ B →
      (σ'.batch j = b ↔ ¬σ.IsTardy (e j) ∧ σ.batch (e j) = b) := by
    intro j b hb
    rw [hb']
    by_cases ht : σ.IsTardy (e j)
    · rw [if_pos ht]
      constructor
      · intro h; exact absurd h.symm hb
      · intro h; exact absurd ht h.1
    · rw [if_neg ht]
      constructor
      · intro h; exact ⟨ht, h⟩
      · intro h; exact h.2
  have hlen : ∀ b, b ≠ B → σ'.batchLen b ≤ σ.batchLen b := by
    intro b hb
    unfold Schedule.batchLen
    have hsetup : (reverseInstance I).setup = I.setup := rfl
    rw [hsetup]
    have hsum : ∑ j ∈ σ'.batchJobs b, (((reverseInstance I).job j).p : ℤ)
        = ∑ j ∈ Finset.univ.filter (fun j => ¬σ.IsTardy j ∧ σ.batch j = b), ((I.job j).p : ℤ) := by
      apply Finset.sum_equiv e
      · intro j
        simp only [Schedule.batchJobs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hbatch_ne j b hb
      · intro j _
        rw [hjp]
    rw [hsum]
    have hsub : Finset.univ.filter (fun j => ¬σ.IsTardy j ∧ σ.batch j = b) ⊆ σ.batchJobs b := by
      intro j
      simp only [Schedule.batchJobs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun h => h.2
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => (Nat.cast_nonneg ((I.job i).p) : (0 : ℤ) ≤ ((I.job i).p : ℤ)))
    linarith
  have hcomp : ∀ b, b ≠ B → σ'.comp b ≤ -σ.start b := by
    intro b hb
    have h1 : σ'.comp b = σ'.start b + σ'.batchLen b := rfl
    have h2 : σ.comp b = σ.start b + σ.batchLen b := rfl
    have h3 : σ'.start b = -σ.comp b := by rw [hs', if_neg hb]
    have h4 := hlen b hb
    linarith
  refine ⟨σ', ⟨?_, ?_⟩, le_trans ?_ hW⟩
  · intro j
    rw [hjr, hb']
    by_cases ht : σ.IsTardy (e j)
    · rw [if_pos ht, hs', if_pos rfl]
      exact hTd (e j)
    · rw [if_neg ht, hs', if_neg (hBne (e j))]
      have h1 : ¬ (I.job (e j)).d < σ.comp (σ.batch (e j)) := ht
      have h2 := not_lt.mp h1
      linarith
  · intro b b' hu hu' hne
    obtain ⟨j, hj⟩ := hu
    obtain ⟨j', hj'⟩ := hu'
    by_cases hbB : b = B
    · have hb'B : b' ≠ B := fun h => hne (hbB.trans h.symm)
      obtain ⟨_, hj'b⟩ := (hbatch_ne j' b' hb'B).mp hj'
      right
      have h1 := hcomp b' hb'B
      have h2 := hTs (e j')
      rw [hj'b] at h2
      have h3 : σ'.start b = T := by rw [hs', if_pos hbB]
      linarith
    · by_cases hb'B : b' = B
      · obtain ⟨_, hjb⟩ := (hbatch_ne j b hbB).mp hj
        left
        have h1 := hcomp b hbB
        have h2 := hTs (e j)
        rw [hjb] at h2
        have h3 : σ'.start b' = T := by rw [hs', if_pos hb'B]
        linarith
      · obtain ⟨_, hjb⟩ := (hbatch_ne j b hbB).mp hj
        obtain ⟨_, hj'b⟩ := (hbatch_ne j' b' hb'B).mp hj'
        have hu1 : σ.Used b := ⟨e j, hjb⟩
        have hu2 : σ.Used b' := ⟨e j', hj'b⟩
        have hc1 : σ'.start b = -σ.comp b := by rw [hs', if_neg hbB]
        have hc2 : σ'.start b' = -σ.comp b' := by rw [hs', if_neg hb'B]
        have hh1 := hcomp b hbB
        have hh2 := hcomp b' hb'B
        rcases hov b b' hu1 hu2 hne with h | h
        · right
          linarith
        · left
          linarith
  · unfold Schedule.tardyWeight
    calc ∑ j, (if σ'.IsTardy j then ((reverseInstance I).job j).w else 0)
        ≤ ∑ j, (if σ.IsTardy (e j) then (I.job (e j)).w else 0) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          by_cases ht : σ.IsTardy (e j)
          · rw [if_pos ht]
            by_cases ht' : σ'.IsTardy j
            · exact le_of_eq (by rw [if_pos ht', hjw])
            · rw [if_neg ht']
              exact Nat.zero_le _
          · have hnt : ¬σ'.IsTardy j := by
              unfold Schedule.IsTardy
              rw [hjd, hb', if_neg ht]
              intro hlt
              have h1 := hcomp _ (hBne (e j))
              have h2 := hrel (e j)
              linarith
            rw [if_neg hnt, if_neg ht]
      _ = ∑ j, (if σ.IsTardy j then (I.job j).w else 0) :=
          Fintype.sum_equiv e _ _ (fun j => rfl)

end Aux_SerialBatchTardy_lemma_12

open SerialBatchTardy Aux_SerialBatchTardy_lemma_12 in
theorem solution (I : Instance) :
    numR (reverseInstance I) = numD I ∧ numD (reverseInstance I) = numR I ∧
      numP (reverseInstance I) = numP I ∧ numW (reverseInstance I) = numW I ∧
      ∀ W : ℕ, (∃ σ : Schedule I, σ.Feasible ∧ σ.tardyWeight ≤ W) ↔
        (∃ σ' : Schedule (reverseInstance I), σ'.Feasible ∧ σ'.tardyWeight ≤ W) := by
  have kr : (reverseInstance I).jobs.map Job.r = (I.jobs.map Job.d).map Neg.neg := by
    simp [reverseInstance, List.map_map, Function.comp_def]
  have kd : (reverseInstance I).jobs.map Job.d = (I.jobs.map Job.r).map Neg.neg := by
    simp [reverseInstance, List.map_map, Function.comp_def]
  have kp : (reverseInstance I).jobs.map Job.p = I.jobs.map Job.p := by
    simp [reverseInstance, List.map_map, Function.comp_def]
  have kw : (reverseInstance I).jobs.map Job.w = I.jobs.map Job.w := by
    simp [reverseInstance, List.map_map, Function.comp_def]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold numR numD
    rw [kr, toFinset_map_eq, Finset.card_image_of_injective _ neg_injective]
  · unfold numR numD
    rw [kd, toFinset_map_eq, Finset.card_image_of_injective _ neg_injective]
  · unfold numP
    rw [kp]
  · unfold numW
    rw [kw]
  · intro W
    constructor
    · exact forward I W
    · intro h
      have h2 := forward (reverseInstance I) W h
      rw [rev_rev] at h2
      exact h2
