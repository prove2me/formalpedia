-- Prove2me | solution 1 for StableMSR.Recovery.WindowCSP.greedy_anchor_covers
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-21T16:10:46.707177+00:00
-- url     : https://prove2.me/submissions/453ac777-b2d8-4fb1-aeaf-00313e7c5faa

import Definitions.Def_StableMSR_WindowCSP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.Supplement StableMSR.Recovery.RegionalSeeds StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
theorem solution {n : ℕ} (d : Point n→Point n→ℝ) (dm : IsMetricArray d)
    (W : Cluster n) (R : ℝ) (hr : 0≤ R) :
    greedyNet d R W⊆W ∧ ∀i∈W,anchor d W R i∈greedyNet d R W ∧ d (anchor d W R i) i≤2*R := by
  classical
  obtain ⟨metric,hm⟩:=dm
  letI : MetricSpace (Point n):=metric
  have sym (a b : Point n) : d a b=d b a := by simpa only [hm] using dist_comm a b
  let step (A : Cluster n) (i : Point n) := if ∀a∈A,2*R< d i a then insert i A else A
  have scan (l : List (Point n)) (A : Cluster n) :
      A⊆l.foldl step A ∧ (∀z∈l.foldl step A,z∈A ∨ z∈l) ∧
      ∀i∈l,∃a∈l.foldl step A,d a i≤2*R := by
    induction l generalizing A with
    | nil => exact ⟨fun _ a=>a,fun _ a=>Or.inl a,by simp⟩
    | cons i l ih =>
      let B:=step A i
      obtain ⟨subB,members,covers⟩:=ih B
      have keep : A⊆B := by dsimp [B,step];split <;> simp
      have added (z : Point n) (hz : z∈B) : z∈A ∨ z=i := by
        dsimp [B,step] at hz;split at hz
        · rcases Finset.mem_insert.mp hz with eq|mem
          · exact Or.inr eq
          · exact Or.inl mem
        · exact Or.inl hz
      have near : ∃a∈B,d a i≤2*R := by
        by_cases test : ∀a∈A,2*R< d i a
        · refine ⟨i,by unfold B step;rw [if_pos test];exact Finset.mem_insert_self ..,?_⟩;rw [←hm,dist_self];linarith
        · push_neg at test
          obtain ⟨a,ha,le⟩:=test
          exact ⟨a,keep ha,by rw [sym a i];exact le⟩
      refine ⟨keep.trans subB,?_,?_⟩
      · intro z hz
        rcases members z hz with prev|tail
        · rcases added z prev with inA|eq
          · exact Or.inl inA
          · exact Or.inr (List.mem_cons.mpr (Or.inl eq))
        · exact Or.inr (List.mem_cons.mpr (Or.inr tail))
      · intro z hz
        rcases List.mem_cons.mp hz with eq|h
        · subst z;obtain ⟨a,ha,le⟩:=near;exact ⟨a,subB ha,le⟩
        · exact covers z h
  obtain ⟨_,members,cov⟩:=scan (W.sort (·≤·)) ∅
  refine ⟨?_,?_⟩
  · intro a ha;simpa using members a ha
  · intro i hi
    obtain ⟨a,ha,near⟩:=cov i (by simpa using hi)
    let S:=(greedyNet d R W).filter (fun z=>d z i≤2*R)
    have hs : S.Nonempty:=⟨a,Finset.mem_filter.mpr ⟨ha,near⟩⟩
    have e : anchor d W R i=S.min' hs := dif_pos hs
    rw [e];exact Finset.mem_filter.mp (S.min'_mem hs)

