-- Prove2me | solution 1 for SteinerShortcuts.Main.claim_3_8
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:33:16.040755+00:00
-- url     : https://prove2.me/submissions/2d6144f1-481f-444b-9c41-a427dc8508ee

import Theorems.Thm_SteinerShortcuts_Main_claim_3_2
import Theorems.Thm_SteinerShortcuts_Main_claim_3_3
import Theorems.Thm_SteinerShortcuts_Main_claim_3_6
import Theorems.Thm_SteinerShortcuts_Main_claim_3_7

open SteinerShortcuts.Main

private theorem reaches_route {V : Type} (G : Digraph V) (u v : V) (h : Reaches G u v) :
    ∃ R : Route V, IsPath G R ∧ R.start = u ∧ R.finish = v := by
  obtain ⟨l,hl,hend⟩ := List.exists_isChain_cons_of_relationReflTransGen h
  refine ⟨⟨u,l⟩,hl,rfl,?_⟩
  change l.getLastD u = v
  simpa only [List.getLast_eq_getLastD] using hend

 theorem solution (L q : ℕ) (h : Admissible L q) (P Q : CriticalData q)
    (hp : P.Valid L) (hq : Q.Valid L)
    (hc : CompatiblePair (construction L q) (P.route L) (Q.route L))
    (R : Route Point) (hr : IsCrossPath (construction L q) (P.route L) (Q.route L) R) :
    Splices (P.route L) (Q.route L) R := by
  obtain ⟨T,hT,hTs,hTt⟩ := reaches_route _ _ _ hc.2
  have hs : PairSetup L q P Q R T := ⟨hp,hq,hc,hr,hT,hTs,hTt⟩
  have hq1 := (claim_3_3 L q h P Q R T hs).1
  have hq2 := claim_3_6 L q h P Q R T hs
  have hq3 := claim_3_7 L q h P Q R T hs
  exact claim_3_2 L q h P Q R T hs hq1 ⟨fun ha => (hq2.1 ha).1,fun hb => (hq2.2 hb).1⟩ hq3
