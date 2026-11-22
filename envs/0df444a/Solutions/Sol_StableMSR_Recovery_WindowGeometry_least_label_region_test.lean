-- Prove2me | solution 1 for StableMSR.Recovery.WindowGeometry.least_label_region_test
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T23:34:17.799637+00:00
-- url     : https://prove2.me/submissions/c017d035-91b6-4865-b74e-922d05619859

import Definitions.Def_StableMSR_SceneRegionAtlas
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowJoins
open StableMSR.Recovery.WindowProfiles (piece index keys Owned subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Word field weight legalize Writes)
open StableMSR.Recovery.WindowPorts
open StableMSR.Recovery.WindowGeometry
theorem solution (x : World) (u i : ℕ) (p : Point x.n) : canonical x u i p.val ↔ p∈piece x u i := by
  classical
  let F:=WindowProfiles.fibre x u p;let a:=WindowProfiles.rep x u p
  have mem : a∈F:=Finset.min'_mem ..
  have least (v : Point x.n) (hv : v∈F) : a≤ v:=F.min'_le v hv 
  have same (v : Point x.n) : v∈F ↔ color x u v.val=color x u p.val:=by
    change (v∈Finset.univ.filter (fun b : Point x.n=>label x u b=label x u p)) ↔ _
    rw [Finset.mem_filter];simp only [Finset.mem_univ,true_and];rfl
  change _ ↔ p∈Finset.univ.filter (fun v=>(WindowProfiles.rep x u v).val=i)
  rw [Finset.mem_filter];simp only [Finset.mem_univ,true_and]
  change canonical x u i p.val ↔ a.val=i
  constructor
  · rintro ⟨hi,eq,small⟩;let v : Point x.n:=⟨i,hi⟩
    have av : a.val≤ i:=least v ((same v).mpr eq)
    by_contra ne;exact small a.val a.isLt (by omega) ((same a).mp mem)
  · intro eq;rw [←eq];refine ⟨a.isLt,(same a).mp mem,?_⟩
    intro j jn ja e;let v : Point x.n:=⟨j,jn⟩
    have low:a.val≤ j:=least v ((same v).mpr e);omega
