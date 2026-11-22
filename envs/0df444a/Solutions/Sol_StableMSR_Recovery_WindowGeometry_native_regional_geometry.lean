-- Prove2me | solution 1 for StableMSR.Recovery.WindowGeometry.native_regional_geometry
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T23:31:59.654595+00:00
-- url     : https://prove2.me/submissions/985c19cd-8fb6-455b-93b2-579d2bfe4724

import Definitions.Def_StableMSR_RegionAtlas
import Theorems.Thm_StableMSR_Recovery_WindowGeometry_regional_geometry_expressions
import Theorems.Thm_StableMSR_Recovery_WindowGeometry_regional_geometry_scan_correct
import Theorems.Thm_StableMSR_Recovery_WindowJoins_clocked_row_iteration
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
theorem solution : ∃P : Polynomial ℕ,∃cmd : Cmd,∀(x : World) (s : Store),0< x.k → 2+x.n+x.n*x.n≤ x.rows →
    Ready x s → ∃t z,Executes x.dist cmd s t z ∧ z≤ P.eval x.cap ∧
    Ready (worldOf x.k x.rows x.dist t) t ∧ Atlas x (worldOf x.k x.rows x.dist t).mem := by
  obtain ⟨f,g,j⟩:=regional_geometry_expressions
  obtain ⟨P,cmd,run⟩:=WindowJoins.clocked_row_iteration reset sweep expose f g j (by intro x;simp [reset]) (by intro x;simp [sweep])
  refine ⟨P,cmd,?_⟩;intro x s hk space ready
  obtain ⟨t,z,ex,bound,rd,h,ini,steps,post⟩:=run x s hk (by omega) ready
  exact ⟨t,z,ex,bound,rd,regional_geometry_scan_correct x hk space h (worldOf x.k x.rows x.dist t).mem ini steps post⟩
