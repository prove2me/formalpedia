-- Prove2me | solution 1 for StableMSR.Recovery.WindowPorts.native_count_expansion
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T23:21:54.801004+00:00
-- url     : https://prove2.me/submissions/38fea2c6-1c53-4f41-a904-44aeae0d4fd7

import Definitions.Def_StableMSR_WindowPortPacking
import Theorems.Thm_StableMSR_Recovery_WindowPorts_physical_port_expressions
import Theorems.Thm_StableMSR_Recovery_WindowPorts_port_packing_preserves_derivations
import Theorems.Thm_StableMSR_Recovery_FewBallRows_tabulate_ball_row_expressions
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowJoins
open StableMSR.Recovery.WindowProfiles (piece index keys Owned subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Word field weight legalize Writes)
open StableMSR.Recovery.WindowPorts
theorem solution : ∃P : Polynomial ℕ,∃cmd : Cmd,∀(x : World) (e : ℚ) (H : ℕ) (s : Store),
    1≤ x.k → x.k< x.n → let y:=worldOf x.k H x.dist s
    Ready y s → Presents x e y → ∃t z,Executes x.dist cmd s t z ∧ z≤ P.eval y.cap ∧
    Ready (worldOf x.k H x.dist t) t ∧ Encodes x e (worldOf x.k H x.dist t) := by
  obtain ⟨P,cmd,tab⟩:=FewBallRows.tabulate_ball_row_expressions WindowPorts.packed physical_port_expressions
  refine ⟨P,cmd,?_⟩
  intro x e H s hk kn;dsimp only;intro ready cert
  let y:=worldOf x.k H x.dist s
  obtain ⟨t,z,ex,bd,rt,wr⟩:=tab y s ready
  refine ⟨t,z,ex,bd,rt,?_⟩
  apply port_packing_preserves_derivations x e H y.mem (worldOf x.k H x.dist t).mem hk kn cert
  intro r hr j hj b;cases b
  · exact (wr r hr j hj).1
  · exact (wr r hr j hj).2
