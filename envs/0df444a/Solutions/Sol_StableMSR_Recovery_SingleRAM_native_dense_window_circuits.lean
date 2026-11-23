-- Prove2me | solution 1 for StableMSR.Recovery.SingleRAM.native_dense_window_circuits
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:34:31.589122+00:00
-- url     : https://prove2.me/submissions/89182c3f-4369-440a-aee0-b7cb0b9cb7f0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_StableMSR_DenseGlobalAssembly
import Theorems.Thm_StableMSR_Recovery_SingleRAM_global_assembly_regional_language
import Theorems.Thm_StableMSR_Recovery_SingleCodes_regional_circuit_language_correct
import Theorems.Thm_StableMSR_Recovery_SingleRAM_native_global_assembly_writer

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 15000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleCodes
open StableMSR.Recovery.WindowProfiles (piece keys)
open StableMSR.Recovery.SingleWindows
open StableMSR.Recovery.SingleRAM

theorem solution : ∃ c D b : ℕ, 0 < c ∧ 0 < b ∧
    ∀ e : ℚ, 0 < e → e < 1 → ∃ cmd : Cmd, SingleRAM.denseSpec e c D b cmd := by
  obtain ⟨c, D, b, hc, hb, hwriter⟩ := native_global_assembly_writer
  refine ⟨c, D, b, hc, hb, ?_⟩
  intro e he hel
  obtain ⟨cmd, hcmd⟩ := hwriter e he hel
  refine ⟨cmd, ?_⟩
  intro x s hk hkn hmetric hready
  obtain ⟨t, z, H, hexec, hz, hH, hy, hmem, hspace, hinput⟩ := hcmd x s hk hkn hmetric hready
  let a := globalAssembly x (budget (e:ℝ)) (widthBound (e:ℝ))
  refine ⟨t, z, H, hexec, hz, hH, hy, hmem, a.gates, a.roots, hspace, hinput, ?_⟩
  apply global_assembly_regional_language x e (by omega)
  intro u hu i hi hkeys hscale
  exact regional_circuit_language_correct x (budget (e:ℝ)) (widthBound (e:ℝ)) u i
