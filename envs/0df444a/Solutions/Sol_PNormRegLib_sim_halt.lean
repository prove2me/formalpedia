-- Prove2me | solution 1 for PNormRegLib.sim_halt
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-15T08:41:51.545943+00:00
-- url     : https://prove2.me/submissions/5873023e-4264-48cb-957e-72846cab4763

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_PNormRegLib_Simulation

open PNormReg PNormRegLib SmaleNinth

theorem solution (p : RelocParams) (F : Frame) (ω : ℕ → Bool) (r v : State)
    (hA : Agree p F r v) :
    Agree p F (exec ω (p.pair .halt).2 (exec ω (p.pair .halt).1 r))
        (exec (fun i => ω (i + F.k)) .halt v) ∧
      (exec ω (p.pair .halt).2 (exec ω (p.pair .halt).1 r)).core.pc = p.exit ∧
      (exec ω (p.pair .halt).2 (exec ω (p.pair .halt).1 r)).halted = r.halted ∧
      (exec (fun i => ω (i + F.k)) .halt v).halted = true := by
  obtain ⟨⟨rpc, rr, rp, rm⟩, ri, rc, rh, rw⟩ := r
  obtain ⟨⟨vpc, vr, vp, vm⟩, vi, vc, vh, vw⟩ := v
  obtain ⟨hR, hQ, hB0, hM, hI, hMo, hIo, hC, hW⟩ := hA
  simp only at hR hQ hB0 hM hI hMo hIo hC hW
  simp only [RelocParams.pair, RelocParams.noop, exec, coreExec, Function.update_eq_self, le_refl,
    if_true, Agree]
  exact ⟨⟨hR, hQ, hB0, hM, hI, hMo, hIo, hC, by omega⟩, by simp, by simp, by simp⟩
