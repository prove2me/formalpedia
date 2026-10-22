-- Prove2me | solution 1 for UnitCapMCF.Excess.lemma3_dlevel_drift
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:13:22.397109+00:00
-- url     : https://prove2.me/submissions/d7f19fbd-0643-4249-b41b-da3605361dbe

import Mathlib
import Definitions.Def_UnitCapMCF_Excess_Setting

set_option autoImplicit false
open UnitCapMCF.Excess

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (N : CostScaling.Refine.Network V) (ε : ℝ) (hε : 0 < ε)
    (f' f : V → V → ℝ) (p' p : V → ℝ)
    (hf' : CostScaling.Refine.IsEpsOptimal N (2 * ε) f' p')
    (hf : CostScaling.Refine.IsEpsOptimal N ε f p)
    (v w : V) (hvw : (v, w) ∈ Eplus N f' f) :
    dlevel ε p' p v ≤ dlevel ε p' p w + 3 := by
  have hm : (v, w) ∈ N.E ∧ f v w < f' v w := by
    unfold Eplus at hvw
    simpa [Finset.mem_filter] using hvw
  obtain ⟨hE, hlt⟩ := hm
  have hEwv : (w, v) ∈ N.E := (N.symm v w).mp hE
  obtain ⟨⟨hu', hanti'⟩, hres'⟩ := hf'
  obtain ⟨⟨hu, hanti⟩, hres⟩ := hf
  have h1 : f' v w ≤ N.u v w := hu' v w hE
  have hpos : 0 < CycleCanceling.MinMean.resCap N f v w := by
    unfold CycleCanceling.MinMean.resCap; linarith
  have A := hres v w ⟨hE, hpos⟩
  have h2 : f w v ≤ N.u w v := hu w v hEwv
  have e1 : f' v w = -f' w v := hanti' v w hE
  have e2 : f v w = -f w v := hanti v w hE
  have hpos' : 0 < CycleCanceling.MinMean.resCap N f' w v := by
    unfold CycleCanceling.MinMean.resCap; linarith
  have B := hres' w v ⟨hEwv, hpos'⟩
  have hc : N.c v w = -N.c w v := N.cost_antisymm v w hE
  unfold CostScaling.Refine.reducedCost at A B
  unfold dlevel
  have key : (p v - p' v) - (p w - p' w) ≤ 3 * ε := by linarith
  have : (p v - p' v) / ε - (p w - p' w) / ε ≤ 3 := by
    rw [← sub_div, div_le_iff₀ hε]; linarith
  linarith
