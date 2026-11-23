-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.cm_rssc_zero_free
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:46:03.94875+00:00
-- url     : https://prove2.me/submissions/017bcc79-765b-474b-a366-b1f36c90ed16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AFIsingKS_Matching
import Definitions.Def_AFIsingKS_toGraph
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
import Theorems.Thm_ZeroFreeRRG_Hardcore_simpleCycles
import Theorems.Thm_ZeroFreeRRG_Hardcore_rsscCond
import Theorems.Thm_ZeroFreeRRG_Hardcore_condToSimple

open scoped Classical
open Filter Topology AFIsingKS
open ZeroFreeRRG.Hardcore

/-- Configuration-model consequence of RSSC, the truncation lemma, and the local moment estimates:
on a fixed closed complex disk about a nontrivial parameter satisfying Conditions 1 and 2, the
normalized partition function is zero-free on simple configuration-model graphs with probability
tending to one. -/
theorem solution (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ)
    (ht : m.Nontrivial t) (hC1 : Condition1 m d t) (hC2 : Condition2 m d t) :
    ∃ R : ℝ, 0 < R ∧
      Tendsto (fun n => cmProb (fun M : Matching n d => IsSimpleM M →
        ∀ z ∈ Metric.closedBall (t : ℂ) R, normZ m z M ≠ 0))
        (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}) (𝓝 1) := by
  obtain ⟨R, hR, E, hE, hcond⟩ := rsscCond m hm d hd t ht hC1 hC2
  refine ⟨R, hR, condToSimple m d t R hR E (fun {n} M => ?_) hcond⟩
  exact simpleCycles M
