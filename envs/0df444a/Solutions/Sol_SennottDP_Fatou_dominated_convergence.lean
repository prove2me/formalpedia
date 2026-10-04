-- Prove2me | solution 1 for SennottDP.Fatou.dominated_convergence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:42:05.171829+00:00
-- url     : https://prove2.me/submissions/2cffd218-f938-4564-9e5b-73a32f80c9ff

import Mathlib
import Definitions.Def_SennottDP_Fatou_Basic
import Theorems.Thm_SennottDP_Fatou_generalized_dominated_convergence

open Filter Topology
open scoped ENNReal

open SennottDP.Fatou in
theorem solution {S : Type*} [Countable S] (P : S → ℝ≥0∞) (hP : ∑' j, P j = 1)
    (u w : S → ℕ → ℝ) (hdom : ∀ j N, |u j N| ≤ w j N)
    (uL wL : S → EReal)
    (hu : ∀ j, Tendsto (fun N => (u j N : EReal)) atTop (𝓝 (uL j)))
    (hw : ∀ j, Tendsto (fun N => (w j N : EReal)) atTop (𝓝 (wL j)))
    (hsum : Tendsto (fun N => wsum P (fun j => (w j N : EReal))) atTop (𝓝 (wsum P wL)))
    (hfin : wsum P wL < ⊤) :
    Tendsto (fun N => wsum P (fun j => (u j N : EReal))) atTop (𝓝 (wsum P uL)) := by
  have hA : ApproxDist P (fun _ => Set.univ) (fun _ => P) :=
    { prob := hP
      mono := fun _ _ _ => le_rfl
      iUnion_eq := Set.iUnion_const _
      prob_N := fun N => by simpa [Set.indicator_univ] using hP
      tendsto := fun j => tendsto_const_nhds }
  have h := generalized_dominated_convergence hA u w (fun N j _ => hdom j N) uL wL hu hw
    (by simpa [Set.indicator_univ] using hsum) hfin
  simpa [Set.indicator_univ] using h


