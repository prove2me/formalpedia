-- Prove2me | solution 1 for P2M_Mdp_abs_sup__sub_sup__le_dbc2ecd51cdd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:22:05.863781+00:00
-- url     : https://prove2.me/submissions/690d7c15-bb24-4a5d-996a-70d26d43a527

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
import Definitions.Def_Mdp_Basic

set_option autoImplicit true
open Mdp
namespace Mdp
theorem _root_.solution {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f g : ι → ℝ) (c : ℝ)
    (h : ∀ a ∈ s, |f a - g a| ≤ c) :
    |s.sup' hs f - s.sup' hs g| ≤ c := by
  have hfg : s.sup' hs f ≤ s.sup' hs g + c := by
    apply Finset.sup'_le
    intro a ha
    have hc := (abs_sub_le_iff.mp (h a ha)).1
    have hle := Finset.le_sup' g ha
    linarith
  have hgf : s.sup' hs g ≤ s.sup' hs f + c := by
    apply Finset.sup'_le
    intro a ha
    have hc := (abs_sub_le_iff.mp (h a ha)).2
    have hle := Finset.le_sup' f ha
    linarith
  rw [abs_sub_le_iff]
  constructor <;> linarith
end Mdp
