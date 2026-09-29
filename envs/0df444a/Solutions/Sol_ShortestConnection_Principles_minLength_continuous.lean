-- Prove2me | solution 1 for ShortestConnection.Principles.minLength_continuous
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:22:16.843449+00:00
-- url     : https://prove2.me/submissions/3539acc2-4cc4-4351-9acf-f478c3d2778c

import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree
import Definitions.Def_ShortestConnection_Principles_Construction

namespace ShortestConnection.Principles

theorem aux_mlc_length_continuous {V : Type*} (F : Finset (Sym2 V)) :
    Continuous (fun w : Sym2 V → ℝ => length w F) := by
  unfold length
  exact continuous_finsetSum _ (fun e _ => continuous_apply e)

theorem aux_mlc_main {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    Continuous (fun w : Sym2 V → ℝ => minLength G w) := by
  classical
  set S : Set (Finset (Sym2 V)) := {F : Finset (Sym2 V) | IsSpanningSubtree G F} with hS
  have hfin : S.Finite := Set.toFinite S
  rcases S.eq_empty_or_nonempty with h | h
  · have : (fun w : Sym2 V → ℝ => minLength G w) = fun _ => 0 := by
      funext w
      unfold minLength
      rw [← hS, h, Set.image_empty, Real.sInf_empty]
    rw [this]
    exact continuous_const
  · have hne : hfin.toFinset.Nonempty := by
      rcases h with ⟨F, hF⟩
      exact ⟨F, hfin.mem_toFinset.2 hF⟩
    have : (fun w : Sym2 V → ℝ => minLength G w) =
        fun w => hfin.toFinset.inf' hne (fun F => length w F) := by
      funext w
      unfold minLength
      rw [Finset.inf'_eq_csInf_image, Set.Finite.coe_toFinset]
    rw [this]
    exact Continuous.finset_inf'_apply hne (fun F _ => aux_mlc_length_continuous F)

end ShortestConnection.Principles

open ShortestConnection.Principles

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) :
    Continuous (fun w : Sym2 V → ℝ => minLength G w) :=
  aux_mlc_main G
