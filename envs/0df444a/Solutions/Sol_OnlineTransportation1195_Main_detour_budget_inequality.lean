-- Prove2me | solution 1 for OnlineTransportation1195.Main.detour_budget_inequality
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:01:21.950657+00:00
-- url     : https://prove2.me/submissions/547d5cb8-40ad-454b-9fcb-9af1cb70cabb

import Definitions.Def_OnlineTransportation1195_Main_RedPatches
section
open scoped BigOperators
open Classical

namespace OnlineTransportation1195.Dev.Patch
open OnlineTransportation1195.Main

variable {n : ℕ} (T : Tree n)

theorem patch_sub_red (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) :
    T.rootPatch d L t ⊆ T.red d L t := Finset.filter_subset _ _

theorem detour_aux {n : ℕ} (T : Tree n) (d : Fin n → ℝ)
    (L : List (Fin n)) (hD : T.Normalized d)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t)
    (heq : T.Rin d L t = T.F d s) :
    T.R d L t ≤ T.F d t → s + T.Rout d L t ≤ t := by
  intro hle
  have hpos := hD.1
  have hsum := hD.2.2
  have hR : T.R d L t = T.Rin d L t + T.Rout d L t := by
    unfold Tree.R Tree.Rin Tree.Rout
    rw [← Finset.sum_sdiff (patch_sub_red T d L t), add_comm]
  have hdiff : T.F d t - T.F d s ≤ (t - s) * ∑ e ∈ T.edges, T.W e / d e := by
    unfold Tree.F
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun e he => ?_
    have hd := hpos e he
    have hW := T.W_pos e (by simpa [Tree.edges] using he)
    have : min 1 (t / d e) - min 1 (s / d e) ≤ (t - s) / d e := by
      rcases le_total 1 (s / d e) with h | h
      · rw [min_eq_left h, min_eq_left (h.trans (by gcongr))]; simp; positivity
      · rw [min_eq_right h]
        have := min_le_right 1 (t / d e)
        have h2 : (t - s) / d e = t / d e - s / d e := by ring
        rw [h2]; linarith
    calc T.W e * min 1 (t / d e) - T.W e * min 1 (s / d e)
        = T.W e * (min 1 (t / d e) - min 1 (s / d e)) := by ring
      _ ≤ T.W e * ((t - s) / d e) := by gcongr
      _ = (t - s) * (T.W e / d e) := by ring
  rw [hsum] at hdiff
  rw [hR, heq] at hle
  linarith

end OnlineTransportation1195.Dev.Patch

namespace OnlineTransportation1195.Main

theorem chk_detour_budget_inequality {n : ℕ} (T : Tree n) (d : Fin n → ℝ)
    (L : List (Fin n)) (hD : T.Normalized d) (hDFS : T.DFS L)
    (s t : ℝ) (ht : 0 < t) (hs : 0 < s) (hst : s ≤ t)
    (heq : T.Rin d L t = T.F d s) :
    T.R d L t ≤ T.F d t → s + T.Rout d L t ≤ t :=
  OnlineTransportation1195.Dev.Patch.detour_aux T d L hD s t hs hst heq
end OnlineTransportation1195.Main
end

theorem solution : type_of% @OnlineTransportation1195.Main.chk_detour_budget_inequality := @OnlineTransportation1195.Main.chk_detour_budget_inequality
