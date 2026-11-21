-- Prove2me | solution 1 for OnlineTransportation1195.Main.root_patch_normalization_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:01:22.014903+00:00
-- url     : https://prove2.me/submissions/d756a0f3-9e41-4a38-aead-84a9edc3f0c2

import Definitions.Def_OnlineTransportation1195_Main_RedPatches
section
open scoped BigOperators
open Classical

namespace OnlineTransportation1195.Dev.Patch
open OnlineTransportation1195.Main

variable {n : ℕ} (T : Tree n)

theorem x_nonneg (L : List (Fin n)) (e : Fin n) : 0 ≤ T.x L e := by
  unfold Tree.x
  split
  · next i _ =>
    unfold Tree.downPrefix Tree.downStep
    refine Finset.sum_nonneg fun j _ => ?_
    split_ifs with h
    · exact (T.W_pos _ h.1).le
    · exact le_refl _
  · exact le_refl _

theorem patch_sub_red (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) :
    T.rootPatch d L t ⊆ T.red d L t := Finset.filter_subset _ _

theorem red_sub_edges (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) :
    T.red d L t ⊆ T.edges := Finset.filter_subset _ _

theorem small_in_patch (d : Fin n → ℝ) (L : List (Fin n)) (hD : T.Normalized d)
    (s t : ℝ) (hst : s ≤ t) (e : Fin n) (he : e ∈ T.edges) (hde : d e < s) :
    e ∈ T.rootPatch d L t := by
  have hred : ∀ a ∈ T.edges, T.IsAnc a e → a ∈ T.red d L t := by
    intro a ha hae
    have : d a ≤ d e := hD.2.1 a ha e he hae
    unfold Tree.red
    rw [Finset.mem_filter]
    refine ⟨ha, ?_⟩
    have := x_nonneg T L a
    linarith
  unfold Tree.rootPatch
  rw [Finset.mem_filter]
  refine ⟨hred e he (⟨0, rfl⟩), hred⟩

theorem iff_aux {n : ℕ} (T : Tree n) (d : Fin n → ℝ)
    (L : List (Fin n)) (hD : T.Normalized d)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    T.patchNormalization d L s t = 1 ↔ T.Rin d L t = T.F d s := by
  have hpos := hD.1
  have hsum := hD.2.2
  set P := T.rootPatch d L t with hP
  have hPE : P ⊆ T.edges := (patch_sub_red T d L t).trans (red_sub_edges T d L t)
  have hout : ∀ e ∈ T.edges \ P, s ≤ d e := by
    intro e he
    rw [Finset.mem_sdiff] at he
    by_contra h
    exact he.2 (small_in_patch T d L hD s t hst e he.1 (not_le.mp h))
  have hper : ∀ e ∈ P, s * (T.W e / min (d e) s) =
      T.W e + s * (T.W e / d e) - T.W e * min 1 (s / d e) := by
    intro e he
    have hd := hpos e (hPE he)
    rcases le_total (d e) s with h | h
    · rw [min_eq_left h, min_eq_left (by rw [le_div_iff₀ hd]; linarith)]
      field_simp; ring
    · rw [min_eq_right h, min_eq_right (by rw [div_le_iff₀ hd]; linarith)]
      field_simp; ring
  have h1 : s * T.patchNormalization d L s t =
      T.Rin d L t + s * ∑ e ∈ P, T.W e / d e - ∑ e ∈ P, T.W e * min 1 (s / d e) := by
    unfold Tree.patchNormalization Tree.Rin
    rw [← hP, Finset.mul_sum, Finset.sum_congr rfl hper, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.mul_sum]
  have h2 : ∑ e ∈ T.edges, T.W e / d e =
      ∑ e ∈ P, T.W e / d e + ∑ e ∈ T.edges \ P, T.W e / d e :=
    (Finset.sum_sdiff hPE).symm.trans (add_comm _ _)
  have h3 : T.F d s = ∑ e ∈ P, T.W e * min 1 (s / d e) + s * ∑ e ∈ T.edges \ P, T.W e / d e := by
    unfold Tree.F
    rw [← Finset.sum_sdiff hPE, add_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    have hd := hpos e (Finset.mem_sdiff.mp he).1
    rw [min_eq_right (by rw [div_le_iff₀ hd]; linarith [hout e he])]
    ring
  have hRin : T.Rin d L t = ∑ e ∈ P, T.W e := rfl
  constructor
  · intro h
    rw [h] at h1
    nlinarith
  · intro h
    have : s * T.patchNormalization d L s t = s * 1 := by
      rw [h1, hRin.symm.symm] at *
      nlinarith
    exact mul_left_cancel₀ hs.ne' this

end OnlineTransportation1195.Dev.Patch

namespace OnlineTransportation1195.Main
theorem chk_root_patch_normalization_iff {n : ℕ} (T : Tree n) (d : Fin n → ℝ)
    (L : List (Fin n)) (hD : T.Normalized d) (hDFS : T.DFS L)
    (s t : ℝ) (ht : 0 < t) (hs : 0 < s) (hst : s ≤ t) :
    T.patchNormalization d L s t = 1 ↔ T.Rin d L t = T.F d s :=
  OnlineTransportation1195.Dev.Patch.iff_aux T d L hD s t hs hst

end OnlineTransportation1195.Main
end

theorem solution : type_of% @OnlineTransportation1195.Main.chk_root_patch_normalization_iff := @OnlineTransportation1195.Main.chk_root_patch_normalization_iff
