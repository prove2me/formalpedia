-- Prove2me | solution 1 for SennottDP.DiscountedASM.tabooProb_tendsto_stepProb
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T16:47:43.845933+00:00
-- url     : https://prove2.me/submissions/9533fa79-ab90-4ba6-b3aa-03f950605f79

import Mathlib
import Definitions.Def_SennottDP_DiscountedASM_MDC
import Definitions.Def_SennottDP_DiscountedASM_ApproxSeq
import Definitions.Def_SennottDP_DiscountedASM_tabooProb

open scoped ENNReal NNReal
open Classical Filter Topology

namespace SennottDP.DiscountedASM.TabooAux

open SennottDP.DiscountedASM

theorem tsum_iSup_mono {S : Type} (g : ℕ → S → ℝ≥0∞) (hg : ∀ k, Monotone (fun N => g N k)) :
    (⨆ N, ∑' k, g N k) = ∑' k, ⨆ N, g N k := by
  rw [ENNReal.tsum_eq_iSup_sum]
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  rw [iSup_comm]
  congr 1
  funext s
  exact (ENNReal.finsetSum_iSup_of_monotone (f := fun k N => g N k) hg).symm

theorem key {S Act : Type} (M : MDC S Act) (Δs : ApproxSeq M) (e : S → Act) (t : ℕ) :
    ∀ i j, Monotone (fun N => M.tabooProb (Δs.SN (N + Δs.N0)) e (t + 1) i j) ∧
      (⨆ N, M.tabooProb (Δs.SN (N + Δs.N0)) e (t + 1) i j) = M.stepProb e (t + 1) i j := by
  induction t with
  | zero =>
    intro i j
    refine ⟨fun _ _ _ => le_rfl, ?_⟩
    simp only [MDC.tabooProb, MDC.stepProb, ciSup_const]
    rw [tsum_eq_single j]
    · simp
    · intro k hk; simp [hk]
  | succ t ih =>
    intro i j
    have hmonoT : ∀ k, Monotone (fun N =>
        (if k ∈ Δs.SN (N + Δs.N0) then
          M.P i (e i) k * M.tabooProb (Δs.SN (N + Δs.N0)) e (t + 1) k j else 0)) := by
      intro k a b hab
      have hsub : Δs.SN (a + Δs.N0) ⊆ Δs.SN (b + Δs.N0) :=
        Δs.SN_mono _ _ (by omega) (by omega)
      dsimp only
      by_cases ha : k ∈ Δs.SN (a + Δs.N0)
      · rw [if_pos ha, if_pos (hsub ha)]
        gcongr
        exact (ih k j).1 hab
      · rw [if_neg ha]; exact zero_le
    have heq : ∀ N, M.tabooProb (Δs.SN (N + Δs.N0)) e (t + 1 + 1) i j =
        ∑' k, (if k ∈ Δs.SN (N + Δs.N0) then
          M.P i (e i) k * M.tabooProb (Δs.SN (N + Δs.N0)) e (t + 1) k j else 0) := by
      intro N; rfl
    refine ⟨?_, ?_⟩
    · intro a b hab
      simp only [heq]
      exact ENNReal.tsum_le_tsum (fun k => hmonoT k hab)
    · simp only [heq]
      rw [tsum_iSup_mono _ hmonoT]
      show _ = ∑' k, M.P i (e i) k * M.stepProb e (t + 1) k j
      congr 1
      funext k
      apply le_antisymm
      · apply iSup_le
        intro N
        split_ifs
        · rw [← (ih k j).2]
          gcongr
          exact le_iSup (fun N => M.tabooProb (Δs.SN (N + Δs.N0)) e (t + 1) k j) N
        · exact zero_le
      · obtain ⟨N1, hN1, hk⟩ := Δs.SN_cover k
        rw [← (ih k j).2, ENNReal.mul_iSup]
        apply iSup_le
        intro N
        have hkm : k ∈ Δs.SN (max N (N1 - Δs.N0) + Δs.N0) :=
          Δs.SN_mono _ _ hN1 (by omega) hk
        refine le_trans ?_ (le_iSup _ (max N (N1 - Δs.N0)))
        rw [if_pos hkm]
        gcongr
        exact (ih k j).1 (le_max_left _ _)

end SennottDP.DiscountedASM.TabooAux

open Classical Filter Topology SennottDP.DiscountedASM in
theorem solution {S Act : Type} [Countable S] (M : MDC S Act)
    (Δs : ApproxSeq M) (e : S → Act) (he : ∀ i, e i ∈ M.A i) (i j : S) (t : ℕ) (ht : 1 ≤ t) :
    Tendsto (fun N => M.tabooProb (Δs.SN N) e t i j) atTop (𝓝 (M.stepProb e t i j)) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [← Filter.tendsto_add_atTop_iff_nat Δs.N0]
  have h := SennottDP.DiscountedASM.TabooAux.key M Δs e s i j
  rw [← h.2]
  exact tendsto_atTop_iSup h.1
