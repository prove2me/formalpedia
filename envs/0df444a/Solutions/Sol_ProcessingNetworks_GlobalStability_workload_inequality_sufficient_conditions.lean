-- Prove2me | solution 1 for ProcessingNetworks.GlobalStability.workload_inequality_sufficient_conditions
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:19:18.203104+00:00
-- url     : https://prove2.me/submissions/83c6f7b7-9895-4977-8230-8b92f0e20787

import Mathlib
import Definitions.Def_ProcessingNetworks_GlobalStability_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_GlobalStability_NonIdlingFluidModel
import Definitions.Def_ProcessingNetworks_GlobalStability_ReentrantLine

open ProcessingNetworks.GlobalStability in
theorem solution : ¬ (∀ (lam1 m1 m2 m3 m4 m5 : ℝ) (hlam1 : 0 < lam1)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hm3 : 0 < m3) (hm4 : 0 < m4) (hm5 : 0 < m5)
    (Dh Fh Th Zh : ℝ → Fin 5 → ℝ)
    (hni : IsNonIdlingSolution (reentrantLineData lam1 m1 m2 m3 m4 m5) Dh Fh Th Zh),
    (∀ x2 x4 ε : ℝ, 0 < x2 → 0 < x4 → 0 < ε →
      lam1 * (x2 + x4) + ε ≤ x2 / m2 → lam1 * (x2 + x4) + ε ≤ x4 / m4 →
      ∀ t : ℝ, 0 < t → 0 < reentrantH2 Zh t →
        ∀ d : ℝ, HasDerivAt (reentrantG2 x2 x4 Zh) d t → d ≤ -ε) ∧
    (∀ x1 x3 x5 ε : ℝ, 0 < x1 → 0 < x3 → 0 < x5 → 0 < ε →
      lam1 * (x1 + x3 + x5) + ε ≤ x1 / m1 → lam1 * (x1 + x3 + x5) + ε ≤ x3 / m3 →
      lam1 * (x1 + x3 + x5) + ε ≤ x5 / m5 →
      ∀ t : ℝ, 0 < t → 0 < reentrantH1 Zh t →
        ∀ d : ℝ, HasDerivAt (reentrantG1 x1 x3 x5 Zh) d t → d ≤ -ε) ∧
    (∀ x1 x2 x3 x4 x5 : ℝ, 0 < x1 → 0 < x2 → 0 < x3 → 0 < x4 → 0 < x5 →
      x2 + x4 ≤ x1 + x3 + x5 → x4 ≤ x3 + x5 →
      ∀ t : ℝ, 0 < t → reentrantH2 Zh t = 0 →
        reentrantG1 x1 x3 x5 Zh t ≤ reentrantG2 x2 x4 Zh t) ∧
    (∀ x1 x2 x3 x4 x5 : ℝ, 0 < x1 → 0 < x2 → 0 < x3 → 0 < x4 → 0 < x5 →
      x3 + x5 ≤ x2 + x4 → x5 ≤ x4 →
      ∀ t : ℝ, 0 < t → reentrantH1 Zh t = 0 →
        reentrantG2 x2 x4 Zh t ≤ reentrantG1 x1 x3 x5 Zh t)) := by
  intro H
  set Th : ℝ → Fin 5 → ℝ := fun s => ![max s 0, max s 0, 0, 0, 0] with hTh
  set Zh : ℝ → Fin 5 → ℝ := fun s => ![1, 0, max s 0, 0, 0] with hZh
  have hpool0 : poolBuffers (reentrantLineData 1 1 1 1 1 1) 0 = {0, 2, 4} := by decide
  have hpool1 : poolBuffers (reentrantLineData 1 1 1 1 1 1) 1 = {1, 3} := by decide
  have hni : IsNonIdlingSolution (reentrantLineData 1 1 1 1 1 1) Th Th Th Zh := by
    refine ⟨⟨?_, ?_, fun _ _ _ => rfl, ?_, ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro t ht i
      have hm : max t 0 = t := max_eq_left ht
      fin_cases i <;> simp [hTh, hZh, reentrantLineData, Fin.sum_univ_five, hm]
    · intro t ht i
      fin_cases i <;> simp [hZh]
    · intro t ht i
      fin_cases i <;> simp [hTh, reentrantLineData]
    · funext i; fin_cases i <;> simp [hTh]
    · intro a b hab i
      fin_cases i <;> simp [hTh, hab] <;> exact (le_total 0 b).imp id (fun h => hab.trans h)
    · intro s t hs hst k
      have h1 : max t 0 = t := max_eq_left (hs.trans hst)
      have h2 : max s 0 = s := max_eq_left hs
      rcases (show k = 0 ∨ k = 1 by fin_cases k <;> simp) with rfl | rfl
      · rw [hpool0]; simp [hTh, reentrantLineData, h1, h2]
      · rw [hpool1]; simp [hTh, reentrantLineData, h1, h2]
    · intro k t ht hpos d hd
      rcases (show k = 0 ∨ k = 1 by fin_cases k <;> simp) with rfl | rfl
      · rw [hpool0] at hd
        have hd' : HasDerivAt (fun s => ∑ i ∈ ({0, 2, 4} : Finset (Fin 5)), Th s i) 1 t := by
          have e : (fun s => ∑ i ∈ ({0, 2, 4} : Finset (Fin 5)), Th s i) =ᶠ[nhds t] fun s => s := by
            filter_upwards [lt_mem_nhds ht] with s hs
            simp [hTh, max_eq_left hs.le]
          exact (hasDerivAt_id t).congr_of_eventuallyEq e
        simpa [reentrantLineData] using hd.unique hd'
      · exfalso
        rw [hpool1] at hpos
        simp [hZh] at hpos
  have h := (H 1 1 1 1 1 1 one_pos one_pos one_pos one_pos one_pos one_pos Th Th Th Zh hni).2.2.1
    1 1 1 1 1 one_pos one_pos one_pos one_pos one_pos (by norm_num) (by norm_num) 1 one_pos
    (by simp [reentrantH2, hZh])
  simp [reentrantG1, reentrantG2, hZh] at h
  norm_num at h


