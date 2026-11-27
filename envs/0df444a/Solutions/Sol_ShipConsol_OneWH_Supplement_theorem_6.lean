-- Prove2me | solution 1 for ShipConsol.OneWH.Supplement.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:38:23.082411+00:00
-- url     : https://prove2.me/submissions/e3aea581-f41b-414a-bea6-6711cc535a74

import Mathlib
import Definitions.Def_ShipConsol_OneWH_Supplement_Variable

open ShipConsol
open ShipConsol.OneWH
open ShipConsol.OneWH.Supplement

/-- The printed first bound is zero at γ=0, but finite-horizon constant thresholds
can be strictly suboptimal. This example already has Bernoulli arrivals. -/
theorem solution :
    example6.SourceData ∧
    (∀ x, example6.v x = (0 : ℝ) * example6.F x) ∧
    fixedMinimizer example6 2 ∧
    h3Total example6 5 1 = 519 / 128 ∧
    h3Total example6 5 2 = 471 / 128 ∧
    h3Total example6 5 3 = 6 ∧
    validThresholds 3 witnessThreshold6 ∧
    h2Total example6 5 witnessThreshold6 = 459 / 128 ∧
    0 < optimalAverage example6 5 ∧
    (h3Average example6 5 - optimalAverage example6 5) / optimalAverage example6 5 >
      bound6 3 2 (3 / 4) 0 := by
        set_option maxHeartbeats 10000000 in
        classical
        have hF : example6.F = fun x => max 2 (4 - x) := rfl
        have hv : example6.v = fun _ => 0 := rfl
        have hd : example6.d = 3 := rfl
        have hp0 : example6.p (0 : Fin (example6.maxBatch + 1)) = 1/4 := by
          show (if (0 : Fin 2).val = 0 then (1:ℝ) - 3/4 else 3/4) = 1/4; norm_num
        have hp1 : example6.p (1 : Fin (example6.maxBatch + 1)) = 3/4 := by
          show (if (1 : Fin 2).val = 0 then (1:ℝ) - 3/4 else 3/4) = 3/4; norm_num
        set M := shippingControl example6 with hM
        have hsum : ∀ g : Fin (example6.maxBatch + 1) → ℝ,
            ∑ e, M.weight e * g e = 1/4 * g 0 + 3/4 * g 1 := by
          intro g
          show ∑ e : Fin 2, (if e.val = 0 then (1:ℝ) - 3/4 else 3/4) * g e = _
          rw [Fin.sum_univ_two]
          norm_num
          rfl
        have hnext : ∀ s a (e : Fin (example6.maxBatch + 1)), M.next s a e = nextSlacks 3 s a e.val := 
          fun _ _ _ => rfl
        have hcost : ∀ s a, M.cost s a = shipmentCost example6 s a := fun _ _ => rfl
        have hacts : ∀ t s, M.actions t s = packageActions t s := fun _ _ => rfl
        have e0 : ((0 : Fin (example6.maxBatch + 1)) : ℕ) = 0 := rfl
        have e1 : ((1 : Fin (example6.maxBatch + 1)) : ℕ) = 1 := rfl
        -- generic evaluation steps for threshold policies
        have hev0 : ∀ θ s, M.evaluate (thresholdPolicy θ) 0 s = 0 := fun _ _ => rfl
        have hship : ∀ θ t (s : List ℕ) (z : ℕ), s ≠ [] →
            (t + 1 = 1 ∨ minSlack s ≤ θ (t + 1) s.length) →
            (∀ h, (Finset.range s.length).inf' h (fun i => s[i]?.getD 0) = z) →
            M.evaluate (thresholdPolicy θ) (t + 1) s =
              max 2 (4 - (z : ℝ)) + (1/4 * M.evaluate (thresholdPolicy θ) t [] +
                3/4 * M.evaluate (thresholdPolicy θ) t [3]) := by
          intro θ t s z hs hc hz
          have hpol : thresholdPolicy θ (t + 1) s = {Finset.range s.length} := by
            rw [thresholdPolicy, if_pos hc]; simp [onePackage, hs]
          have hne : (Finset.range s.length).Nonempty := by
            simp [Finset.nonempty_range_iff, hs]
          have hshp : shipped {Finset.range s.length} = Finset.range s.length := by
            simp [shipped]
          have hnx : ∀ m, nextSlacks 3 s {Finset.range s.length} m = List.replicate m 3 := by
            intro m
            simp only [nextSlacks, hshp]
            rw [List.filter_eq_nil_iff.mpr]
            · simp
            · intro x hx
              have := List.snd_lt_of_mem_zipIdx hx
              simp at this ⊢; omega
          rw [ScenarioControl.evaluate, hsum, hpol, hnext, hnext, hnx, hnx, hcost, e0, e1]
          simp only [shipmentCost, Finset.sum_singleton, packageCost, dif_pos hne, hz, hF, hv]
          simp
        have hwait : ∀ θ t (s r : List ℕ),
            ¬ (t + 1 = 1 ∨ minSlack s ≤ θ (t + 1) s.length) → s.map (· - 1) = r →
            M.evaluate (thresholdPolicy θ) (t + 1) s =
              1/4 * M.evaluate (thresholdPolicy θ) t r +
                3/4 * M.evaluate (thresholdPolicy θ) t (r ++ [3]) := by
          intro θ t s r hc hr
          have hpol : thresholdPolicy θ (t + 1) s = ∅ := by
            simp only [thresholdPolicy, if_neg hc]
          have hnx : ∀ m, nextSlacks 3 s ∅ m = r ++ List.replicate m 3 := by
            intro m
            simp only [nextSlacks, shipped, Finset.biUnion_empty, Finset.notMem_empty, not_false_eq_true,
              decide_true, List.filter_true]
            rw [← hr, ← List.zipIdx_map_fst 0 s, List.map_map]
            congr 1
            · simp [List.zipIdx_map_fst]
          rw [ScenarioControl.evaluate, hsum, hpol, hnext, hnext, hnx, hnx, hcost, e0, e1]
          simp [shipmentCost]
        have hnil : ∀ θ t, M.evaluate (thresholdPolicy θ) (t + 1) [] =
              1/4 * M.evaluate (thresholdPolicy θ) t [] +
                3/4 * M.evaluate (thresholdPolicy θ) t [3] := by
          intro θ t
          have hpol : thresholdPolicy θ (t + 1) [] = ∅ := by
            simp [thresholdPolicy, onePackage]
          rw [ScenarioControl.evaluate, hsum, hpol, hnext, hnext, hcost, e0, e1]
          simp [shipmentCost, nextSlacks]
        have a1_1_n : M.evaluate (thresholdPolicy (fun _ _ => 1)) 1 [] = (0 : ℝ) / 1 :=
          (hnil (fun _ _ => 1) 0).trans (by norm_num [hev0, hev0])
        have a1_1_3 : M.evaluate (thresholdPolicy (fun _ _ => 1)) 1 [3] = (2 : ℝ) / 1 :=
          (hship (fun _ _ => 1) 0 [3] 3 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [hev0, hev0])
        have a1_2_n : M.evaluate (thresholdPolicy (fun _ _ => 1)) 2 [] = (3 : ℝ) / 2 :=
          (hnil (fun _ _ => 1) 1).trans (by norm_num [a1_1_n, a1_1_3])
        have a1_1_2 : M.evaluate (thresholdPolicy (fun _ _ => 1)) 1 [2] = (2 : ℝ) / 1 :=
          (hship (fun _ _ => 1) 0 [2] 2 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [hev0, hev0])
        have a1_1_23 : M.evaluate (thresholdPolicy (fun _ _ => 1)) 1 [2, 3] = (2 : ℝ) / 1 :=
          (hship (fun _ _ => 1) 0 [2, 3] 2 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [hev0, hev0])
        have a1_2_3 : M.evaluate (thresholdPolicy (fun _ _ => 1)) 2 [3] = (2 : ℝ) / 1 :=
          (hwait (fun _ _ => 1) 1 [3] [2] (by decide) rfl).trans (by norm_num [a1_1_2, a1_1_23])
        have a1_3_n : M.evaluate (thresholdPolicy (fun _ _ => 1)) 3 [] = (15 : ℝ) / 8 :=
          (hnil (fun _ _ => 1) 2).trans (by norm_num [a1_2_n, a1_2_3])
        have a1_1_1 : M.evaluate (thresholdPolicy (fun _ _ => 1)) 1 [1] = (3 : ℝ) / 1 :=
          (hship (fun _ _ => 1) 0 [1] 1 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [hev0, hev0])
        have a1_1_13 : M.evaluate (thresholdPolicy (fun _ _ => 1)) 1 [1, 3] = (3 : ℝ) / 1 :=
          (hship (fun _ _ => 1) 0 [1, 3] 1 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [hev0, hev0])
        have a1_2_2 : M.evaluate (thresholdPolicy (fun _ _ => 1)) 2 [2] = (3 : ℝ) / 1 :=
          (hwait (fun _ _ => 1) 1 [2] [1] (by decide) rfl).trans (by norm_num [a1_1_1, a1_1_13])
        have a1_1_12 : M.evaluate (thresholdPolicy (fun _ _ => 1)) 1 [1, 2] = (3 : ℝ) / 1 :=
          (hship (fun _ _ => 1) 0 [1, 2] 1 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [hev0, hev0])
        have a1_1_123 : M.evaluate (thresholdPolicy (fun _ _ => 1)) 1 [1, 2, 3] = (3 : ℝ) / 1 :=
          (hship (fun _ _ => 1) 0 [1, 2, 3] 1 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [hev0, hev0])
        have a1_2_23 : M.evaluate (thresholdPolicy (fun _ _ => 1)) 2 [2, 3] = (3 : ℝ) / 1 :=
          (hwait (fun _ _ => 1) 1 [2, 3] [1, 2] (by decide) rfl).trans (by norm_num [a1_1_12, a1_1_123])
        have a1_3_3 : M.evaluate (thresholdPolicy (fun _ _ => 1)) 3 [3] = (3 : ℝ) / 1 :=
          (hwait (fun _ _ => 1) 2 [3] [2] (by decide) rfl).trans (by norm_num [a1_2_2, a1_2_23])
        have a1_4_n : M.evaluate (thresholdPolicy (fun _ _ => 1)) 4 [] = (87 : ℝ) / 32 :=
          (hnil (fun _ _ => 1) 3).trans (by norm_num [a1_3_n, a1_3_3])
        have a1_2_1 : M.evaluate (thresholdPolicy (fun _ _ => 1)) 2 [1] = (9 : ℝ) / 2 :=
          (hship (fun _ _ => 1) 1 [1] 1 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [a1_1_n, a1_1_3])
        have a1_2_13 : M.evaluate (thresholdPolicy (fun _ _ => 1)) 2 [1, 3] = (9 : ℝ) / 2 :=
          (hship (fun _ _ => 1) 1 [1, 3] 1 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [a1_1_n, a1_1_3])
        have a1_3_2 : M.evaluate (thresholdPolicy (fun _ _ => 1)) 3 [2] = (9 : ℝ) / 2 :=
          (hwait (fun _ _ => 1) 2 [2] [1] (by decide) rfl).trans (by norm_num [a1_2_1, a1_2_13])
        have a1_2_12 : M.evaluate (thresholdPolicy (fun _ _ => 1)) 2 [1, 2] = (9 : ℝ) / 2 :=
          (hship (fun _ _ => 1) 1 [1, 2] 1 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [a1_1_n, a1_1_3])
        have a1_2_123 : M.evaluate (thresholdPolicy (fun _ _ => 1)) 2 [1, 2, 3] = (9 : ℝ) / 2 :=
          (hship (fun _ _ => 1) 1 [1, 2, 3] 1 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [a1_1_n, a1_1_3])
        have a1_3_23 : M.evaluate (thresholdPolicy (fun _ _ => 1)) 3 [2, 3] = (9 : ℝ) / 2 :=
          (hwait (fun _ _ => 1) 2 [2, 3] [1, 2] (by decide) rfl).trans (by norm_num [a1_2_12, a1_2_123])
        have a1_4_3 : M.evaluate (thresholdPolicy (fun _ _ => 1)) 4 [3] = (9 : ℝ) / 2 :=
          (hwait (fun _ _ => 1) 3 [3] [2] (by decide) rfl).trans (by norm_num [a1_3_2, a1_3_23])
        have a1_5_n : M.evaluate (thresholdPolicy (fun _ _ => 1)) 5 [] = (519 : ℝ) / 128 :=
          (hnil (fun _ _ => 1) 4).trans (by norm_num [a1_4_n, a1_4_3])
        have a2_1_n : M.evaluate (thresholdPolicy (fun _ _ => 2)) 1 [] = (0 : ℝ) / 1 :=
          (hnil (fun _ _ => 2) 0).trans (by norm_num [hev0, hev0])
        have a2_1_3 : M.evaluate (thresholdPolicy (fun _ _ => 2)) 1 [3] = (2 : ℝ) / 1 :=
          (hship (fun _ _ => 2) 0 [3] 3 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [hev0, hev0])
        have a2_2_n : M.evaluate (thresholdPolicy (fun _ _ => 2)) 2 [] = (3 : ℝ) / 2 :=
          (hnil (fun _ _ => 2) 1).trans (by norm_num [a2_1_n, a2_1_3])
        have a2_1_2 : M.evaluate (thresholdPolicy (fun _ _ => 2)) 1 [2] = (2 : ℝ) / 1 :=
          (hship (fun _ _ => 2) 0 [2] 2 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [hev0, hev0])
        have a2_1_23 : M.evaluate (thresholdPolicy (fun _ _ => 2)) 1 [2, 3] = (2 : ℝ) / 1 :=
          (hship (fun _ _ => 2) 0 [2, 3] 2 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [hev0, hev0])
        have a2_2_3 : M.evaluate (thresholdPolicy (fun _ _ => 2)) 2 [3] = (2 : ℝ) / 1 :=
          (hwait (fun _ _ => 2) 1 [3] [2] (by decide) rfl).trans (by norm_num [a2_1_2, a2_1_23])
        have a2_3_n : M.evaluate (thresholdPolicy (fun _ _ => 2)) 3 [] = (15 : ℝ) / 8 :=
          (hnil (fun _ _ => 2) 2).trans (by norm_num [a2_2_n, a2_2_3])
        have a2_2_2 : M.evaluate (thresholdPolicy (fun _ _ => 2)) 2 [2] = (7 : ℝ) / 2 :=
          (hship (fun _ _ => 2) 1 [2] 2 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [a2_1_n, a2_1_3])
        have a2_2_23 : M.evaluate (thresholdPolicy (fun _ _ => 2)) 2 [2, 3] = (7 : ℝ) / 2 :=
          (hship (fun _ _ => 2) 1 [2, 3] 2 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [a2_1_n, a2_1_3])
        have a2_3_3 : M.evaluate (thresholdPolicy (fun _ _ => 2)) 3 [3] = (7 : ℝ) / 2 :=
          (hwait (fun _ _ => 2) 2 [3] [2] (by decide) rfl).trans (by norm_num [a2_2_2, a2_2_23])
        have a2_4_n : M.evaluate (thresholdPolicy (fun _ _ => 2)) 4 [] = (99 : ℝ) / 32 :=
          (hnil (fun _ _ => 2) 3).trans (by norm_num [a2_3_n, a2_3_3])
        have a2_3_2 : M.evaluate (thresholdPolicy (fun _ _ => 2)) 3 [2] = (31 : ℝ) / 8 :=
          (hship (fun _ _ => 2) 2 [2] 2 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [a2_2_n, a2_2_3])
        have a2_3_23 : M.evaluate (thresholdPolicy (fun _ _ => 2)) 3 [2, 3] = (31 : ℝ) / 8 :=
          (hship (fun _ _ => 2) 2 [2, 3] 2 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [a2_2_n, a2_2_3])
        have a2_4_3 : M.evaluate (thresholdPolicy (fun _ _ => 2)) 4 [3] = (31 : ℝ) / 8 :=
          (hwait (fun _ _ => 2) 3 [3] [2] (by decide) rfl).trans (by norm_num [a2_3_2, a2_3_23])
        have a2_5_n : M.evaluate (thresholdPolicy (fun _ _ => 2)) 5 [] = (471 : ℝ) / 128 :=
          (hnil (fun _ _ => 2) 4).trans (by norm_num [a2_4_n, a2_4_3])
        have a3_1_n : M.evaluate (thresholdPolicy (fun _ _ => 3)) 1 [] = (0 : ℝ) / 1 :=
          (hnil (fun _ _ => 3) 0).trans (by norm_num [hev0, hev0])
        have a3_1_3 : M.evaluate (thresholdPolicy (fun _ _ => 3)) 1 [3] = (2 : ℝ) / 1 :=
          (hship (fun _ _ => 3) 0 [3] 3 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [hev0, hev0])
        have a3_2_n : M.evaluate (thresholdPolicy (fun _ _ => 3)) 2 [] = (3 : ℝ) / 2 :=
          (hnil (fun _ _ => 3) 1).trans (by norm_num [a3_1_n, a3_1_3])
        have a3_2_3 : M.evaluate (thresholdPolicy (fun _ _ => 3)) 2 [3] = (7 : ℝ) / 2 :=
          (hship (fun _ _ => 3) 1 [3] 3 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [a3_1_n, a3_1_3])
        have a3_3_n : M.evaluate (thresholdPolicy (fun _ _ => 3)) 3 [] = (3 : ℝ) / 1 :=
          (hnil (fun _ _ => 3) 2).trans (by norm_num [a3_2_n, a3_2_3])
        have a3_3_3 : M.evaluate (thresholdPolicy (fun _ _ => 3)) 3 [3] = (5 : ℝ) / 1 :=
          (hship (fun _ _ => 3) 2 [3] 3 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [a3_2_n, a3_2_3])
        have a3_4_n : M.evaluate (thresholdPolicy (fun _ _ => 3)) 4 [] = (9 : ℝ) / 2 :=
          (hnil (fun _ _ => 3) 3).trans (by norm_num [a3_3_n, a3_3_3])
        have a3_4_3 : M.evaluate (thresholdPolicy (fun _ _ => 3)) 4 [3] = (13 : ℝ) / 2 :=
          (hship (fun _ _ => 3) 3 [3] 3 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [a3_3_n, a3_3_3])
        have a3_5_n : M.evaluate (thresholdPolicy (fun _ _ => 3)) 5 [] = (6 : ℝ) / 1 :=
          (hnil (fun _ _ => 3) 4).trans (by norm_num [a3_4_n, a3_4_3])
        have w_1_n : M.evaluate (thresholdPolicy witnessThreshold6) 1 [] = (0 : ℝ) / 1 :=
          (hnil witnessThreshold6 0).trans (by norm_num [hev0, hev0])
        have w_1_3 : M.evaluate (thresholdPolicy witnessThreshold6) 1 [3] = (2 : ℝ) / 1 :=
          (hship witnessThreshold6 0 [3] 3 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [hev0, hev0])
        have w_2_n : M.evaluate (thresholdPolicy witnessThreshold6) 2 [] = (3 : ℝ) / 2 :=
          (hnil witnessThreshold6 1).trans (by norm_num [w_1_n, w_1_3])
        have w_1_2 : M.evaluate (thresholdPolicy witnessThreshold6) 1 [2] = (2 : ℝ) / 1 :=
          (hship witnessThreshold6 0 [2] 2 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [hev0, hev0])
        have w_1_23 : M.evaluate (thresholdPolicy witnessThreshold6) 1 [2, 3] = (2 : ℝ) / 1 :=
          (hship witnessThreshold6 0 [2, 3] 2 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [hev0, hev0])
        have w_2_3 : M.evaluate (thresholdPolicy witnessThreshold6) 2 [3] = (2 : ℝ) / 1 :=
          (hwait witnessThreshold6 1 [3] [2] (by decide) rfl).trans (by norm_num [w_1_2, w_1_23])
        have w_3_n : M.evaluate (thresholdPolicy witnessThreshold6) 3 [] = (15 : ℝ) / 8 :=
          (hnil witnessThreshold6 2).trans (by norm_num [w_2_n, w_2_3])
        have w_1_1 : M.evaluate (thresholdPolicy witnessThreshold6) 1 [1] = (3 : ℝ) / 1 :=
          (hship witnessThreshold6 0 [1] 1 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [hev0, hev0])
        have w_1_13 : M.evaluate (thresholdPolicy witnessThreshold6) 1 [1, 3] = (3 : ℝ) / 1 :=
          (hship witnessThreshold6 0 [1, 3] 1 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [hev0, hev0])
        have w_2_2 : M.evaluate (thresholdPolicy witnessThreshold6) 2 [2] = (3 : ℝ) / 1 :=
          (hwait witnessThreshold6 1 [2] [1] (by decide) rfl).trans (by norm_num [w_1_1, w_1_13])
        have w_1_12 : M.evaluate (thresholdPolicy witnessThreshold6) 1 [1, 2] = (3 : ℝ) / 1 :=
          (hship witnessThreshold6 0 [1, 2] 1 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [hev0, hev0])
        have w_1_123 : M.evaluate (thresholdPolicy witnessThreshold6) 1 [1, 2, 3] = (3 : ℝ) / 1 :=
          (hship witnessThreshold6 0 [1, 2, 3] 1 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [hev0, hev0])
        have w_2_23 : M.evaluate (thresholdPolicy witnessThreshold6) 2 [2, 3] = (3 : ℝ) / 1 :=
          (hwait witnessThreshold6 1 [2, 3] [1, 2] (by decide) rfl).trans (by norm_num [w_1_12, w_1_123])
        have w_3_3 : M.evaluate (thresholdPolicy witnessThreshold6) 3 [3] = (3 : ℝ) / 1 :=
          (hwait witnessThreshold6 2 [3] [2] (by decide) rfl).trans (by norm_num [w_2_2, w_2_23])
        have w_4_n : M.evaluate (thresholdPolicy witnessThreshold6) 4 [] = (87 : ℝ) / 32 :=
          (hnil witnessThreshold6 3).trans (by norm_num [w_3_n, w_3_3])
        have w_3_2 : M.evaluate (thresholdPolicy witnessThreshold6) 3 [2] = (31 : ℝ) / 8 :=
          (hship witnessThreshold6 2 [2] 2 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [w_2_n, w_2_3])
        have w_3_23 : M.evaluate (thresholdPolicy witnessThreshold6) 3 [2, 3] = (31 : ℝ) / 8 :=
          (hship witnessThreshold6 2 [2, 3] 2 (by simp) (by decide) (fun _ => rfl)).trans (by norm_num [w_2_n, w_2_3])
        have w_4_3 : M.evaluate (thresholdPolicy witnessThreshold6) 4 [3] = (31 : ℝ) / 8 :=
          (hwait witnessThreshold6 3 [3] [2] (by decide) rfl).trans (by norm_num [w_3_2, w_3_23])
        have w_5_n : M.evaluate (thresholdPolicy witnessThreshold6) 5 [] = (459 : ℝ) / 128 :=
          (hnil witnessThreshold6 4).trans (by norm_num [w_4_n, w_4_3])
        have hw : ∀ e, 0 ≤ M.weight e := by
          intro e
          show 0 ≤ (if e.val = 0 then (1:ℝ) - 3/4 else 3/4)
          split_ifs <;> norm_num
        have hw1 : ∑ e, M.weight e = 1 := by
          have := hsum (fun _ => 1); simp only [mul_one] at this; rw [this]; norm_num
        have hminle : ∀ (s : List ℕ), ∀ x ∈ s, minSlack s ≤ x := by
          intro s x hx
          unfold minSlack
          generalize s.headD 0 = c
          induction s with
          | nil => simp at hx
          | cons a l ih =>
            simp only [List.foldr_cons]
            rcases List.mem_cons.mp hx with rfl | h
            · exact min_le_left _ _
            · exact (min_le_right _ _).trans (ih h)
        have hfeas : ∀ θ : ℕ → ℕ → ℕ, (∀ t n, 1 ≤ θ t n) → ∀ t s,
            thresholdPolicy θ t s ∈ M.actions t s := by
          intro θ hθ t s
          rw [hacts]
          unfold thresholdPolicy
          split_ifs with hc
          · unfold packageActions onePackage
            split_ifs with h
            · subst h; simp
            · simp [Finset.mem_filter, shipped]
              exact ⟨h, fun i hi _ => hi⟩
          · simp only [packageActions, Finset.mem_filter]
            refine ⟨by simp, by simp, by simp, ?_⟩
            intro i hi h1
            exfalso
            push Not at hc
            rcases h1 with h1 | h1
            · exact hc.1 h1
            · have hi' : i < s.length := Finset.mem_range.mp hi
              rw [List.getElem?_eq_getElem hi'] at h1
              simp only [Option.getD_some] at h1
              have := hminle s (s[i]) (List.getElem_mem hi')
              have := hθ t s.length
              omega
        have hwit1 : ∀ t n, 1 ≤ witnessThreshold6 t n := by
          intro t n; unfold witnessThreshold6; split_ifs <;> omega
        have hle : ∀ t s, M.value t s ≤ M.evaluate (thresholdPolicy witnessThreshold6) t s := by
          intro t
          induction t with
          | zero => intro s; simp [ScenarioControl.value, ScenarioControl.evaluate]
          | succ t ih =>
            intro s
            rw [ScenarioControl.value, ScenarioControl.evaluate]
            have hmem := hfeas _ hwit1 (t + 1) s
            unfold finiteMin; rw [dif_pos ⟨_, hmem⟩]
            refine (Finset.inf'_le _ hmem).trans ?_
            exact add_le_add le_rfl (Finset.sum_le_sum fun e _ =>
              mul_le_mul_of_nonneg_left (ih _) (hw e))
        have hpkg : ∀ s b, 0 ≤ packageCost example6.F example6.v s b := by
          intro s b
          unfold packageCost
          split_ifs with hb
          · simp only [hF, hv]; simp
          · exact le_rfl
        have hpkg2 : ∀ s b, b.Nonempty → 2 ≤ packageCost example6.F example6.v s b := by
          intro s b hb
          unfold packageCost
          rw [dif_pos hb]
          simp only [hF, hv]; simp
        have hcostnn : ∀ s a, 0 ≤ M.cost s a := by
          intro s a; rw [hcost]; exact Finset.sum_nonneg fun b _ => hpkg s b
        have hnn : ∀ t s, 0 ≤ M.value t s := by
          intro t
          induction t with
          | zero => intro s; exact le_rfl
          | succ t ih =>
            intro s
            rw [ScenarioControl.value]; unfold finiteMin
            split_ifs with h
            · exact Finset.le_inf' _ _ fun a _ => add_nonneg (hcostnn _ _)
                (Finset.sum_nonneg fun e _ => mul_nonneg (hw e) (ih _))
            · exact le_rfl
        have hstep : ∀ t (s : List ℕ), s ≠ [] →
            (∀ s' : List ℕ, s' ≠ [] → t ≠ 0 → 2 ≤ M.value t s') → 2 ≤ M.value (t + 1) s := by
          intro t s hs IH
          have hne : (M.actions (t + 1) s).Nonempty :=
            ⟨_, hfeas (fun _ _ => 1) (fun _ _ => le_rfl) (t + 1) s⟩
          rw [ScenarioControl.value]; unfold finiteMin; rw [dif_pos hne]
          refine Finset.le_inf' _ _ (fun a ha => ?_)
          have ha' := ha
          rw [hacts] at ha'
          simp only [packageActions, Finset.mem_filter] at ha'
          obtain ⟨_, hbne, _, hcover⟩ := ha'
          rcases Finset.eq_empty_or_nonempty a with rfl | ⟨b, hb⟩
          · have ht : t ≠ 0 := by
              rintro rfl
              have := hcover 0 (by simp [Finset.mem_range, List.length_pos_iff.mpr hs]) (Or.inl rfl)
              simp [shipped] at this
            have hc0 : M.cost s ∅ = 0 := by simp [hcost, shipmentCost]
            have hnx : ∀ e, M.next s ∅ e ≠ [] := by
              intro e; rw [hnext]; simp [nextSlacks, shipped, hs]
            rw [hc0, zero_add]
            calc (2:ℝ) = ∑ e, M.weight e * 2 := by rw [← Finset.sum_mul, hw1]; norm_num
              _ ≤ ∑ e, M.weight e * M.value t (M.next s ∅ e) :=
                Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (IH _ (hnx e) ht) (hw e)
          · have hbn := hbne b hb
            have h1 : 2 ≤ M.cost s a := by
              rw [hcost]; unfold shipmentCost
              exact (hpkg2 s b hbn).trans (Finset.single_le_sum (fun c _ => hpkg s c) hb)
            have h2 : 0 ≤ ∑ e, M.weight e * M.value t (M.next s a e) :=
              Finset.sum_nonneg fun e _ => mul_nonneg (hw e) (hnn _ _)
            linarith
        have hpos : ∀ t (s : List ℕ), s ≠ [] → 2 ≤ M.value (t + 1) s := by
          intro t
          induction t with
          | zero => intro s hs; exact hstep 0 s hs (fun _ _ h => absurd rfl h)
          | succ t ih => intro s hs; exact hstep (t + 1) s hs (fun s' hs' _ => ih s' hs')
        have hv5 : 3/2 ≤ M.value 5 [] := by
          have hne : (M.actions 5 []).Nonempty :=
            ⟨_, hfeas (fun _ _ => 1) (fun _ _ => le_rfl) 5 []⟩
          show 3/2 ≤ finiteMin (M.actions 5 []) fun a =>
            M.cost [] a + ∑ e, M.weight e * M.value 4 (M.next [] a e)
          unfold finiteMin; rw [dif_pos hne]
          refine Finset.le_inf' _ _ (fun a ha => ?_)
          have hn1 : M.next [] a 1 = [3] := by rw [hnext, e1]; simp [nextSlacks]
          have h1 : M.weight 1 * M.value 4 (M.next [] a 1) ≤ ∑ e, M.weight e * M.value 4 (M.next [] a e) :=
            Finset.single_le_sum (f := fun e => M.weight e * M.value 4 (M.next [] a e))
              (fun e _ => mul_nonneg (hw e) (hnn _ _)) (Finset.mem_univ _)
          have h2 : 2 ≤ M.value 4 [3] := hpos 3 [3] (by simp)
          have h3 : M.weight 1 = 3/4 := hp1
          rw [hn1, h3] at h1
          have := hcostnn [] a
          linarith
        have hv5' : M.value 5 [] ≤ 459/128 := by
          have := hle 5 []
          rw [w_5_n] at this; linarith
        have hb6 : bound6 3 2 (3 / 4) 0 = 0 := by norm_num [bound6]
        have hopt : optimalAverage example6 5 = M.value 5 [] / 5 := by
          simp [optimalAverage, M]
        have hh3 : 471/640 ≤ h3Average example6 5 := by
          unfold h3Average finiteMin
          rw [hd]
          have hne : (Finset.Icc 1 3).Nonempty := ⟨1, by simp⟩
          rw [dif_pos hne]
          have : 471/128 ≤ (Finset.Icc 1 3).inf' hne (h3Total example6 5) := by
            refine Finset.le_inf' _ _ (fun k hk => ?_)
            simp only [Finset.mem_Icc] at hk
            obtain ⟨hk1, hk2⟩ := hk
            interval_cases k
            · show (471:ℝ)/128 ≤ M.evaluate (thresholdPolicy fun _ _ => 1) 5 []
              rw [a1_5_n]; norm_num
            · show (471:ℝ)/128 ≤ M.evaluate (thresholdPolicy fun _ _ => 2) 5 []
              rw [a2_5_n]
            · show (471:ℝ)/128 ≤ M.evaluate (thresholdPolicy fun _ _ => 3) 5 []
              rw [a3_5_n]; norm_num
          push_cast
          linarith
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · refine ⟨by rw [hd]; norm_num, ?_, ?_, ?_, ?_⟩
          · rw [hF]
            refine ⟨⟨convex_Ici 1, ?_⟩, ?_, ?_⟩
            · intro x _ y _ a b ha hb hab
              simp only [smul_eq_mul]
              refine max_le ?_ ?_
              · have h1 := mul_le_mul_of_nonneg_left (le_max_left (2:ℝ) (4 - x)) ha
                have h2 := mul_le_mul_of_nonneg_left (le_max_left (2:ℝ) (4 - y)) hb
                linarith
              · have h1 := mul_le_mul_of_nonneg_left (le_max_right (2:ℝ) (4 - x)) ha
                have h2 := mul_le_mul_of_nonneg_left (le_max_right (2:ℝ) (4 - y)) hb
                linarith
            · intro x _ y _ hxy
              exact max_le_max le_rfl (by linarith)
            · intro x _
              exact le_trans (by norm_num) (le_max_left _ _)
          · rw [hv]
            exact ⟨convexOn_const 0 (convex_Ici 1), antitoneOn_const, fun _ _ => le_rfl⟩
          · intro m; exact hw m
          · exact hw1
        · intro x; rw [hv]; simp
        · refine ⟨by norm_num, by rw [hd]; norm_num, ?_⟩
          intro k hk1 hk2
          rw [hd] at hk2
          have hnp : nonemptyProbability example6 = 3/4 := by
            unfold nonemptyProbability; rw [hp0]; norm_num
          rw [hnp, hd, hF]
          interval_cases k <;> norm_num [fixedCriterion]
        · show M.evaluate (thresholdPolicy fun _ _ => 1) 5 [] = _
          rw [a1_5_n]
        · show M.evaluate (thresholdPolicy fun _ _ => 2) 5 [] = _
          rw [a2_5_n]
        · show M.evaluate (thresholdPolicy fun _ _ => 3) 5 [] = _
          rw [a3_5_n]; norm_num
        · intro t n; unfold witnessThreshold6; split_ifs <;> omega
        · show M.evaluate (thresholdPolicy witnessThreshold6) 5 [] = _
          rw [w_5_n]
        · rw [hopt]; apply div_pos <;> linarith
        · rw [hopt, hb6]
          apply div_pos
          · linarith
          · linarith
