-- Prove2me | solution 1 for SpilloverDuopoly.Switchers.Supplement.lemma_D1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:20:41.314977+00:00
-- url     : https://prove2.me/submissions/69857454-072d-49ec-aa7a-ef5a6cf8afc2

import Mathlib
import Definitions.Def_SpilloverDuopoly_Switchers_Supplement_ThreePeriod

open SpilloverDuopoly
open SpilloverDuopoly.Switchers
open SpilloverDuopoly.Switchers.Supplement

/-- Lemma D.1 (p. 52 (PDF 54)): in any equilibrium of the third-period pricing game of segment
`(k, l)`, every firm's third-period profit `π_i^{kl}` from that segment is nonnegative. -/
theorem solution (G : ThreePeriod) (o2 : Fin 4 → Fin 4 → Offer)
    (o3 : Fin 4 → (Fin 4 → Offer) → Option (Fin 4) → Fin 4 → Offer) (k : Fin 4) (l : Option (Fin 4))
    (heq : G.IsTermEq k (o2 k) l (o3 k (o2 k) l)) (i : Fin 4) :
    0 ≤ G.piKL o2 o3 i k l := by
      have hdev :
          G.termProfit k (o2 k) l (Function.update (o3 k (o2 k) l) i none) i ≤
            G.termProfit k (o2 k) l (o3 k (o2 k) l) i :=
        heq.2 i none (Set.mem_univ _)
      have hzero :
          G.termProfit k (o2 k) l (Function.update (o3 k (o2 k) l) i none) i = 0 := by
        simp [ThreePeriod.termProfit, margin]
      simpa [ThreePeriod.piKL, hzero] using hdev
