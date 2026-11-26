-- Prove2me | solution 1 for OCTKernel.Main.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T09:02:33.089181+00:00
-- url     : https://prove2.me/submissions/98b31f6c-a6bd-4ffc-ae53-30facc6887a2

import Definitions.Def_OCTKernel_Main_Polynomials
import Theorems.Thm_SumsHighPowers_PITLifting_theorem_2_3

open OCTKernel.Main

theorem solution (p s d : ℕ) [Fact p.Prime] (hs : 1 ≤ s) (hd : d < p)
    (f : Fin s → Polynomial (ZMod p)) (hf : ∀ i, (f i).degree ≤ (d : WithBot ℕ)) :
    LinearIndependent (ZMod p) f ↔ wronskian f ≠ 0 := by
  classical
  have h := SumsHighPowers.PITLifting.theorem_2_3 f d
    (fun i => Polynomial.natDegree_le_iff_degree_le.mpr (hf i))
    (Or.inr (by simpa only [ZMod.ringChar_zmod_n] using hd))
  change LinearIndependent (ZMod p) f ↔ ¬ BorderDiffEq.wronskian f = 0
  exact ⟨fun hi hz => (h.mpr hz) hi, fun hn => Classical.byContradiction (fun hni => hn (h.mp hni))⟩
