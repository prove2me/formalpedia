-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sc_append_li
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:13:20.322474+00:00
-- url     : https://prove2.me/submissions/dfea6cd1-2cbb-4a5f-8e37-554e902c8902

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_Lemmata_GeneralBFactSecond_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField Module
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (N : Matrix (Fin r) (Fin r) K) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K)
    (hbN : ∀ i, N *ᵥ b i = 0) (hb : LinearIndependent K b)
    (hc : LinearIndependent K (fun j => N *ᵥ c j)) : LinearIndependent K (Fin.append b c) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_add] at hg
  simp only [Fin.append_left, Fin.append_right] at hg
  have h1 : ∑ j, g (Fin.natAdd k j) • (N *ᵥ c j) = 0 := by
    have := congrArg N.mulVecLin hg
    simpa [map_add, map_sum, map_smul, Matrix.mulVecLin_apply, hbN] using this
  have hc0 := Fintype.linearIndependent_iff.mp hc _ h1
  have hb0 : ∀ i, g (Fin.castAdd m i) = 0 := by
    apply Fintype.linearIndependent_iff.mp hb
    simpa [hc0] using hg
  intro i
  exact Fin.addCases (fun i => hb0 i) (fun j => hc0 j) i
end ReciprocityTheory.MultiplicativeHeights
