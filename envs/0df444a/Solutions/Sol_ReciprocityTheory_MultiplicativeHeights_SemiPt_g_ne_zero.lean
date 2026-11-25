-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.g_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:55:16.986536+00:00
-- url     : https://prove2.me/submissions/e38cf20f-6e3f-4560-b115-261e166abec2

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegZ
import Definitions.Def_Lemmata_GeneralBFactSecondAlt_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegZA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ)
    (g : Fin r → K)
    (haniso : ∀ t : Fin r → K, (∀ i : Fin r, (i : ℕ) < m ∨ r ≤ (i : ℕ) + m → t i = 0) →
      ∑ i, S.c (t i) * g i * t i = 0 → t = 0) :
    ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → g i ≠ 0 := by
  classical
  intro i h1 h2 hg
  have ht := haniso (Pi.single i 1) (fun j hj => by
    have : j ≠ i := fun e => by rw [e] at hj; omega
    simp [this]) (by
    rw [Finset.sum_eq_single i]
    · simp [hg]
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd (Finset.mem_univ _) h)
  have := congr_fun ht i
  simp at this
end ReciprocityTheory.MultiplicativeHeights.SemiPt
