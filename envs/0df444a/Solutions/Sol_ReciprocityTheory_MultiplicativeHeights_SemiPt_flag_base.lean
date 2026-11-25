-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.flag_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:16:35.972867+00:00
-- url     : https://prove2.me/submissions/8673f2d0-0544-4613-8d2a-7ef61c0f88e4

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegQ
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegW
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_cutSub_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_kBasisIn_bot_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_latDeg_zero_fam


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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ}
    (D : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (Lp : Submodule (𝓞 K) (Fin r → K)) :
    ∀ B ≤ Lp ⊓ cutSub K r 0, ∀ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn B b →
      latDeg D B b ≤ 0 := by
  intro B hB k b hb
  have hB0 : B = ⊥ := eq_bot_iff.2 (hB.trans (inf_le_right.trans (by rw [cutSub_zero])))
  subst hB0
  have hk := kBasisIn_bot_eq b hb
  subst hk
  exact (latDeg_zero_fam D ⊥ b hb).le
end ReciprocityTheory.MultiplicativeHeights.SemiPt
