-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.flag_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:16:38.057551+00:00
-- url     : https://prove2.me/submissions/cd46df33-0941-4813-b7a4-1190e810be25

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegQ
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegW
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_exists_kBasisIn


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
theorem _root_.solution (hE : GradedExtStatement) {K : Type} [Field K] [NumberField K] {r : ℕ}
    (δ : (K →+* ℂ) → Fin r → ℝ) (hδ : ∀ σ i, 0 < δ σ i) (Lp : Submodule (𝓞 K) (Fin r → K))
    (hLp : Lp.FG) (e' e : ℕ)
    (hP : ∀ B ≤ Lp ⊓ cutSub K r e', ∀ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn B b →
      latDeg (diagMet δ) B b ≤ 0)
    (hG : ∀ C ≤ (Lp ⊓ cutSub K r e).map (projGe K r e'), ∀ (k : ℕ) (c : Fin k → Fin r → K),
      IsKBasisIn C c → latDeg (diagMet δ) C c ≤ 0) :
    ∀ B ≤ Lp ⊓ cutSub K r e, ∀ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn B b →
      latDeg (diagMet δ) B b ≤ 0 := by
  intro B hB k b hb
  have hBfg : B.FG := Submodule.FG.of_le hLp (hB.trans inf_le_left)
  obtain ⟨k0, b0, hb0⟩ := exists_kBasisIn (B ⊓ cutSub K r e')
  obtain ⟨k1, b1, hb1⟩ := exists_kBasisIn (B.map (projGe K r e'))
  have h := hE K r e' k k0 k1 δ B b b0 b1 hδ hBfg hb hb0 hb1
  have h0 := hP (B ⊓ cutSub K r e') (inf_le_inf_right _ (hB.trans inf_le_left)) k0 b0 hb0
  have h1 := hG (B.map (projGe K r e')) (Submodule.map_mono hB) k1 b1 hb1
  linarith
end ReciprocityTheory.MultiplicativeHeights.SemiPt
