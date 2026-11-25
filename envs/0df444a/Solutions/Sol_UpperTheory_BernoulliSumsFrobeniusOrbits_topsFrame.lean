-- Prove2me | solution 1 for UpperTheory.BernoulliSumsFrobeniusOrbits.topsFrame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:46:33.457827+00:00
-- url     : https://prove2.me/submissions/93a4d5dd-d030-4ac0-bc35-666f29c3bdfc

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_topsGroup
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_topsFrame
import Theorems.Thm_Formalism_HC_Frame_index_A0_eq_o
import Theorems.Thm_Formalism_HC_Frame_natCard_A
import Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_topsGroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
namespace UpperTheory.BernoulliSumsFrobeniusOrbits
theorem _root_.solution :
    ∀ eps Co Lb : ℝ, 0 < eps → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ x ≥ x₀, ∀ (φ : Formalism.HC.Frame) (L₂ : ℕ),
      x ^ hE eps / 2 ≤ (φ.ord : ℝ) → (φ.ord : ℝ) ≤ Co * x ^ hE eps → (φ.o : ℝ) ≤ Co → (L₂ : ℝ) ≤ Lb →
      ∀ bs : φ.A → φ.A → φ.A, (∀ h t, ∃ i : ℕ, bs h t + i • h = t) →
      ∀ (PP : Finset ℕ) (hp : ℕ → φ.A) (ω : ℕ → ℝ), (∀ p, 0 ≤ ω p) → (∀ p ∈ PP, x ^ (eps / 4) ≤ (addOrderOf (hp p) : ℝ)) →
      ∃ TT : Finset φ.A, dE eps x * φ.ord / 2 ≤ (TT.card : ℝ) ∧ (TT.card : ℝ) ≤ 2 * dE eps x * φ.ord ∧
        φ.Shares TT (x ^ (-1 + eps)) ∧
        ∑ p ∈ PP, ω p * (({t : φ.A | t ∈ TT ∧ ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p))
            (Finset.univ.filter (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ TT)) L₂ (KE eps) (rE eps)
            (dE eps x) (hE eps) x}.ncard : ℕ) : ℝ) ≤ 4 * (Cb * x ^ (-2 : ℝ)) * dE eps x * φ.ord * ∑ p ∈ PP, ω p := by
  intro eps Co Lb heps
  obtain ⟨Cb, x₀, hCb, hmain⟩ := topsGroup eps Co Lb heps
  refine ⟨Cb, x₀, hCb, ?_⟩
  intro x hx φ L₂ h1 h2 h3 h4 bs hbs PP hp ω hω hord
  classical
  have hcard : (Fintype.card φ.A : ℝ) = φ.ord := by
    rw [← Nat.card_eq_fintype_card, Formalism.HC.Frame.natCard_A]
  have hidx : (φ.A0.index : ℝ) = φ.o := by
    rw [Formalism.HC.Frame.index_A0_eq_o]
  obtain ⟨TT, t1, t2, t3, t4⟩ := hmain x hx φ.A φ.A0 L₂ (by rw [hcard]; exact h1)
    (by rw [hcard]; exact h2) (by rw [hidx]; exact h3) h4 bs hbs PP hp ω hω hord
  refine ⟨TT, ?_, ?_, ?_, ?_⟩
  · rw [← hcard]
    exact t1
  · rw [← hcard]
    exact t2
  · intro γ
    have := t3 γ
    rw [hidx] at this
    unfold Formalism.HC.Frame.lam
    convert this using 4
  · rw [← hcard]
    convert t4 using 6
end UpperTheory.BernoulliSumsFrobeniusOrbits
