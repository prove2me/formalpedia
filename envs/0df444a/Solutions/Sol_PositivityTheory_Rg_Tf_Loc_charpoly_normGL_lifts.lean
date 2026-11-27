-- Prove2me | solution 1 for PositivityTheory.Rg.Tf.Loc.charpoly_normGL_lifts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:20:51.024427+00:00
-- url     : https://prove2.me/submissions/5012dffd-e48d-4c47-9b70-b230d5d2df31

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_InvTransposeGLInvTransposeGL
import Theorems.Thm_PositivityTheory_Rg_Tf_Loc_coeff_charpoly_normGL_fixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Polynomial
open scoped ENNReal
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Tf PositivityTheory.Rg.Tf.Loc
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {k E : Type*} [Field k] [Field E] [Algebra k E]
namespace PositivityTheory.Rg.Tf.Loc
theorem _root_.solution [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E)
    (hgen : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) (δ : GL n E) :
    ∃ P : k[X], P.map (algebraMap k E) = ((normGL σ δ : GL n E) : Matrix n n E).charpoly := by
  have hℓ : σ ^ Module.finrank k E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  have hfix : ∀ i, ((normGL σ δ : GL n E) : Matrix n n E).charpoly.coeff i ∈
      Set.range (algebraMap k E) := by
    intro i
    set x := ((normGL σ δ : GL n E) : Matrix n n E).charpoly.coeff i
    have hσ : σ ∈ MulAction.stabilizer (E ≃ₐ[k] E) x := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
      exact coeff_charpoly_normGL_fixed σ hℓ δ i
    have hall : ∀ τ : E ≃ₐ[k] E, τ x = x := by
      intro τ
      have := (Subgroup.zpowers_le.mpr hσ) (hgen τ)
      rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
    have := (IsGalois.mem_bot_iff_fixed x).mpr hall
    rwa [IntermediateField.mem_bot] at this
  exact (Polynomial.lifts_iff_coeff_lifts _).mpr hfix
end PositivityTheory.Rg.Tf.Loc
