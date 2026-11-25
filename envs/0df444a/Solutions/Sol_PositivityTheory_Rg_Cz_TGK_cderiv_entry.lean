-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TGK.cderiv_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:38:10.78282+00:00
-- url     : https://prove2.me/submissions/2b4b2239-34c8-42eb-8c98-dfea2a0ce3fc

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TGK
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
namespace PositivityTheory.Rg.Cz.TGK
theorem _root_.solution {ι Γ : Type} [DecidableEq ι] (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (bar : ι → ι) (τ : ι)
    (hne : bar τ ≠ τ) (hconj : ∀ σ γ i j, κ (bar σ) γ i j = star (κ σ γ i j))
    (X : Matrix (Fin n) (Fin n) ℂ) (c : ℝ → Γ)
    (hd : ∀ i j, HasDerivAt (fun t => κ τ (c t) i j) (X i j) 0)
    (hoth : ∀ τ', τ' ≠ τ → τ' ≠ bar τ → ∀ t, κ τ' (c t) = 1) (σ : ι) (i j : Fin n) :
    HasDerivAt (fun t => κ σ (c t) i j) (cD bar τ X σ i j) 0 := by
  unfold cD
  by_cases h1 : σ = τ
  · subst h1
    rw [if_pos rfl, if_neg (fun h => hne h.symm), add_zero]
    exact hd i j
  · by_cases h2 : σ = bar τ
    · subst h2
      rw [if_neg h1, if_pos rfl, zero_add]
      simp_rw [hconj τ]
      exact (hd i j).star
    · rw [if_neg h1, if_neg h2, add_zero]
      rw [show (fun t => κ σ (c t) i j) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) i j from
        funext fun t => by rw [hoth σ h1 h2 t]]
      exact hasDerivAt_const _ _
end PositivityTheory.Rg.Cz.TGK
