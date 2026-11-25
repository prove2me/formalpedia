-- Prove2me | solution 1 for PI.QnHermHaar.Gen.repOn_list
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:08:10.349471+00:00
-- url     : https://prove2.me/submissions/3a2f31c1-6007-4805-a4fa-85a91d1c63ca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepOnAlgebraMap
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_mul
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
open PI PI.QnHermHaar PI.QnHermHaar.Gen
variable {α β : Type*} [MeasurableSpace α]
variable {μ : Measure α} {ι : α → β} {𝓕 : Submodule ℂ (β → ℂ)}
variable (hI : IntOn μ ι 𝓕)
variable (G : Set β) (hG : ∀ᵐ x ∂μ, ι x ∈ G)
variable {G}
variable (hG : ∀ᵐ x ∂μ, ι x ∈ G)
namespace PI.QnHermHaar.Gen
theorem _root_.solution (t : ℕ) (F : Fin t → A hI) (Φ : Fin t → (β → ℂ) → β → ℂ)
    (h : ∀ k, RepOn hI (F k) (Φ k)) :
    RepOn hI (List.ofFn F).prod (fun f => (List.ofFn Φ).foldr (fun T h => T h) f) := by
  induction t with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil, List.foldr_nil]
    exact repOn_one hI
  | succ t ih =>
    simp only [List.ofFn_succ, List.prod_cons, List.foldr_cons]
    exact repOn_mul hI (h 0) (ih (fun i => F i.succ) (fun i => Φ i.succ) (fun i => h i.succ))
end PI.QnHermHaar.Gen
