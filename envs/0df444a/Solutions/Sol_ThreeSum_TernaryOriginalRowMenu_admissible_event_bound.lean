-- Prove2me | solution 1 for ThreeSum.TernaryOriginalRowMenu.admissible_event_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:18:49.508022+00:00
-- url     : https://prove2.me/submissions/b9669234-7aa9-4f4c-ad1f-300e2f71af8e

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.FieldTheory.Finite.GaloisField
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_menuEvent_nine_eighths
import Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_admissible_at_least_half

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalRowMenu
open Finset
open Polynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [Fintype K] [Fintype E] [DecidableEq K] [DecidableEq E]
namespace ThreeSum.TernaryOriginalRowMenu
theorem _root_.solution {Λ t : ℕ} (ℓ : E →ₗ[K] K) (hℓ : ℓ ≠ 0)
    (V : Submodule K (Fin Λ → K)) (hV : V ≠ ⊤) (hp : 3 ≤ Fintype.card K)
    (v : Fin t → Fin Λ → K) (hv : LinearIndependent K v) (target : Fin t → K)
    (hsize1 : 8*Λ*Fintype.card K ^ 2 ≤ Fintype.card E)
    (hsize : 8*Λ*Fintype.card K ^ (2*t) ≤ Fintype.card E) :
    Fintype.card K ^ t * ((admissible Λ ℓ V) ∩ menuEvent ℓ v target).card ≤
      3 * (admissible Λ ℓ V).card := by
  have ha := admissible_at_least_half Λ ℓ hℓ V hV hp hsize1
  have he := menuEvent_nine_eighths ℓ hℓ v hv target hsize
  have hc := Nat.mul_le_mul_left (8*Fintype.card K ^ t)
    (card_le_card (inter_subset_right (s₁ := admissible Λ ℓ V) (s₂ := menuEvent ℓ v target)))
  nlinarith
end ThreeSum.TernaryOriginalRowMenu
