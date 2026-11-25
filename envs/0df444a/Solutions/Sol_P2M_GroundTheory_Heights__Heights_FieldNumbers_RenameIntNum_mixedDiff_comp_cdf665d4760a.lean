-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameIntNum_mixedDiff_comp_cdf665d4760a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:24:05.777449+00:00
-- url     : https://prove2.me/submissions/ffcdf44e-69fc-495e-bd58-140a743496ec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameIntNum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.RenameIntNum
variable {K₁ K₂ : Type*} (e : K₁ ≃ K₂)
namespace GroundTheory.Heights₂.Heights.FieldNumbers.RenameIntNum
theorem _root_.solution {n : ℕ} (bs : Fin n → K₂ → ℤ) (h : (K₁ → ℤ) → ℤ) :
    mixedDiff bs (fun m => h (m ∘ e)) = fun m => mixedDiff (fun i => bs i ∘ e) h (m ∘ e) := by
  unfold mixedDiff
  have hl : List.ofFn (fun i => bs i ∘ e) = (List.ofFn bs).map (fun b => b ∘ e) := by
    rw [List.map_ofFn]
    rfl
  rw [hl]
  generalize List.ofFn bs = l
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.foldr_cons, List.map_cons, List.foldr_cons, ih]
    rfl
end GroundTheory.Heights₂.Heights.FieldNumbers.RenameIntNum
