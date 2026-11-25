-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_irreducible_of_totalDegree_le_one_dc5ad9495e50
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:35:21.788866+00:00
-- url     : https://prove2.me/submissions/9ae942d9-4296-49d0-83c8-7e2dff404d9a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormIrreducible
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_isUnit_of_totalDegree_eq_zero_85561495d956

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial TensorProduct Matrix
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
open GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
variable {K : Type*} [Field K] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
theorem _root_.solution {ℓ : MvPolynomial (Fin n) K} (h1 : ℓ.totalDegree ≤ 1)
    (hc : ∀ r, ℓ ≠ C r) : Irreducible ℓ := by
  have hne : ℓ ≠ 0 := by simpa using hc 0
  refine irreducible_iff.mpr ⟨fun hu => ?_, fun a b hab => ?_⟩
  · obtain ⟨r, -, hr⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
    exact hc r hr
  · by_contra hnot
    rw [not_or] at hnot
    have ha : a ≠ 0 := by rintro rfl; exact hne (by rw [hab, zero_mul])
    have hb : b ≠ 0 := by rintro rfl; exact hne (by rw [hab, mul_zero])
    have hda : a.totalDegree ≠ 0 := fun h => hnot.1 (isUnit_of_totalDegree_eq_zero ha h)
    have hdb : b.totalDegree ≠ 0 := fun h => hnot.2 (isUnit_of_totalDegree_eq_zero hb h)
    have := totalDegree_mul_of_isDomain ha hb
    rw [← hab] at this
    omega
end GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
