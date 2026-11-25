-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.psiPos_posDef_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:23:43.766808+00:00
-- url     : https://prove2.me/submissions/9b290dc5-6bf1-4037-88dc-30b1dfec5e14

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_KinstSecondCountable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_PsiPos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ComplexOrder InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
open S7
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (k : KG ε) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    (toMK k⁻¹ * x * toMK k).PosDef := by
  unfold toMK
  have hk : toM (k : UJ ε) ∈ Kset ε := k.2
  unfold Kset at hk
  obtain ⟨hU, -⟩ := hk
  unfold toM at hU ⊢
  have gen' : ∀ U : Matrix (Fin n) (Fin n) ℂ, U ∈ unitary (Matrix (Fin n) (Fin n) ℂ) →
      (star U * x * U).PosDef := by
    intro U hU'
    rw [Matrix.star_eq_conjTranspose]
    apply hx.conjTranspose_mul_mul_same
    apply Matrix.mulVec_injective_iff_isUnit.mpr
    first
      | exact ⟨⟨U, star U, Unitary.mul_star_self_of_mem hU', Unitary.star_mul_self_of_mem hU'⟩, rfl⟩
      | exact ⟨⟨U, star U, unitary.mul_star_self_of_mem hU', unitary.star_mul_self_of_mem hU'⟩, rfl⟩
  have hinv2 : ((((k⁻¹ : KG ε) : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
      star ((((k : KG ε) : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
    rw [InvMemClass.coe_inv, InvMemClass.coe_inv]
    apply Units.inv_eq_of_mul_eq_one_left
    first
      | exact Unitary.star_mul_self_of_mem hU
      | exact unitary.star_mul_self_of_mem hU
  rw [hinv2]
  exact gen' _ hU
end ReciprocityTheory.ChartRestriction.DS
