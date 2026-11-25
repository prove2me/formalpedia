-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.pDRho_bracket
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:54:37.940342+00:00
-- url     : https://prove2.me/submissions/ba3789bc-7eb2-4332-9f06-8f04afe38cba

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Unique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_PrhoEntryHasDerivAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_adDFull_bracket
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_adDFull_zero_out

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open scoped Kronecker
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
variable {ε : Fin n → Bool} {β : Bool}
variable (ε β)
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X * Jm ε = Jm ε * X)
    (hY : Y * Jm ε = Jm ε * Y) :
    pDRho ε β X * pDRho ε β Y - pDRho ε β Y * pDRho ε β X = pDRho ε β (X * Y - Y * X) := by
  have e : ∀ Z : Matrix (Fin n) (Fin n) ℂ, pDRho ε β Z = (adDFull Z).submatrix Subtype.val Subtype.val :=
    fun _ => rfl
  have hs : ∀ A B : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ,
      ((A - B).submatrix Subtype.val Subtype.val : Matrix (pIdx ε β) (pIdx ε β) ℂ) =
        (A.submatrix Subtype.val Subtype.val : Matrix (pIdx ε β) (pIdx ε β) ℂ) -
          (B.submatrix Subtype.val Subtype.val : Matrix (pIdx ε β) (pIdx ε β) ℂ) := fun _ _ => rfl
  rw [e, e, e, ← prho_submatrix_mul (fun p : Fin n × Fin n => ε p.1 = β ∧ ε p.2 = !β) _ _
      (fun i k hi hk => adDFull_zero_out hX i k hi hk),
    ← prho_submatrix_mul (fun p : Fin n × Fin n => ε p.1 = β ∧ ε p.2 = !β) _ _
      (fun i k hi hk => adDFull_zero_out hY i k hi hk), ← hs, adDFull_bracket]
end ReciprocityTheory.ChartRestriction.DS.HW
