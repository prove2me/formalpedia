-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.kRepPiece_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:16:19.814289+00:00
-- url     : https://prove2.me/submissions/35902615-fddd-42d9-99c8-0e29ebfd5a5a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_EntryEqZeroOfComm
import Theorems.Thm_Formalism_REAL_isCompactInvariant_compactSpan


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open PieceCon
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (hR : KRepRelStatement) (hS : KRepStableStatement) : KRepPieceStatement := by
  intro n ε R μ x hx hhi
  set W := Formalism.REAL.kSpan ε R.units x with hWdef
  have hK : Formalism.REAL.KStable ε R.units W := Formalism.REAL.isCompactInvariant_compactSpan x
  have hτ : ∀ k : KG ε, ∀ v ∈ W, R.op k v ∈ W := (hS n ε R W).mpr hK
  refine ⟨pieceKType R hS hR μ x hx hhi, LinearIsometryEquiv.refl ℂ W, ?_, ?_, ?_⟩
  · intro k v
    change ↥W at v
    exact cut_apply_mem W _ v (hτ k v v.2)
  · intro X hX v
    change ↥W at v
    have hb : ∀ a b, ε a ≠ ε b → X a b = 0 := fun a b h => entry_eq_zero_of_comm hX h
    show ((cut W (R.dτ (blockPart ε X)) v : W) : R.V) = R.dτ X v
    rw [blockPart_eq hb]
    exact cut_apply_mem W _ v (dτ_mem R hK hb v v.2)
  · rfl
end ReciprocityTheory.ChartRestriction.DS.HW
