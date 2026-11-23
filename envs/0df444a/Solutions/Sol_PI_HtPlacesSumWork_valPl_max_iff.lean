-- Prove2me | solution 1 for PI.HtPlacesSumWork.valPl_max_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:59.746593+00:00
-- url     : https://prove2.me/submissions/3d4f28aa-6cbf-4b5d-871f-edfb30554d30

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_ValPlWtAddEqZero
import Theorems.Thm_PI_HtPlacesSumWork_valPl_wt_add_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.HtPlacesSumWork
open IsDedekindDomain WithZero IsLocalRing ReciprocityTheory.ChartRestriction.G.T0
namespace PI.HtPlacesSumWork
theorem _root_.solution {Φ : Type*} [Field Φ] (V : ValuationSubring Φ)
    (u : AddValuation Φ (WithTop ℤ)) (hV : ∀ x, x ∈ V ↔ 0 ≤ u x) (y : V) :
    y ∈ maximalIdeal V ↔ 0 < u (y : Φ) := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hnu
    rcases ((hV y).1 y.2).lt_or_eq with h | h
    · exact h
    exfalso
    apply hnu
    have hy0 : (y : Φ) ≠ 0 := by
      intro e
      rw [e, AddValuation.map_zero] at h
      exact WithTop.top_ne_zero h.symm
    have hinv : (y : Φ)⁻¹ ∈ V := (hV _).2 (by rw [AddValuation.map_inv, ← h, neg_zero])
    exact (Units.mkOfMulEqOne y ⟨_, hinv⟩ (Subtype.ext (by simp [hy0]))).isUnit
  · intro hpos hu
    obtain ⟨z, hz⟩ := hu.exists_right_inv
    have e : u ((y : Φ) * (z : Φ)) = 0 := by
      have := congrArg (fun t : V => u (t : Φ)) hz
      simpa using this
    rw [AddValuation.map_mul] at e
    exact hpos.ne' (valPl_wt_add_eq_zero ((hV y).1 y.2) ((hV z).1 z.2) e)
end PI.HtPlacesSumWork
