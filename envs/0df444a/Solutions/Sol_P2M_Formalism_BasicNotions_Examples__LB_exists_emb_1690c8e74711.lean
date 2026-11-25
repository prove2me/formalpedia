-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_exists_emb_1690c8e74711
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:53:02.088814+00:00
-- url     : https://prove2.me/submissions/41612d24-b380-4455-8893-bf879f92148b

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocA
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_mem_placeJ_8e5da26ccc5a
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_val_lt_one_iff_ff0494b5971d
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_isPlaceOver_vQ_17c88a143786
import Theorems.Thm_ReciprocityTheory_Gal_exists_smul_eq_of_isPlaceOver


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise
variable (l : ℕ) [hl : Fact l.Prime]
variable {l} {Ω : Type} [Field Ω]
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω)
    (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    ∃ j : Ω →+* PadicAlgCl l, ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1 := by
  have : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  let j0 : Ω →ₐ[ℚ] PadicAlgCl l := IsAlgClosed.lift
  have h0 : (placeJ (j0 : Ω →+* PadicAlgCl l)).valuation ((l : ℕ) : Ω) < 1 := by
    rw [val_lt_one_iff (mem_placeJ _), map_natCast]
    have h1 : ‖((l : ℕ) : PadicAlgCl l)‖ = ‖((l : ℕ) : ℚ_[l])‖ := by
      rw [← PadicAlgCl.norm_extends, map_natCast]
    rw [h1]
    exact Padic.norm_p_lt_one
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (F := ℚ) (isPlaceOver_vQ _ h0) (isPlaceOver_vQ A hA)
  refine ⟨(j0 : Ω →+* PadicAlgCl l).comp ((σ⁻¹ : G ℚ Ω) : Ω →+* Ω), fun x => ?_⟩
  rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, mem_placeJ]
  rfl
end Formalism.BasicNotions.Examples₂.LB
