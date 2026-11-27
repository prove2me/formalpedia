-- Prove2me | solution 1 for PositivityTheory.FamInh.res_mem_inertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:18:36.034988+00:00
-- url     : https://prove2.me/submissions/068b4be6-1bbc-4c6a-97b1-15e8659ea5b7

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_WeilBound_CoreStatements_PlaceConnectedComponents_ArtinA
import Theorems.Thm_PositivityTheory_FamInh_coe_res_smul
import Theorems.Thm_PositivityTheory_FamInh_val_int_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise
open PositivityTheory PositivityTheory.FamInh
variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra L Ω]
  [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsAlgClosure L Ω]
variable [IsGalois K L]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)}
omit [IsAlgClosure K Ω] [IsAlgClosure L Ω]
namespace PositivityTheory.FamInh
theorem _root_.solution (hw : IsPlaceOver A w) {σ : G K Ω} (hσ : σ ∈ Ine (F := K) A) :
    AlgEquiv.restrictNormalHom L σ ∈ w.asIdeal.inertia (L ≃ₐ[K] L) := by
  intro x
  show _ ∈ w.asIdeal
  rw [← hw]
  have := hσ.2 _ (val_int_le_one A x)
  rw [← coe_res_smul, ← map_sub] at this
  exact this
end PositivityTheory.FamInh
