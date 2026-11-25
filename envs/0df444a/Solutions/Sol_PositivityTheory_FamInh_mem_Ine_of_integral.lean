-- Prove2me | solution 1 for PositivityTheory.FamInh.mem_Ine_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:26:09.639093+00:00
-- url     : https://prove2.me/submissions/091c90fd-7379-463e-9d45-cbd369e86ff2

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_WeilBound_CoreStatements_PlaceConnectedComponents_ArtinA
import Theorems.Thm_ReciprocityTheory_Gal_exists_den


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
namespace PositivityTheory.FamInh
theorem _root_.solution {A : ValuationSubring Ω} {σ : G K Ω} (hσ : σ ∈ Dec (F := K) A)
    (h : ∀ b : Ω, IsIntegral ℤ b → A.valuation (σ b - b) < 1) : σ ∈ Ine (F := K) A := by
  refine ⟨hσ, fun x hx => ?_⟩
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den K A hx
  have hσx : A.valuation (σ x) ≤ 1 := by
    rw [A.valuation_le_one_iff, apply_mem_iff_of_mem_Dec hσ, ← A.valuation_le_one_iff]
    exact hx
  have he' : σ s * σ x = σ t := by rw [← map_mul, e]
  have key : s * (σ x - x) = (σ t - t) - (σ s - s) * σ x := by
    rw [← he', ← e]; ring
  have hv : A.valuation (s * (σ x - x)) < 1 := by
    rw [key]
    apply Valuation.map_sub_lt _ (h t ht)
    rw [Valuation.map_mul]
    calc A.valuation (σ s - s) * A.valuation (σ x) ≤ A.valuation (σ s - s) * 1 := mul_le_mul_right hσx _
      _ < 1 := by rw [mul_one]; exact h s hs
  rwa [Valuation.map_mul, hs1, one_mul] at hv
end PositivityTheory.FamInh
