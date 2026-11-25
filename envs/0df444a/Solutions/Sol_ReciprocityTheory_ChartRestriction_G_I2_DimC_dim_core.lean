-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimC.dim_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:07:16.036144+00:00
-- url     : https://prove2.me/submissions/bbf7d808-73d3-4deb-87a5-829b4620c760

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PerpSurj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsPairs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_exists_pairs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_T_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex Module
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.DimC
variable {ι : Type} [Fintype ι]
variable (Y : GT ι)
variable (e f : Fin (Fintype.card ι) → EuclideanSpace ℂ ι)
  (hee : ∀ i j, (Hf (e i) (e j)).im = 0)
  (hef : ∀ i j, (Hf (e i) (f j)).im = if i = j then 1 else 0)
namespace ReciprocityTheory.ChartRestriction.G.I2.DimC
theorem _root_.solution (q : ℕ) (hq : 1 ≤ q) :
    FiniteDimensional ℂ (Y.Sec q) ∧ finrank ℂ (Y.Sec q) ≤ q ^ Fintype.card ι := by
  obtain ⟨e, f, he, hf, hee, hef⟩ := exists_pairs Y
  have hinj := T_inj Y e f hee hef he hf q hq
  haveI hfin : FiniteDimensional ℂ (Y.Sec q) := Module.Finite.of_injective (T Y e q) hinj
  refine ⟨hfin, ?_⟩
  calc finrank ℂ (Y.Sec q) ≤ finrank ℂ ((Fin (Fintype.card ι) → Fin q) → ℂ) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = q ^ Fintype.card ι := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
end ReciprocityTheory.ChartRestriction.G.I2.DimC
