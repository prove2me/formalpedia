-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValPl.norm_eq_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:11:30.491889+00:00
-- url     : https://prove2.me/submissions/e2f58644-9edd-46c9-9858-1dc826acf28b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValPlRes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_norm_eq_heightOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_placesOver_bij
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_resDeg_addv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.ValPl
open IsDedekindDomain IsLocalRing
variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]
namespace ReciprocityTheory.ChartRestriction.G.T0.ValPl
theorem _root_.solution (y : L) (hy : y ≠ 0) {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ u : O, IsUnit u ∧
      Algebra.norm F y = (algebraMap O F ϖ) ^
        (∑ᶠ (w : AddValuation L (WithTop ℤ)) (_ : w ∈ PlacesOver O L),
          (letI := resAlg (F := F) w
           (Module.finrank (ResidueField ((vRing w).comap (algebraMap F L)))
             (ResidueField (vRing w)) : ℤ)) * WithTop.untopD 0 (w y)) * algebraMap O F u := by
  obtain ⟨u, hu, h⟩ := norm_eq_heightOne (F := F) y hy hϖ
  refine ⟨u, hu, ?_⟩
  rw [h]
  congr 2
  obtain ⟨e, he⟩ := placesOver_bij (O := O) (F := F) (L := L)
  rw [← finsum_set_coe_eq_finsum_mem, ← finsum_comp_equiv e]
  apply finsum_congr
  intro v
  rw [he v]
  congr 1
  exact congrArg (fun n : ℕ => (n : ℤ)) (resDeg_addv (F := F) v).symm
end ReciprocityTheory.ChartRestriction.G.T0.ValPl
