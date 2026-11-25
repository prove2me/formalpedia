-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_geoNum_comp_perm_a68f58b0bb57
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:32:52.459802+00:00
-- url     : https://prove2.me/submissions/7cc309d9-e3ad-4964-94c4-af214d5aeb12

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsWellDefined
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChoice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmISymm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmISymm
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.ThmISymm
theorem _root_.solution
    (hEU : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement (ZMod p) ι)
    (hSy : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.AI.I1.SymmStatement (ZMod p) ι)
    (hGN : ReciprocityTheory.ChartRestriction.G.AI.I1.GeoNumStatement ι) (hFC : FibreCompStatement)
    {P : Ideal (MRing ι)} {n : ℕ} {A : HermLine ι} {s : MRing ι} {W : Ideal (MRing ι)}
    (hP : IsArithVar P (n + 1)) (hs : IsSectionOn P A s) (hW : W ∈ divSupp P s)
    (hv : ¬ IsHorizontal W) (a : Fin n → K → ℤ) (τ : Equiv.Perm (Fin n)) :
    geoNum n W (a ∘ τ) = geoNum n W a := by
  obtain ⟨hp, hpW, hWm, hWv⟩ := hFC K ι P n A s W hP hs hW hv
  have : Fact (charOf W).Prime := ⟨hp⟩
  obtain ⟨I, hI, -⟩ := hEU (charOf W)
  rw [hGN (charOf W) I hI W n (a ∘ τ) hWm hpW hWv, hGN (charOf W) I hI W n a hWm hpW hWv]
  exact hSy (charOf W) I hI _ n a τ hWv
end GroundTheory.Heights₂.Heights.Inter.ThmISymm
