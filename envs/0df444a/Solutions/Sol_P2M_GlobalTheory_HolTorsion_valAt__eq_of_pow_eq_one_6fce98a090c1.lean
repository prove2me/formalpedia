-- Prove2me | solution 1 for P2M_GlobalTheory_HolTorsion_valAt__eq_of_pow_eq_one_6fce98a090c1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:31:51.698094+00:00
-- url     : https://prove2.me/submissions/b2c96d2d-e4fe-412d-89ad-bb67cb319ce2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionEqAndWeilIsOfIsHolTo
import Theorems.Thm_P2M_GlobalTheory_valAt__one_9935cf2928d8
import Theorems.Thm_P2M_GlobalTheory_valAt__pow_e372e8ea15a8


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.HolTorsion
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E}
namespace GlobalTheory.HolTorsion
theorem _root_.solution {Z : Scheme.{0}} {c : E → (Sp ℂ ⟶ Z)} (hc : IsHolTo B c) (hB : IsPreconnected B)
    {e : Γ(Z, ⊤)} {k : ℕ} (hk : 0 < k) (he : e ^ k = 1) {b₀ b : E} (hb₀ : b₀ ∈ B) (hb : b ∈ B) :
    valAt' (c b) ⊤ e = valAt' (c b₀) ⊤ e := by
  have hcont : ContinuousOn (fun w => valAt' (c w) ⊤ e) B :=
    (hc ⊤ e).2.continuousOn.mono fun w hw => ⟨hw, le_top⟩
  have hfin : (Polynomial.nthRootsFinset k (1 : ℂ) : Set ℂ).Finite := Finset.finite_toSet _
  refine hB.constant_of_mapsTo hfin.isDiscrete hcont (fun w _ => ?_) hb hb₀
  rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset hk, ← valAt'_pow _ le_top, he, valAt'_one _ le_top]
end GlobalTheory.HolTorsion
