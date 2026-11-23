-- Prove2me | solution 1 for P2M_GlobalTheory_TorusEnd_valAt__eval__5db942836e7d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:30:18.346972+00:00
-- url     : https://prove2.me/submissions/384674dd-a4d8-4ab1-bcc0-b769a56be3a2

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTopLePreimageOfISupEqTop
import Theorems.Thm_P2M_GlobalTheory_valAt__constFn_1b31686fad50
import Theorems.Thm_P2M_GlobalTheory_valAt__eq_valAtHom_eb5802171cfc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.TorusEnd
namespace GlobalTheory.TorusEnd
theorem _root_.solution {X : Over (Sp ℂ)} {κ : Type*} (x : 𝟙_ (Over (Sp ℂ)) ⟶ X) (U : X.left.Opens)
    (h : ⊤ ≤ x.left ⁻¹ᵁ U) (r : κ → Γ(X.left, U)) (P : MvPolynomial κ ℂ) :
    valAt' x.left U (MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ U le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r P) = MvPolynomial.eval (fun i => valAt' x.left U (r i)) P := by
  have hc : (valAtHom x.left U h).comp (RingHom.comp (X.hom.appLE ⊤ U le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) = RingHom.id ℂ := by
    ext a
    have := valAt'_constFn x.left X.hom (Over.w x) U a h
    rw [valAt'_eq_valAtHom _ h] at this
    exact this
  rw [valAt'_eq_valAtHom _ h, MvPolynomial.hom_eval₂, hc]
  simp only [valAt'_eq_valAtHom _ h]
  rfl
end GlobalTheory.TorusEnd
