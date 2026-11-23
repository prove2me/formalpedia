-- Prove2me | solution 1 for P2M_GlobalTheory_Conv_valAt__halfCurve_ca595a84c520
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:49.513436+00:00
-- url     : https://prove2.me/submissions/c3a6f7d7-b870-4d78-81be-d0e13a80fa6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSumsAtHalfCurveFraction
import Theorems.Thm_GlobalTheory_Conv_halfCurve_eq
import Theorems.Thm_GlobalTheory_HolHom_valR_spMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Filter Topology
open scoped PowerSeries LaurentSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HolHom
open GlobalTheory GlobalTheory.Conv
variable {Z : Scheme.{0}}
namespace GlobalTheory.Conv
theorem _root_.solution {T : ℝ} (yT : Sp (halfRing T) ⟶ Z) {U : Z.Opens} (hU : ⊤ ≤ yT ⁻¹ᵁ U)
    {w : ℂ} (hw : T < w.im) :
    ⊤ ≤ halfCurve yT w ⁻¹ᵁ U ∧ ∀ f, valAt' (halfCurve yT w) U f = ev T w hw (valR yT U f) := by
  rw [halfCurve_eq _ hw]
  exact ⟨fun p _ => hU (x := spMap _ p) trivial, fun f => valR_spMap _ yT U hU f⟩
end GlobalTheory.Conv
