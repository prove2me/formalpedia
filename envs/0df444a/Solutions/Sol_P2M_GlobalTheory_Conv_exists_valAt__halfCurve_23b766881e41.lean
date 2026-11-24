-- Prove2me | solution 1 for P2M_GlobalTheory_Conv_exists_valAt__halfCurve_23b766881e41
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:00:40.893581+00:00
-- url     : https://prove2.me/submissions/03d93da1-c6da-4a34-b288-6f64951b0ebf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSumsAtHalfCurveFraction
import Theorems.Thm_GlobalTheory_Conv_exists_le_preimage_inclusion
import Theorems.Thm_GlobalTheory_Conv_halfCurve_inclusion
import Theorems.Thm_P2M_GlobalTheory_Conv_valAt__halfCurve_ca595a84c520
import Theorems.Thm_GlobalTheory_Conv_ev_congr
import Theorems.Thm_GlobalTheory_HolHom_valR_spMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


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
theorem _root_.solution {T : ℝ} {yT : Sp (halfRing T) ⟶ Z} {y : Sp convLaurent ⟶ Z}
    (hy : spMap (halfIncl T : halfRing T →+* convLaurent) ≫ yT = y) {U : Z.Opens}
    (hU : ⊤ ≤ y ⁻¹ᵁ U) :
    ∃ T' ≥ T, (∀ w : ℂ, T' < w.im → ⊤ ≤ halfCurve yT w ⁻¹ᵁ U) ∧
      ∀ f : Γ(Z, U), ∃ hf : ((valR y U f : convLaurent) : ℂ⸨X⸩) ∈ halfRing T',
        ∀ (w : ℂ) (hw : T' < w.im), valAt' (halfCurve yT w) U f = ev T' w hw ⟨_, hf⟩ := by
  subst hy
  obtain ⟨T', h, hU'⟩ := exists_le_preimage_inclusion yT hU
  refine ⟨T', h, fun w hw => ?_, fun f => ?_⟩
  · rw [← halfCurve_inclusion h yT hw]
    exact (valAt'_halfCurve _ hU' hw).1
  · have e := valR_spMap (halfIncl T' : halfRing T' →+* convLaurent) _ U hU' f
    rw [← Category.assoc, ← spMap_comp] at e
    have e' : ((valR (spMap (halfIncl T : halfRing T →+* convLaurent) ≫ yT) U f : convLaurent) :
        ℂ⸨X⸩) = (valR (spMap (Subalgebra.inclusion (halfRing_mono h) :
          halfRing T →+* halfRing T') ≫ yT) U f : halfRing T') :=
      congrArg (fun x : convLaurent => (x : ℂ⸨X⸩)) e
    refine ⟨e' ▸ Subtype.property _, fun w hw => ?_⟩
    rw [← halfCurve_inclusion h yT hw, (valAt'_halfCurve _ hU' hw).2]
    exact ev_congr hw hw e'.symm
end GlobalTheory.Conv
