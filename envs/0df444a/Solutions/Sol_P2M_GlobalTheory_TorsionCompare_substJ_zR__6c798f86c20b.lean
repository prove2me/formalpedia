-- Prove2me | solution 1 for P2M_GlobalTheory_TorsionCompare_substJ_zR__6c798f86c20b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:33:50.1773+00:00
-- url     : https://prove2.me/submissions/6025e3a9-ac65-49f7-bbfa-ee4d3a3d903a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_OriginChartMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NotIsUnitNatCastOfIsLocalHom
import Theorems.Thm_GlobalTheory_TorsionCompare_psJet_eq_jetOfSeries
import Theorems.Thm_GlobalTheory_TorsionCompare_substJ_zR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionCompare
variable {R : Type} [CommRing R]
namespace GlobalTheory.TorsionCompare
theorem _root_.solution {n d : ℕ} [NeZero n] (m : ℕ) (φ : Fin d → PS R n d)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (q : Fin 1 × Fin d) :
    substJ m φ hφ (zR m q) = jetOfSeries m (φ q.2) := by
  have : Nonempty (Fin n × Fin d) := ⟨(0, q.2)⟩
  rw [substJ_zR, psJet_eq_jetOfSeries]
end GlobalTheory.TorsionCompare
