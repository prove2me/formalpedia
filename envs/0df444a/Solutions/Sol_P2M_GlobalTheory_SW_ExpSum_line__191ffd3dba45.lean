-- Prove2me | solution 1 for P2M_GlobalTheory_SW_ExpSum_line__191ffd3dba45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:31:25.245354+00:00
-- url     : https://prove2.me/submissions/ea568546-0c38-4929-be0e-5f9fe16b5040

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ExpSum
variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
open Classical
namespace GlobalTheory.SW.ExpSum
theorem _root_.solution (Z : CF Ψ N N) (z z' : CF Ψ n N) (τ : Ψ) (a b : Fin N) (s : ℂ) :
    (Z, z, z') + s • ((dir Ψ τ a b, 0, 0) : CF Ψ N N × CF Ψ n N × CF Ψ n N) =
      (Z + s • dir Ψ τ a b, z, z') := by simp
end GlobalTheory.SW.ExpSum
