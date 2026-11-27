-- Prove2me | solution 1 for P2M_GlobalTheory_WachLettersCompare__D_fixed_4a0839ac6157
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:53:35.320484+00:00
-- url     : https://prove2.me/submissions/a8615568-40c3-4017-9295-6fd64b55ff23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_LettersFreeOfRank
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_WachLettersFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LetterSandwichOfFrobMatrices
import Theorems.Thm_GlobalTheory_WachLettersCompare_mem_Nl_iff
import Theorems.Thm_P2M_GlobalTheory_WachLettersCompare__D_smulA_1d6e3a28cb08
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LetterBasisDecomposition_phi_letE


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.WachLettersCompare
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
attribute [local instance] letterModule
variable {W T}
namespace GlobalTheory.WachLettersCompare
theorem _root_.solution (i : ZMod n) {x : W.DD T} (hx : x ∈ W.Nl T (i - 1)) :
    (letE i : LetA O n) • W.φD T x = W.φD T x := by
  rw [← phi_letE W i, ← φD_smulA, ((mem_Nl_iff W T _ x).1 hx).2]
end GlobalTheory.WachLettersCompare
