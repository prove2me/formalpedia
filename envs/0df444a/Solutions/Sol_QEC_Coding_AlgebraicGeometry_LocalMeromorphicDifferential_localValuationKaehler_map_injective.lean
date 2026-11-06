-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localValuationKaehler_map_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:25:31.627194+00:00
-- url     : https://prove2.me/submissions/b74309c1-4aef-45de-86a2-d2e48188ac2e

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalKaehlerCyclic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalMeromorphicDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AnalyticGermEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicValuationDifferentials
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalMeromorphicDifferential_localValuationResidueEvaluation_ker
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DiscreteAnalyticOrder_exists_uniformizer_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalMeromorphicDifferential_uniformizerDifferential_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_localKaehler_map_injective_of_splitResidue


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
noncomputable section
variable (K : Type*) [Field K] [Algebra ℂ K] (a : ℂ)
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary004
variable [Algebra K (MeromorphicGermRing a)] [IsScalarTower ℂ K (MeromorphicGermRing a)]
local notation "V" => localValuationRing K a
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary005
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary006
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary007
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary008
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary009
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary010
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary011
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary012
namespace QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
theorem _root_.solution
    [IsDiscreteValuationRing V] [Algebra.EssFiniteType ℂ V] :
    Function.Injective (KaehlerDifferential.map ℂ ℂ V K) := by
  obtain ⟨pi,m,hpi,hm,he⟩ := exists_uniformizer_order (localFieldOrder K a)
  exact QEC.Coding.AlgebraicGeometry.localKaehler_map_injective_of_splitResidue ℂ V K
    (localValuationResidueEvaluation K a) (localValuationResidueEvaluation_ker K a) pi
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer pi).mp hpi)
    (fun _ _ h => Subtype.ext h)
    (uniformizerDifferential_ne_zero K a pi m hm he)
end QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
