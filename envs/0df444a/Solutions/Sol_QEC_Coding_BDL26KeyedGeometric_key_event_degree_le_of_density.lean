-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.key_event_degree_le_of_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:04:43.070979+00:00
-- url     : https://prove2.me/submissions/242c9355-a3c0-4594-97cb-8950deefb9b5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricEvents
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricCounts
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_event_degree_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_localPool_card_le_integer


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory
namespace QEC.Coding.BDL26KeyedGeometric
theorem _root_.solution (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (K M : ℕ)
    (t : ℝ) (hJ : BDL26ReplacementEmbedding.IsBoundedDensityLocalMap P J t)
    (hv : BoundedValence P) (hM : (2*K+1 : ℕ)^3*(250*t) ≤ (M : ℝ))
    (e : KeyEvent P key hk J K) :
    ((supportGraph (keySupport P key hk J K)).neighborFinset e).card ≤ 12*56*M^3 :=
  key_event_degree_le P key hk J K M hv (localPool_card_le_integer P J t hJ K M hM) e
end QEC.Coding.BDL26KeyedGeometric
