-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.event_degree_le_of_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:04:46.68519+00:00
-- url     : https://prove2.me/submissions/a929eb2a-a279-42a3-8d05-6e56de3bfa65

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_event_degree_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_localPool_card_le_integer


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K M : ℕ)
    (t : ℝ) (hJ : BDL26ReplacementEmbedding.IsBoundedDensityLocalMap P J t)
    (hv : BoundedValence P) (hM : (2*K+1 : ℕ)^3*(250*t) ≤ (M : ℝ))
    (e : Event P J K) :
    ((supportGraph (eventSupport P J K)).neighborFinset e).card ≤ 12*56*M^3 :=
  event_degree_le P J K M hv (localPool_card_le_integer P J t hJ K M hM) e
end QEC.Coding.BDL26RandomPerturbation
