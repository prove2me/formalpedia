-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.exists_local_pool_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:17:07.985347+00:00
-- url     : https://prove2.me/submissions/0044c2e5-5361-4cd1-b2df-8388d15c60f8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalCounts

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (t : ℝ) (K : ℕ) :
    ∃ M : ℕ, (2*K+1 : ℕ)^3*(250*t) ≤ (M : ℝ) := by
  obtain ⟨M,hM⟩ := exists_nat_gt ((2*K+1 : ℕ)^3*(250*t))
  exact ⟨M,hM.le⟩
end QEC.Coding.BDL26RandomPerturbation
