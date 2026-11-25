-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLatNm_isOfDegree_readElt_1d0629766c62
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:12:08.870853+00:00
-- url     : https://prove2.me/submissions/a8c5268e-5960-43d1-a4c9-028322c66d78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatNmSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_exists_reads_rep_225d7bce90a6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_reads_readElt_97ddeb3ac6cc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.ChartLatNm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
variable (P : ArithVariety n) (y : Coord n → Ω)
variable (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (hb : Geo.Birational (ι := blockIdx n) y)
namespace GroundTheory.Heights₂.Heights.ChartLatNm
theorem _root_.solution (c₀ : (k : ι) → Fin (n k + 1)) (hc₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0) (b : ι → ℤ)
    (s : Ω) : P.IsOfDegree b (readElt P y hP hb c₀ b s) := by
  obtain ⟨f, q, δf, δq, hf, hq, hd, hq0, he⟩ := exists_reads_rep y hb c₀ hc₀ b s
  have hmk := (reads_readElt P y hP hb c₀ hc₀ b s f q δf δq hf hq hd).mp he
  have hQ : P.mkF q ≠ 0 := fun h => hq0 ((mkF_eq_zero_iff' P y hP hq).mp h)
  refine ⟨f, q, δf, δq, hf, hq, fun k => by linarith [hd k], ?_, ?_⟩
  · rw [hP, mem_mCoordIdeal_iff y hq]
    exact hq0
  · rw [hmk, mul_div_cancel_right₀ _ hQ]
end GroundTheory.Heights₂.Heights.ChartLatNm
