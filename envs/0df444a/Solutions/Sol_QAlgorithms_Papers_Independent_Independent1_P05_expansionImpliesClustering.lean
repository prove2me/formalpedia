-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P05.expansionImpliesClustering
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:44:46.741807+00:00
-- url     : https://prove2.me/submissions/cab1370d-e98b-4161-b245-36ac83d6e491

import Mathlib
import Definitions.Def_QAlgorithms_Defs_NLTSPreparationCircuits
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P05_Model
set_option autoImplicit false

/-! Statements from Anshu--Breuckmann--Nirkhe, arXiv:2206.13228v4.
Theorem 5 and three construction-specific expansion claims are deferred in HARD.md.
All new definitions are specific to this paper. -/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P05
open PresentedCSS

/-- Lemma 8, printed on PDF p.6 (Definitions 6--7 on p.5).
Positive parameters from its proof and following paragraph exclude delta=0. -/


theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (V : Set (NLTSWord n)) (delta mu nu : ℝ) (hd : 0 < delta) (hm : 0 < mu)
    (hmn : mu < nu) (hexp : nltsExpanding A V nu (delta/mu)) :
    nltsClustering A V delta mu nu := by
  intro x hx hAx
  by_cases h1 : (hammingNorm x : ℝ) ≤ mu*n
  · exact Or.inl h1
  right
  by_contra h2
  push_neg at h1 h2
  have := hexp x hx h2.le
  have hx0 : (0:ℝ) ≤ hammingNorm x := by positivity
  have : delta/mu*(hammingNorm x : ℝ) ≤ delta*n := le_trans this hAx
  rw [div_mul_eq_mul_div, div_le_iff₀ hm] at this
  nlinarith

