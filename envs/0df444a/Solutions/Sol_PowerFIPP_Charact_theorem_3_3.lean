-- Prove2me | solution 1 for PowerFIPP.Charact.theorem_3_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T10:22:19.193992+00:00
-- url     : https://prove2.me/submissions/4c666b26-3f86-4af0-a10c-ee5c32c25111
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PowerFIPP_Charact_Model
import Theorems.Thm_PowerFIPP_Charact_lemma_3_2_i
import Theorems.Thm_PowerFIPP_Charact_lemma_3_2_ii
import Theorems.Thm_PowerFIPP_Charact_theorem_3_3_QM

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal

open PowerFIPP.Charact

theorem solution {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (mkt : Market Ω n) (p : ℝ)
    (hS : mkt.Standing P ℱ) (hp0 : p ≠ 0) (hp1 : p < 1) (hAC : AC mkt) (hAD : AD P mkt)
    (M Dc J : ℝ≥0 → Ω → ℝ) (hM : IsLemma31MV P ℱ mkt M Dc J)
    (Q : Measure Ω) (hQ : IsQM P ℱ mkt M Q)
    (bM : ℝ≥0 → Ω → Fin n → ℝ) (FM : ℝ≥0 → Ω → Measure (Fin n → ℝ))
    (hchar : IsDiffChar Q ℱ mkt.R bM mkt.c FM)
    (RMc : ℝ≥0 → Ω → Fin n → ℝ) (hRMc : IsContPart Q ℱ mkt.R bM RMc)
    (πstar : ℝ≥0 → Ω → Fin n → ℝ) (hπ : πstar ∈ Gamma P P ℱ mkt (U mkt p)) :
    IsFIPP P P ℱ mkt (U mkt p) πstar ↔
      cond_i P Q ℱ mkt p M RMc πstar ∧ cond_ii P mkt p bM FM πstar ∧
        cond_iii P mkt p bM FM := by
  -- Lemma 3.2 (i): the admissible classes coincide, `Γ^P_𝒞 = Γ^{Q^M}_𝒞`
  have hG : Gamma P P ℱ mkt (U mkt p) = Gamma Q P ℱ mkt (UV mkt p) :=
    lemma_3_2_i P ℱ mkt p hS hp0 hp1 hAD M Dc J hM Q hQ
  -- Lemma 3.2 (ii): `U` is a `P`-FIPP iff `U^V` is a `Q^M`-FIPP, with the same `π*`
  rw [lemma_3_2_ii P ℱ mkt p hS hp0 hp1 hAD M Dc J hM Q hQ πstar]
  -- the characterization of `Q^M`-FIPPs of the form `U^V`
  exact theorem_3_3_QM P ℱ mkt p hS hp0 hp1 hAC hAD M Dc J hM Q hQ bM FM hchar RMc hRMc πstar
    (hG ▸ hπ)
