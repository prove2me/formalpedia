-- Prove2me | solution 1 for PriceQualityService.Surplus.optimal_profit_order
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:34:28.79527+00:00
-- url     : https://prove2.me/submissions/2cd78187-85aa-442b-ab71-7a9469c0d68b

import Mathlib
import Definitions.Def_PriceQualityService_Surplus_Problems
set_option autoImplicit false
open PriceQualityService.Surplus

theorem solution {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ)
    (hc : ∀ i, 0 < c i) (hts : ts ≤ tl)
    (q t : Fin N → ℝ) (ht : ∀ i, t i ∈ Set.Icc ts tl)
    (pDag : Fin N → ℝ) (hDag : IsPriceOptimal α a b c s q t pDag)
    (pDdag tDdag : Fin N → ℝ) (hDdag : IsPriceServiceOptimal α a b c s ts tl q pDdag tDdag)
    (pStar qStar tStar : Fin N → ℝ) (hStar : IsJointOptimal α a b c s ts tl pStar qStar tStar) :
    PriceQualityService.Joint.profit α a b c s pDag q t ≤ PriceQualityService.Joint.profit α a b c s pDdag q tDdag ∧
      PriceQualityService.Joint.profit α a b c s pDdag q tDdag ≤ PriceQualityService.Joint.profit α a b c s pStar qStar tStar :=
  ⟨hDdag.2 pDag t ht, hStar.2 pDdag q tDdag hDdag.1⟩
