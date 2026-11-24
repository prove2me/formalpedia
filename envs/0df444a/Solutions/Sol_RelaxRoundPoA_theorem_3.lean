-- Prove2me | solution 1 for RelaxRoundPoA.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T08:11:31.328003+00:00
-- url     : https://prove2.me/submissions/ec9bbccd-78b6-4ef4-8083-b8a90787ae54

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism
import Definitions.Def_RelaxRoundPoA_HalfClosed
import Definitions.Def_RelaxRoundPoA_IsPayYourBid
import Definitions.Def_RelaxRoundPoA_ExpFinite
import Definitions.Def_RelaxRoundPoA_IsExactMaximizer
import Definitions.Def_RelaxRoundPoA_IsObliviousRounding
import Definitions.Def_RelaxRoundPoA_IsRounded
import Definitions.Def_RelaxRoundPoA_IsSmooth
import Theorems.Thm_RelaxRoundPoA_lemma_1
import Theorems.Thm_RelaxRoundPoA_theorem_3_prime
import Theorems.Thm_RelaxRoundPoA_isSmooth_of_half

open MeasureTheory ProbabilityTheory NNReal RelaxRoundPoA

theorem solution {N : Type*} [Fintype N] [DecidableEq N] {Ω' : Type*} [MeasurableSpace Ω']
    (Val : N → Set (Ω' → ℝ≥0))
    (Ω : Set Ω') (α : ℝ) (R : Kernel Ω' Ω') (M' M : Mechanism N Ω') (lam mu : ℝ)
    (hhalf : HalfClosed Val) (hpay' : IsPayYourBid Val M') (hpay : IsPayYourBid Val M)
    (hfin' : ExpFinite Val M') (hfin : ExpFinite Val M)
    (hexact' : IsExactMaximizer Val Set.univ M') (hsmooth' : IsSmooth Val Set.univ M' lam mu)
    (hround : IsObliviousRounding Val Ω α R) (hrel : IsRounded Val M' R M) :
    IsSmooth Val Ω M (lam / (2 * α)) mu := by
  have hhalf_smooth' : IsSmoothHalf Val Set.univ M' (lam / 2) mu :=
    lemma_1 Val Set.univ M' lam mu hhalf hpay' hfin' hexact' hsmooth'
  have hhalf_smooth : IsSmoothHalf Val Ω M (lam / 2 / α) mu :=
    theorem_3_prime Val Ω α R M' M (lam / 2) mu hhalf hpay' hpay hfin' hfin hexact' hround hrel
      hhalf_smooth'
  rw [div_div] at hhalf_smooth
  exact isSmooth_of_half Val Ω M (lam / (2 * α)) mu hhalf hhalf_smooth
