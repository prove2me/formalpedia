-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LelongLimitGoodPoints_proof_51f69a1f7f0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:02:44.188277+00:00
-- url     : https://prove2.me/submissions/0c6801af-b832-4563-bf23-c2aba971255d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitGoodPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGeneralPointBranches
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitAtBranches
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongLimitGoodPoints
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_varInt_eq_zero_of_vanish_87c7772e6a98


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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
namespace GroundTheory.Heights₂.Heights
namespace LelongLimitGoodPoints
theorem _root_.solution (hBr : DivisorGeneralPointBranches.Statement)
    (hLim : LelongLimitAtBranches.Statement) (hOrd : LocalOrder.Statement) :
    LelongLimitGoodPoints.Statement := by
  classical
  intro n d J u φ hJ hdim hu hφ
  obtain ⟨I, hI, hIdim, hgood⟩ := hBr n d J u hJ hdim hu
  refine ⟨I, hI, hIdim, fun q hqJ hqu hqI => ?_⟩
  obtain ⟨W, hWm, hqW, hone, hWloc, m, γ, ord, π, hcov, hsl, hmeet, hvan, hbij⟩ :=
    hgood q hqJ hqu hqI
  obtain ⟨N, hN, hlim⟩ :=
    hLim n d J W u q m γ ord π φ hJ hdim hu hWm hqW hφ hWloc hcov hsl hmeet hvan hbij
  have hmult := hOrd n d J W u q m γ ord hJ hdim hu hWm hqW hcov hsl hmeet hvan
  have hclosed : ∀ W' : Ideal (MvPolynomial (Fin n) ℂ), IsClosed (zeroSet W') := fun W' => by
    have : zeroSet W' = ⋂ p ∈ W', {x : Fin n → ℂ | MvPolynomial.eval x p = 0} := by
      ext x; simp [zeroSet]
    rw [this]
    exact isClosed_biInter fun p _ => isClosed_eq (MvPolynomial.continuous_eval p) continuous_const

  set O := ⋂ W' ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes \ {W}, (zeroSet W')ᶜ
  have hO : O ∈ 𝓝 q :=
    (Filter.biInter_mem
      ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).sdiff)).2 fun W' hW' =>
      (hclosed W').isOpen_compl.mem_nhds fun h => hW'.2 (hone W' hW'.1 h)
  refine ⟨N ∩ O, Filter.inter_mem hN hO, fun f hf hfc hfN => ?_⟩
  have hL : (∑ᶠ (W' : Ideal (MvPolynomial (Fin n) ℂ))
      (_ : W' ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
      (localMult (J ⊔ Ideal.span {linForm u}) W' : ℝ) * varInt W' d f φ) =
      (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ := by
    rw [finsum_eq_single _ W fun W' hne => ?_, finsum_eq_dif, dif_pos hWm]
    rw [finsum_eq_dif]
    split_ifs with hW'
    · rw [varInt_eq_zero_of_vanish W' f φ fun x hx => image_eq_zero_of_notMem_tsupport fun hxs =>
        Set.mem_iInter₂.1 (hfN hxs).2 W' ⟨hW', hne⟩ hx, mul_zero]
    · rfl
  rw [hL, hmult]
  exact hlim f hf hfc fun x hx => (hfN hx).1
end LelongLimitGoodPoints
end GroundTheory.Heights₂.Heights
