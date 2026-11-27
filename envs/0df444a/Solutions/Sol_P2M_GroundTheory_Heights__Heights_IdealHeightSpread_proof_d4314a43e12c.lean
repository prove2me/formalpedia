-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IdealHeightSpread_proof_d4314a43e12c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:57:40.141373+00:00
-- url     : https://prove2.me/submissions/1cb36461-0fe0-4871-92ce-4da8ff9bb88c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIdealHeightSpread
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIdealHeightSpread

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
namespace GroundTheory.Heights₂.Heights
namespace IdealHeightSpread
theorem _root_.solution : IdealHeightSpread.Statement := by
  intro R _ _ I P _ _
  classical
  have hF := I.finite_minimalPrimes_of_isNoetherianRing R

  let a : Ideal R → R := fun p =>
    if h : ¬ (p : Set R) ⊆ P then Classical.choose (Set.not_subset.mp h) else 1
  have ha : ∀ p : Ideal R, ¬ p ≤ P → a p ∈ p ∧ a p ∉ P := by
    intro p h
    have h' : ¬ (p : Set R) ⊆ P := h
    simp only [a, dif_pos h']
    exact Classical.choose_spec (Set.not_subset.mp h')
  let s : Finset (Ideal R) := hF.toFinset.filter (fun p => ¬ p ≤ P)
  refine ⟨∏ p ∈ s, a p, ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨p, hp, hpP⟩
    exact (ha p (Finset.mem_filter.mp hp).2).2 hpP
  · intro Q _ _ hgQ
    rw [Ideal.height_eq_inf_minimalPrimes (I.map (algebraMap R (Localization.AtPrime Q)))]
    refine le_iInf₂ fun J hJ => ?_
    have hJp : J.IsPrime := hJ.isPrime
    have hmin : J.comap (algebraMap R (Localization.AtPrime Q)) ∈ I.minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map Q.primeCompl] at hJ
      exact hJ
    set p := J.comap (algebraMap R (Localization.AtPrime Q)) with hpdef
    have hpp : p.IsPrime := hmin.1.1

    have hpQ : p ≤ Q := by
      intro x hx
      by_contra hxQ
      have hu := IsLocalization.map_units (Localization.AtPrime Q) (⟨x, hxQ⟩ : Q.primeCompl)
      exact hJp.ne_top (Ideal.eq_top_of_isUnit_mem J hx hu)

    have hpP : p ≤ P := by
      by_contra hnot
      apply hgQ
      apply hpQ
      have hps : p ∈ s := Finset.mem_filter.mpr ⟨hF.mem_toFinset.mpr hmin, hnot⟩
      exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem a hps) (ha p hnot).1
    have hdisj : Disjoint (P.primeCompl : Set R) (p : Set R) := by
      rw [Set.disjoint_left]
      intro x hx hxp
      exact hx (hpP hxp)
    have hJh : J.height = p.height := (IsLocalization.height_under Q.primeCompl J).symm
    rw [hJh, ← IsLocalization.height_map_of_disjoint P.primeCompl (S := Localization.AtPrime P) p hdisj]
    exact Ideal.height_mono (Ideal.map_mono hmin.1.2)
end IdealHeightSpread
end GroundTheory.Heights₂.Heights
