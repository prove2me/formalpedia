-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_OneComponentGeneralPoint_proof_fa315c84eb62
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:59:53.75923+00:00
-- url     : https://prove2.me/submissions/f9f217de-9777-4c9c-80c7-b2757743d253

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOneComponentGeneralPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVanishNearPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_POneComponentGeneralPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace OneComponentGeneralPoint
theorem _root_.solution (hV : VanishNearPoint.Statement) :
    OneComponentGeneralPoint.Statement := by
  classical
  intro n I W hW
  have hWp : W.IsPrime := hW.1.1
  have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ I

  have hsep : ∀ W' ∈ I.minimalPrimes, W' ≠ W → ∃ g ∈ W', g ∉ W := by
    intro W' hW' hne
    by_contra h
    push Not at h
    exact hne (le_antisymm h (hW.2 hW'.1 h))
  choose! g hgW' hgW using hsep
  set S := hfin.toFinset.erase W with hS
  set f : MvPolynomial (Fin n) ℂ := ∏ W' ∈ S, g W' with hfdef
  have hf : f ∉ W := by
    intro hmem
    obtain ⟨W', hW'S, hgm⟩ := (Ideal.IsPrime.prod_mem_iff (p := W)).1 hmem
    rw [Finset.mem_erase, Set.Finite.mem_toFinset] at hW'S
    exact hgW W' hW'S.2 hW'S.1 hgm
  have hUo : IsOpen {x : Fin n → ℂ | eval x f ≠ 0} :=
    isOpen_ne_fun (MvPolynomial.continuous_eval (p := f)) continuous_const
  refine ⟨{x | eval x f ≠ 0}, hUo, ?_, ?_⟩
  ·
    intro x hx
    rw [mem_closure_iff_nhds]
    intro t ht
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    apply hf
    refine hV n W f x hWp hx ?_
    filter_upwards [ht] with y hyt hyW
    by_contra hne
    have hy : y ∈ t ∩ (GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ {x | eval x f ≠ 0}) :=
      ⟨hyt, hyW, hne⟩
    rw [hempty] at hy
    exact hy
  ·
    rintro x ⟨-, hxf⟩
    refine ⟨{x | eval x f ≠ 0}, hUo.mem_nhds hxf, ?_⟩
    rintro y ⟨hyI, hyf⟩
    have : (RingHom.ker (eval y : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime := RingHom.ker_isPrime _
    have hker : I ≤ RingHom.ker (eval y : MvPolynomial (Fin n) ℂ →+* ℂ) :=
      fun q hq => RingHom.mem_ker.2 (hyI q hq)
    obtain ⟨W', hW', hle⟩ := Ideal.exists_minimalPrimes_le hker
    by_cases hne : W' = W
    · rw [hne] at hle
      intro q hq
      exact RingHom.mem_ker.1 (hle hq)
    · exfalso
      apply hyf
      have hmem : W' ∈ S := by
        rw [hS, Finset.mem_erase, Set.Finite.mem_toFinset]
        exact ⟨hne, hW'⟩
      show eval y (∏ W' ∈ S, g W') = 0
      rw [map_prod]
      exact Finset.prod_eq_zero hmem (RingHom.mem_ker.1 (hle (hgW' W' hW' hne)))
end OneComponentGeneralPoint
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
