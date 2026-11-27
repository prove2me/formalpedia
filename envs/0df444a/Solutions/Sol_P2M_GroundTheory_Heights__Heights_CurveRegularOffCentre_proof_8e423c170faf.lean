-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CurveRegularOffCentre_proof_8e423c170faf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:54:50.319074+00:00
-- url     : https://prove2.me/submissions/01e6cc31-3aa1-41cd-987d-63959f3df0fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveRegularOffCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveRegularOffFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveProperClosedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveRegularOffCentre

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
open MvPolynomial ComplexSets Filter Topology
namespace GroundTheory.Heights₂.Heights
namespace CurveRegularOffCentre
theorem _root_.solution (hG : CurveGermComponents.Statement) (hR : CurveRegularOffFinite.Statement)
    (hF : CurveProperClosedFinite.Statement) : CurveRegularOffCentre.Statement := by
  classical
  intro n I q hdim
  obtain ⟨N, hN, hcomp⟩ := hG n I q hdim
  have hZc : ∀ J : Ideal (MvPolynomial (Fin n) ℂ), IsClosed (zeroSet J) := fun J ↦ by
    have : zeroSet J = ⋂ p ∈ J, {x : Fin n → ℂ | eval x p = 0} := by ext x; simp [zeroSet]
    rw [this]
    exact isClosed_biInter fun p _ ↦ isClosed_eq (MvPolynomial.continuous_eval p) continuous_const
  have hM : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ I
  set S := {W | W ∈ I.minimalPrimes ∧ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = 1}
  have hS : S.Finite := hM.subset fun W hW ↦ hW.1
  choose! F hFfin hFchart using fun W (hW : W ∈ S) ↦ hR n W hW.1.1.1 hW.2
  have hnle : ∀ W ∈ S, ∀ W' ∈ I.minimalPrimes \ {W}, ¬ W' ≤ W := fun W hW W' hW' hle ↦
    hW'.2 (le_antisymm hle (hW.1.2 hW'.1.1 hle))
  set Bad := (⋃ W ∈ S, F W) ∪ ⋃ W ∈ S, ⋃ W' ∈ I.minimalPrimes \ {W}, zeroSet W ∩ zeroSet W'
  have hBad : Bad.Finite := (hS.biUnion hFfin).union (hS.biUnion fun W hW ↦
    hM.sdiff.biUnion fun W' hW' ↦ hF n W W' hW.1.1.1 hW.2 (hnle W hW W' hW'))
  have hN'o : IsOpen (interior N \ (Bad \ {q})) := isOpen_interior.sdiff hBad.sdiff.isClosed
  refine ⟨_, hN'o.mem_nhds ⟨mem_interior_iff_mem_nhds.2 hN, fun h ↦ h.2 rfl⟩, ?_⟩
  rintro x ⟨hxI, hxN, hxB⟩ hxq
  have hxBad : x ∉ Bad := fun h ↦ hxB ⟨h, hxq⟩
  obtain ⟨W, hWm, hWd, -, hxW⟩ := hcomp x ⟨hxI, interior_subset hxN⟩
  have hWS : W ∈ S := ⟨hWm, hWd⟩
  obtain ⟨A, O, V, g, hO, hV, hxV, hg, hAg, hWV⟩ :=
    hFchart W hWS x hxW fun h ↦ hxBad (Or.inl (Set.mem_biUnion hWS h))
  set V' := V ∩ interior N ∩ ⋂ W' ∈ I.minimalPrimes \ {W}, (zeroSet W')ᶜ
  have hV' : IsOpen V' := (hV.inter isOpen_interior).inter
    (hM.sdiff.isOpen_biInter fun W' _ ↦ (hZc W').isOpen_compl)
  have hIV' : zeroSet I ∩ V' = zeroSet W ∩ V' := by
    ext z
    refine ⟨fun ⟨hzI, hzV⟩ ↦ ⟨?_, hzV⟩, fun ⟨hzW, hzV⟩ ↦ ⟨fun p hp ↦ hzW p (hWm.1.2 hp), hzV⟩⟩
    obtain ⟨W'', hW''m, -, -, hzW''⟩ := hcomp z ⟨hzI, interior_subset hzV.1.2⟩
    by_cases h : W'' = W
    · exact h ▸ hzW''
    · exact absurd hzW'' (Set.mem_iInter₂.1 hzV.2 W'' ⟨hW''m, h⟩)
  refine ⟨A, O ∩ g ⁻¹' V', V', g, hg.continuousOn.isOpen_inter_preimage hO hV', hV',
    ⟨⟨hxV, hxN⟩, Set.mem_iInter₂.2 fun W' hW' hxW' ↦ hxBad (Or.inr (Set.mem_biUnion hWS
      (Set.mem_biUnion hW' ⟨hxW, hxW'⟩)))⟩, hg.mono Set.inter_subset_left,
    fun y hy ↦ hAg y hy.1, ?_⟩
  rw [hIV', Set.image_inter_preimage, ← hWV]
  ext z
  exact ⟨fun ⟨hzW, hzV⟩ ↦ ⟨⟨hzW, hzV.1.1⟩, hzV⟩, fun ⟨⟨hzW, _⟩, hzV⟩ ↦ ⟨hzW, hzV⟩⟩
end CurveRegularOffCentre
end GroundTheory.Heights₂.Heights
