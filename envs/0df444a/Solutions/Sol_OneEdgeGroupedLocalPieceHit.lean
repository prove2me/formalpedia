-- Prove2me | solution 1 for OneEdgeGroupedLocalPieceHit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:35:40.999049+00:00
-- url     : https://prove2.me/submissions/0b012fac-b0b4-438e-9a13-c10f3c377349

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Analysis.Convex.Between
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_PlaneFaceData
import Definitions.Def_PolygonallyPathConnected

import Mathlib

open Classical

namespace OE_3cac

theorem joined_aux (γ : PolygonalPath) :
    ∀ i (hi : i < γ.vertices.length),
      JoinedIn γ.carrier (γ.vertices[0]'(by omega)) (γ.vertices[i]) := by
  intro i
  induction i with
  | zero =>
    intro hi
    refine JoinedIn.refl ?_
    rw [γ.carrier_eq]
    left
    left
    have := γ.source_eq_head
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hi] at this
    simp only [Option.some.injEq] at this
    rw [this]
  | succ n ih =>
    intro hi
    have h1 := ih (by omega)
    refine h1.trans ?_
    have hsub : segment ℝ (γ.vertices[n]) (γ.vertices[n+1]) ⊆ γ.carrier := by
      intro p hp
      rw [γ.carrier_eq]
      right
      exact ⟨n, hi, hp⟩
    have hpc : IsPathConnected (segment ℝ (γ.vertices[n]) (γ.vertices[n+1])) :=
      (convex_segment _ _).isPathConnected ⟨_, left_mem_segment ℝ _ _⟩
    have hj : JoinedIn (segment ℝ (γ.vertices[n]) (γ.vertices[n+1]))
        (γ.vertices[n]) (γ.vertices[n+1]) :=
      hpc.joinedIn _ (left_mem_segment ℝ _ _) _ (right_mem_segment ℝ _ _)
    exact hj.mono hsub

theorem joined (γ : PolygonalPath) : JoinedIn γ.carrier γ.source γ.target := by
  have hlen : 0 < γ.vertices.length := List.length_pos_iff.mpr γ.vertices_nonempty
  have h := joined_aux γ (γ.vertices.length - 1) (by omega)
  have hs := γ.source_eq_head
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlen] at hs
  simp only [Option.some.injEq] at hs
  have ht := γ.target_eq_last
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at ht
  simp only [Option.some.injEq] at ht
  rw [← hs, ← ht]
  exact h

end OE_3cac

noncomputable section

theorem solution
    (A Csigma C localUnion : Set (EuclideanSpace ℝ (Fin 2)))
    (a b : EuclideanSpace ℝ (Fin 2))
    {ι : Type*}
    (rawPieces : Finset ι)
    (piece : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (groupedLocalPieces : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (groupedLocalPieceOf : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (hC : ComplementComponent (A ∪ segment ℝ a b) C)
    (hC_subset_Csigma : C ⊆ Csigma)
    (hCsigma_subset_old_compl : Csigma ⊆ Aᶜ)
    (hCsigma_path : PolygonallyPathConnected Csigma)
    (hOpenSegment_Csigma : openSegment ℝ a b ⊆ Csigma)
    (hLocalUnion_open : IsOpen localUnion)
    (hSegment_subset_localUnion : segment ℝ a b ⊆ localUnion)
    (hraw_cover :
      ∀ x : EuclideanSpace ℝ (Fin 2),
        x ∈ localUnion ∩ Csigma →
          x ∉ segment ℝ a b →
            ∃ k ∈ rawPieces, x ∈ piece k)
    (hgroupedLocalPiece_mem :
      ∀ i, i ∈ rawPieces → groupedLocalPieceOf i ∈ groupedLocalPieces)
    (hrawPiece_subset_groupedLocalPiece :
      ∀ i, i ∈ rawPieces → piece i ⊆ groupedLocalPieceOf i) :
    ∃ G ∈ groupedLocalPieces, (C ∩ G).Nonempty := by
  obtain ⟨⟨x, hx⟩, hCsub, hCconn, hCmax⟩ := hC
  have hxS : x ∉ segment ℝ a b := fun h => hCsub hx (Or.inr h)
  obtain ⟨m, hm⟩ : (openSegment ℝ a b).Nonempty := by
    rcases eq_or_ne a b with rfl | hab
    · rw [openSegment_same]; exact ⟨a, rfl⟩
    · exact ⟨midpoint ℝ a b, mem_openSegment_iff_div.mpr
        ⟨1, 1, one_pos, one_pos, by norm_num [midpoint_eq_smul_add, smul_add]⟩⟩
  have hmS : m ∈ segment ℝ a b := openSegment_subset_segment ℝ a b hm
  obtain ⟨γ, hγs, hγt, hγc⟩ := hCsigma_path (hC_subset_Csigma hx) (hOpenSegment_Csigma hm)
  have hJ := OE_3cac.joined γ
  rw [hγs, hγt] at hJ
  set p := hJ.somePath
  have hp : ∀ t, p t ∈ Csigma := fun t => hγc (hJ.somePath_mem t)
  have hsegC : IsCompact (segment ℝ a b) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  set Z : Set unitInterval := {t | p t ∈ segment ℝ a b}
  have hZc : IsClosed Z := hsegC.isClosed.preimage p.continuous
  have hZn : Z.Nonempty := ⟨1, by simp [Z, p, hmS]⟩
  set τ := sInf Z
  have hτ : τ ∈ Z := hZc.sInf_mem hZn
  have hτlt : ∀ t, t < τ → p t ∉ segment ℝ a b := fun t ht hz =>
    absurd (csInf_le (OrderBot.bddBelow Z) hz) (not_le.mpr ht)
  have hτpos : 0 < τ := by
    rcases (unitInterval.nonneg' (t := τ)).lt_or_eq with h | h
    · exact h
    · exfalso; apply hxS
      have : p 0 ∈ segment ℝ a b := by rw [h]; exact hτ
      simpa using this
  -- p t ∈ C for t < τ
  have hinC : ∀ t, t < τ → p t ∈ C := by
    have himg : IsConnected (p '' Set.Iio τ) :=
      ⟨⟨_, ⟨0, hτpos, rfl⟩⟩, isPreconnected_Iio.image _ p.continuous.continuousOn⟩
    have hx' : x ∈ p '' Set.Iio τ := ⟨0, hτpos, by simp⟩
    have hU : IsConnected (C ∪ p '' Set.Iio τ) := hCconn.union ⟨x, hx, hx'⟩ himg
    have hsub : C ∪ p '' Set.Iio τ ⊆ (A ∪ segment ℝ a b)ᶜ := by
      rintro y (hy | ⟨t, ht, rfl⟩)
      · exact hCsub hy
      · rintro (h | h)
        · exact hCsigma_subset_old_compl (hp t) h
        · exact hτlt t ht h
    have := hCmax _ ⟨x, Or.inl hx⟩ hsub hU Set.subset_union_left
    intro t ht
    exact this (Or.inr ⟨t, ht, rfl⟩)
  have hev : ∀ᶠ t in nhdsWithin τ (Set.Iio τ), p t ∈ localUnion ∧ t < τ := by
    refine Filter.Eventually.and ?_ self_mem_nhdsWithin
    exact nhdsWithin_le_nhds (p.continuous.continuousAt.preimage_mem_nhds
      (hLocalUnion_open.mem_nhds (hSegment_subset_localUnion hτ)))
  have : (nhdsWithin τ (Set.Iio τ)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hτpos⟩
  obtain ⟨t, htL, htτ⟩ := hev.exists
  obtain ⟨k, hk, hpk⟩ := hraw_cover (p t) ⟨htL, hp t⟩ (hτlt t htτ)
  exact ⟨_, hgroupedLocalPiece_mem k hk, p t, hinC t htτ,
    hrawPiece_subset_groupedLocalPiece k hk hpk⟩
