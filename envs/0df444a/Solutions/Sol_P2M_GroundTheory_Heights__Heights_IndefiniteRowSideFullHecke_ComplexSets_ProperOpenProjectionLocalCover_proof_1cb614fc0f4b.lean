-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperOpenProjectionLocalCover_proof_1cb614fc0f4b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:58:12.990238+00:00
-- url     : https://prove2.me/submissions/8f9cb1c7-8c36-486a-b561-5c65a4dc97ac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperOpenProjectionLocalCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperOpenProjectionLocalUnbranched
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PUnbranchedProperCountLocallyConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PManifoldZerosComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProperOpenProjectionLocalCover
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_proof_6f657cf29ce3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_UnbranchedProperCountConstant_proof_09b25db4e1f8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_UnbranchedProperCountLocallyConstant_proof_5de2b3cf567d


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
open Topology
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace ProperOpenProjectionLocalCover
theorem _root_.solution (hR : ProperOpenProjectionLocalUnbranched.Statement) :
    ProperOpenProjectionLocalCover.Statement := by
  intro σ _ X B k f d A D hB hf hXB hDo hmaps hprop hopen y₀ hy₀
  obtain ⟨U₁, g, hU₁o, hy₀U₁, hU₁D, hg, hgd, hsec⟩ :=
    hR σ X B k f d A D hB hf hXB hDo hmaps hprop hopen y₀ hy₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU₁o y₀ hy₀U₁
  set U := Metric.ball y₀ r with hUdef
  have hUo : IsOpen U := Metric.isOpen_ball
  have hy₀U : y₀ ∈ U := Metric.mem_ball_self hr
  have hUD : U ⊆ D := hball.trans hU₁D
  have hgU : AnalyticOnNhd ℂ g U := hg.mono hball
  have hgdU : ∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, g t ≠ 0 :=
    fun W hW hWU hWne => hgd W hW (hWU.trans hball) hWne

  set Y : Set (σ → ℂ) := {x | x ∈ X ∩ B ∧ A x ∈ U} with hYdef
  have hfib : ∀ y ∈ U, {x | x ∈ Y ∧ A x = y} = {x | x ∈ X ∩ B ∧ A x = y} := by
    intro y hy
    ext x
    simp only [hYdef, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hx, _⟩, hAx⟩
      exact ⟨hx, hAx⟩
    · rintro ⟨hx, hAx⟩
      exact ⟨⟨hx, hAx ▸ hy⟩, hAx⟩
  have hYmaps : Set.MapsTo A Y U := fun x hx => hx.2
  have hYprop : ∀ K ⊆ U, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K} := by
    intro K hKU hK
    have : {x | x ∈ Y ∧ A x ∈ K} = {x | x ∈ X ∩ B ∧ A x ∈ K} := by
      ext x
      simp only [hYdef, Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hKU h.2⟩, h.2⟩⟩
    rw [this]
    exact hprop K (hKU.trans hUD) hK
  have hYsec : ∀ x ∈ Y, g (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ ContinuousOn h O ∧ (∀ y ∈ O, A (h y) = y) ∧ Y ∩ V = h '' O := by
    intro x hx hgx
    obtain ⟨O, V, h, hO, hV, hxV, hh, hAh, hXV⟩ := hsec (A x) (hball hx.2) hgx x hx.1 rfl
    refine ⟨O ∩ U, V ∩ A ⁻¹' U, h, hO.inter hUo, hV.inter (hUo.preimage A.continuous), ⟨hxV, hx.2⟩,
      hh.continuousOn.mono Set.inter_subset_left, fun y hy => hAh y hy.1, ?_⟩
    ext z
    constructor
    · rintro ⟨⟨hzXB, hzU⟩, hzV, -⟩
      have : z ∈ h '' O := hXV ▸ ⟨hzXB, hzV⟩
      obtain ⟨y, hyO, rfl⟩ := this
      exact ⟨y, ⟨hyO, by rwa [hAh y hyO] at hzU⟩, rfl⟩
    · rintro ⟨y, ⟨hyO, hyU⟩, rfl⟩
      have hmem : h y ∈ X ∩ B ∩ V := hXV ▸ ⟨y, hyO, rfl⟩
      have hAy : A (h y) ∈ U := by rw [hAh y hyO]; exact hyU
      exact ⟨⟨hmem.1, hAy⟩, hmem.2, hAy⟩

  obtain ⟨n, hn⟩ := UnbranchedProperCountConstant.proof UnbranchedProperCountLocallyConstant.proof
    ManifoldZerosComplementConnected.proof σ Y d A U g hUo (convex_ball y₀ r).isPreconnected hYmaps hYprop
    hgU hYsec
  have hcount : ∀ y ∈ U, g y ≠ 0 → {x | x ∈ X ∩ B ∧ A x = y}.encard = n := by
    intro y hy hgy
    rw [← hfib y hy]
    exact hn y hy hgy

  have hle : ∀ y ∈ U, {x | x ∈ X ∩ B ∧ A x = y}.encard ≤ n := by
    intro y hy
    by_contra hlt
    rw [not_le] at hlt
    have hn1 : ((n + 1 : ℕ) : ℕ∞) ≤ {x | x ∈ X ∩ B ∧ A x = y}.encard := by
      rw [Nat.cast_add, Nat.cast_one]
      exact Order.add_one_le_of_lt hlt
    obtain ⟨T, hTF, hTcard⟩ := Set.exists_subset_encard_eq hn1
    have hTfin : T.Finite := Set.finite_of_encard_eq_coe hTcard
    obtain ⟨S, hS, hSdisj⟩ := hTfin.t2_separation
    have hW : U ∩ ⋂ x ∈ T, A '' (X ∩ B ∩ S x) ∈ 𝓝 y := by
      refine Filter.inter_mem (hUo.mem_nhds hy) ((Filter.biInter_mem hTfin).2 fun x hx => ?_)
      have hxF := hTF hx
      have := hopen x hxF.1 (S x) ((hS x).2.mem_nhds (hS x).1)
      rwa [hxF.2] at this
    obtain ⟨t, ⟨htW, hgt⟩⟩ := hgdU (interior (U ∩ ⋂ x ∈ T, A '' (X ∩ B ∩ S x))) isOpen_interior
      (interior_subset.trans Set.inter_subset_left) ⟨y, mem_interior_iff_mem_nhds.2 hW⟩
    have htW' := interior_subset htW
    have htU : t ∈ U := htW'.1
    have hpick : ∀ x ∈ T, ∃ z, z ∈ X ∩ B ∩ S x ∧ A z = t := by
      intro x hx
      have := Set.mem_iInter₂.1 htW'.2 x hx
      obtain ⟨z, hz, hAz⟩ := this
      exact ⟨z, hz, hAz⟩
    choose! z hz hAz using hpick
    have hinj : Set.InjOn z T := by
      intro a ha b hb hab
      by_contra hne
      exact Set.disjoint_left.1 (hSdisj ha hb hne) (hz a ha).2 (hab ▸ (hz b hb).2)
    have hsub : z '' T ⊆ {x | x ∈ X ∩ B ∧ A x = t} := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨(hz x hx).1, hAz x hx⟩
    have := (Set.encard_le_encard hsub).trans_eq (hcount t htU hgt)
    rw [hinj.encard_image, hTcard] at this
    exact absurd this (by norm_cast; omega)
  refine ⟨U, g, n, hUo, hy₀U, hUD, hgU, hgdU, hle, fun y hy hgy => ⟨hcount y hy hgy, ?_⟩⟩
  intro x hx hAx
  exact hsec y (hball hy) hgy x hx hAx
end ProperOpenProjectionLocalCover
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
