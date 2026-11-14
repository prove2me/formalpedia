-- Prove2me | solution 1 for PGDRevision20261113.curvature_relation_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-11-13T09:59:53.600029+00:00
-- url     : https://prove2.me/submissions/5879b6b2-a060-4e79-a684-85eb803b240f

import Definitions.Def_PGDRevision20261113_Geometry
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

set_option autoImplicit false
open PGDRevision20261113
open scoped ENNReal

private lemma penalty_range (G : GeometryData) (hG : AdmissibleGeometry G)
    (hf : G.family = .realLine) :
    (∀ x : ℝ, 1 ≤ G.b x) ∧ (∀ s : ℝ, 1 ≤ s → ∃ x : ℝ, G.b x = s) := by
  rcases hG with ⟨_, _, _, _, hG⟩
  simp only [hf] at hG
  rcases hG with ⟨_, hb, hb0, hb1, _, _, htail⟩
  constructor
  · intro x
    by_cases hx : x = 0
    · subst x
      exact hb0.ge
    · exact (hb1 x hx).le
  · intro s hs
    obtain ⟨R, hR, hbound⟩ := htail s
    have hbR : s ≤ G.b R := hbound R (by rw [abs_of_pos hR])
    have hbs : s ∈ Set.Icc (G.b 0) (G.b R) := ⟨by rwa [hb0], hbR⟩
    obtain ⟨x, _, hx⟩ := intermediate_value_Icc hR.le hb.continuous.continuousOn hbs
    exact ⟨x, hx⟩

private lemma rho_relation (G : GeometryData) (hG : AdmissibleGeometry G)
    (hf : G.family = .realLine) (a : ℝ → ℝ) (ha : ∀ x : ℝ, G.A x = a (G.b x))
    (c p : ℝ) :
    geometryRho G c p = ⨆ s ∈ Set.Ici (1 : ℝ),
      ENNReal.ofReal |(p * Real.rpow s c - a s) / (p * Real.rpow s c + G.lambda * s)| := by
  obtain ⟨hb, hsurj⟩ := penalty_range G hG hf
  simp only [geometryRho, geometryDomain, geometryError, geometryKernel, hf, ha]
  apply le_antisymm
  · refine iSup_le fun x => iSup_le fun _ => ?_
    exact le_iSup_of_le (G.b x) (le_iSup_of_le (hb x) le_rfl)
  · refine iSup_le fun s => iSup_le fun hs => ?_
    obtain ⟨x, hx⟩ := hsurj s hs
    rw [← hx]
    exact le_iSup_of_le x (le_iSup_of_le (Set.mem_univ x) le_rfl)

theorem solution : CurvatureRelationClaim := by
  intro G a hG hf ha
  refine ⟨?_, ?_⟩
  · intro c p _ _
    exact rho_relation G hG hf a ha c p
  · intro H hH hfH hlam haH z
    have heq (c p : ℝ) : geometryRho G c p = geometryRho H c p := by
      rw [rho_relation G hG hf a ha, rho_relation H hH hfH a haH, hlam]
    constructor
    · intro hz
      refine ⟨hz.1, ?_⟩
      intro w hw
      simpa only [← heq] using hz.2 w hw
    · intro hz
      refine ⟨hz.1, ?_⟩
      intro w hw
      simpa only [heq] using hz.2 w hw
