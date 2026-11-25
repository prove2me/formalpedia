-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isProjVarQ_of_isArithVar_5640a3c8ef08
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:04:41.872715+00:00
-- url     : https://prove2.me/submissions/bdf6fc0d-42f4-43fc-8aff-99129d0fcfe5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothMetricOfIsSmoothHerm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_isMultiProjPrime_iff_a67b98d88a86
import Theorems.Thm_ReciprocityTheory_AnForm_R_extQ_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} {e : ℕ}
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1)) :
    IsProjVarQ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) e := by
  obtain ⟨-, ⟨hprime, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have := hprime
  have hch : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ P → m = 0 := by
    intro m hm
    have hm' : m ∈ P.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) := Ideal.mem_comap.mpr hm
    rw [show P.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) = ⊥ from hhor, Ideal.mem_bot] at hm'
    exact hm'
  obtain ⟨hQ, hcomap, hd⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hch
  refine ⟨(GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiProjPrime_iff _).mpr
    ⟨hQ, ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩, ?_⟩, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · rw [hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, MvPolynomial.map_X]
    exact h
  · have hd' : ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸
        P.map (MvPolynomial.map (Int.castRingHom ℚ))) + 1 =
        ((e + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [← hdim]
      exact hd
    show ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸ P.map (MvPolynomial.map (Int.castRingHom ℚ))) =
      ((e + Fintype.card K : ℕ) : WithBot ℕ∞)
    generalize ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸
      P.map (MvPolynomial.map (Int.castRingHom ℚ))) = d at hd'
    induction d using WithBot.recBotCoe with
    | bot =>
      rw [WithBot.bot_add] at hd'
      exact absurd hd' (WithBot.bot_ne_coe)
    | coe d =>
      induction d using ENat.recTopCoe with
      | top =>
        have h3 : (⊤ : ℕ∞) + 1 = ((e + 1 + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast hd'
        rw [top_add] at h3
        exact absurd h3.symm (ENat.natCast_ne_top _)
      | coe n =>
        have h1 : n + 1 = e + 1 + Fintype.card K := by exact_mod_cast hd'
        have h2 : n = e + Fintype.card K := by omega
        rw [h2]
        rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
