-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootPointsFinite_proof_6e6841ac90b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:08:00.276918+00:00
-- url     : https://prove2.me/submissions/b5a217b0-6a58-4a47-89d1-daa622e9eef3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootPointsFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootPointsFiniteAlt_homog_mem_dc4ded6d7943
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootPointsFiniteAlt_homog_eval_6ddab3863880
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootPointsFiniteAlt_rootCoord_isIntegral_4297a36abd8e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_anchor_minor_b307d35ccb1e


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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open RootPointsFiniteAlt
namespace GroundTheory.Heights₂.Heights
namespace RootPointsFinite
theorem _root_.solution (h : RootAnchorNonzero.Statement) : RootPointsFinite.Statement := by
  intro f j m ζ hζ
  have hint : ∀ p, ∃ q : Polynomial ℤ, q.Monic ∧ q.eval₂ (Int.castRingHom ℂ) (rootCoord ζ p) = 0 := by
    intro p
    obtain ⟨q, hqm, hq⟩ := rootCoord_isIntegral ζ hζ p
    exact ⟨q, hqm, by rwa [← RingHom.ext_int (algebraMap ℤ ℂ) (Int.castRingHom ℂ)]⟩
  choose q hqm hq using hint
  let S : Set ((Σ _ : Fin f, PlIdx j m) → ℂ) :=
    Set.pi Set.univ fun p => {u | Polynomial.IsRoot ((q p).map (Int.castRingHom ℂ)) u}
  have hS : S.Finite := Set.Finite.pi fun p =>
    Polynomial.finite_setOfPred_isRoot ((hqm p).map _).ne_zero
  have hmem : ∀ z ∈ mcPts (rootPointIdeal ζ),
      (fun p : Σ _ : Fin f, PlIdx j m => z p / z ⟨p.1, plAnchor j m⟩) ∈ S := by
    intro z hz p _
    have hza := h f j m ζ hζ z hz p.1
    have h0 := hz.2 _ (homog_mem (rootCoord ζ) p.1 p.2 (plAnchor j m)
      (by simp [rootCoord, anchor_minor]) (q p) (hq p))
    rw [homog_eval z _ _ hza] at h0
    simpa [Polynomial.IsRoot, Polynomial.eval_map, hza] using h0
  let F : McClasses (rootPointIdeal ζ) → S := Quot.lift
    (fun z => ⟨fun p => z.1 p / z.1 ⟨p.1, plAnchor j m⟩, hmem z.1 z.2⟩) (by
      rintro z z' ⟨c, hc, hz'⟩
      apply Subtype.ext
      funext p
      simp only [hz']
      exact (mul_div_mul_left _ _ (hc p.1)).symm)
  have := hS.to_subtype
  refine Finite.of_injective F ?_
  intro x x'
  induction x using Quot.ind with | mk z => ?_
  induction x' using Quot.ind with | mk z' => ?_
  intro hF
  have hfun := fun p => congrFun (congrArg Subtype.val hF) p
  apply Quot.sound
  refine ⟨fun τ => z'.1 ⟨τ, plAnchor j m⟩ / z.1 ⟨τ, plAnchor j m⟩,
    fun τ => div_ne_zero (h f j m ζ hζ z'.1 z'.2 τ) (h f j m ζ hζ z.1 z.2 τ), ?_⟩
  funext p
  have hza := h f j m ζ hζ z.1 z.2 p.1
  have hza' := h f j m ζ hζ z'.1 z'.2 p.1
  have e : z.1 p / z.1 ⟨p.1, plAnchor j m⟩ = z'.1 p / z'.1 ⟨p.1, plAnchor j m⟩ := hfun p
  rw [div_eq_div_iff hza hza'] at e
  rw [div_mul_eq_mul_div, eq_div_iff hza]
  linear_combination -e
end RootPointsFinite
end GroundTheory.Heights₂.Heights
