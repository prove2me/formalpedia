-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_ReducedBasisBound_proof_863981f97e76
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:59:31.673595+00:00
-- url     : https://prove2.me/submissions/814349b0-8b44-48cf-92b9-9a5c612f8403

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StReducedBasisBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeGram
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PReducedBasisBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ReducedBasisBound_short_basis_433a14dbcd30
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_covolume_eq_sqrt_det_gram_f70fe7996734


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Module Submodule Matrix GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
noncomputable section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace ReducedBasisBound
theorem _root_.solution : ReducedBasisBound.Statement := by
  intro d t c ht
  obtain ⟨R, hR⟩ := ReducedBasisBound.short_basis (W := EuclideanSpace ℝ (Fin d)) d t ht (c ^ 2)
  refine ⟨R, fun L _ _ hmin hcov => ?_⟩
  have hrk : finrank ℤ L = d := by rw [ZLattice.rank ℝ L, finrank_euclideanSpace_fin]
  let e : Basis (Fin d) ℤ L := Module.finBasisOfFinrankEq ℤ L hrk
  have hspan : span ℤ (Set.range fun i => (e i : EuclideanSpace ℝ (Fin d))) = L := by
    rw [show (Set.range fun i => (e i : EuclideanSpace ℝ (Fin d))) = L.subtype '' Set.range e by
      rw [← Set.range_comp]; rfl, ← Submodule.map_span, e.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hli : LinearIndependent ℝ fun i => (e i : EuclideanSpace ℝ (Fin d)) := by
    have h := (e.ofZLatticeBasis ℝ L).linearIndependent
    rwa [show ⇑(e.ofZLatticeBasis ℝ L) = fun i => (e i : EuclideanSpace ℝ (Fin d)) from
      funext fun i => e.ofZLatticeBasis_apply ℝ L i] at h
  have hdet : (gram ℝ fun i => (e i : EuclideanSpace ℝ (Fin d))).det ≤ c ^ 2 := by
    have h1 := GroundTheory.Heights₂.Heights.covolume_eq_sqrt_det_gram L e
    rcases le_or_gt 0 (gram ℝ fun i => (e i : EuclideanSpace ℝ (Fin d))).det with h | h
    · rw [← Real.sq_sqrt h, ← h1]
      exact pow_le_pow_left₀ (ZLattice.covolume_pos L).le hcov 2
    · nlinarith [sq_nonneg c]
  have hsep : Sep (span ℤ (Set.range fun i => (e i : EuclideanSpace ℝ (Fin d)))) t := by
    rw [hspan]; exact hmin
  obtain ⟨b', hb'span, hb'R⟩ := hR _ hli hsep hdet
  rw [hspan] at hb'span
  have htop : ⊤ ≤ span ℝ (Set.range b') := by
    rw [← IsZLattice.span_top (K := ℝ) (L := L), ← hb'span, Submodule.span_span_of_tower]
  have hliR : LinearIndependent ℝ b' :=
    linearIndependent_of_top_le_span_of_card_eq_finrank htop (by simp)
  refine ⟨(Basis.span (hliR.restrict_scalars' ℤ)).map (LinearEquiv.ofEq _ _ hb'span), fun i => ?_⟩
  simpa using hb'R i
end ReducedBasisBound
end GroundTheory.Heights₂.Heights.FiniteCovolume
