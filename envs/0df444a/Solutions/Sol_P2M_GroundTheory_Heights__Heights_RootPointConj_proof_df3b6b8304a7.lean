-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootPointConj_proof_df3b6b8304a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:14:50.020607+00:00
-- url     : https://prove2.me/submissions/439c3583-329f-47e5-b1fb-d04f55e73ef9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootPointConj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootPointConjugation_homog_vanish_73dd4aea5fe2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootPointConjugation_entry_eq_minor_a8075f6b6ae0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootPointConjugation_map_minor_86bd49ff7f1a

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
open RootPointConjugation
namespace GroundTheory.Heights₂.Heights
namespace RootPointConj
theorem _root_.solution (h : RootAnchorNonzero.Statement) : RootPointConj.Statement := by
  intro f j m ζ hζ z hz τ
  classical
  have h0 : z ⟨τ, plAnchor j m⟩ ≠ 0 := h f j m ζ hζ z hz τ
  set u : PlIdx j m → ℂ := fun I => z ⟨τ, I⟩ / z ⟨τ, plAnchor j m⟩
  have hu : ∀ I, z ⟨τ, I⟩ = z ⟨τ, plAnchor j m⟩ * u I := fun I => by simp [u, mul_div_cancel₀ _ h0]
  have hker : ∀ Q : MvPolynomial (PlIdx j m) ℤ,
      aeval (fun I => rootCoord ζ ⟨τ, I⟩) Q = 0 → aeval u Q = 0 := fun Q hQ =>
    (mul_eq_zero.mp (homog_vanish ζ z hz τ u hu Q hQ)).resolve_left (pow_ne_zero _ h0)
  choose s hs using fun a b => entry_eq_minor (j := j) (m := m) a b
  let E : Matrix (Fin j) (Fin m) (MvPolynomial (PlIdx j m) ℤ) :=
    Matrix.of fun a b => C (s a b) * X (idxAB a b)
  have hE : E.map (aeval fun I => rootCoord ζ ⟨τ, I⟩) = ζ τ := by
    ext a b
    simp [E, rootCoord, ← hs a b ℂ (ζ τ)]
  refine ⟨E.map (aeval u), fun a b => ?_, fun I => ?_⟩
  · obtain ⟨k, hk, hk1⟩ := hζ τ a b
    refine ⟨k, hk, ?_⟩
    have hq := hker (E a b ^ k - 1) (by
      rw [map_sub, map_pow, map_one, ← hk1, ← hE]; simp)
    simpa [sub_eq_zero] using hq
  · have hq := hker (X I - (colsOf (onePipe E) I).det) (by
      rw [map_sub, aeval_X]
      have := map_minor (aeval fun I => rootCoord ζ ⟨τ, I⟩).toRingHom E I
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
      rw [this, hE]
      exact sub_eq_zero.mpr rfl)
    rw [map_sub, aeval_X, sub_eq_zero] at hq
    have := map_minor (aeval u).toRingHom E I
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
    rw [hu I, hq, this]
end RootPointConj
end GroundTheory.Heights₂.Heights
