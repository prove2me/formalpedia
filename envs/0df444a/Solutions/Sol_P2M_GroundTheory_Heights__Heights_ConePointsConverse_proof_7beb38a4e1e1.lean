-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConePointsConverse_proof_7beb38a4e1e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:53:50.441988+00:00
-- url     : https://prove2.me/submissions/a85daa2a-75fc-41aa-8c01-c601a3064f5c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ExtVal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057


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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ConePointsConverse
theorem _root_.solution (hV : ChartVanishing.Statement) : ConePointsConverse.Statement := by
  intro ι _ _ n P D d g hg z hz c hm
  obtain ⟨j₀, hj₀⟩ : ∃ j, evalCone z (g c j) ≠ 0 := by
    by_contra h
    exact hm ((hV ι n P D d g hg z hz c).1 fun j ↦ by_contra fun hj ↦ h ⟨j, hj⟩)
  have hlive : P.IsLive c := by
    by_contra hl
    apply hj₀
    rw [hg.dead c hl j₀]
    simp [evalCone]

  let sub : Coord D.extSizes → MvPolynomial (Coord n) ℤ := fun v ↦ match v with
    | ⟨none, j⟩ => g c j
    | ⟨some k, i⟩ => X ⟨k, i⟩
  let Φ : MvPolynomial (Coord D.extSizes) ℤ →+* MvPolynomial (Coord n) ℤ :=
    eval₂Hom (Int.castRingHom _) sub
  set w := D.joinPt z fun j ↦ evalCone z (g c j) with hw
  have key1 : (eval₂Hom (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2)).comp Φ =
      eval₂Hom (Int.castRingHom ℂ) (fun v : Coord D.extSizes ↦ w v.1 v.2) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [Φ]
    · rintro ⟨_ | k, i⟩
      · simp [Φ, sub, hw, AddBlockData.joinPt, evalCone]
      · simp [Φ, sub, hw, AddBlockData.joinPt]
  have key2 : P.mkF.comp Φ =
      (MvPolynomial.eval fun o : Option ι ↦ o.elim (P.mkF (chartMonomial c d)) fun _ ↦ 1).comp
        D.extMap := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [Φ]
    · rintro ⟨_ | k, i⟩
      · simp only [RingHom.comp_apply, Φ, sub, AddBlockData.extMap, AddBlockData.extVal, coe_eval₂Hom,
          eval₂_X, eval_mul, eval_C, eval_X, Option.elim]
        exact (hg.value c hlive i).trans (mul_comm _ _)
      · simp [Φ, sub, AddBlockData.extMap, AddBlockData.extVal]
  refine ⟨?_, ?_⟩
  · rintro (_ | k)
    · intro h
      exact hj₀ (congrFun h j₀)
    · exact hz.1 k
  · intro F hF
    have h0 : P.mkF (Φ F) = 0 := by
      have := RingHom.congr_fun key2 F
      rw [RingHom.comp_apply, RingHom.comp_apply, (RingHom.mem_ker).1 hF, map_zero] at this
      exact this
    have hmem : Φ F ∈ P.ideal := (P.mkF_eq_zero_iff _).1 h0
    have h1 := RingHom.congr_fun key1 F
    have h2 : evalCone z (Φ F) = 0 := hz.2 _ hmem
    simp only [RingHom.comp_apply, coe_eval₂Hom] at h1
    simpa [evalCone, h1] using h2
end ConePointsConverse
end GroundTheory.Heights₂.Heights
