-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLatNm_isIntegral_theta_iff_fe641e3ebc90
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:26:47.918255+00:00
-- url     : https://prove2.me/submissions/294707e6-caa0-4175-abc5-ebb895b0b3f0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatNmSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_exists_theta_eq_3f0873cb1a45

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.ChartLatNm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
variable (P : ArithVariety n) (y : Coord n → Ω)
variable (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (hb : Geo.Birational (ι := blockIdx n) y)
namespace GroundTheory.Heights₂.Heights.ChartLatNm
theorem _root_.solution (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (v : Ω) :
    IsIntegral (P.chartRing c) (theta P y hP hb v) ↔
      IsIntegral (Geo.chartRingZ (ι := blockIdx n) y c) v := by
  constructor
  · intro hv
    have hinj : Function.Injective (thetaChart P y hP hb c hc) := fun a a' h =>
      Subtype.ext ((theta P y hP hb).injective (congrArg Subtype.val h))
    have hsurj : Function.Surjective (thetaChart P y hP hb c hc) := by
      rintro ⟨u, hu⟩
      obtain ⟨x, hx, rfl⟩ := exists_theta_eq P y hP hb c hc hu
      exact ⟨⟨x, hx⟩, rfl⟩
    let e := RingEquiv.ofBijective (thetaChart P y hP hb c hc) ⟨hinj, hsurj⟩
    obtain ⟨p, hp, hev⟩ := hv
    refine ⟨p.map (e.symm : P.chartRing c →+* Geo.chartRingZ (ι := blockIdx n) y c), hp.map _,
      (theta P y hP hb).injective ?_⟩
    have hcomp : ((theta P y hP hb).comp (algebraMap (Geo.chartRingZ (ι := blockIdx n) y c) Ω)).comp
        (e.symm : P.chartRing c →+* Geo.chartRingZ (ι := blockIdx n) y c) =
        algebraMap (P.chartRing c) P.FunField := by
      refine RingHom.ext fun x => ?_
      have h1 : e (e.symm x) = x := e.apply_symm_apply x
      exact congrArg Subtype.val h1
    rw [Polynomial.hom_eval₂, map_zero, Polynomial.eval₂_map, hcomp]
    exact hev
  · intro hv
    exact IsIntegral.map_of_comp_eq (thetaChart P y hP hb c hc) (theta P y hP hb)
      (RingHom.ext fun _ => rfl) hv
end GroundTheory.Heights₂.Heights.ChartLatNm
