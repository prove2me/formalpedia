-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_IsomInvariance_snoc_eq_8fa27cda6eb8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:46:48.103849+00:00
-- url     : https://prove2.me/submissions/3f3dda9e-5e98-4db1-8952-afc6ede13170

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PIsomInvariance
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_IsomInvariance_exists_ratSection_7ff018dbcb48
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_mul_92fa4aba8533
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_ptsIntegral_congr_mcPts_6069163e8079
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_cycR_eq_sum_15b112079e4e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_cycR_mul_c633929bbe81


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
open GroundTheory.Heights₂.Heights.HilbertSamuel.IsomInvariance
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.IsomInvariance
theorem _root_.solution (hR : RatRStatement) {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {P : Ideal (MRing ι)} {m : ℕ} (N : Fin m → HermLine ι) (A B : HermLine ι)
    (hP : IsArithVar P (m + 1)) (hN : ∀ j, IsSmoothHerm (N j)) (hA : IsSmoothHerm A) (hB : IsSmoothHerm B)
    (hAB : IsIsometricOn P A B) : I P (m + 1) (Fin.snoc N A) = I P (m + 1) (Fin.snoc N B) := by
  obtain ⟨f, g, α, β, hf, hg, hfP, hgP, hdeg, hdiv, hnorm⟩ := hAB
  have hPp : P.IsPrime := hP.2.1.1
  have nm : ∀ {x y : MRing ι}, x ∉ P → y ∉ P → x * y ∉ P := fun hx hy h => (hPp.mem_or_mem h).elim hx hy
  obtain ⟨s, t, σ, τ, hs, ht, hsP, htP, hst⟩ := exists_ratSection hPp hP.2.1.2.2 B
  have hB' : IsRatSectionOn P B (s * g) (t * g) :=
    ⟨σ + β, τ + β, Inter.AvoidRing.isMultiHomog_mul hs hg, Inter.AvoidRing.isMultiHomog_mul ht hg,
      nm hsP hgP, nm htP hgP, fun k => by have := hst k; simp only [Pi.add_apply]; push_cast; linarith⟩
  have hA' : IsRatSectionOn P A (s * f * g) (t * g * g) :=
    ⟨σ + α + β, τ + β + β,
      Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul hs hf) hg,
      Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul ht hg) hg,
      nm (nm hsP hfP) hgP, nm (nm htP hgP) hgP,
      fun k => by have := hst k; have := hdeg k; simp only [Pi.add_apply]; push_cast; linarith⟩
  rw [hR K ι I hI P m N A _ _ hP hN hA hA', hR K ι I hI P m N B _ _ hP hN hB hB']
  unfold recRRat
  have hfg : cycR I P N f = cycR I P N g := by
    rw [Inter.cycR_eq_sum, Inter.cycR_eq_sum, hdiv]
  have hint : ptsIntegral P (pot N) (logNormRat A (s * f * g) (t * g * g)) =
      ptsIntegral P (pot N) (logNormRat B (s * g) (t * g)) := by
    refine Inter.DiagRAux.ptsIntegral_congr_mcPts P (fun _ _ _ => rfl) fun z hz => ?_
    unfold logNormRat
    congr 1
    have ha := A.pos z hz.1
    have hb := B.pos z hz.1
    have hn := hnorm z hz
    simp only [map_mul, norm_mul] at hn ⊢
    set S := ‖eval z (map (Int.castRingHom ℂ) s)‖
    set T := ‖eval z (map (Int.castRingHom ℂ) t)‖
    set F := ‖eval z (map (Int.castRingHom ℂ) f)‖
    set G := ‖eval z (map (Int.castRingHom ℂ) g)‖
    rcases eq_or_ne T 0 with hT | hT
    · simp [hT]
    rcases eq_or_ne G 0 with hG | hG
    · simp [hG]
    rw [div_div, div_div, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (S * G * G * T) * hn
  rw [Inter.cycR_mul I hPp N (nm hsP hfP) hgP, Inter.cycR_mul I hPp N hsP hfP,
    Inter.cycR_mul I hPp N (nm htP hgP) hgP, Inter.cycR_mul I hPp N htP hgP,
    Inter.cycR_mul I hPp N hsP hgP, hint, hfg]
  ring
end GroundTheory.Heights₂.Heights.HilbertSamuel.IsomInvariance
