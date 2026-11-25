-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_projectiveLineClassData_tsum_psi_f565265bd92d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:37:23.040491+00:00
-- url     : https://prove2.me/submissions/d3816ce3-bda7-4a18-abb0-efbd15daad66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DedekindZetaEqSumRealEisenstein
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_psi_surjective_84800f6dd64e
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_natCard_units_ca5c537aacec


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.projectiveLineClassData
open NumberField UpperHalfPlane
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
open FractionalIdeal
local notation "↑ᶠ" J => ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
namespace GroundTheory.Heights₂.Theta.projectiveLineClassData
theorem _root_.solution (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (g : InvClassIdeals J → ENNReal) :
    ∑' x : Nz J, g (psi J x) = (Units.torsionOrder K : ENNReal) * ∑' t, g t := by
  classical
  have hcard := natCard_units hK σ hσ
  have hfin : Finite (𝓞 K)ˣ :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Units.torsionOrder_ne_zero K)
  have := Fintype.ofFinite (𝓞 K)ˣ
  rw [← ENNReal.tsum_fiberwise (fun x => g (psi J x)) (psi J), ← ENNReal.tsum_mul_left]
  refine tsum_congr fun t => ?_
  obtain ⟨x₀, rfl⟩ := psi_surjective J t
  rw [tsum_congr (fun y : (psi J ⁻¹' {psi J x₀}) => by
      rw [show psi J (y : Nz J) = psi J x₀ from y.2]),
    ← (fiberEquiv J x₀).tsum_eq, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, hcard]
end GroundTheory.Heights₂.Theta.projectiveLineClassData
