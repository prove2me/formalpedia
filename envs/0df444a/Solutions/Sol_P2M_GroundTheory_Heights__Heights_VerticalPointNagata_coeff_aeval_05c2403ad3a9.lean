-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPointNagata_coeff_aeval_05c2403ad3a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:38:43.364519+00:00
-- url     : https://prove2.me/submissions/20f5cbfc-7d6b-4f59-9060-ab193275a3f6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertPointNagata
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointMultChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointNagata
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointNagata_aeval_C_mul_X__435eef58e544
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_isMultiHomog_iff_06eee657011e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isMultiHomog_iff_fb8717c574c6


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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.VerticalPointNagata
variable {T : Type} [Fintype T]
namespace GroundTheory.Heights₂.Heights.VerticalPointNagata
theorem _root_.solution {S : Type*} [CommRing S] [Algebra ℤ S] [Algebra ℤ (Polynomial S)] (r : (Σ _ : Unit, T) → S) (f : MRing (fun _ : Unit => T))
    (n : ℕ) :
    (aeval (fun p => Polynomial.C (r p) * Polynomial.X) f : Polynomial S).coeff n = aeval r (comp n f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial u c =>
    have hu : IsMultiHomog (monomial u c : MRing (fun _ : Unit => T)) (fun _ => ∑ i, u ⟨(), i⟩) := by
      intro m hm k
      have := Finset.mem_singleton.mp (support_monomial_subset hm)
      subst this
      rfl
    rw [aeval_C_mul_X' r _ _ hu, Polynomial.coeff_C_mul_X_pow]
    have hw := Inter.LocRingPow.isMultiHomog_iff.mp hu
    by_cases h : n = ∑ i, u ⟨(), i⟩
    · rw [if_pos h, comp, h, hw.weightedHomogeneousComponent_same]
    · rw [if_neg h, comp, hw.weightedHomogeneousComponent_ne _ (fun e => h (congrFun e ())), map_zero]
  | add p q hp hq => rw [map_add, Polynomial.coeff_add, hp, hq, comp, comp, comp, map_add, map_add]
end GroundTheory.Heights₂.Heights.VerticalPointNagata
