-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GenChowIrreducible_constantCoeff_specRest_439e19de31d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:23:09.501868+00:00
-- url     : https://prove2.me/submissions/431780f8-af4a-4210-a9d5-3b877e23845d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenChowIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.GenChowIrreducible
variable {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.Vertical.GenChowIrreducible
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {δ : ℕ}
    (hδ : 1 ≤ δ) {f : MvPolynomial (Fin (e + 1) × Fin n) R} (hf : IsMultiHomog δ f)
    (y : Par e n → S) : constantCoeff (specRest φ f y) = 0 := by
  unfold specRest
  rw [← coe_eval₂Hom, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom]
  rw [coe_eval₂Hom, eval₂_eq']
  refine Finset.sum_eq_zero fun d hd => ?_
  obtain ⟨j, hj⟩ : ∃ j, d (0, j) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 := congrFun (hf (mem_support_iff.mp hd)) 0
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finset.sum_eq_zero] at h0
    · omega
    · rintro ⟨i, j'⟩ _
      simp only [groupWeight, Pi.smul_apply, smul_eq_mul]
      by_cases hi : i = 0
      · subst hi; simp [hcon j']
      · simp [Ne.symm hi]
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := (0, j)) (Finset.mem_univ _) ?_)
  simp [zero_pow hj]
end GroundTheory.Heights₂.Heights.Vertical.GenChowIrreducible
