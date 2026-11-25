-- Prove2me | solution 1 for PI.FJMB.cd_mono_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:38:26.63325+00:00
-- url     : https://prove2.me/submissions/26d4b965-4e57-4558-8497-e6497d5d750f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurCauchy
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_DiagonalImageBlockFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
open PI PI.FJMB
variable {σ : Type*}
namespace PI.FJMB
theorem _root_.solution {m : ℕ} (ι : Fin m × Fin m → σ) (hι : Function.Injective ι) (e : σ →₀ ℕ) :
    aeval (killS (offD ι)) (monomial e (1 : ℂ)) =
      (∏ i, X (ι (i, i)) ^ (∑ k : Fin m, e (ι (i, k)))) * aeval (diagOne' ι) (monomial e (1 : ℂ)) := by
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, map_one, one_mul, one_mul]
  by_cases hoff : ∃ v ∈ e.support, v ∈ offD ι
  · obtain ⟨v, hv, hvo⟩ := hoff
    have h1 : (e.prod fun v k => killS (offD ι) v ^ k) = 0 := by
      refine Finset.prod_eq_zero hv ?_
      simp only [killS, if_pos hvo]
      exact zero_pow (Finsupp.mem_support_iff.mp hv)
    have h2 : (e.prod fun v k => diagOne' ι v ^ k) = 0 := by
      refine Finset.prod_eq_zero hv ?_
      simp only [diagOne', if_pos hvo]
      exact zero_pow (Finsupp.mem_support_iff.mp hv)
    rw [h1, h2, mul_zero]
  · push_neg at hoff
    have hsum : ∀ i, ∑ k : Fin m, e (ι (i, k)) = e (ι (i, i)) := by
      intro i
      rw [Finset.sum_eq_single i]
      · intro k _ hk
        by_contra hne
        exact hoff (ι (i, k)) (Finsupp.mem_support_iff.mpr hne) ⟨i, k, rfl, fun h => hk (Fin.ext h).symm⟩
      · intro h
        exact absurd (Finset.mem_univ i) h
    simp only [hsum]
    have hL : (e.prod fun v k => killS (offD ι) v ^ k) = ∏ v ∈ e.support, (X v : MvPolynomial σ ℂ) ^ e v := by
      unfold Finsupp.prod
      refine Finset.prod_congr rfl fun v hv => ?_
      simp only [killS, if_neg (hoff v hv)]
    have hR : (e.prod fun v k => diagOne' ι v ^ k) =
        ∏ v ∈ e.support, (if (∃ i k, ι (i, k) = v ∧ (i : ℕ) = k) then 1 else (X v : MvPolynomial σ ℂ) ^ e v) := by
      unfold Finsupp.prod
      refine Finset.prod_congr rfl fun v hv => ?_
      simp only [diagOne', if_neg (hoff v hv)]
      split_ifs <;> simp
    have hsplit : ∏ v ∈ e.support, (X v : MvPolynomial σ ℂ) ^ e v =
        (∏ v ∈ e.support, if (∃ i k, ι (i, k) = v ∧ (i : ℕ) = k) then (X v : MvPolynomial σ ℂ) ^ e v else 1) *
          ∏ v ∈ e.support, (if (∃ i k, ι (i, k) = v ∧ (i : ℕ) = k) then 1 else (X v : MvPolynomial σ ℂ) ^ e v) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun v _ => ?_
      split_ifs <;> simp
    have hF : ∏ v ∈ e.support.filter (fun v => ∃ i k, ι (i, k) = v ∧ (i : ℕ) = k), (X v : MvPolynomial σ ℂ) ^ e v =
        ∏ v ∈ e.support, if (∃ i k, ι (i, k) = v ∧ (i : ℕ) = k) then (X v : MvPolynomial σ ℂ) ^ e v else 1 := by
      rw [Finset.prod_filter]
    have hinj : Function.Injective (fun i : Fin m => ι (i, i)) := fun a b h => (Prod.mk.inj (hι h)).1
    have himg : ∏ i, (X (ι (i, i)) : MvPolynomial σ ℂ) ^ e (ι (i, i)) =
        ∏ v ∈ Finset.univ.image (fun i : Fin m => ι (i, i)), (X v : MvPolynomial σ ℂ) ^ e v := by
      rw [Finset.prod_image (fun a _ b _ h => hinj h)]
    rw [hL, hR, hsplit, ← hF, himg]
    congr 1
    apply Finset.prod_subset
    · intro v hv
      rw [Finset.mem_filter] at hv
      obtain ⟨i, k, hik, hk⟩ := hv.2
      rw [Finset.mem_image]
      refine ⟨i, Finset.mem_univ _, ?_⟩
      rw [← hik, ← Fin.ext hk]
    · intro v hv hvf
      rw [Finset.mem_image] at hv
      obtain ⟨i, _, rfl⟩ := hv
      have h0 : e (ι (i, i)) = 0 := by
        by_contra hne
        exact hvf (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, i, i, rfl, rfl⟩)
      rw [h0, pow_zero]
end PI.FJMB
