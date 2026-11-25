-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_algebraicIndependent_pair_linear_9149b1566c10
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:03:03.017805+00:00
-- url     : https://prove2.me/submissions/92f87fc4-6e52-4e65-a389-c9881a796a2a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PGenericLinearTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_coeff_X_pow_mul_linear_pow_f3c190105c08

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
open GroundTheory.Heights₂.Heights.GenericLinearTrdeg
namespace GroundTheory.Heights₂.Heights.GenericLinearTrdeg
theorem _root_.solution {R A : Type*} [CommRing R] [CommRing A] [IsDomain A]
    [Algebra R A] {η r x : A} (hη : Transcendental R η)
    (hx : Transcendental (Algebra.adjoin R ({η, r} : Set A)) x) :
    AlgebraicIndependent R ![x, x * η + r] := by
  classical
  set B' := Algebra.adjoin R ({η, r} : Set A)
  let η' : B' := ⟨η, Algebra.subset_adjoin (by simp)⟩
  let r' : B' := ⟨r, Algebra.subset_adjoin (by simp)⟩
  rw [algebraicIndependent_iff]
  intro p hp
  by_contra hp0
  set D := p.totalDegree
  let f : Fin 2 → Polynomial B' := ![Polynomial.X, Polynomial.C η' * Polynomial.X + Polynomial.C r']
  let Q : Polynomial B' := MvPolynomial.aeval f p
  have hQ : Polynomial.aeval x Q = 0 := by
    have : Polynomial.aeval x Q =
        MvPolynomial.aeval (fun i => (Polynomial.aeval x).restrictScalars R (f i)) p := by
      rw [← MvPolynomial.comp_aeval]
      rfl
    have hf : (fun i => (Polynomial.aeval x).restrictScalars R (f i)) = ![x, x * η + r] := by
      funext i
      fin_cases i <;> simp [f, η', r'] <;> ring
    rw [this, hf, hp]
  have hQ0 : Q = 0 := transcendental_iff.mp hx Q hQ
  have hdeg : ∀ μ ∈ p.support, μ 0 + μ 1 ≤ D := fun μ hμ => by
    have := MvPolynomial.le_totalDegree hμ
    rwa [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at this
  have hcoeff : Q.coeff D = ∑ μ ∈ p.support,
      algebraMap R B' (p.coeff μ) * (if μ 0 + μ 1 = D then η' ^ (μ 1) else 0) := by
    simp only [Q, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Fin.prod_univ_two,
      Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [Polynomial.algebraMap_apply, Polynomial.coeff_C_mul]
    congr 1
    exact coeff_X_pow_mul_linear_pow η' r' (μ 0) (μ 1) D (hdeg μ hμ)
  let g : Polynomial R := ∑ μ ∈ p.support,
    if μ 0 + μ 1 = D then Polynomial.C (p.coeff μ) * Polynomial.X ^ (μ 1) else 0
  have hg : Polynomial.aeval η g = ((Q.coeff D : B') : A) := by
    rw [hcoeff]
    simp only [g, map_sum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    split_ifs <;> simp [η']
  have hg0 : g ≠ 0 := by
    obtain ⟨μ, hμ, hμD⟩ := Finset.exists_mem_eq_sup p.support
      (MvPolynomial.support_nonempty.mpr hp0) (fun s => s.sum fun _ e => e)
    have hμD' : μ 0 + μ 1 = D := by
      rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at hμD
      exact hμD.symm
    intro h0
    have hc := congrArg (fun q => Polynomial.coeff q (μ 1)) h0
    simp only [g, Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single μ] at hc
    · rw [if_pos hμD', Polynomial.coeff_C_mul_X_pow, if_pos rfl] at hc
      exact (MvPolynomial.mem_support_iff.mp hμ) hc
    · intro ν _ hνμ
      split_ifs with hν
      · rw [Polynomial.coeff_C_mul_X_pow, if_neg]
        intro h1
        apply hνμ
        ext i
        fin_cases i
        · simp only [Fin.zero_eta]; omega
        · exact h1.symm
      · simp
    · intro h; exact absurd hμ h
  have := transcendental_iff.mp hη g (by rw [hg, hQ0]; simp)
  exact hg0 this
end GroundTheory.Heights₂.Heights.GenericLinearTrdeg
