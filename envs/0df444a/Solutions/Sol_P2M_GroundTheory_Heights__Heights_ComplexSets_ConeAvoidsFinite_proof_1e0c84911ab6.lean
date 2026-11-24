-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_ConeAvoidsFinite_proof_1e0c84911ab6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:43.606198+00:00
-- url     : https://prove2.me/submissions/d1b12fdd-afb4-423a-9273-3a3222a00366

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeAvoidsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_homogeneousComponent_mul_of_isHomogeneous_right_3ca43a8912fb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_isHomogeneous_linPoly_741f83c4b563

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.ComplexSets
namespace ConeAvoidsFinite
theorem _root_.solution : ConeAvoidsFinite.Statement := by
  intro n d N J A hcone
  letI alg : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  letI : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := alg.toModule
  show Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)
  classical
  let gen : Finset (MvPolynomial (Fin n) ℂ ⧸ J) := Finset.univ.image fun f : Fin n → Fin N =>
    Ideal.Quotient.mk J (monomial (Finsupp.equivFunOnFinite.symm fun i => (f i : ℕ)) 1)
  let M := Submodule.span (MvPolynomial (Fin d) ℂ) (gen : Set (MvPolynomial (Fin n) ℂ ⧸ J))
  have hsmul : ∀ (s : MvPolynomial (Fin d) ℂ) (p : MvPolynomial (Fin n) ℂ),
      Ideal.Quotient.mk J p ∈ M → Ideal.Quotient.mk J (pullback A s * p) ∈ M := by
    intro s p hp
    have : Ideal.Quotient.mk J (pullback A s * p) = s • Ideal.Quotient.mk J p := by
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul]; rfl
    rw [this]; exact M.smul_mem s hp
  have hsum : ∀ {ι : Type} (s : Finset ι) (q : ι → MvPolynomial (Fin n) ℂ),
      (∀ i ∈ s, Ideal.Quotient.mk J (q i) ∈ M) → Ideal.Quotient.mk J (∑ i ∈ s, q i) ∈ M :=
    fun s q h => by rw [map_sum]; exact M.sum_mem h
  have hmain : ∀ k (q : MvPolynomial (Fin n) ℂ), q.IsHomogeneous k → Ideal.Quotient.mk J q ∈ M := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>

    have key : ∀ (b x : MvPolynomial (Fin n) ℂ),
        x ∈ leadForm '' (J : Set (MvPolynomial (Fin n) ℂ)) ∪ Set.range (linPoly A) →
        Ideal.Quotient.mk J (homogeneousComponent k (b * x)) ∈ M := by
      rintro b x (⟨f, hf, rfl⟩ | ⟨j, rfl⟩)
      · rw [homogeneousComponent_mul_of_isHomogeneous_right b (leadForm f) (e := f.totalDegree)
          (homogeneousComponent_isHomogeneous f.totalDegree f)]
        split_ifs with hek
        · have hs := sum_homogeneousComponent f
          rw [Finset.sum_range_succ] at hs
          have hf' : leadForm f = f - ∑ i ∈ Finset.range f.totalDegree, homogeneousComponent i f := by
            rw [leadForm]; linear_combination hs
          rw [hf', mul_sub, map_sub, Finset.mul_sum,
            Ideal.Quotient.eq_zero_iff_mem.2 (J.mul_mem_left _ hf), zero_sub]
          refine M.neg_mem (hsum _ _ fun i hi => ih _ ?_ _
            ((homogeneousComponent_isHomogeneous _ _).mul (homogeneousComponent_isHomogeneous _ _)))
          have := Finset.mem_range.1 hi; omega
        · simp
      · rw [homogeneousComponent_mul_of_isHomogeneous_right b _ (isHomogeneous_linPoly A j)]
        split_ifs with hk
        · have hl : linPoly A j = pullback A (X j) := by simp [pullback]
          rw [mul_comm, hl]
          exact hsmul _ _ (ih _ (by omega) _ (homogeneousComponent_isHomogeneous _ _))
        · simp

    intro q hq
    rw [q.as_sum]
    refine hsum _ _ fun s hs => ?_
    have hdeg : s.degree = k := by
      have := hq (mem_support_iff.mp hs)
      rw [Finsupp.degree_eq_weight_one]; exact this
    have hCs : monomial s (coeff s q) = pullback A (C (coeff s q)) * monomial s 1 := by
      simp [pullback, C_mul_monomial]
    rw [hCs]
    refine hsmul _ _ ?_
    by_cases hlow : ∀ i, s i < N
    · refine Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image.2
        ⟨fun i => ⟨s i, hlow i⟩, Finset.mem_univ _, ?_⟩))
      congr 2; ext i; simp
    simp only [not_forall, not_lt] at hlow
    obtain ⟨i, hi⟩ := hlow

    have hmem : monomial s (1 : ℂ) ∈ leadIdeal J ⊔ linIdeal A := by
      apply hcone
      have hsplit : monomial s (1 : ℂ) = X i ^ N * monomial (s - Finsupp.single i N) 1 := by
        rw [← monomial_single_add, add_tsub_cancel_of_le (Finsupp.single_le_iff.2 hi)]
      rw [hsplit]
      exact Ideal.mul_mem_right _ _
        (Ideal.pow_mem_pow (show X i ∈ originIdeal n from Ideal.subset_span ⟨i, rfl⟩) N)
    rw [leadIdeal, linIdeal, ← Ideal.span_union] at hmem
    obtain ⟨r, a, g, hag⟩ := Submodule.mem_span_set'.1 hmem
    have hm : monomial s (1 : ℂ) = homogeneousComponent k (∑ t, a t • (g t : MvPolynomial (Fin n) ℂ)) := by
      rw [hag, homogeneousComponent_eq_self (isHomogeneous_monomial _ hdeg)]
    rw [hm, map_sum]
    exact hsum _ _ fun t _ => by rw [smul_eq_mul]; exact key _ _ (g t).2
  have htop : M = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← sum_homogeneousComponent p]
    exact hsum _ _ fun i _ => hmain i _ (homogeneousComponent_isHomogeneous i p)
  exact ⟨⟨gen, htop⟩⟩
end ConeAvoidsFinite
end GroundTheory.Heights₂.Heights.ComplexSets
