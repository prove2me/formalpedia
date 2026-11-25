-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:26:34.960936+00:00
-- url     : https://prove2.me/submissions/dddf9670-f301-4f78-ac80-3fd96cfb7ee0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_eval_pullback_d784c0eada3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_exists_linear_injOn_5abfc7a649f0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_exists_monic_aeval_eq_zero_ca6fb5170379

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
variable {n d : ℕ}
open GroundTheory.Heights₂.Heights.ComplexSets.FibreBound
namespace GroundTheory.Heights₂.Heights.ComplexSets.FibreBound
theorem _root_.solution : FibreBound.Statement := by
  intro n d J A hJ _ hA y
  have := hJ
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  let _ : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.toModule
  have : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := hA.finite
  have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    Algebra.IsIntegral.of_finite _ _
  have hbound : ∀ T : Finset (Fin n → ℂ), (↑T : Set (Fin n → ℂ)) ⊆ fibre J A y →
      T.card ≤ projDegree J A := by
    intro T hT
    obtain ⟨c, hc⟩ := exists_linear_injOn T
    obtain ⟨g, hgm, hgd, hg⟩ :=
      exists_monic_aeval_eq_zero J A hA (Ideal.Quotient.mk J (∑ j, C (c j) * X j))
    have hgy : (g.map (MvPolynomial.eval y)).Monic := hgm.map _
    have hroot : ∀ x ∈ T, (∑ j, c j * x j) ∈ (g.map (MvPolynomial.eval y)).roots.toFinset := by
      intro x hx
      obtain ⟨hxJ, hxA⟩ := hT (Finset.mem_coe.mpr hx)
      let ev : (MvPolynomial (Fin n) ℂ ⧸ J) →+* ℂ :=
        Ideal.Quotient.lift J (eval x) (fun q hq => hxJ q hq)
      have hev : ev.comp (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)) =
          MvPolynomial.eval y := by
        refine RingHom.ext fun P => ?_
        change ev (Ideal.Quotient.mk J (pullback A P)) = _
        rw [Ideal.Quotient.lift_mk, eval_pullback, hxA]
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hgy.ne_zero, Polynomial.IsRoot.def,
        Polynomial.eval_map]
      have h := congrArg ev hg
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hev, map_zero] at h
      have hs : ev (Ideal.Quotient.mk J (∑ j, C (c j) * X j)) = ∑ j, c j * x j := by
        change eval x (∑ j, C (c j) * X j) = _
        simp
      rw [hs] at h
      exact h
    calc T.card = (T.image fun x => ∑ j, c j * x j).card := (Finset.card_image_of_injOn hc).symm
      _ ≤ (g.map (MvPolynomial.eval y)).roots.toFinset.card := Finset.card_le_card (by
          intro v hv
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
          exact hroot x hx)
      _ ≤ Multiset.card (g.map (MvPolynomial.eval y)).roots := Multiset.toFinset_card_le _
      _ ≤ (g.map (MvPolynomial.eval y)).natDegree := Polynomial.card_roots' _
      _ = g.natDegree := hgm.natDegree_map _
      _ ≤ projDegree J A := hgd
  have hne : (fibre J A y).Nonempty := by
    have hmax : (RingHom.ker (MvPolynomial.eval y)).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨C a, eval_C _⟩)
    obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
      (S := MvPolynomial (Fin n) ℂ ⧸ J) (RingHom.ker (MvPolynomial.eval y)) (by
        intro P hP
        have hP0 : P = 0 := hA.injective (by rw [map_zero]; exact hP)
        rw [hP0]; exact Ideal.zero_mem _)
    have := hQ
    have hQ' : (Q.comap (Ideal.Quotient.mk J)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hQ'
    have hmem : ∀ q, Ideal.Quotient.mk J q ∈ Q → eval x q = 0 := by
      intro q hq
      have hq' : q ∈ Q.comap (Ideal.Quotient.mk J) := hq
      rw [hx] at hq'
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x q).mp hq'
    refine ⟨x, fun q hq => hmem q (by rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq]; exact Q.zero_mem), ?_⟩
    funext i
    have h1 : X i - C (y i) ∈ RingHom.ker (MvPolynomial.eval y) := by simp [RingHom.mem_ker]
    rw [← hQc] at h1
    have h2 := hmem (pullback A (X i - C (y i))) h1
    rw [eval_pullback] at h2
    simpa [sub_eq_zero] using h2
  have hfin : (fibre J A y).Finite := by
    by_contra hinf
    obtain ⟨T, hT, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (projDegree J A + 1)
    have := hbound T hT
    omega
  refine ⟨hne, hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact hbound _ (by simp)
end GroundTheory.Heights₂.Heights.ComplexSets.FibreBound
