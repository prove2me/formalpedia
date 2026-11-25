-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_krullDim_le_of_rel_5aa08ca6aebb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:56:16.730116+00:00
-- url     : https://prove2.me/submissions/ded63e21-9820-4b7a-826e-7241b7d47053

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetParam
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeProjHyperplaneDim
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_sum
import Theorems.Thm_GroundTheory_Arith_Toric_ringKrullDim_le_of_isIntegral


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj segre mcPts psiPoly)
open GroundTheory.Heights₂.Heights.ConeProjHyperplaneDim
namespace GroundTheory.Heights₂.Heights.ConeProjHyperplaneDim
theorem _root_.solution {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (L : Fin m → MvPolynomial (Fin n) ℂ) (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (H : Fin n → Fin m → MvPolynomial (Fin n) ℂ) (hH : ∀ i j, (H i j).totalDegree ≤ r i - 1)
    (hrel : ∀ i, X i ^ r i - ∑ j, L j * H i j ∈ I) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) ≤ ((m : ℕ) : WithBot ℕ∞) := by
  classical
  let φ : MvPolynomial (Fin m) ℂ →+* (MvPolynomial (Fin n) ℂ ⧸ I) :=
    (Ideal.Quotient.mk I).comp (aeval L).toRingHom
  let instA : Algebra (MvPolynomial (Fin m) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) := φ.toAlgebra
  let instM : Module (MvPolynomial (Fin m) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) := instA.toModule
  have hsmul : ∀ (s : MvPolynomial (Fin m) ℂ) (p : MvPolynomial (Fin n) ℂ),
      s • Ideal.Quotient.mk I p = Ideal.Quotient.mk I (aeval L s * p) := by
    intro s p
    rw [Algebra.smul_def]
    rfl
  set M := Submodule.span (MvPolynomial (Fin m) ℂ)
    (((Fintype.piFinset fun i => Finset.range (r i)).image
      (fun α => Ideal.Quotient.mk I (monomial (Finsupp.equivFunOnFinite.symm α) 1))) :
        Set (MvPolynomial (Fin n) ℂ ⧸ I)) with hM
  have hdeg : ∀ N, ∀ β : Fin n →₀ ℕ, (β.sum fun _ e => e) = N →
      Ideal.Quotient.mk I (monomial β 1) ∈ M := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro β hβ
      have hpoly : ∀ q : MvPolynomial (Fin n) ℂ, q.totalDegree < N →
          Ideal.Quotient.mk I q ∈ M := by
        intro q hq
        rw [q.as_sum, map_sum]
        refine Submodule.sum_mem _ fun d hd => ?_
        have hd' : (d.sum fun _ e => e) < N := lt_of_le_of_lt (le_totalDegree hd) hq
        have h1 := ih _ hd' d rfl
        have : Ideal.Quotient.mk I (monomial d (coeff d q)) =
            (C (coeff d q) : MvPolynomial (Fin m) ℂ) • Ideal.Quotient.mk I (monomial d 1) := by
          rw [hsmul, aeval_C, algebraMap_eq, C_mul_monomial, mul_one]
        rw [this]
        exact Submodule.smul_mem _ _ h1
      by_cases hsmall : ∀ i, β i < r i
      · apply Submodule.subset_span
        refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨Finsupp.equivFunOnFinite β, ?_, ?_⟩)
        · exact Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr (hsmall i)
        · simp
      · push Not at hsmall
        obtain ⟨i, hi⟩ := hsmall
        set β' := β - Finsupp.single i (r i) with hβ'
        have hβeq : β = β' + Finsupp.single i (r i) := by
          ext i'
          simp only [hβ', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
          by_cases h : i' = i
          · subst h; simp; omega
          · simp [Ne.symm h]
        have hmk : Ideal.Quotient.mk I (monomial β 1) =
            ∑ j, (X j : MvPolynomial (Fin m) ℂ) •
              Ideal.Quotient.mk I (monomial β' 1 * H i j) := by
          have h1 : monomial β (1 : ℂ) = monomial β' 1 * X i ^ r i := by
            rw [hβeq, X_pow_eq_monomial, monomial_mul, one_mul]
          have h2 : Ideal.Quotient.mk I (X i ^ r i) =
              Ideal.Quotient.mk I (∑ j, L j * H i j) :=
            Ideal.Quotient.eq.mpr (hrel i)
          rw [h1, map_mul, h2, ← map_mul, Finset.mul_sum, map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hsmul, aeval_X]
          congr 1
          ring
        rw [hmk]
        refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hpoly _ ?_)
        have hβsum : (β.sum fun _ e => e) = (β'.sum fun _ e => e) + r i := by
          rw [hβeq, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
            Finsupp.sum_single_index rfl]
        calc (monomial β' 1 * H i j).totalDegree
            ≤ (monomial β' (1 : ℂ)).totalDegree + (H i j).totalDegree := totalDegree_mul _ _
          _ ≤ (β'.sum fun _ e => e) + (r i - 1) := by
            rw [totalDegree_monomial _ one_ne_zero]
            exact Nat.add_le_add_left (hH i j) _
          _ < N := by have := hr i; omega
  have : Module.Finite (MvPolynomial (Fin m) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) := by
    refine ⟨⟨(Fintype.piFinset fun i => Finset.range (r i)).image
      (fun α => Ideal.Quotient.mk I (monomial (Finsupp.equivFunOnFinite.symm α) 1)), ?_⟩⟩
    rw [← hM, eq_top_iff]
    rintro x -
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [p.as_sum, map_sum]
    refine Submodule.sum_mem _ fun d _ => ?_
    have : Ideal.Quotient.mk I (monomial d (coeff d p)) =
        (C (coeff d p) : MvPolynomial (Fin m) ℂ) • Ideal.Quotient.mk I (monomial d 1) := by
      rw [hsmul, aeval_C, algebraMap_eq, C_mul_monomial, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (hdeg _ d rfl)
  have : Algebra.IsIntegral (MvPolynomial (Fin m) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    Algebra.IsIntegral.of_finite _ _
  calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) ≤ ringKrullDim (MvPolynomial (Fin m) ℂ) :=
        GroundTheory.Arith.Toric.ringKrullDim_le_of_isIntegral
    _ = ((m : ℕ) : WithBot ℕ∞) := by
        rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
          Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]
end GroundTheory.Heights₂.Heights.ConeProjHyperplaneDim
