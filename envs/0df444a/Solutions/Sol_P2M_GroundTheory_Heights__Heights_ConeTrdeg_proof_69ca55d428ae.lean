-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeTrdeg_proof_69ca55d428ae
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:08.489046+00:00
-- url     : https://prove2.me/submissions/f4c78ac4-8f96-4b54-8670-e79bdb604331

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PConeTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeTrdeg_mConeMap_of_isMultiHomog_42bb4e513f85
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexAt_algebraMap_apply_de37bb391a59


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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights
namespace ConeTrdeg
theorem _root_.solution : ConeTrdeg.Statement := by
  intro K _ ι _ Ω _ y hbir hnz hhor
  classical

  have hinjΩ : Function.Injective (algebraMap ℤ Ω) := by
    rw [injective_iff_map_eq_zero]
    intro n hn
    have hmem : (MvPolynomial.C n : Geo.MRing ι) ∈ Geo.mCoordIdeal y := by
      rw [Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_apply, hn, map_zero]
    have h2 : n ∈ (Geo.mCoordIdeal y).comap (MvPolynomial.C : ℤ →+* Geo.MRing ι) := hmem
    simp only [Geo.IsHorizontal] at hhor
    rw [hhor] at h2
    exact (Ideal.mem_bot).1 h2
  have : FaithfulSMul ℤ Ω := (faithfulSMul_iff_algebraMap_injective ℤ Ω).mpr hinjΩ
  have : FaithfulSMul Ω (MvPolynomial K Ω) :=
    (faithfulSMul_iff_algebraMap_injective Ω (MvPolynomial K Ω)).mpr (MvPolynomial.C_injective K Ω)
  have hB : Algebra.trdeg ℤ (MvPolynomial K Ω) = Algebra.trdeg ℤ Ω + Fintype.card K := by
    rw [← trdeg_add_eq ℤ Ω (A := MvPolynomial K Ω), MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id,
      Cardinal.mk_fintype]
  have hZB : Function.Injective (algebraMap ℤ (MvPolynomial K Ω)) := by
    rw [IsScalarTower.algebraMap_eq ℤ Ω (MvPolynomial K Ω), RingHom.coe_comp]
    exact (MvPolynomial.C_injective K Ω).comp hinjΩ
  let S := (Geo.mConeMap y).range
  have hA : Algebra.trdeg ℤ (Geo.MRing ι ⧸ Geo.mCoordIdeal y) = Algebra.trdeg ℤ S :=
    (Ideal.quotientKerEquivRange (Geo.mConeMap y)).trdeg_eq
  have : FaithfulSMul ℤ S := (faithfulSMul_iff_algebraMap_injective ℤ S).mpr
    (Function.Injective.of_comp (f := algebraMap S (MvPolynomial K Ω))
      (by rwa [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]))
  have : FaithfulSMul S (MvPolynomial K Ω) :=
    (faithfulSMul_iff_algebraMap_injective S (MvPolynomial K Ω)).mpr Subtype.val_injective

  have halgC : ∀ a : Ω, IsAlgebraic S (MvPolynomial.C a : MvPolynomial K Ω) := by
    intro a
    obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hbir a
    have hgS : Geo.mConeMap y g ∈ S := AlgHom.mem_range_self _ _
    have hhS : Geo.mConeMap y h ∈ S := AlgHom.mem_range_self _ _
    have hne : Geo.mConeMap y h ≠ 0 := by
      rw [ConeTrdeg.mConeMap_of_isMultiHomog y hh]
      exact mul_ne_zero (MvPolynomial.C_ne_zero.2 hh0)
        (Finset.prod_ne_zero_iff.2 fun k _ ↦ pow_ne_zero _ (MvPolynomial.X_ne_zero k))
    refine IsAlgebraic.of_mul (y := Geo.mConeMap y h) (mem_nonZeroDivisors_of_ne_zero hne)
      (isAlgebraic_algebraMap (⟨_, hhS⟩ : S)) ?_
    have hmul : Geo.mConeMap y h * MvPolynomial.C a = Geo.mConeMap y g := by
      rw [ConeTrdeg.mConeMap_of_isMultiHomog y hh, ConeTrdeg.mConeMap_of_isMultiHomog y hg, hgh, map_mul]
      ring
    rw [hmul]
    exact isAlgebraic_algebraMap (⟨_, hgS⟩ : S)

  choose c hc using hnz
  have halgX : ∀ k, IsAlgebraic S (X k : MvPolynomial K Ω) := by
    intro k
    have hS : Geo.mConeMap y (X ⟨k, c k⟩) ∈ S := AlgHom.mem_range_self _ _
    refine IsAlgebraic.of_mul (y := MvPolynomial.C (y ⟨k, c k⟩))
      (mem_nonZeroDivisors_of_ne_zero (MvPolynomial.C_ne_zero.2 (hc k))) (halgC _) ?_
    have hmul : (MvPolynomial.C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω) = Geo.mConeMap y (X ⟨k, c k⟩) := by
      simp [Geo.mConeMap]
    rw [hmul]
    exact isAlgebraic_algebraMap (⟨_, hS⟩ : S)
  have : Algebra.IsAlgebraic S (MvPolynomial K Ω) := ⟨fun p ↦ by
    induction p using MvPolynomial.induction_on with
    | C a => exact halgC a
    | add p q hp hq => exact hp.add hq
    | mul_X p k hp => exact hp.mul (halgX k)⟩
  have hSB := trdeg_add_eq ℤ S (A := MvPolynomial K Ω)
  rw [trdeg_eq_zero (R := S) (A := MvPolynomial K Ω), add_zero] at hSB
  rw [hA, hSB, hB]
end ConeTrdeg
end GroundTheory.Heights₂.Heights
