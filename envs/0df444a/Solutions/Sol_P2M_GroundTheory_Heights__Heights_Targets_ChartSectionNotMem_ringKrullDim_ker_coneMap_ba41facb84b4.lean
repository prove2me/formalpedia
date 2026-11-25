-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ChartSectionNotMem_ringKrullDim_ker_coneMap_ba41facb84b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:29:54.573825+00:00
-- url     : https://prove2.me/submissions/8d33a864-c491-4235-a175-447f57bbaab6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothMetricOfIsSmoothHerm
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PChartSectionNotMem
import Theorems.Thm_GroundTheory_Arith_Iwasawa_isDomain
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_CA_exists_dim_trdeg_field
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial Algebra
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsSectionOn mcPts segre)
open GroundTheory.Heights₂.Heights.Targets.ChartSectionNotMem
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
set_option maxHeartbeats 1000000
namespace GroundTheory.Heights₂.Heights.Targets.ChartSectionNotMem
theorem _root_.solution (𝔮 : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [𝔮.IsPrime] (p : (k : K) → ι k)
    (h1 : ∀ k, (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ 𝔮) (d : ℕ)
    (hd : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) = (d : WithBot ℕ∞)) :
    ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker (coneMap (K := K) 𝔮)) =
      ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  classical
  have : IsDomain (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) := Ideal.Quotient.isDomain 𝔮
  let θ : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) := coneMap 𝔮
  let y : (Σ k, ι k) → MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    fun q => C (Ideal.Quotient.mk 𝔮 (X q))
  show ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) = _
  have : (RingHom.ker θ).IsPrime := RingHom.ker_isPrime _
  have : IsDomain (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) := Ideal.Quotient.isDomain _
  let κ : (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) →ₐ[ℂ] MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    Ideal.kerLiftAlg θ
  have hκ : Function.Injective κ := Ideal.kerLiftAlg_injective θ
  letI : Algebra (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    κ.toRingHom.toAlgebra
  have : IsScalarTower ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    IsScalarTower.of_algebraMap_eq fun c => (κ.commutes c).symm
  have hκmk : ∀ f, algebraMap (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))
      (Ideal.Quotient.mk _ f) = θ f := fun f => Ideal.kerLiftAlg_mk θ f
  have : Algebra.FiniteType ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  have : Algebra.FiniteType ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ 𝔮) (Ideal.Quotient.mkₐ_surjective ℂ 𝔮)
  obtain ⟨sA, hAdim, hAtr⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))
  obtain ⟨sR, hRdim, hRtr⟩ :=
    ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ))
  have : FaithfulSMul ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    (faithfulSMul_iff_algebraMap_injective ℂ _).mpr (algebraMap ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)).injective
  have : FaithfulSMul (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (MvPolynomial.C_injective K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))
  have : FaithfulSMul ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) :=
    (faithfulSMul_iff_algebraMap_injective ℂ _).mpr
      (algebraMap ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ)).injective
  have : FaithfulSMul (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hκ
  have hT1 : trdeg ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) +
      trdeg (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) =
      trdeg ℂ (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    trdeg_add_eq ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)
  have hmk1 : ∀ k, Ideal.Quotient.mk 𝔮 (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) = 1 := by
    intro k
    rw [← map_one (Ideal.Quotient.mk 𝔮), Ideal.Quotient.eq]
    exact h1 k
  let AC := Subalgebra.algebraicClosure (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ)
    (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))
  have hRAC : ∀ f, θ f ∈ AC := fun f => by
    rw [Subalgebra.mem_algebraicClosure, ← hκmk]
    exact isAlgebraic_algebraMap _
  have hXk : ∀ k, θ (X ⟨k, p k⟩) = (X k : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) := by
    intro k
    simp only [θ, coneMap, aeval_X, hmk1, map_one, mul_one]
  have hXq : ∀ q, θ (X q) = (X q.1 : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) * y q := fun q => by
    simp only [θ, coneMap, aeval_X, y]
  have hyAC : ∀ q, y q ∈ AC := fun q => by
    have h2 := hRAC (X ⟨q.1, p q.1⟩)
    have h3 := hRAC (X q)
    rw [hXk] at h2
    rw [hXq] at h3
    exact (Subalgebra.mem_algebraicClosure _ _).mpr (IsAlgebraic.of_mul
      (mem_nonZeroDivisors_of_ne_zero (X_ne_zero q.1))
      ((Subalgebra.mem_algebraicClosure _ _).mp h2) ((Subalgebra.mem_algebraicClosure _ _).mp h3))
  have hCAC : ∀ f : MvPolynomial (Σ k, ι k) ℂ, C (Ideal.Quotient.mk 𝔮 f) ∈ AC := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C c =>
      have h2 := hRAC (C c)
      have h3 : θ (C c) = C (Ideal.Quotient.mk 𝔮 (C c)) := by
        simp only [θ, coneMap, aeval_C, MvPolynomial.algebraMap_apply]
        rfl
      rwa [h3] at h2
    | add f g hf hg =>
      rw [map_add, map_add]
      exact AC.add_mem hf hg
    | mul_X f q hf =>
      rw [map_mul, map_mul]
      exact AC.mul_mem hf (hyAC q)
  have hall : ∀ t : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮), t ∈ AC := by
    intro t
    induction t using MvPolynomial.induction_on with
    | C a =>
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact hCAC f
    | add f g hf hg => exact AC.add_mem hf hg
    | mul_X f k hf =>
      have h2 := hRAC (X ⟨k, p k⟩)
      rw [hXk] at h2
      exact AC.mul_mem hf h2
  have : Algebra.IsAlgebraic (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ)
      (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    ⟨fun t => (Subalgebra.mem_algebraicClosure _ _).mp (hall t)⟩
  have hT2 : trdeg ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) +
      trdeg (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) =
      trdeg ℂ (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    trdeg_add_eq ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ)
  have h0 : trdeg (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker θ) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) = 0 :=
    trdeg_eq_zero
  rw [h0, add_zero] at hT2
  have hK : trdeg (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) =
      (Fintype.card K : Cardinal) := by
    rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype]
  rw [hK, hAtr, ← hT2, hRtr] at hT1
  have hnat : sA + Fintype.card K = sR := by exact_mod_cast hT1
  have hsA : sA = d := by
    rw [hAdim] at hd
    exact_mod_cast hd
  rw [hRdim, ← hnat, hsA]
end GroundTheory.Heights₂.Heights.Targets.ChartSectionNotMem
