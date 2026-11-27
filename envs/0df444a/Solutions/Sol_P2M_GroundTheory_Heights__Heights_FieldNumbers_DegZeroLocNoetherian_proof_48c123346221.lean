-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocNoetherian_proof_48c123346221
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:55:10.809683+00:00
-- url     : https://prove2.me/submissions/d5947d62-37a6-4b69-90a4-e34329c76f0d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDegZeroLocNoetherian
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_pow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_div_mem_degZeroLoc_250927a4bb6d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace DegZeroLocNoetherian
theorem _root_.solution (h : DegZeroLocQuot.Statement.{u}) :
    DegZeroLocNoetherian.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  have := hW.isPrime
  let φ : MRing ι F →ₐ[F] FractionRing (MRing ι F ⧸ P) :=
    (IsScalarTower.toAlgHom F (MRing ι F ⧸ P) _).comp (Ideal.Quotient.mkₐ F P)
  have hφ : ∀ f, f ∉ P → φ f ≠ 0 := fun f hf h0 => hf (by
    rwa [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at h0)
  choose v hv using hW.relevant
  let e : MRing ι F →ₐ[F] FractionRing (MRing ι F ⧸ P) :=
    aeval fun x => φ (X x) / φ (X ⟨x.1, v x.1⟩)
  let c : (K → ℕ) → MRing ι F := fun b => ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ b k
  have hcW : ∀ b, c b ∉ W := by
    intro b
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨k, -, hk⟩
    exact hv k (Ideal.IsPrime.mem_of_pow_mem inferInstance _ hk)
  have hc : ∀ b, IsMultiHomog (c b) b := by
    intro b
    have hprod := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
      (fun k => (X ⟨k, v k⟩ : MRing ι F) ^ b k) (fun k => b k • blockWeight ι ⟨k, v k⟩)
      (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) _).pow (b k))
    have hb : (∑ k, b k • blockWeight ι ⟨k, v k⟩) = b := by
      funext k'
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hb] at hprod
    exact hprod
  have hcadd : ∀ b b', c (b + b') = c b * c b' := fun b b' => by
    simp only [c, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

  have hmono : ∀ m : (Σ k, ι k) →₀ ℕ,
      φ (monomial m 1) = e (monomial m 1) * φ (c (Finsupp.weight (blockWeight ι) m)) := by
    intro m
    refine Finsupp.induction m ?_ ?_
    · simp [c]
    · intro x n m _ _ ih
      have hs : φ (monomial (Finsupp.single x n) 1) = e (monomial (Finsupp.single x n) 1) *
          φ (c (Finsupp.weight (blockWeight ι) (Finsupp.single x n))) := by
        rw [Finsupp.weight_single, ← X_pow_eq_monomial, map_pow, map_pow, aeval_X]
        have hcs : c (n • blockWeight ι x) = (X ⟨x.1, v x.1⟩ : MRing ι F) ^ n := by
          simp only [c, blockWeight]
          rw [Finset.prod_eq_single x.1]
          · simp
          · intro k _ hk
            simp [hk]
          · simp
        rw [hcs, map_pow, ← mul_pow, div_mul_cancel₀ _ (hφ _ fun hm => hv x.1 (hPW hm))]
      rw [← mul_one (1 : F), ← monomial_mul, map_mul, map_mul, ih, map_add, hcadd, map_mul, hs]
      ring

  have hhom : ∀ (b : K → ℕ) (f : MRing ι F), IsMultiHomog f b → φ f = e f * φ (c b) := by
    intro b f hf
    conv_lhs => rw [f.as_sum]
    conv_rhs => rw [f.as_sum]
    rw [map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hw : Finsupp.weight (blockWeight ι) m = b := hf (mem_support_iff.mp hm)
    have hmon : monomial m (coeff m f) = coeff m f • monomial m (1 : F) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hmon, map_smul, map_smul, hmono, hw, smul_mul_assoc]
  have hle : e.range ≤ degZeroLoc P {W} := by
    rw [← Algebra.adjoin_range_eq_range_aeval, Algebra.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    exact div_mem_degZeroLoc P {W} (isWeightedHomogeneous_X F (blockWeight ι) x)
      (isWeightedHomogeneous_X F (blockWeight ι) ⟨x.1, v x.1⟩) (fun hm => hv x.1 (hPW hm))
      (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hv x.1)
  have : Algebra.FiniteType F e.range :=
    Algebra.FiniteType.of_surjective e.rangeRestrict e.rangeRestrict_surjective
  have _ : IsNoetherianRing e.range := Algebra.FiniteType.isNoetherianRing F e.range
  let _ : Algebra e.range (degZeroLoc P {W}) := (Subalgebra.inclusion hle).toAlgebra
  let M : Submonoid e.range :=
    (IsUnit.submonoid (degZeroLoc P {W})).comap (algebraMap e.range (degZeroLoc P {W}))
  have hloc : IsLocalization M (degZeroLoc P {W}) := by
    rw [isLocalization_iff]
    refine ⟨fun y => y.2, fun z => ?_,
      fun {x y} hxy => ⟨1, by rw [Subalgebra.inclusion_injective hle hxy]⟩⟩
    obtain ⟨b, f, g, hf, hg, hgP, hgW, hz⟩ := h F K ι P {W}
      (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hW.isPrime) z.1 z.2
    have hgW' : g ∉ W := hgW W rfl
    have hcb : φ (c b) ≠ 0 := hφ _ fun hm => hcW b (hPW hm)
    have hz' : (z : FractionRing (MRing ι F ⧸ P)) = φ f / φ g := hz
    have heg : e g ≠ 0 := by
      intro h0
      apply hφ g hgP
      rw [hhom b g hg, h0, zero_mul]
    have hinv : (e g)⁻¹ ∈ degZeroLoc P {W} := by
      have hq : (e g)⁻¹ = φ (c b) / φ g := by
        rw [hhom b g hg]
        field_simp
      rw [hq]
      exact div_mem_degZeroLoc P {W} (hc b) hg hgP
        (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hgW')
    have hunit : (⟨e g, g, rfl⟩ : e.range) ∈ M :=
      isUnit_iff_exists_inv.mpr ⟨⟨(e g)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ heg)⟩
    refine ⟨(⟨e f, f, rfl⟩, ⟨⟨e g, g, rfl⟩, hunit⟩), Subtype.ext ?_⟩
    change (z : FractionRing (MRing ι F ⧸ P)) * e g = e f
    rw [hz', hhom b f hf, hhom b g hg]
    field_simp
  exact IsLocalization.isNoetherianRing M _ inferInstance
end DegZeroLocNoetherian
end GroundTheory.Heights₂.Heights.FieldNumbers
