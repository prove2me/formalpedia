-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_idealQuotient_eq_zero_of_isCoprime_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:47:21.756939+00:00
-- url     : https://prove2.me/submissions/bfd51b8f-87db-4330-9c3d-3d2c0ccc2f54

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CoprimeQuotientTrace
section
namespace QEC.Coding.AlgebraicGeometry
universe u v
variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
private theorem primaryTorsionLayer_idealQuotient_eq_bot_of_isCoprime_map
    (p : Ideal R) (J : Ideal S)
    (hcop : IsCoprime (Ideal.map (algebraMap R S) p) J)
    (i : ℕ) :
    primaryTorsionLayer p (S ⧸ J) i = ⊥ := by
  obtain ⟨c, hc, d, hd, hcd⟩ := Ideal.isCoprime_iff_exists.mp hcop
  have hc_one : Ideal.Quotient.mk J c = 1 := by
    rw [Ideal.Quotient.mk_eq_one_iff_sub_mem, ← hcd]
    have hsub : c - (c + d) = -d := by ring
    rw [hsub]
    exact J.neg_mem hd
  apply eq_bot_iff.mpr
  intro x hx
  rw [primaryTorsionLayer, Submodule.mem_torsionBySet_iff] at hx
  let A : Ideal S := LinearMap.ker
    (LinearMap.toSpanSingleton S (S ⧸ J) (x : S ⧸ J))
  have hmap : Ideal.map (algebraMap R S) (p ^ i) ≤ A := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change algebraMap R S r • (x : S ⧸ J) = 0
    rw [IsScalarTower.algebraMap_smul]
    exact hx ⟨r, hr⟩
  have hc_pow : c ^ i ∈ Ideal.map (algebraMap R S) (p ^ i) := by
    rw [Ideal.map_pow]
    exact Ideal.pow_mem_pow hc i
  have hc_pow_zero : c ^ i • (x : S ⧸ J) = 0 := by
    exact hmap hc_pow
  have hc_pow_identity : c ^ i • (x : S ⧸ J) = x := by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_pow,
      hc_one, one_pow, one_mul]
  exact hc_pow_identity.symm.trans hc_pow_zero
private theorem primaryTorsionGrade_idealQuotient_subsingleton_of_isCoprime_map
    (p : Ideal R) (J : Ideal S)
    (hcop : IsCoprime (Ideal.map (algebraMap R S) p) J)
    (i : ℕ) :
    Subsingleton (primaryTorsionGrade p (S ⧸ J) i) := by
  rw [Submodule.Quotient.subsingleton_iff]
  apply eq_top_iff.mpr
  intro x _hx
  have hxzero : (x : S ⧸ J) = 0 := by
    have hx : (x : S ⧸ J) ∈ (⊥ : Submodule R (S ⧸ J)) := by
      rw [← primaryTorsionLayer_idealQuotient_eq_bot_of_isCoprime_map
        p J hcop (i + 1)]
      exact x.property
    simpa only [Submodule.mem_bot] using hx
  change (x : S ⧸ J) ∈ primaryTorsionLayer p (S ⧸ J) i
  rw [hxzero]
  exact Submodule.zero_mem _
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
universe u v
variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    [IsNoetherianRing R] [Module.Finite R S]
    (p : Ideal R) [p.IsMaximal]
    (J : Ideal S)
    (hcop : IsCoprime (Ideal.map (algebraMap R S) p) J)
    (f : (S ⧸ J) →ₗ[R] (S ⧸ J)) (n : ℕ) :
    primaryTorsionTrace p f n = 0 := by
  classical
  rw [primaryTorsionTrace]
  apply Finset.sum_eq_zero
  intro i _hi
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI := primaryTorsionGradeModule (M := S ⧸ J) p i
  letI : Module.Finite (R ⧸ p) (primaryTorsionGrade p (S ⧸ J) i) :=
    primaryTorsionGradeFinite (M := S ⧸ J) p i
  letI : Subsingleton (primaryTorsionGrade p (S ⧸ J) i) :=
    primaryTorsionGrade_idealQuotient_subsingleton_of_isCoprime_map
      p J hcop i
  rw [primaryTorsionGradeTrace]
  have hend : primaryTorsionGradeEndomorphism p f i = 0 :=
    Subsingleton.elim _ _
  rw [hend, map_zero]
end QEC.Coding.AlgebraicGeometry
