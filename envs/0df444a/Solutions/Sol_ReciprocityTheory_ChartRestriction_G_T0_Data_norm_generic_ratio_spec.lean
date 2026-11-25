-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.norm_generic_ratio_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:36:15.493789+00:00
-- url     : https://prove2.me/submissions/db7c9ed4-6739-41cd-a92b-6731300eeaae

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BasisBlock0
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormGenericRatioSpec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_hx4v2_ratio_wx
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_basis_block0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    ∃ P Q : KTp K d.D d.N, Q ≠ 0 ∧ (∀ x, d.sub0 x Q = Q) ∧
      (letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra;
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) P =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q * Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c)) ∧
      ∀ x : Fin (d.N + 1) → K, d.wx x c ≠ 0 →
        (letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra;
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.sub0 x P) =
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q *
              Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N)
                (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c)))) := by
  let _ : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  obtain ⟨n, b, Q0, M, hQ0, hQ0s, hMs, hM⟩ := d.basis_block0 hd h c
  let r : Fin (d.N + 1) → OmS (Ω c) d.D d.N := fun j =>
    algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))
  let ι0 : KTp K d.D d.N →+* KTf K d.D d.N := algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
  have hQ0' : ι0 Q0 ≠ 0 := fun e =>
    hQ0 (IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N) (by rw [e, map_zero]))
  have key : ∀ a : Fin (d.N + 1) → KTp K d.D d.N,
      Algebra.norm (KTf K d.D d.N) (∑ j, ι0 (a j) • r j) = ι0 (∑ j, a j • M j).det / ι0 Q0 ^ n := by
    intro a
    rw [Algebra.norm_eq_matrix_det b, map_sum]
    simp_rw [map_smul]
    have hmat : (∑ j, ι0 (a j) • Algebra.leftMulMatrix b (r j)) =
        (ι0 Q0)⁻¹ • (∑ j, a j • M j).map ι0 := by
      ext i i'
      rw [Matrix.smul_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.sum_apply, map_sum,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hM j, Matrix.smul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
        smul_eq_mul, map_mul]
      ring
    rw [hmat, Matrix.det_smul, Fintype.card_fin]
    have hdet : ((∑ j, a j • M j).map ι0).det = ι0 (∑ j, a j • M j).det :=
      (RingHom.map_det ι0 _).symm
    rw [hdet, inv_pow, div_eq_mul_inv, mul_comm]
  have hw0 : d.rationalBaseRow c = ∑ j, ι0 (MvPolynomial.X ((0 : Fin (d.D + 1)), j) : KTp K d.D d.N) • r j := by
    simp only [Data.rationalBaseRow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    simp only [Data.KTtoS, ι0, IsFractionRing.lift_algebraMap, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, r]
  refine ⟨(∑ j, (MvPolynomial.X ((0 : Fin (d.D + 1)), j) : KTp K d.D d.N) • M j).det, Q0 ^ n, pow_ne_zero _ hQ0,
    fun x => by rw [map_pow, hQ0s], ?_, ?_⟩
  · show ι0 _ = ι0 (Q0 ^ n) * Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c)
    rw [hw0, key, map_pow]
    field_simp
  · intro x _
    have hs : d.sub0 x (∑ j, (MvPolynomial.X ((0 : Fin (d.D + 1)), j) : KTp K d.D d.N) • M j).det =
        (∑ j, (MvPolynomial.C (x j) : KTp K d.D d.N) • M j).det := by
      have hmd := RingHom.map_det (d.sub0 x : KTp K d.D d.N →+* KTp K d.D d.N)
        (∑ j, (MvPolynomial.X ((0 : Fin (d.D + 1)), j) : KTp K d.D d.N) • M j)
      rw [RingHom.coe_coe] at hmd
      rw [hmd]
      congr 1
      ext i i'
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul, map_sum, map_mul, RingHom.coe_coe, hMs]
      simp
    have hr : algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c)) =
        ∑ j, ι0 (MvPolynomial.C (x j) : KTp K d.D d.N) • r j := by
      rw [d.hx4v2_ratio_wx hd c x, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      congr 1
      simp only [Data.KTtoS, ι0, IsFractionRing.lift_algebraMap, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe]
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      exact (IsScalarTower.algebraMap_apply K (Ω c) (OmS (Ω c) d.D d.N) (x j)).symm
    show ι0 _ = ι0 (Q0 ^ n) * _
    rw [hs, hr, key, map_pow]
    field_simp
end ReciprocityTheory.ChartRestriction.G.T0.Data
