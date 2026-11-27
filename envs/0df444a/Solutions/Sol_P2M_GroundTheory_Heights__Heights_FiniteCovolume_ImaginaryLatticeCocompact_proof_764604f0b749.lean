-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_ImaginaryLatticeCocompact_proof_764604f0b749
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:01:24.128263+00:00
-- url     : https://prove2.me/submissions/9f1c4bd2-6620-441e-b4af-10d7e13ed122

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StImaginaryLatticeCocompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PImaginaryLatticeCocompact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_im_embedding_algebraMap_3378dac9341f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_imaginary_integer_17bb0c015b5a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_card_infinitePlace_eq_4816e5c7e85e
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_algebraMap
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace ImaginaryLatticeCocompact
theorem _root_.solution : ImaginaryLatticeCocompact.Statement F E := by
  classical
  intro m hm
  obtain ⟨t, ht0, htc⟩ := exists_imaginary_integer F E
  let L : Free.ChooseBasisIndex ℤ (𝓞 F) → InfinitePlace E → ℝ := fun i w =>
    (w.embedding ((m : E) * algebraMap F E (integralBasis F i) * (t : E))).im
  let T : (Free.ChooseBasisIndex ℤ (𝓞 F) → ℝ) →ₗ[ℝ] (InfinitePlace E → ℝ) :=
    { toFun := fun c w => ∑ i, c i * L i w
      map_add' := by
        intro c d; ext w; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro r c; ext w; simp [Finset.mul_sum, mul_assoc] }

  have hr : ∀ w : InfinitePlace E, (w.embedding (t : E)).im ≠ 0 := by
    intro w h
    have hre : (w.embedding (t : E)).re = 0 := by
      have h1 := embedding_conj (F := F) w.embedding (t : E)
      rw [htc, map_neg] at h1
      have h2 := congrArg Complex.re h1
      simp only [Complex.neg_re, Complex.conj_re] at h2
      linarith
    exact ht0 ((map_eq_zero _).mp (Complex.ext hre h))
  have hL : ∀ i w, L i w =
      m * (w.embedding (algebraMap F E (integralBasis F i))).re * (w.embedding (t : E)).im := by
    intro i w
    simp only [L, map_mul, map_natCast, Complex.mul_im, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, im_embedding_algebraMap]
    ring
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hw : ∀ w : InfinitePlace E,
        ∑ i, c i * (w.embedding (algebraMap F E (integralBasis F i))).re = 0 := by
      intro w
      have h1 : ∑ i, c i * L i w = 0 := congrFun hc w
      have h2 : (∑ i, c i * (w.embedding (algebraMap F E (integralBasis F i))).re) *
          ((m : ℝ) * (w.embedding (t : E)).im) = 0 := by
        rw [Finset.sum_mul, ← h1]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hL]; ring
      exact (mul_eq_zero.mp h2).resolve_right
        (mul_ne_zero (by exact_mod_cast hm.ne') (hr w))
    have hτ : ∀ τ : F →+* ℂ, ∑ i, (c i : ℂ) * τ (integralBasis F i) = 0 := by
      intro τ
      let _ : Algebra F ℂ := τ.toAlgebra
      let σ : E →ₐ[F] ℂ := IsAlgClosed.lift
      have hστ : ∀ x : F, (σ : E →+* ℂ) (algebraMap F E x) = τ x := fun x => σ.commutes x
      have hre : ∀ x : F,
          ((InfinitePlace.mk (σ : E →+* ℂ)).embedding (algebraMap F E x)).re = (τ x).re := by
        intro x
        rcases InfinitePlace.embedding_mk_eq (σ : E →+* ℂ) with h | h
        · rw [h, hστ]
        · rw [h, ComplexEmbedding.conjugate_coe_eq, hστ, Complex.conj_re]
      have him : ∀ x : F, (τ x).im = 0 := by
        intro x
        rw [← hστ]
        exact im_embedding_algebraMap (F := F) (σ : E →+* ℂ) x
      apply Complex.ext
      · rw [Complex.re_sum, Complex.zero_re, ← hw (InfinitePlace.mk (σ : E →+* ℂ))]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.re_ofReal_mul, hre]
      · rw [Complex.im_sum, Complex.zero_im]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [Complex.im_ofReal_mul, him, mul_zero]
    have hli := (canonicalEmbedding.latticeBasis F).linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    funext i
    have h0 := hli (fun i => (c i : ℂ)) (by
      funext τ
      simp only [Finset.sum_apply, Pi.smul_apply, canonicalEmbedding.latticeBasis_apply,
        canonicalEmbedding.apply_at, smul_eq_mul, Pi.zero_apply]
      exact hτ τ) i
    exact_mod_cast h0
  have hsurj : Function.Surjective T := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      card_infinitePlace_eq F E, finrank_eq_card_basis (integralBasis F)]
  refine ⟨∑ i, ∑ w, |L i w|, fun s => ?_⟩
  obtain ⟨c, hc⟩ := hsurj s
  have hint : ∀ i, IsIntegral ℤ (algebraMap F E (integralBasis F i)) := by
    intro i
    rw [integralBasis_apply]
    exact map_isIntegral_int (algebraMap F E) (RingOfIntegers.basis F i).2
  have hk : ∀ k : ℤ, IsIntegral ℤ (k : E) := fun k => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := k)
  let x : E := ∑ i, (⌊c i⌋ : E) * algebraMap F E (integralBasis F i) * (t : E)
  have hx : IsIntegral ℤ x :=
    IsIntegral.sum _ fun i _ => ((hk _).mul (hint i)).mul t.2
  refine ⟨⟨x, hx⟩, ?_, fun w => ?_⟩
  · change (m : E) * x + conj F E ((m : E) * x) = 0
    have : conj F E x = -x := by
      simp only [x, map_sum, map_mul, map_intCast, conj_algebraMap, htc]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [map_mul, map_natCast, this]
    ring
  · change |(w.embedding ((m : E) * x)).im - s w| ≤ ∑ i, ∑ w, |L i w|
    have key : (w.embedding ((m : E) * x)).im = ∑ i, (⌊c i⌋ : ℝ) * L i w := by
      have e : (m : E) * x = ∑ i, (⌊c i⌋ : E) * ((m : E) * algebraMap F E (integralBasis F i) * (t : E)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [e, map_sum, Complex.im_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_intCast]
      simp [Complex.mul_im, L]
    have hs : s w = ∑ i, c i * L i w := by rw [← hc]; rfl
    rw [key, hs, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    have h1 : |(⌊c i⌋ : ℝ) * L i w - c i * L i w| ≤ |L i w| := by
      rw [← sub_mul, abs_mul]
      have : |(⌊c i⌋ : ℝ) - c i| ≤ 1 := by
        rw [abs_sub_comm, abs_le]
        constructor <;> linarith [Int.floor_le (c i), Int.lt_floor_add_one (c i)]
      exact mul_le_of_le_one_left (abs_nonneg _) this
    exact h1.trans (Finset.single_le_sum (f := fun w' => |L i w'|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ w))
end ImaginaryLatticeCocompact
end GroundTheory.Heights₂.Heights.FiniteCovolume
