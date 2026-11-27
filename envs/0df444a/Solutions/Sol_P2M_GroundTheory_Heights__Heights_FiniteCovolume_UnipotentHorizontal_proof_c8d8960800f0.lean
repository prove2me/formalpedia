-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentHorizontal_proof_c8d8960800f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:05:25.644731+00:00
-- url     : https://prove2.me/submissions/6ef4136a-54ce-4f62-8f1d-79a1c4686123

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipotentHorizontal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StRationalUnipotent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipRadicalOfRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StComplementArchCocompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PMahlerCompactness
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentHorizontal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_archUnitary_preserves_form_29e3039d0c28
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ArchInvariant_proof_c3cce6e49c61
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proof_b489f5d0bce6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramAtData_proof_6f69e474274d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HermAtPlace_proof_4b36a3148377
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_MahlerCompactness_proof_5174a6040fc4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_vecAt_add_377129494f15
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_vecAt_smul_805c51e80ff2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_unipCoord_apply_32954df33c4e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecAt_unitary_06ccbf9ff635
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
open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace UnipotentHorizontal
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W)
    (h0 : RationalUnipotent.Statement h) (h4 : UnipRadicalOfRational.Statement h v)
    (h5 : ComplementArchCocompact.Statement h v) : UnipotentHorizontal.Statement h v := by
  intro D La x₀ w₀ hD hx₀ hp
  obtain ⟨m, hm, hγ⟩ := h0 D La x₀ w₀ hD hx₀ hp
  obtain ⟨K5, hK5, hK⟩ := h5 La x₀ w₀ (2 * m) hD.isLattice hp (by omega)
  refine ⟨-K5, hK5.neg, fun n => ?_⟩
  obtain ⟨hxx, -, hxw⟩ := hp
  have hwx : h.toSesq w₀ x₀ = 1 := by
    rw [← LinearMap.isSymm_def.mp h.isSymm x₀ w₀, hxw, map_one]
  have hH := HermAtPlace.proof h v
  have bXX : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 := fun w => by
    rw [← hH, hxx, map_zero]
  have bWX : ∀ w, star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 1 := fun w => by
    rw [← hH, hwx, map_one]
  have hn := mem_unipRadical.1 n.2

  obtain ⟨u, hu⟩ : ∃ u, u = unipCoord h v x₀ w₀ n := ⟨_, rfl⟩
  have bXu : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ u w) = 0 := fun w => by
    have e := archUnitary_preserves_form h v n w (vecAt v x₀ w) (vecAt v w₀ w)
    rw [(hn w).1] at e
    rw [hu, unipCoord_apply, mulVec_sub, dotProduct_sub, e, sub_self]
  obtain ⟨t0, ht0⟩ : ∃ t0 : InfinitePlace E → ℂ,
      ∀ w, t0 w = star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ u w) := ⟨fun _ => _, fun _ => rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : InfinitePlace E → ι → ℂ,
      ∀ w, Y w = u w - t0 w • vecAt v x₀ w := ⟨fun _ => _, fun _ => rfl⟩
  have bXY : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w) = 0 := fun w => by
    rw [hY, mulVec_sub, dotProduct_sub, mulVec_smul, dotProduct_smul, bXu, bXX, smul_zero,
      sub_zero]
  have bWY : ∀ w, star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w) = 0 := fun w => by
    rw [hY, mulVec_sub, dotProduct_sub, mulVec_smul, dotProduct_smul, bWX, ← ht0, smul_eq_mul,
      mul_one, sub_self]

  obtain ⟨y, hyW, ⟨z, hzLa, hyz⟩, hyK⟩ := hK (-Y) fun w => by
    simp only [Pi.neg_apply, mulVec_neg, dotProduct_neg, neg_eq_zero]
    exact ⟨bXY w, bWY w⟩
  have hzz : h.toSesq z z ∈ integralClosure ℤ E := hD.integral z hzLa z hzLa
  have hzzc : conj F E (h.toSesq z z) = h.toSesq z z := LinearMap.isSymm_def.mp h.isSymm z z
  let a : 𝓞 E := -((2 * m : ℕ) : 𝓞 E) * ⟨h.toSesq z z, hzz⟩
  have haE : (a : E) = -((2 * m : ℕ) : E) * h.toSesq z z := by
    have h2 : (((2 * m : ℕ) : 𝓞 E) : E) = ((2 * m : ℕ) : E) :=
      map_natCast (algebraMap (𝓞 E) E) (2 * m)
    rw [show (a : E) = -(((2 * m : ℕ) : 𝓞 E) : E) * h.toSesq z z from rfl, h2]
  let c : E := (m : E) * (a : E)
  have hyy : h.toSesq y y = ((2 * m : ℕ) : E) * ((2 * m : ℕ) : E) * h.toSesq z z := by
    rw [hyz]
    simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
    ring
  have hc : c + conj F E c = -h.toSesq y y := by
    simp only [c, hyy, haE, map_mul, map_neg, map_natCast, hzzc]
    push_cast
    ring
  obtain ⟨γ, hγLa, hγx, hγw, hγz⟩ := hγ y c hyW
    ⟨2 • z, nsmul_mem hzLa 2, by rw [hyz, smul_smul, mul_comm]⟩ ⟨a, rfl⟩ hc

  have hgood : ∀ z : W, h.toSesq x₀ z = 0 → ∃ b : E, γ • z = z + b • x₀ := by
    intro z hz
    have hz' : z - h.toSesq w₀ z • x₀ ∈ hypComplement h x₀ w₀ := by
      rw [mem_hypComplement]
      constructor
      · rw [map_sub, map_smul, hz, hxx, smul_zero, sub_zero]
      · rw [map_sub, map_smul, hwx, smul_eq_mul, mul_one, sub_self]
    refine ⟨-h.toSesq y (z - h.toSesq w₀ z • x₀), ?_⟩
    have e : (γ : W ≃ₗ[E] W) z = (γ : W ≃ₗ[E] W) (z - h.toSesq w₀ z • x₀) +
        h.toSesq w₀ z • (γ : W ≃ₗ[E] W) x₀ := by
      rw [← map_smul, ← map_add, sub_add_cancel]
    have e1 : (γ : W ≃ₗ[E] W) (z - h.toSesq w₀ z • x₀) =
        (z - h.toSesq w₀ z • x₀) - h.toSesq y (z - h.toSesq w₀ z • x₀) • x₀ := hγz _ hz'
    have e2 : (γ : W ≃ₗ[E] W) x₀ = x₀ := hγx
    change (γ : W ≃ₗ[E] W) z = _
    rw [e, e1, e2, neg_smul]
    abel
  have hδ := h4 x₀ γ hγx hgood
  have hδw := mem_unipRadical.1 hδ
  have hs : ∀ w, ∃ s : ℂ, (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
      Matrix ι ι ℂ) *ᵥ Y w = Y w + s • vecAt v x₀ w := fun w => (hδw w).2 (Y w) (bXY w)
  choose s hs using hs
  refine ⟨⟨archEmbed h v γ, hδ⟩, Subgroup.mem_map.2 ⟨⟨γ, hγLa⟩, MulAction.mem_stabilizer_iff.2 hγx,
    rfl⟩, fun w => w.embedding c + t0 w + s w, ?_⟩
  have hprod : ∀ w, unipCoord h v x₀ w₀ (⟨archEmbed h v γ, hδ⟩ * n) w =
      (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
        ((((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w) -
          vecAt v w₀ w := fun w => by
    rw [unipCoord_apply, Matrix.mulVec_mulVec]
    rfl
  have hdW : ∀ w, (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
      Matrix ι ι ℂ) *ᵥ vecAt v w₀ w = vecAt v w₀ w + vecAt v y w + w.embedding c • vecAt v x₀ w :=
    fun w => by
      rw [← vecAt_unitary, show (γ : W ≃ₗ[E] W) w₀ = γ • w₀ from rfl, hγw, StabilizerLevi.vecAt_add,
        StabilizerLevi.vecAt_add, StabilizerLevi.vecAt_smul]
  have hgW : ∀ w, (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
      vecAt v w₀ w = u w + vecAt v w₀ w := fun w => by
    rw [hu, unipCoord_apply, sub_add_cancel]
  have huY : ∀ w, u w = Y w + t0 w • vecAt v x₀ w := fun w => by rw [hY, sub_add_cancel]
  rw [Set.mem_neg]
  convert hyK using 1
  funext w
  simp only [Pi.neg_apply, Pi.sub_apply, hprod w, hgW w, huY w, mulVec_add, mulVec_smul, hs w,
    (hδw w).1, hdW w, add_smul]
  abel
end UnipotentHorizontal
end GroundTheory.Heights₂.Heights.FiniteCovolume
