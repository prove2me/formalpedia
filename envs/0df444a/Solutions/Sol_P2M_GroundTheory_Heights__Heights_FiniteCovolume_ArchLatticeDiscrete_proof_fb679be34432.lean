-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_ArchLatticeDiscrete_proof_fb679be34432
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:49:00.706055+00:00
-- url     : https://prove2.me/submissions/0510ab71-bbd3-418c-a897-4d60076cfd1b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchLatticeDiscrete
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_zero_of_isIntegral_of_forall_place_lt_one_7a41888a79e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_archEmbed_apply_val_02d3cfa618b2
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
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
namespace ArchLatticeDiscrete
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W) :
    ArchLatticeDiscrete.Statement h v := by
  classical
  intro La hLa
  obtain ⟨S, hS⟩ := hLa.fg
  have hSLa : ∀ s ∈ S, s ∈ La := fun s hs => hS ▸ AddSubgroup.subset_closure hs

  obtain ⟨d, hd0, hd⟩ := exists_integral_multiples ℤ ℚ
    (S.biUnion fun s => Finset.univ.image fun i => v.repr s i)
  let T : AddSubgroup W :=
    { carrier := {y | ∀ i, IsIntegral ℤ (d • v.repr y i)}
      add_mem' := fun {a b} ha hb i => by
        simpa only [map_add, Finsupp.add_apply, smul_add] using (ha i).add (hb i)
      zero_mem' := fun i => by
        simpa only [map_zero, Finsupp.zero_apply, smul_zero] using isIntegral_zero
      neg_mem' := fun {a} ha i => by
        simpa only [map_neg, Finsupp.neg_apply, smul_neg] using (ha i).neg }
  have hLaT : La ≤ T := by
    rw [← hS, AddSubgroup.closure_le]
    intro s hs i
    exact hd _ (Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
  have hdE : (d : E) ≠ 0 := Int.cast_ne_zero.2 hd0

  have key : ∀ y ∈ La, (∀ (w : InfinitePlace E) (i : ι),
      |(d : ℝ)| * ‖w.embedding (v.repr y i)‖ < 1) → y = 0 := by
    intro y hy hsmall
    refine v.repr.injective (Finsupp.ext fun i => ?_)
    have hz := eq_zero_of_isIntegral_of_forall_place_lt_one (hLaT hy i) fun w => by
      rw [← InfinitePlace.norm_embedding_eq, zsmul_eq_mul, map_mul, map_intCast, norm_mul,
        Complex.norm_intCast]
      exact hsmall w i
    rw [zsmul_eq_mul] at hz
    simpa [hdE] using hz

  set B : ℝ := ∑ s ∈ S, ∑ w : InfinitePlace E, ∑ j, ‖w.embedding (v.repr s j)‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hdpos : 0 < |(d : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hd0)
  set δ : ℝ := 1 / (|(d : ℝ)| * (B + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hdδB : |(d : ℝ)| * δ * B < 1 := by
    have e : |(d : ℝ)| * δ = 1 / (B + 1) := by
      rw [hδ]; field_simp
    rw [e, div_mul_eq_mul_div, one_mul, div_lt_one (by linarith)]
    linarith
  let U : Set (InfinitePlace E → GL ι ℂ) :=
    {g | ∀ w i j, ‖((g w : GL ι ℂ) : Matrix ι ι ℂ) i j - (1 : Matrix ι ι ℂ) i j‖ < δ}
  have hU : IsOpen U := by
    have e : U = ⋂ w, ⋂ i, ⋂ j, {g : InfinitePlace E → GL ι ℂ |
        ‖((g w : GL ι ℂ) : Matrix ι ι ℂ) i j - (1 : Matrix ι ι ℂ) i j‖ < δ} := by
      ext g; simp [U]
    rw [e]
    refine isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun i =>
      isOpen_iInter_of_finite fun j => isOpen_lt ?_ continuous_const
    exact (((Units.continuous_val.comp (continuous_apply w)).matrix_elem i j).sub
      continuous_const).norm

  have hone : ∀ γ ∈ latticeStab h La,
      ((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) ∈ U → γ = 1 := by
    intro γ hγ hγU
    set M := LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) with hM
    have hγLa : ∀ x ∈ La, (γ : W ≃ₗ[E] W) x ∈ La := by
      intro x hx
      have h1 : γ • x ∈ γ • La := AddSubgroup.smul_mem_pointwise_smul x γ La hx
      rwa [MulAction.mem_stabilizer_iff.1 hγ] at h1
    have hrep : ∀ x : W, ∀ i, v.repr ((γ : W ≃ₗ[E] W) x - x) i =
        ∑ j, (M i j - (1 : Matrix ι ι E) i j) * v.repr x j := by
      intro x i
      have h1 := congrFun (LinearMap.toMatrix_mulVec_repr v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) x) i
      simp only [LinearEquiv.coe_coe] at h1
      rw [map_sub, Finsupp.sub_apply, ← h1]
      simp only [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply,
        ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, hM]
    have h1ij : ∀ (w : InfinitePlace E) i j,
        w.embedding ((1 : Matrix ι ι E) i j) = (1 : Matrix ι ι ℂ) i j := by
      intro w i j
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have hfix : ∀ s ∈ S, (γ : W ≃ₗ[E] W) s = s := by
      intro s hs
      refine sub_eq_zero.1 (key _ (sub_mem (hγLa s (hSLa s hs)) (hSLa s hs)) fun w i => ?_)
      have entry : ∀ j, ‖w.embedding (M i j - (1 : Matrix ι ι E) i j)‖ < δ := by
        intro j
        have := hγU w i j
        rw [archEmbed_apply_val, Matrix.map_apply] at this
        rwa [map_sub, h1ij]
      have hsum : ‖w.embedding (v.repr ((γ : W ≃ₗ[E] W) s - s) i)‖ ≤
          δ * ∑ j, ‖w.embedding (v.repr s j)‖ := by
        rw [hrep, map_sum, Finset.mul_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [map_mul, norm_mul]
        exact mul_le_mul_of_nonneg_right (entry j).le (norm_nonneg _)
      have hsB : ∑ j, ‖w.embedding (v.repr s j)‖ ≤ B := by
        refine le_trans ?_ (Finset.single_le_sum (f := fun s => ∑ w : InfinitePlace E, ∑ j,
          ‖w.embedding (v.repr s j)‖) (fun _ _ => Finset.sum_nonneg fun _ _ =>
            Finset.sum_nonneg fun _ _ => norm_nonneg _) hs)
        exact Finset.single_le_sum (f := fun w : InfinitePlace E => ∑ j,
          ‖w.embedding (v.repr s j)‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
          (Finset.mem_univ w)
      calc |(d : ℝ)| * ‖w.embedding (v.repr ((γ : W ≃ₗ[E] W) s - s) i)‖
          ≤ |(d : ℝ)| * (δ * B) := by
            gcongr
            exact hsum.trans (mul_le_mul_of_nonneg_left hsB hδpos.le)
        _ = |(d : ℝ)| * δ * B := by ring
        _ < 1 := hdδB
    have hfixLa : ∀ x ∈ La, (γ : W ≃ₗ[E] W) x = x := by
      intro x hx
      rw [← hS] at hx
      induction hx using AddSubgroup.closure_induction with
      | mem x hx => exact hfix x hx
      | zero => simp
      | add x y _ _ hx hy => simp [map_add, hx, hy]
      | neg x _ hx => simp [map_neg, hx]
    have hlin : ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) = LinearMap.id :=
      LinearMap.ext_on hLa.span_eq_top fun x hx => hfixLa x hx
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    simpa using LinearMap.congr_fun hlin x

  refine discreteTopology_of_isOpen_singleton_one ?_
  have hcont : Continuous fun x : archLatticeGroup h v La =>
      ((x : archUnitary h v) : InfinitePlace E → GL ι ℂ) :=
    continuous_subtype_val.comp continuous_subtype_val
  have e : ({1} : Set (archLatticeGroup h v La)) = (fun x : archLatticeGroup h v La =>
      ((x : archUnitary h v) : InfinitePlace E → GL ι ℂ)) ⁻¹' U := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl w i j
      simpa using hδpos
    · intro hx
      obtain ⟨γ, hγ, hγx⟩ := Subgroup.mem_map.1 x.2
      have h1 := hone γ hγ (by rw [hγx]; exact hx)
      apply Subtype.ext
      rw [← hγx, h1, map_one]
      rfl
  rw [e]
  exact hU.preimage hcont
end ArchLatticeDiscrete
end GroundTheory.Heights₂.Heights.FiniteCovolume
