-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointHeightDegree_proof_7e9af8e52ee3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:07:41.738588+00:00
-- url     : https://prove2.me/submissions/b1a25a88-cbd7-45c6-98b1-fd5ef73b76d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsPointHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PPointHeightDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_height_eq_of_ringHom_4fab993a720d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finsum_log_eq_log_finprod_4287d2cc8f03
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_hasFiniteMulSupport_iSup_place_6bf3c48ba8b2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_iSup_place_pos_10fee29093fa


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
open NumberField Module Matrix
open scoped ComplexOrder
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace PointHeightDegree
theorem _root_.solution (hPts : OneBlockPoints.Statement) (hLine : LatticeLineExists.Statement)
    (hDual : LineIdealDual.Statement) (hIdx : IdealIndexPlaces.Statement) :
    PointHeightDegree.Statement := by
  intro K _ _ r N F φ hφ
  refine ⟨hLine K r N F φ hφ, ?_⟩
  intro A hA hagree K' _ _ _ v hv τ
  set y : Fin (N + 1) → K' := latticeValue φ v with hy_def

  have hx : latticePoint φ (τ.comp (algebraMap K K')) (fun j ↦ τ (v j)) = fun _ b ↦ τ (y b) := by
    funext u b
    simp [latticePoint, hy_def, latticeValue, map_sum, map_mul]

  have hσ : ∀ σ' : K' →+* ℂ, (fun (_ : Unit) b ↦ σ' (y b)) =
      latticePoint φ (σ'.comp (algebraMap K K')) (fun j ↦ σ' (v j)) := by
    intro σ'
    funext u b
    simp [latticePoint, hy_def, latticeValue, map_sum, map_mul]

  have hy0 : y ≠ 0 := by
    intro h0
    apply hv
    have hne : Nonempty (K' →+* ℂ) := by
      rw [← Fintype.card_pos_iff, NumberField.Embeddings.card]
      exact Module.finrank_pos
    obtain ⟨σ'⟩ := hne
    funext j0
    obtain ⟨R, hR⟩ := (hPts K r N F φ hφ).2.2 (σ'.comp (algebraMap K K')) j0
    have key : ∑ b, R b * σ' (y b) = σ' (v j0) := by
      have h1 := congrFun (hσ σ') ()
      have h2 : ∀ b, σ' (y b) = ∑ j, (σ'.comp (algebraMap K K')) (φ b j) * σ' (v j) := fun b ↦
        congrFun h1 b
      simp only [h2, Finset.mul_sum]
      rw [Finset.sum_comm]
      have h3 : ∀ j, ∑ b, R b * ((σ'.comp (algebraMap K K')) (φ b j) * σ' (v j)) =
          (∑ b, R b * (σ'.comp (algebraMap K K')) (φ b j)) * σ' (v j) := by
        intro j
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ ↦ by ring
      simp only [h3, hR]
      simp
    have : σ' (v j0) = 0 := by
      rw [← key]
      simp [h0]
    exact (map_eq_zero_iff σ' σ'.injective).mp this
  have hblock : BlockNonzero (fun (_ : Unit) b ↦ y b) := fun _ h ↦ hy0 (funext fun b ↦ congrFun h b)
  rw [hx, height_eq_of_ringHom A τ (fun _ b ↦ y b) hblock]

  have hpos : ∀ w : FinitePlace K', 0 < ⨆ b, w (y b) := iSup_place_pos hy0
  have hfin : ∑ᶠ w : FinitePlace K', finiteTerm A w (fun _ b ↦ y b) =
      -Real.log (genIndex (multiplierIdeal y).toAddSubgroup (1 : Submodule (𝓞 K') K').toAddSubgroup) := by
    have hterm : ∀ w : FinitePlace K', finiteTerm A w (fun _ b ↦ y b) = Real.log (⨆ b, w (y b)) := by
      intro w
      simp [finiteTerm, hA]
    simp only [hterm]
    rw [finsum_log_eq_log_finprod hpos (hasFiniteMulSupport_iSup_place hy0)]
    have hI := hIdx K' (Fin (N + 1)) y hy0
    rw [eq_inv_of_mul_eq_one_right hI, Real.log_inv]

  have harch : ∀ σ' : K' →+* ℂ, Real.log (A.metric fun _ b ↦ σ' (y b)) =
      1 / 2 * Real.log (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 ↦ v)).det.re := by
    intro σ'
    have hw : (fun j ↦ σ' (v j)) ≠ 0 := by
      intro h
      apply hv
      funext j
      exact (map_eq_zero_iff σ' σ'.injective).mp (congrFun h j)
    rw [show (fun (_ : Unit) b ↦ σ' (y b)) = _ from hσ σ', hagree _ _ hw, Matrix.det_unique]
    have hq : 0 ≤ (star (fun j ↦ σ' (v j)) ⬝ᵥ
        (F.metric (σ'.comp (algebraMap K K')) *ᵥ fun j ↦ σ' (v j))).re :=
      le_of_lt (Complex.lt_def.mp ((F.posDef _).dotProduct_mulVec_pos hw)).1
    rw [Real.log_sqrt hq]
    simp only [gramAt]
    unfold embVec
    ring

  have hline : genIndex ((latticeExtend K' F.lattice ⊓
        (Submodule.span K' (Set.range fun _ : Fin 1 ↦ v)).restrictScalars (𝓞 K')).toAddSubgroup)
        (Submodule.span (𝓞 K') (Set.range fun _ : Fin 1 ↦ v)).toAddSubgroup =
      genIndex (multiplierIdeal y).toAddSubgroup (1 : Submodule (𝓞 K') K').toAddSubgroup := by
    let f : K' →+ (Fin (r + 1) → K') :=
      { toFun := fun a ↦ a • v, map_zero' := zero_smul _ _, map_add' := fun a a' ↦ add_smul a a' v }
    have hf : Function.Injective f := smul_left_injective K' hv
    have e1 : (latticeExtend K' F.lattice ⊓
        (Submodule.span K' (Set.range fun _ : Fin 1 ↦ v)).restrictScalars (𝓞 K')).toAddSubgroup =
        (multiplierIdeal y).toAddSubgroup.map f := by
      ext x
      simp only [Submodule.mem_toAddSubgroup, Submodule.mem_inf, Submodule.restrictScalars_mem,
        Set.range_const, Submodule.mem_span_singleton, AddSubgroup.mem_map]
      constructor
      · rintro ⟨hxL, a, rfl⟩
        exact ⟨a, (hDual K r N F φ hφ K' v a).mp hxL, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨(hDual K r N F φ hφ K' v a).mpr ha, a, rfl⟩
    have e2 : (Submodule.span (𝓞 K') (Set.range fun _ : Fin 1 ↦ v)).toAddSubgroup =
        (1 : Submodule (𝓞 K') K').toAddSubgroup.map f := by
      ext x
      simp only [Submodule.mem_toAddSubgroup, Set.range_const, Submodule.mem_span_singleton,
        AddSubgroup.mem_map, Submodule.mem_one]
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨algebraMap (𝓞 K') K' c, ⟨c, rfl⟩, (algebraMap_smul K' c v)⟩
      · rintro ⟨a, ⟨c, rfl⟩, rfl⟩
        exact ⟨c, (algebraMap_smul K' c v).symm⟩
    rw [e1, e2, genIndex, genIndex, AddSubgroup.relIndex_map_map_of_injective _ _ hf,
      AddSubgroup.relIndex_map_map_of_injective _ _ hf]

  have hdeg : F.lineDegree K' v = normalise K' (-(-Real.log
      (genIndex (multiplierIdeal y).toAddSubgroup (1 : Submodule (𝓞 K') K').toAddSubgroup)) -
      ∑ σ' : K' →+* ℂ, Real.log (A.metric fun _ b ↦ σ' (y b))) := by
    unfold HermLattice.lineDegree subDegree
    change normalise K' (Real.log (genIndex ((latticeExtend K' F.lattice ⊓ _).toAddSubgroup) _) - _) = _
    rw [hline, Finset.sum_congr rfl fun σ' _ ↦ harch σ', ← Finset.mul_sum, neg_neg]
  rw [hdeg, hfin, normalise]
  ring
end PointHeightDegree
end GroundTheory.Heights₂.Heights
