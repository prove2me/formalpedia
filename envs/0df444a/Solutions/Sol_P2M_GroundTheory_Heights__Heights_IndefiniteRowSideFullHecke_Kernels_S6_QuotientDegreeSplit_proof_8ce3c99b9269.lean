-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotientDegreeSplit_proof_8ce3c99b9269
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:04.095171+00:00
-- url     : https://prove2.me/submissions/f217a85a-5e33-4c8d-8284-bc3a04bf2e69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesQuotIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_RelIndexSplitOfLe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_QuotientDegreeSplitAlt_genIndex_split_9ff3498b8c6c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesQuotIndex_ker_coordProj_eba1c16731d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesCoordDet_full_c35610a5b491
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesCoordImage_full_39a2e8bb2bcf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesDiagGram_full_8ff11ddb230b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesExtendBasis_full_63f55d25134d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesFischer_full_deb5581a4d66
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGenIndexDet_full_b60a8a3c7864
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGenIndexMono_full_6f6f30f807ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGenIndexPi_full_33ed3f72d0c2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGenIndexTrans_full_3ca845fd298c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGramChange_full_dcb0a61411bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGramDetChange_full_12fe0540b59d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGramFischerBound_full_1469f2c017cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGramPosDef_full_e43342dbfc82
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesIdealIndexPos_full_4f9c5f06aec4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesIdealLatticeFG_full_1aee04d7db78
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesIdealStdIndex_full_42daaad5b08f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesIsLattice_full_bf47e659fe20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesLatticeBasis_full_7e8167254293
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesLineDegree_full_c44e0f792b53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesProductFormula_full_ff39a65d05f0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesProjIndexLower_full_1df55b623de3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesProjLattice_full_509886f65659
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotDegreeBound_full_f1f9aab9b801
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotGramLog_full_1c29f5d3742d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotIndexLog_full_349909a2722b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotIndexSplit_full_f051c7119c9e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotIndex_full_e73217d08651
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesStdIndexDet_full_f76414530167
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesStdPi_full_9d1e83483f6d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrthogonalLines_full_ff0437c876fb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors
noncomputable section
open QuotientDegreeSplitAlt
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
namespace S6.QuotientDegreeSplit
theorem _root_.solution : S6.QuotientDegreeSplit.Statement := by
  intro K _ _ n Λ H hFG hspan m k b c hli hmk
  have hcard : Fintype.card (Fin m ⊕ Fin k) = Module.finrank K (Fin n → K) := by
    simp [hmk]
  set B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K) :=
    basisOfLinearIndependentOfCardEqFinrank' (Sum.elim b c) hli hcard with hBdef
  have hB : ⇑B = Sum.elim b c := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  have hBl : (fun i => B (Sum.inl i)) = b := by
    funext i; simp [hB]
  set W : Submodule (𝓞 K) (Fin n → K) :=
    (Submodule.span K (Set.range b)).restrictScalars (𝓞 K) with hWdef
  set π' : (Fin n → K) →ₗ[𝓞 K] (Fin k → K) := (coordProj B).restrictScalars (𝓞 K) with hπ'
  have hkerK : ∀ v, coordProj B v = 0 ↔ v ∈ Submodule.span K (Set.range b) := by
    intro v
    rw [← LinearMap.mem_ker, KLinesQuotIndex.ker_coordProj, hBl]
  have hb0 : ∀ i, coordProj B (b i) = 0 := fun i =>
    (hkerK _).mpr (Submodule.subset_span ⟨i, rfl⟩)
  have hc1 : ∀ j, coordProj B (c j) = Pi.single j 1 := by
    intro j
    have hcj : c j = B (Sum.inr j) := by simp [hB]
    rw [hcj]
    funext j'
    simp [coordProj, Pi.single_apply, Finsupp.single_apply]
    by_cases h : j = j'
    · subst h; simp
    · simp [h, Ne.symm h]

  set O : Submodule (𝓞 K) (Fin n → K) := Submodule.span (𝓞 K) (Set.range (Sum.elim b c)) with hOdef
  have htop : Submodule.span K (Set.range (Sum.elim b c)) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' hcard
  have hOspan : Submodule.span K (O : Set (Fin n → K)) = ⊤ := by
    rw [hOdef, Submodule.span_span_of_tower, htop]
  have hΛlat : Submodule.IsLattice ℚ (Λ.restrictScalars ℤ) :=
    LinesIsLattice.full K (Fin n) Λ hFG.restrictScalars hspan
  have hOlat : Submodule.IsLattice ℚ (O.restrictScalars ℤ) :=
    LinesIsLattice.full K (Fin n) O (Submodule.fg_span (Set.finite_range _)).restrictScalars hOspan
  have hpos : 0 < genIndex Λ.toAddSubgroup O.toAddSubgroup :=
    (LinesGenIndexTrans.full (Fin n → K) (Λ.restrictScalars ℤ) (O.restrictScalars ℤ)
      (O.restrictScalars ℤ) hΛlat hOlat hOlat).1

  have hker : (π' : (Fin n → K) →+ (Fin k → K)).ker = W.toAddSubgroup := by
    ext v
    rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, hWdef, Submodule.restrictScalars_mem,
      ← hkerK]
    rfl

  have hOW : O ⊓ W = Submodule.span (𝓞 K) (Set.range b) := by
    apply le_antisymm
    · rintro x ⟨hxO, hxW⟩
      obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hxO
      have h0 : π' (∑ i, r i • Sum.elim b c i) = 0 := (hkerK _).mpr hxW
      rw [Fintype.sum_sum_type] at h0 ⊢
      simp only [Sum.elim_inl, Sum.elim_inr] at h0 ⊢
      have hs : ∀ j, r (Sum.inr j) = 0 := by
        intro j
        have h1 := congrFun h0 j
        simp only [map_add, map_sum, map_smul, hπ', LinearMap.restrictScalars_apply, hb0, hc1,
          smul_zero, Finset.sum_const_zero, zero_add, Finset.sum_apply, Pi.smul_apply,
          Pi.single_apply, smul_ite, Finset.sum_ite_eq, Finset.mem_univ, if_true,
          Pi.zero_apply] at h1
        exact (smul_eq_zero.mp h1).resolve_right one_ne_zero
      simp only [hs, zero_smul, Finset.sum_const_zero, add_zero]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · refine le_inf (Submodule.span_mono ?_) (Submodule.span_le_restrictScalars (𝓞 K) K _)
      rintro _ ⟨i, rfl⟩
      exact ⟨Sum.inl i, rfl⟩

  have hOmap : O.map π' = Submodule.span (𝓞 K) (Set.range (coordProj B ∘ c)) := by
    have hcomp : ⇑π' ∘ Sum.elim b c = Sum.elim (fun _ => 0) (coordProj B ∘ c) := by
      funext x
      rcases x with i | j
      · exact hb0 i
      · rfl
    rw [hOdef, Submodule.map_span, ← Set.range_comp, hcomp, Set.Sum.elim_range,
      Submodule.span_union]
    have hbot : Submodule.span (𝓞 K) (Set.range (fun _ : Fin m => (0 : Fin k → K))) = ⊥ :=
      Submodule.span_eq_bot.mpr (by rintro _ ⟨i, rfl⟩; rfl)
    rw [hbot, bot_sup_eq]

  have hsplit := genIndex_split (π' : (Fin n → K) →+ (Fin k → K)) Λ.toAddSubgroup O.toAddSubgroup hpos
  rw [hker, ← Submodule.map_toAddSubgroup, ← Submodule.map_toAddSubgroup, hOmap] at hsplit
  have hinf1 : Λ.toAddSubgroup ⊓ W.toAddSubgroup = (Λ ⊓ W).toAddSubgroup := rfl
  have hinf2 : O.toAddSubgroup ⊓ W.toAddSubgroup = (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup := by
    rw [← hOW]; rfl
  rw [hinf1, hinf2] at hsplit
  have hq := LinesQuotIndex.full K n m k B Λ c
  rw [hBl] at hq

  set x := genIndex (Λ ⊓ W).toAddSubgroup (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup with hx
  set y := genIndex (Λ.map π').toAddSubgroup
    (Submodule.span (𝓞 K) (Set.range (coordProj B ∘ c))).toAddSubgroup with hy
  have hx0 : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hxy : 0 < x * y := hsplit ▸ hpos
  have hxne : x ≠ 0 := by rintro h; rw [h, zero_mul] at hxy; exact lt_irrefl _ hxy
  have hyne : y ≠ 0 := by rintro h; rw [h, mul_zero] at hxy; exact lt_irrefl _ hxy
  unfold quotDegree subDegree
  rw [htop, Submodule.restrictScalars_top, inf_top_eq, hq, hsplit, Real.log_mul hxne hyne,
    Finset.sum_sub_distrib]
  ring
end S6.QuotientDegreeSplit
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
