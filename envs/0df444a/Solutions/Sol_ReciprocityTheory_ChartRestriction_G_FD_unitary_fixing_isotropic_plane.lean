-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.unitary_fixing_isotropic_plane
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:33:14.216593+00:00
-- url     : https://prove2.me/submissions/942d3752-49e8-4a73-840a-1b09626e9fa3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowerBlockMatrices
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryFixingIsotropicPlane
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BlockIdentityExpansion_key
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LowerBlockMatrices_Neg_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LowerBlockMatrices_Pos_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LowerBlockMatrices_colW_expand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LowerBlockMatrices_colZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LowerBlockMatrices_yvec_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_Neg_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_eq_zero_of_Pos_Neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_span_eq_of_mat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_zero_of_mem_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_zero_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution (r : ℕ) (X : DataX E r) (ξ : Fin r → E) (z0 x0 : Frame X.Ψ r)
    (f : X.Ψ → Fin (r - 2) → Fin r → ℂ) (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (δ : ℝ)
    (hξ : X.IsIso ξ) (hz : z0 ∈ X.dom) (hx0 : x0 ∈ X.dom) (hortho : X.IsOrtho x0)
    (hflag : X.SameFlag z0 x0) (hf : X.UBasis z0 ξ f) (hδ : 0 ≤ δ) (hU : X.IsUnitaryC h1)
    (hI : ∀ s t : X.Ψ → ℂ, X.applyV h1 (X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) =
      X.lineV ξ s + X.Jz z0 (X.lineV ξ t))
    (hUz : ∀ u ∈ X.Uz z0 ξ, X.applyV h1 u ∈ X.Uz z0 ξ)
    (hgraph : ∀ τ (v : Fin r → ℂ), v ∈ Submodule.span ℂ (f τ '' {k | (k : ℕ) < X.p0 - 1}) →
      ∀ c : Fin (r - 2) → ℂ, (h1 τ) *ᵥ v = ∑ k, c k • f τ k →
        (∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then 0 else ‖c k‖ ^ 2) ≤
          δ ^ 2 * ∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then ‖c k‖ ^ 2 else 0) :
    ∃ Z1 : X.Coord, X.SameFlag (X.lmulC h1 z0) (X.xZ x0 Z1) ∧ X.zN Z1 ≤ δ := by
  classical
  have hdetOf : ∀ x ∈ X.dom, ∀ τ, (mat x τ).det ≠ 0 := by
    intro x hx τ
    simp only [Data.dom, GG, Set.mem_setOf_eq] at hx
    exact (hx τ).1
  have hcolLI : ∀ x ∈ X.dom, ∀ τ,
      LinearIndependent ℂ (fun b : Fin X.p0 => col (mat x τ) (Fin.castLE X.p0_le b)) := by
    intro x hx τ
    have hu : IsUnit (mat x τ) := (Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit (hdetOf x hx τ))
    exact (Matrix.linearIndependent_cols_iff_isUnit.mpr hu).comp (Fin.castLE X.p0_le)
      (Fin.castLE_injective _)
  have hineq : ∀ τ (u : Fin X.p0 → ℂ),
      ∑ a, ‖(LowerBlockMatrices.Bmat X.toData h1 z0 x0 τ *ᵥ u) a‖ ^ 2 ≤
        δ ^ 2 * ∑ b', ‖(LowerBlockMatrices.Amat X.toData h1 z0 x0 τ *ᵥ u) b'‖ ^ 2 := by
    intro τ u
    have hv : (∑ b, u b • col (mat z0 τ) (Fin.castLE X.p0_le b)) ∈ PositiveSpanMatrices.Spos X.toData z0 τ :=
      Submodule.sum_mem _ (fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))
    have k := BlockIdentityExpansion.key X ξ z0 x0 f h1 δ hz hx0 hortho hflag hf hI hUz hgraph τ _ hv
    rw [← LowerBlockMatrices.yvec_eq (X := X.toData), LowerBlockMatrices.Neg_eq (X := X.toData),
      LowerBlockMatrices.Pos_eq (X := X.toData)] at k
    exact k
  have hAdet : ∀ τ, (LowerBlockMatrices.Amat X.toData h1 z0 x0 τ).det ≠ 0 := by
    intro τ
    rw [Ne, ← Matrix.exists_mulVec_eq_zero_iff]
    rintro ⟨u, hu0, hAu⟩
    set v : Fin r → ℂ := ∑ b, u b • col (mat z0 τ) (Fin.castLE X.p0_le b) with hvdef
    set y : Fin r → ℂ := ∑ b, u b • col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b) with hydef
    have hP : PositiveSpanMatrices.Pos X.toData x0 τ y = 0 := by
      rw [hydef, LowerBlockMatrices.Pos_eq (X := X.toData), hAu]
      simp
    have hNle : PositiveSpanMatrices.Neg X.toData x0 τ y ≤ 0 := by
      have k := hineq τ u
      rw [hAu] at k
      rw [hydef, LowerBlockMatrices.Neg_eq (X := X.toData)]
      simpa using k
    have hN : PositiveSpanMatrices.Neg X.toData x0 τ y = 0 :=
      le_antisymm hNle (PositiveSpanMatrices.Neg_nonneg (X := X.toData) x0 τ y)
    have hy0 : y = 0 :=
      PositiveSpanMatrices.eq_zero_of_Pos_Neg (X := X.toData) hortho τ (hdetOf x0 hx0 τ) y hP hN
    have hyv : y = h1 τ *ᵥ v := by
      rw [hydef, hvdef, LowerBlockMatrices.yvec_eq (X := X.toData)]
    have hvv : hermC τ.1 X.Gm v v = 0 := by
      rw [← hU τ v v, ← hyv, hy0, hermC_zero_left]
    have hvx0 : v ∈ PositiveSpanMatrices.Spos X.toData x0 τ := by
      have hv : v ∈ PositiveSpanMatrices.Spos X.toData z0 τ :=
        Submodule.sum_mem _ (fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))
      unfold PositiveSpanMatrices.Spos at hv ⊢
      rw [← hflag τ]
      exact hv
    have hv0 : v = 0 :=
      PositiveSpanMatrices.zero_of_mem_self (X := X.toData) hortho τ (hdetOf x0 hx0 τ) v hvx0 hvv
    apply hu0
    funext b
    exact Fintype.linearIndependent_iff.mp (hcolLI z0 hz τ) u hv0 b
  let Z1 : X.Coord := fun τ =>
    (LowerBlockMatrices.Bmat X.toData h1 z0 x0 τ * (LowerBlockMatrices.Amat X.toData h1 z0 x0 τ)⁻¹ :
      Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ)
  refine ⟨Z1, ?_, ?_⟩
  · intro τ
    have hA := hAdet τ
    refine PositiveSpanMatrices.span_eq_of_mat _ _ (LowerBlockMatrices.Amat X.toData h1 z0 x0 τ) hA (fun b => ?_)
    have hZA : ∀ a, ∑ b', Z1 τ a b' * LowerBlockMatrices.Amat X.toData h1 z0 x0 τ b' b =
        LowerBlockMatrices.Bmat X.toData h1 z0 x0 τ a b := by
      intro a
      have h := congrFun (congrFun (Matrix.nonsing_inv_mul_cancel_right
        (LowerBlockMatrices.Amat X.toData h1 z0 x0 τ) (LowerBlockMatrices.Bmat X.toData h1 z0 x0 τ)
        ((Matrix.isUnit_iff_isUnit_det _).mp ((Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hA)))) a) b
      rw [Matrix.mul_apply] at h
      exact h
    show col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b) = _
    rw [LowerBlockMatrices.colW_expand (X := X.toData) h1 z0 hortho τ (hdetOf x0 hx0 τ) b]
    simp only [LowerBlockMatrices.colZ (X := X.toData), smul_add, Finset.sum_add_distrib, Finset.smul_sum,
      smul_smul]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_smul, ← hZA a]
    congr 1
    refine Finset.sum_congr rfl (fun b' _ => ?_)
    ring
  · refine Real.iSup_le (fun τ => ?_) hδ
    unfold Data.opN
    refine Real.sSup_le (fun t ht => ?_) hδ
    obtain ⟨v, hv, rfl⟩ := ht
    set A := LowerBlockMatrices.Amat X.toData h1 z0 x0 τ with hAdef
    set B := LowerBlockMatrices.Bmat X.toData h1 z0 x0 τ with hBdef
    have hA := hAdet τ
    set u := A⁻¹ *ᵥ v with hudef
    have hAu : A *ᵥ u = v := by
      rw [hudef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hA), Matrix.one_mulVec]
    have hZv : Matrix.of (Z1 τ) *ᵥ v = B *ᵥ u := by
      rw [hudef, Matrix.mulVec_mulVec]
      rfl
    rw [hZv]
    have k := hineq τ u
    rw [hAu] at k
    have hpos : 0 < ∑ j, ‖v j‖ ^ 2 := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
      exact Finset.sum_pos' (fun _ _ => by positivity) ⟨j, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hj) 2⟩
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hpos)]
    calc Real.sqrt (∑ i, ‖(B *ᵥ u) i‖ ^ 2) ≤ Real.sqrt (δ ^ 2 * ∑ j, ‖v j‖ ^ 2) := Real.sqrt_le_sqrt k
      _ = δ * Real.sqrt (∑ j, ‖v j‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ]
end ReciprocityTheory.ChartRestriction.G.FD
