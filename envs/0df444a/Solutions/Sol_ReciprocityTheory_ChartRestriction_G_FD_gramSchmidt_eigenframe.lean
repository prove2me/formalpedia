-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.gramSchmidt_eigenframe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:57:22.640131+00:00
-- url     : https://prove2.me/submissions/2c48504c-facb-4884-8aa8-2550f949e9ab

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramSchmidtEigenframe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EigenframeMatrices_Mmat_comb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EigenframeMatrices_Mmat_f
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EigenframeMatrices_Mmat_fix
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EigenframeMatrices_Mmat_span
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EigenframeMatrices_Mmat_unitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramSchmidtSelfImaginary_gs_exists
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramSchmidtSelfImaginary_perp_span
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramSchmidtSelfImaginary_sum_mem_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
private theorem hermC_sub_left_eq_sub {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (u u' v : Fin r → ℂ) : hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v :=
  map_sub (AddMonoidHom.mk' (fun x => hermC τ G x v) (fun a b => hermC_add_left τ G a b v)) u u'
private theorem hermC_finset_sum_left' {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    {ι : Type} (s : Finset ι) (u : ι → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ i ∈ s, u i) v = ∑ i ∈ s, hermC τ G (u i) v :=
  map_sum (AddMonoidHom.mk' (fun x => hermC τ G x v) (fun a b => hermC_add_left τ G a b v)) u s
private theorem hermC_finset_sum_right_of_conj_symm {r : ℕ} (τ : E →+* ℂ) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (G a b) = G b a) {ι : Type} (s : Finset ι) (u : Fin r → ℂ)
    (v : ι → Fin r → ℂ) : hermC τ G u (∑ i ∈ s, v i) = ∑ i ∈ s, hermC τ G u (v i) := by
  rw [← hermC_conj τ hG _ u, hermC_finset_sum_left', map_sum]
  exact Finset.sum_congr rfl (fun i _ => hermC_conj τ hG _ _)
private theorem hermC_sub_right_of_conj_symm {r : ℕ} (τ : E →+* ℂ) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (G a b) = G b a) (u v v' : Fin r → ℂ) :
    hermC τ G u (v - v') = hermC τ G u v - hermC τ G u v' := by
  rw [← hermC_conj τ hG _ u, hermC_sub_left_eq_sub, map_sub, hermC_conj τ hG, hermC_conj τ hG]
private theorem ppos_self_adjoint_hermC {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ)
    (w v : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ w) v = hermC τ.1 X.Gm w (X.ppos x τ v) := by
  have hH : (X.gramPos x τ).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Data.gramPos, Matrix.submatrix_apply, gram,
      Matrix.of_apply]
    rw [← starRingEnd_apply]
    exact hermC_conj _ X.Gm_herm _ _
  have hM := hH.inv
  simp only [Data.ppos]
  rw [hermC_finset_sum_left', hermC_finset_sum_right_of_conj_symm _ X.Gm_herm]
  simp only [hermC_smul_left, hermC_smul_right, Finset.sum_mul, map_sum, map_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [hermC_conj _ X.Gm_herm, starRingEnd_apply, hM.apply]
  ring
private theorem hermC_ppos_eq_zero_of_hermC_eq_zero_of_Jt {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ)
    (w v : Fin r → ℂ) (h0 : hermC τ.1 X.Gm w v = 0) (hJ : hermC τ.1 X.Gm w (X.Jt x τ v) = 0) :
    hermC τ.1 X.Gm w (X.ppos x τ v) = 0 := by
  simp only [Data.Jt] at hJ
  rw [hermC_smul_right, hermC_sub_right_of_conj_symm _ X.Gm_herm, hermC_smul_right, h0] at hJ
  simpa using hJ
end
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution (r : ℕ) (X : DataX E r) (ξ : Fin r → E) (z0 : Frame X.Ψ r)
    (f Y : X.Ψ → Fin (r - 2) → Fin r → ℂ) (hξ : X.IsIso ξ) (hz : z0 ∈ X.dom) (hf : X.UBasis z0 ξ f)
    (hYind : ∀ τ, LinearIndependent ℂ (Y τ))
    (hYU : ∀ τ j, Y τ j ∈ Submodule.span ℂ (Set.range (f τ)))
    (hYorth : ∀ τ (j k : Fin (r - 2)), (j : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) →
      hermC τ.1 X.Gm (Y τ j) (Y τ k) = 0)
    (hYpos : ∀ τ (w : Fin (r - 2) → ℂ), (∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) → w j = 0) → w ≠ 0 →
      0 < (hermC τ.1 X.Gm (∑ j, w j • Y τ j) (∑ j, w j • Y τ j)).re)
    (hYneg : ∀ τ (w : Fin (r - 2) → ℂ), (∀ j : Fin (r - 2), (j : ℕ) < X.p0 - 1 → w j = 0) → w ≠ 0 →
      (hermC τ.1 X.Gm (∑ j, w j • Y τ j) (∑ j, w j • Y τ j)).re < 0) :
    ∃ h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ, X.IsUnitaryC h1 ∧
      (∀ s t : X.Ψ → ℂ, X.applyV h1 (X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) =
        X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) ∧
      (∀ u ∈ X.Uz z0 ξ, X.applyV h1 u ∈ X.Uz z0 ξ) ∧
      (∀ τ (v : Fin r → ℂ), v ∈ Submodule.span ℂ (f τ '' {k | (k : ℕ) < X.p0 - 1}) →
        (h1 τ) *ᵥ v ∈ Submodule.span ℂ (Y τ '' {j | (j : ℕ) < X.p0 - 1})) ∧
      (∀ τ (j : Fin (r - 2)), ∃ u : Fin r → ℂ,
        u ∈ Submodule.span ℂ (f τ '' {k | ((k : ℕ) < X.p0 - 1 ↔ (j : ℕ) < X.p0 - 1)}) ∧ (h1 τ) *ᵥ u = Y τ j) := by
  have hgs := fun τ : X.Ψ => GramSchmidtSelfImaginary.gs_exists (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (Y := Y τ)
    (hind := hYind τ) (horth := hYorth τ) (hpos := hYpos τ) (hneg := hYneg τ) X.Gm_herm
  choose g hg1 hg2 hg3 hg4 using hgs
  have hgf : ∀ τ k, g τ k ∈ Submodule.span ℂ (Set.range (f τ)) := by
    intro τ k
    have hsub : Submodule.span ℂ (Set.range (Y τ)) ≤ Submodule.span ℂ (Set.range (f τ)) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hYU τ j
    exact hsub (hg3 τ k)
  have e0 : ∀ τ : X.Ψ, ∀ k, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (f τ k) = 0 := fun τ k => by
    rw [← hermC_conj τ.1 X.Gm_herm, ((hf τ).1 k).1, map_zero]
  have eP : ∀ τ : X.Ψ, ∀ k, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (X.ppos z0 τ (f τ k)) = 0 := fun τ k => by
    refine hermC_ppos_eq_zero_of_hermC_eq_zero_of_Jt X.toData z0 τ _ _ (e0 τ k) ?_
    rw [(hf τ).2.1 k, hermC_smul_right, e0 τ k, mul_zero]
  have hspan : ∀ τ : X.Ψ, ∀ y ∈ Submodule.span ℂ (Set.range (f τ)),
      hermC τ.1 X.Gm y (Data.emb τ.1 ξ) = 0 ∧ hermC τ.1 X.Gm y (X.ppos z0 τ (Data.emb τ.1 ξ)) = 0 := by
    intro τ y hy
    refine ⟨GramSchmidtSelfImaginary.perp_span (τ := τ.1) (G := X.Gm) ?_ y hy,
      GramSchmidtSelfImaginary.perp_span (τ := τ.1) (G := X.Gm) ?_ y hy⟩
    · rintro _ ⟨k, rfl⟩
      exact ((hf τ).1 k).1
    · rintro _ ⟨k, rfl⟩
      rw [← ppos_self_adjoint_hermC, ← hermC_conj τ.1 X.Gm_herm, eP τ k, map_zero]
  have hJspan : ∀ τ : X.Ψ, ∀ y ∈ Submodule.span ℂ (Set.range (f τ)),
      hermC τ.1 X.Gm (I • ((2 : ℂ) • X.ppos z0 τ y - y)) (Data.emb τ.1 ξ) = 0 := by
    intro τ y hy
    rw [hermC_smul_left, hermC_sub_left_eq_sub, hermC_smul_left, ppos_self_adjoint_hermC, (hspan τ y hy).1,
      (hspan τ y hy).2]
    simp
  refine ⟨fun τ => EigenframeMatrices.Mmat (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ) (g := g τ),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro τ u w
    exact EigenframeMatrices.Mmat_unitary (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ) (g := g τ) (hG := X.Gm_herm)
      (hf := (hf τ).2.2.1)
      (hgf τ) (hg1 τ) u w
  · intro s t
    funext τ
    simp only [Data.applyV]
    refine EigenframeMatrices.Mmat_fix (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ) (g := g τ) (hG := X.Gm_herm)
      (hf := (hf τ).2.2.1) _
      (fun k => ?_)
    simp only [Pi.add_apply, Data.lineV, Data.Jz]
    simp only [hermC_add_left, hermC_smul_left, hermC_sub_left_eq_sub, ppos_self_adjoint_hermC, e0, eP,
      mul_zero, sub_zero, add_zero, zero_add]
  · intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    have hmem : ∀ τ : X.Ψ, EigenframeMatrices.Mmat (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ)
        (g := g τ) *ᵥ u τ ∈ Submodule.span ℂ (Set.range (f τ)) := fun τ =>
      EigenframeMatrices.Mmat_span (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ) (g := g τ) (hG := X.Gm_herm)
      (hf := (hf τ).2.2.1) (hgf τ)
        (u τ) ((hf τ).2.2.2.2 (u τ) (hu1 τ) (hu2 τ))
    exact And.intro (fun τ => (hspan τ _ (hmem τ)).1) (fun τ => hJspan τ _ (hmem τ))
  · intro τ v hv
    have hle : Submodule.span ℂ (f τ '' {k | (k : ℕ) < X.p0 - 1}) ≤
        (Submodule.span ℂ (Y τ '' {j | (j : ℕ) < X.p0 - 1})).comap
          (Matrix.mulVecLin (EigenframeMatrices.Mmat (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ)
            (g := g τ))) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, hk, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply,
        EigenframeMatrices.Mmat_f (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ) (g := g τ) (hG := X.Gm_herm)
      (hf := (hf τ).2.2.1)]
      exact hg2 τ k hk
    have hv' := hle hv
    rwa [Submodule.mem_comap, Matrix.mulVecLin_apply] at hv'
  · intro τ j
    obtain ⟨β, hβ, hYj⟩ := hg4 τ j
    refine ⟨∑ c, β c • f τ c, GramSchmidtSelfImaginary.sum_mem_of (f τ) _ β hβ, ?_⟩
    show EigenframeMatrices.Mmat (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ) (g := g τ) *ᵥ
      (∑ c, β c • f τ c) = Y τ j
    rw [EigenframeMatrices.Mmat_comb (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ) (g := g τ) (hG := X.Gm_herm)
      (hf := (hf τ).2.2.1), hYj]
end ReciprocityTheory.ChartRestriction.G.FD
