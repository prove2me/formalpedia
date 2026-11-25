-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.sec_div_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:26:08.813908+00:00
-- url     : https://prove2.me/submissions/acef2638-4dcc-4641-be24-d6ddd7d4a157

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjectiveFrameCoordNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_BasisOfLinearIndependentOfCardEqFinrank
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_coord_div_isIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_sec_div_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
theorem _root_.solution (x : κ → Ω) (e : Fin (D + 1) → κ) [Fintype κ] (h : IsProjFrame x e)
    (l : Fin (D + 1)) (n : ℕ) {s : Ω} (hs : s ∈ sec ℤ x n) :
    IsIntegral (chartRing x e l) (⟨s / x (e l) ^ n, sec_div_mem x (e l) hs⟩ :
      IntermediateField.extendScalars (fnField_comp_le' x e)) := by
  classical
  obtain ⟨p, hp, hps⟩ := Submodule.mem_map.1 hs
  have hph : p.IsHomogeneous n := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hp

  have hhom : MvPolynomial.aeval (fun i => x i / x (e l)) p = s / x (e l) ^ n := by
    rw [← hps]
    show MvPolynomial.aeval (fun i => x i / x (e l)) p = MvPolynomial.aeval x p / x (e l) ^ n
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
      MvPolynomial.eval₂_eq', Finset.sum_div]
    refine Finset.sum_congr rfl fun d hd => ?_
    have h1 := hph (MvPolynomial.mem_support_iff.1 hd)
    have hdeg : ∑ i, d i = n := by
      rw [← h1]
      first
        | simp [Finsupp.weight_apply, Finsupp.sum_fintype]
        | simp [Finsupp.degree_eq_sum]
        | exact (Finsupp.sum_fintype _ _ (by simp)).symm
        | simp [Finsupp.degree, Finsupp.sum_fintype]
    rw [mul_div_assoc]
    congr 1
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  have hΩ : IsIntegral (chartRing x e l) (s / x (e l) ^ n) := by
    let S := (integralClosure (chartRing x e l) Ω).restrictScalars ℤ
    have hy : ∀ i, x i / x (e l) ∈ S := fun i => coord_div_isIntegral x e h l i
    let y' : κ → S := fun i => ⟨x i / x (e l), hy i⟩
    have hS : MvPolynomial.aeval (fun i => x i / x (e l)) p = S.val (MvPolynomial.aeval y' p) := by
      first
        | (rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]; rfl)
        | (rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval])
        | exact (DFunLike.congr_fun (MvPolynomial.comp_aeval (R := ℤ) S.val) p).symm
    rw [← hhom, hS]
    exact (MvPolynomial.aeval y' p).2
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (chartRing x e l)
    (IntermediateField.extendScalars (fnField_comp_le' x e)) Ω)
    (fun a b hab => Subtype.ext hab)).1 hΩ
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
