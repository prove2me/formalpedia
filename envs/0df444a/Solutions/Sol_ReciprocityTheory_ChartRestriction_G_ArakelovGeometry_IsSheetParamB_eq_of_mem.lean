-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IsSheetParamB.eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:14:42.789583+00:00
-- url     : https://prove2.me/submissions/5b600804-fd1f-4020-b034-ad89c0f2a28b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStBA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adb_segre_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Topology
open scoped ComplexOrder
variable {κ : Type} [Fintype κ] {D : ℕ}
variable {P : Ideal (MRing (GlobalTheory κ))} {Ψ : (((k : Unit) → GlobalTheory κ k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)}
  {U : Set (Fin D → ℂ)} {γ : (Fin D → ℂ) → Ix κ → ℂ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
namespace IsSheetParamB
theorem _root_.solution (hs : IsSheetParamB P Ψ U γ) {z : Ix κ → ℂ}
    (hz : z ∈ coneOver U γ) {y : Fin D → ℂ} (hΨ : Ψ (segre (ι := GlobalTheory κ) z) = Fin.cons 1 y) :
    y ∈ U ∧ z = γ y := by
  obtain ⟨y0, hy0, c, hc, rfl⟩ := hz
  have h1 := hs.2 y0 hy0
  rw [adb_segre_smul, map_smul, h1] at hΨ
  have h0 := congrFun hΨ 0
  simp only [Pi.smul_apply, Fin.cons_zero, smul_eq_mul, mul_one] at h0
  subst h0
  rw [one_smul] at hΨ
  have hyy : y0 = y := by
    funext i
    have := congrFun hΨ i.succ
    simpa using this
  subst hyy
  exact ⟨hy0, by rw [one_smul]⟩
end IsSheetParamB
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
