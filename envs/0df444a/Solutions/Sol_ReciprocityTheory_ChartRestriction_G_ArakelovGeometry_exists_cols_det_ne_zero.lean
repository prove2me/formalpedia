-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_cols_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:37:18.715647+00:00
-- url     : https://prove2.me/submissions/da499001-5e0c-4fd7-b095-b10dc35e681a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coe_dehK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.coe_dehK



set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {r : ℕ} {ι : Type} [Finite ι] (u : ι → Fin r → ℤ)
    (hspan : ∀ v : Fin r → ℤ, v ∈ Submodule.span ℤ (Set.range u)) :
    ∃ f : Fin r → ι, (Matrix.of fun p q => u (f q) p).det ≠ 0 := by
  classical
  set uq : ι → Fin r → ℚ := fun i p => (u i p : ℚ) with huq
  have h1 : ∀ v : Fin r → ℤ, (fun p => (v p : ℚ)) ∈ Submodule.span ℚ (Set.range uq) := by
    intro v
    induction hspan v using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero =>
      have h0 : (fun p => ((0 : Fin r → ℤ) p : ℚ)) = 0 := by funext p; simp
      rw [h0]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : (fun p => ((x + y) p : ℚ)) = (fun p => (x p : ℚ)) + fun p => (y p : ℚ) := by
        funext p; simp
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have : (fun p => ((a • x) p : ℚ)) = (a : ℚ) • fun p => (x p : ℚ) := by
        funext p; simp
      rw [this]; exact Submodule.smul_mem _ _ hx
  have htop : Submodule.span ℚ (Set.range uq) = ⊤ := by
    refine eq_top_iff.mpr fun v _ => ?_
    have hv : v = ∑ p, v p • (fun q => ((Pi.single p (1 : ℤ) : Fin r → ℤ) q : ℚ)) := by
      funext q
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (h1 _)
  obtain ⟨κ', a, ha, hsp, hli⟩ := exists_linearIndependent' ℚ uq
  have : Finite κ' := Finite.of_injective a ha
  have : Fintype κ' := Fintype.ofFinite κ'
  have hsp' : ⊤ ≤ Submodule.span ℚ (Set.range (uq ∘ a)) := by rw [hsp, htop]
  have hcard : Fintype.card κ' = r := by
    have := Module.finrank_eq_card_basis (Basis.mk hli hsp')
    simpa using this.symm
  set eq := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ eq, ?_⟩
  have hli2 : LinearIndependent ℚ ((Matrix.of fun p q => u ((a ∘ eq) q) p).map
      (Int.cast : ℤ → ℚ)).col := by
    have : ((Matrix.of fun p q => u ((a ∘ eq) q) p).map (Int.cast : ℤ → ℚ)).col = uq ∘ a ∘ eq := by
      funext q p; simp [Matrix.col, huq]
    rw [this]
    exact hli.comp eq eq.injective
  rw [Matrix.linearIndependent_cols_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    ← Int.cast_det] at hli2
  exact_mod_cast hli2
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
