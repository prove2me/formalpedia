-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.adjoin_reesChart_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:00:54.330821+00:00
-- url     : https://prove2.me/submissions/854d61f7-862f-4127-a43e-cbee437acfef

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {R : Type} [CommRing R] (c : ℂ →+* R) {σ : Type} (z : σ → R)
    (hz : ∀ r : R, ∃ f : MvPolynomial σ ℂ, r = eval₂ c z f) {m : ℕ} (g : Fin m → R) (i : Fin m)
    {n : ℕ} (y : Fin n → FinalTheorems.reesChart g i)
    (hyz : ∀ q, ∃ l, y l = algebraMap R _ (z q)) (hyt : ∀ k, ∃ l, y l = fracR g i k) :
    @Algebra.adjoin ℂ (FinalTheorems.reesChart g i) _ _ ((algebraMap R (FinalTheorems.reesChart g i)).comp c).toAlgebra
      (Set.range y) = ⊤ := by
  let _ : Algebra ℂ (FinalTheorems.reesChart g i) := ((algebraMap R (FinalTheorems.reesChart g i)).comp c).toAlgebra
  have hR : ∀ r : R, algebraMap R (FinalTheorems.reesChart g i) r ∈ Algebra.adjoin ℂ (Set.range y) := by
    intro r
    obtain ⟨f, rfl⟩ := hz r
    induction f using MvPolynomial.induction_on with
    | C a =>
      rw [eval₂_C]
      exact Subalgebra.algebraMap_mem _ a
    | add f h hf hh => rw [eval₂_add, map_add]; exact add_mem hf hh
    | mul_X f q hf =>
      rw [eval₂_mul, eval₂_X, map_mul]
      obtain ⟨l, hl⟩ := hyz q
      refine mul_mem hf ?_
      rw [← hl]
      exact Algebra.subset_adjoin ⟨l, rfl⟩
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    obtain ⟨l, hl⟩ := hyt k
    have h2 : y l ∈ Algebra.adjoin ℂ (Set.range y) := Algebra.subset_adjoin ⟨l, rfl⟩
    rw [hl] at h2
    exact h2
  | algebraMap r => exact hR r
  | add x y hx hy ihx ihy => exact add_mem ihx ihy
  | mul x y hx hy ihx ihy => exact mul_mem ihx ihy
end ReciprocityTheory.AnForm.R
