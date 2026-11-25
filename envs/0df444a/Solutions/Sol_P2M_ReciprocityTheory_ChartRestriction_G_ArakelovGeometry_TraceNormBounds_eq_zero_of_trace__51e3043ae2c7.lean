-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_eq_zero_of_trace__51e3043ae2c7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:26:34.393802+00:00
-- url     : https://prove2.me/submissions/38e3f5ee-faa8-4f2f-b040-a9812e3cb3f9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_BasisOfLinearIndependentOfCardEqFinrank
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_XZeroPowDvdOfIsHomogeneousAeval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_eq_zero_of_trace
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_mul_mem_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_sec_div_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
private theorem coord_ne_zero_of_coordIdeal_eq_bot (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) (i : Fin (D + 1)) :
    y i ≠ 0 := by
  intro h0
  have hmem : (MvPolynomial.X i : MvPolynomial (Fin (D + 1)) ℤ) ∈ coordIdeal ℤ y := by
    rw [coordIdeal, RingHom.mem_ker]
    simp [coneMap, h0]
  rw [hfree, Ideal.mem_bot] at hmem
  exact MvPolynomial.X_ne_zero i hmem
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
theorem _root_.solution [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e)
    {k : ℕ} (ε : Fin (projDeg x e) → Ω) (hε : ∀ l, ε l ∈ sec ℤ x k)
    (hli : LinearIndependent (fnField (x ∘ e)) ε) (n : ℕ) {s : Ω} (hs : s ∈ sec ℤ x n)
    (h0 : ∀ l, ((Algebra.trace (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le' x e))
        ⟨s * ε l / x (e 0) ^ (n + k), sec_div_mem x (e 0) (mul_mem_sec x hs (hε l))⟩ :
          fnField (x ∘ e)) : Ω) = 0) : s = 0 := by
  have hx0 : x (e 0) ≠ 0 := coord_ne_zero_of_coordIdeal_eq_bot (x ∘ e) h.free 0
  have ht := eq_zero_of_trace x e h ε hε hli ⟨s / x (e 0) ^ n, sec_div_mem x (e 0) hs⟩ (fun l => by
    have e1 : (⟨s / x (e 0) ^ n, sec_div_mem x (e 0) hs⟩ : IntermediateField.extendScalars (fnField_comp_le' x e)) *
        ⟨ε l / x (e 0) ^ k, sec_div_mem x (e 0) (hε l)⟩ =
        ⟨s * ε l / x (e 0) ^ (n + k), sec_div_mem x (e 0) (mul_mem_sec x hs (hε l))⟩ := by
      apply Subtype.ext
      show s / x (e 0) ^ n * (ε l / x (e 0) ^ k) = s * ε l / x (e 0) ^ (n + k)
      rw [pow_add, div_mul_div_comm]
    rw [e1]
    exact Subtype.ext (h0 l))
  have h2 := congrArg Subtype.val ht
  simpa [hx0] using h2
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
