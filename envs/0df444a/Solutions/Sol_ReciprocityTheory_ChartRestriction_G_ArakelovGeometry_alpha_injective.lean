-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.alpha_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:11:50.95434+00:00
-- url     : https://prove2.me/submissions/f4073fa3-d50d-4aa8-b3f9-4bde4090a2b5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionModuleEqSpanPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ChooseLePowDivFactorial
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_coord_ne_zero_of_free

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Module Filter Asymptotics
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) {n δ : ℕ}
    (ε : Fin δ → Ω) (hli : LinearIndependent (fnField (x ∘ e)) ε) (P : Fin δ → Ω)
    (hP : ∀ l, P l ∈ sec ℤ (x ∘ e) n) (h0 : ∑ l, P l * ε l = 0) : P = 0 := by
  have hx0 : x (e 0) ≠ 0 := coord_ne_zero_of_free (x ∘ e) h.free 0
  rw [Fintype.linearIndependent_iff] at hli
  have hmem : ∀ l, P l / (x ∘ e) 0 ^ n ∈ fnField (x ∘ e) := fun l => div_pow_mem_fnField (x ∘ e) 0 (hP l)
  have hsum : ∑ l, (⟨P l / (x ∘ e) 0 ^ n, hmem l⟩ : fnField (x ∘ e)) • ε l = 0 := by
    have hrw : ∑ l, (⟨P l / (x ∘ e) 0 ^ n, hmem l⟩ : fnField (x ∘ e)) • ε l =
        (∑ l, P l * ε l) / (x ∘ e) 0 ^ n := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [Algebra.smul_def, IntermediateField.algebraMap_apply]
      ring
    rw [hrw, h0, zero_div]
  have hg := hli _ hsum
  funext l
  have h2 : P l / (x ∘ e) 0 ^ n = 0 := congrArg Subtype.val (hg l)
  exact (div_eq_zero_iff.1 h2).resolve_right (pow_ne_zero _ hx0)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
