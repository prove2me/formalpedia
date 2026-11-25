-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.eq_zero_of_secTrace_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:46:14.578806+00:00
-- url     : https://prove2.me/submissions/b461f842-1a98-4d0a-9e62-5075d6e44751

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_XZeroPowDvdOfIsHomogeneousAeval
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_eq_zero_of_trace__51e3043ae2c7
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_mul_mem_sec
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e)
    {k : ℕ} (ε : Fin (projDeg x e) → Ω) (hε : ∀ l, ε l ∈ sec ℤ x k)
    (hli : LinearIndependent (fnField (x ∘ e)) ε) (n : ℕ) {s : Ω} (hs : s ∈ sec ℤ x n)
    (h0 : ∀ l, secTrace x e (n + k) (s * ε l) = 0) : s = 0 := by
  have hx0 : x (e 0) ≠ 0 := by
    intro h0
    have hmem : (MvPolynomial.X 0 : MvPolynomial (Fin (D + 1)) ℤ) ∈ coordIdeal ℤ (x ∘ e) := by
      rw [coordIdeal, RingHom.mem_ker]
      simp [coneMap, h0]
    rw [h.free] at hmem
    exact MvPolynomial.X_ne_zero 0 ((Ideal.mem_bot).1 hmem)
  refine TraceNormBounds.eq_zero_of_trace' x e h ε hε hli n hs (fun l => ?_)
  have h1 := h0 l
  unfold secTrace fnTrace at h1
  split_ifs at h1 with hm
  · exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ hx0)
  · exact absurd (TraceNormBounds.sec_div_mem x (e 0) (by first | exact TraceNormBounds.mul_mem_sec x hs (hε l) | exact mul_mem_sec x hs (hε l) | exact ReciprocityTheory.ChartRestriction.G.Geo.mul_mem_sec x hs (hε l))) hm
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
