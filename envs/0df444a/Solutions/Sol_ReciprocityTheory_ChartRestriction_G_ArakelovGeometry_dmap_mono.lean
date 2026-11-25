-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.dmap_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:40:56.307802+00:00
-- url     : https://prove2.me/submissions/3acbd210-2b1c-4b3d-b813-c33c13745c8e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NatCardEqPowLength
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_xpow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_mk_xpow


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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (W : Ideal (MRing ι)) (i : ∀ k, ι k) {a a' : K → ℕ} (h : ∀ k, a k ≤ a' k)
    (x : mPiece W a) : ∃ x' : mPiece W a', dmap W i a' x' = dmap W i a x := by
  classical
  have homog_of_mem : ∀ {b : K → ℕ} {f : MRing ι}, f ∈ mHom ι b → IsMultiHomog f b := by
    intro b f hf
    unfold mHom at hf
    induction hf using Submodule.span_induction with
    | mem x hx => exact hx
    | zero =>
      intro m hm
      simp at hm
    | add x y _ _ hx hy =>
      intro m hm k
      rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
      · exact hx m h k
      · exact hy m h k
    | smul n x _ hx =>
      intro m hm k
      exact hx m (MvPolynomial.support_smul hm) k
  obtain ⟨_, s, hs, rfl⟩ := x
  have hprod : s * xpow i (fun k => a' k - a k) ∈ mHom ι a' := by
    apply Submodule.subset_span
    have := isMultiHomog_mul (homog_of_mem hs) (isMultiHomog_xpow i (fun k => a' k - a k))
    have hsum : a + (fun k => a' k - a k) = a' := by
      funext k
      simp only [Pi.add_apply]
      have := h k
      omega
    rw [hsum] at this
    exact this
  refine ⟨⟨_, Submodule.mem_map_of_mem hprod⟩, ?_⟩
  show Ideal.Quotient.mk (dehomI W i) (s * xpow i (fun k => a' k - a k)) = Ideal.Quotient.mk (dehomI W i) s
  rw [map_mul, mk_xpow, mul_one]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
