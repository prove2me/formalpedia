-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.dmap_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:59:26.94665+00:00
-- url     : https://prove2.me/submissions/91b58c28-d6b3-42ed-a2a9-dab95dd66683

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NatCardEqPowLength
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_monomial
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
theorem _root_.solution (W : Ideal (MRing ι)) (i : ∀ k, ι k) (y : MRing ι ⧸ dehomI W i) :
    ∃ (a : K → ℕ) (x : mPiece W a), dmap W i a x = y := by
  classical
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  let deg : ((Σ k, ι k) →₀ ℕ) → K → ℕ := fun m k => ∑ j, m ⟨k, j⟩
  let a : K → ℕ := fun k => f.support.sup (fun m => deg m k)
  have hle : ∀ m ∈ f.support, ∀ k, deg m k ≤ a k := fun m hm k =>
    Finset.le_sup (f := fun m => deg m k) hm
  have hterm : ∀ m ∈ f.support,
      monomial m (f.coeff m) * xpow i (fun k => a k - deg m k) ∈ mHom ι a := by
    intro m hm
    apply Submodule.subset_span
    have := isMultiHomog_mul (isMultiHomog_monomial m (f.coeff m))
      (isMultiHomog_xpow i (fun k => a k - deg m k))
    have hsum : (fun k => ∑ j, m ⟨k, j⟩) + (fun k => a k - deg m k) = a := by
      funext k
      simp only [Pi.add_apply]
      have := hle m hm k
      simp only [deg] at this ⊢
      omega
    rw [hsum] at this
    exact this
  have hF : (∑ m ∈ f.support, monomial m (f.coeff m) * xpow i (fun k => a k - deg m k)) ∈ mHom ι a :=
    Submodule.sum_mem _ hterm
  refine ⟨a, ⟨_, Submodule.mem_map_of_mem hF⟩, ?_⟩
  show Ideal.Quotient.mk (dehomI W i)
      (∑ m ∈ f.support, monomial m (f.coeff m) * xpow i (fun k => a k - deg m k)) =
    Ideal.Quotient.mk (dehomI W i) f
  simp only [map_sum, map_mul, mk_xpow, mul_one]
  conv_rhs => rw [f.as_sum]
  rw [map_sum]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
