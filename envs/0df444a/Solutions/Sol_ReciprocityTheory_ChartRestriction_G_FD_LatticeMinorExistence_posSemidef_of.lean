-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence.posSemidef_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:03:31.977164+00:00
-- url     : https://prove2.me/submissions/6866759d-0d2a-4d15-8630-60377396bdd4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeMinorExistence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
theorem _root_.solution {χ : X.Ψ → Fin 2 → Fin 2 → ℂ} (hχ : IsHermFam χ) (τ0 : X.Ψ)
    (h : ∀ x : Fin 2 → ℂ, x ≠ 0 → 0 ≤ (∑ i, ∑ k, χ τ0 i k * conj (x i) * x k).re) :
    (Matrix.of (χ τ0)).PosSemidef := by
  have hH : (Matrix.of (χ τ0)).IsHermitian := by
    ext i k
    simp [Matrix.conjTranspose_apply, hχ τ0 k i]
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hH, fun x => ?_⟩
  have hre : (star x ⬝ᵥ (Matrix.of (χ τ0)).mulVec x) =
      ∑ i, ∑ k, χ τ0 i k * conj (x i) * x k := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [RCLike.star_def]
    ring
  have him := hH.im_star_dotProduct_mulVec_self x
  rw [hre, Complex.nonneg_iff]
  refine ⟨?_, ?_⟩
  · by_cases hx : x = 0
    · simp [hx]
    · exact h x hx
  · rw [← hre]
    exact him.symm
end ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
