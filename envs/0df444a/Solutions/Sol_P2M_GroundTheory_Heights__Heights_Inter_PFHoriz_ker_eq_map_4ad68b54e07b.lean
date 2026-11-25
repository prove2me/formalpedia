-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_ker_eq_map_4ad68b54e07b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:21.022468+00:00
-- url     : https://prove2.me/submissions/07c8346d-207a-4fe0-962c-66e748854f01

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFHoriz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFHoriz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PFHoriz
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
namespace GroundTheory.Heights₂.Heights.Inter.PFHoriz
theorem _root_.solution {σ τ Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ']
    (β : MvPolynomial τ ℤ →+* MvPolynomial σ Φ) (y : σ → Φ') (φ : MvPolynomial τ ℤ →+* Φ')
    (W : Ideal (MvPolynomial τ ℤ)) (hφ : RingHom.ker φ = W) (hcomp : ∀ F, aeval y (β F) = φ F)
    (hclear : ∀ g, ∃ c : Φ, c ≠ 0 ∧ ∃ F, C c * g = β F) :
    RingHom.ker (aeval y : MvPolynomial σ Φ →ₐ[Φ] Φ') = Ideal.map β W := by
  apply le_antisymm
  · intro g hg
    obtain ⟨c, hc, F, e⟩ := hclear g
    have hF : F ∈ W := by
      rw [← hφ, RingHom.mem_ker, ← hcomp, ← e, map_mul, RingHom.mem_ker.mp hg, mul_zero]
    have hg' : g = C c⁻¹ * β F := by
      rw [← e, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul]
    rw [hg']
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hF)
  · rw [Ideal.map_le_iff_le_comap]
    intro F hF
    rw [Ideal.mem_comap, RingHom.mem_ker, hcomp, ← RingHom.mem_ker, hφ]
    exact hF
end GroundTheory.Heights₂.Heights.Inter.PFHoriz
