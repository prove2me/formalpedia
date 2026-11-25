-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.good_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:54:41.409571+00:00
-- url     : https://prove2.me/submissions/38431ab4-c577-43dc-92e1-ee7c90f791ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ConjMemEichSet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_tor_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_tor_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_good_of_closure
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_good_tor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_good_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_closure_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include hσ hJ he hff hef
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {g : Matrix ι ι K} (hg : g ∈ Good σ J e f) :
    ∃ g' ∈ Good σ J e f, g' * g = 1 ∧ g * g' = 1 := by
  obtain ⟨n, hn, l, m, hml, rfl⟩ := hg
  obtain ⟨ni, hni, h1, h2⟩ := closure_inv hσ hJ he hff hn
  have hlm : l * σ m = 1 := by rw [← hσ l, ← map_mul, mul_comm, hml, map_one]
  have hml' : σ l * σ (σ m) = 1 := by rw [hσ, mul_comm, hml]
  refine ⟨tor σ J e f (σ m) (σ l) * ni, good_mul hσ hJ he hff hef (good_tor hσ hJ he hff hef hml')
    (good_of_closure hσ hJ he hff hef hni), ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc ni, h1, Matrix.one_mul, tor_mul hσ hJ he hff hef,
      mul_comm (σ m), hlm, mul_comm (σ l) m, hml, tor_one hσ hJ he hff hef]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (tor σ J e f l m), tor_mul hσ hJ he hff hef, hlm,
      hml, tor_one hσ hJ he hff hef, Matrix.one_mul, h2]
end ReciprocityTheory.ChartRestriction.G.SA
