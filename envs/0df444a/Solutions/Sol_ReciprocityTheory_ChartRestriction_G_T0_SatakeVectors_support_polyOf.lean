-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.support_polyOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:48:06.794898+00:00
-- url     : https://prove2.me/submissions/8b758ba9-2310-491e-ac50-7aab2775cf75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsIntMultiple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
theorem _root_.solution {κ : Type} [DecidableEq κ] (G : MvPolynomial κ K) (S T : Finset (κ →₀ ℕ))
    (hST : ∀ m ∈ S, (G * MvPolynomial.monomial m 1).support ⊆ T) (p : Fin S.card → K) :
    (G * polyOf S p).support ⊆ T := by
  intro s hs
  rw [polyOf, Finset.mul_sum] at hs
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hs)
  have hm : mS S j ∈ S := (S.equivFin.symm j).2
  apply hST _ hm
  rw [MvPolynomial.mem_support_iff] at hj ⊢
  rw [show MvPolynomial.monomial (mS S j) (p j) =
      MvPolynomial.C (p j) * MvPolynomial.monomial (mS S j) 1 by
    rw [MvPolynomial.C_mul_monomial, mul_one], mul_left_comm G, MvPolynomial.coeff_C_mul] at hj
  exact right_ne_zero_of_mul hj
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
