-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.linInd_bG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T06:09:57.663548+00:00
-- url     : https://prove2.me/submissions/9c6f420f-b8a5-4846-a467-599bdb19a57b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsIntMultiple
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_polyOf_coeff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_sum_smul_bG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_support_polyOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_eq_zero_of_coord

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
theorem _root_.solution {κ : Type} [DecidableEq κ] (G : MvPolynomial κ K) (hG : G ≠ 0)
    (S T : Finset (κ →₀ ℕ)) {r : ℕ} (e : T ≃ Fin r)
    (hST : ∀ m ∈ S, (G * MvPolynomial.monomial m 1).support ⊆ T) :
    LinearIndependent K (bG G S e) := by
  rw [Fintype.linearIndependent_iff]
  intro p hp j
  have h1 : G * polyOf S p = 0 :=
    eq_zero_of_coord e _ (support_polyOf G S T hST p) (by rw [← sum_smul_bG]; exact hp)
  have h2 : polyOf S p = 0 := (mul_eq_zero.mp h1).resolve_left hG
  rw [← polyOf_coeff S p j, h2, MvPolynomial.coeff_zero]
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
