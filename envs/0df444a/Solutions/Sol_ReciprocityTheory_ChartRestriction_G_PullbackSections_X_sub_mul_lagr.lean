-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.X_sub_mul_lagr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:27:42.011738+00:00
-- url     : https://prove2.me/submissions/d1c46f7d-8cde-441b-8d0e-e5d6a15ddc67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_LieBridgeB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open Polynomial
variable {K S M O ι : Type} [Field K] [CharZero K] [CommRing S] [Algebra K S] [AddCommGroup M] [Module S M]
  [CommRing O] [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (x : ι → K) (hx : Function.Injective x) (τ : ι) :
    (X - C (x τ)) * lagr x τ = C (∏ τ' ∈ Finset.univ.erase τ, (x τ - x τ')⁻¹) * ∏ τ', (X - C (x τ')) := by
  unfold lagr
  rw [Lagrange.basis]
  simp only [Lagrange.basisDivisor, Finset.prod_mul_distrib]
  rw [← map_prod, ← Finset.mul_prod_erase Finset.univ (fun τ' => X - C (x τ')) (Finset.mem_univ τ)]
  ring
end ReciprocityTheory.ChartRestriction.G.PullbackSections
