-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_aeval_homog_512c9ab4a78a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:55:15.094797+00:00
-- url     : https://prove2.me/submissions/c09106eb-e4ca-458a-97a9-95b89867b543

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsBirationalCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PBirationalCoordinatesA
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
variable {κ : Type} [Fintype κ] {Ω Ω'' : Type} [Field Ω] [Field Ω'']
  (j : Ω'' →+* Ω) {μ : Ω} (hμ : μ ≠ 0) {x : Ix κ → Ω} {y : Ix κ → Ω''} (hx : ∀ p, x p = μ * j (y p))
include hμ hx
omit hμ
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
theorem _root_.solution {g : MRing (GlobalTheory κ)} {d : Unit → ℕ} (hg : IsMultiHomog g d) :
    aeval x g = μ ^ d () * j (aeval y g) := by
  have hsum : ∀ m ∈ g.support, ∑ p ∈ m.support, m p = d () := by
    intro m hm
    rw [Finset.sum_subset (Finset.subset_univ m.support) (fun p _ hp => by simpa using hp),
      Fintype.sum_sigma]
    simpa using hg m hm ()
  have hjx : j (aeval y g) = aeval (fun p => j (y p)) g := by
    rw [← RingHom.toIntAlgHom_apply, comp_aeval_apply]
    rfl
  rw [hjx, show x = fun p => μ * j (y p) from funext hx]
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum m hm]
  ring
end GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
