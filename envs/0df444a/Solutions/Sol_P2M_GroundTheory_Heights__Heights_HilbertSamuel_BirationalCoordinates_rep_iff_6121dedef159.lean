-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_rep_iff_6121dedef159
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:30:09.165436+00:00
-- url     : https://prove2.me/submissions/1fb10968-ddae-4c13-9a7e-4c3247ee1712

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsBirationalCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PBirationalCoordinatesA
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_aeval_homog_512c9ab4a78a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
variable {κ : Type} [Fintype κ] {Ω Ω'' : Type} [Field Ω] [Field Ω'']
  (j : Ω'' →+* Ω) {μ : Ω} (hμ : μ ≠ 0) {x : Ix κ → Ω} {y : Ix κ → Ω''} (hx : ∀ p, x p = μ * j (y p))
include hμ hx
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
theorem _root_.solution (A : HermLine (GlobalTheory κ)) (τ : ℕ) (s' : Ω'') {dg dh : Unit → ℕ} {g h : MRing (GlobalTheory κ)}
    (hg : IsMultiHomog g dg) (hh : IsMultiHomog h dh) (hd : ∀ k, (dg k : ℤ) = dh k + τ * A.a k) :
    aeval x g = μ ^ ((τ : ℤ) * A.a ()) * j s' * aeval x h ↔ aeval y g = s' * aeval y h := by
  rw [aeval_homog j hx hg, aeval_homog j hx hh, ← zpow_natCast, ← zpow_natCast, hd (), add_comm,
    zpow_add₀ hμ, mul_assoc, mul_assoc]
  have hm : μ ^ ((τ : ℤ) * A.a ()) * μ ^ ((dh () : ℕ) : ℤ) ≠ 0 := mul_ne_zero (zpow_ne_zero _ hμ) (zpow_ne_zero _ hμ)
  rw [show μ ^ ((τ : ℤ) * A.a ()) * (j s' * (μ ^ ((dh () : ℕ) : ℤ) * j (aeval y h))) =
      μ ^ ((τ : ℤ) * A.a ()) * μ ^ ((dh () : ℕ) : ℤ) * j (s' * aeval y h) by rw [map_mul]; ring,
    ← mul_assoc, mul_right_inj' hm]
  exact j.injective.eq_iff
end GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
