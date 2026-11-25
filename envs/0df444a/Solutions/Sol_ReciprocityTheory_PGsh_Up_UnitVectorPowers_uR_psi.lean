-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.UnitVectorPowers.uR_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:00:41.742376+00:00
-- url     : https://prove2.me/submissions/632d14ec-81bd-407b-bddf-bd7501da5010

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatementHolds
import Definitions.Def_ReciprocityTheory_DualLattices_ProdPowUnitVectorVal
import Theorems.Thm_ReciprocityTheory_PGsh_Up_UnitVectorPowers_u_psi
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusValuationMatrix_uR_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.UnitVectorPowers
open ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}
namespace ReciprocityTheory.PGsh.Up.UnitVectorPowers
theorem _root_.solution (hv : v.Integers R) (D : Lifts H U X) (j : Ix g) (k : Fin D.s) (y : Nb p g) :
    uR hv D j (psi (H := H) (D.b k) y) = U.sg (D.κ j) (D.b k) * uR hv D j y := by
  apply hv.hom_inj
  rw [uR_spec, map_mul, uR_spec, u_psi]
end ReciprocityTheory.PGsh.Up.UnitVectorPowers
