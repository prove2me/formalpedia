-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.UnitVectorPowers.Lk_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:18:15.163099+00:00
-- url     : https://prove2.me/submissions/341258d5-56ff-42f3-8b2b-ddef1588bd5a

import Definitions.Def_ReciprocityTheory_DualLattices_ProdPowUnitVectorVal
import Definitions.Def_ReciprocityTheory_DualLattices_FormMonomialUnitVector

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
variable [IsLocalRing R] [CharP (IsLocalRing.ResidueField R) p]
namespace ReciprocityTheory.PGsh.Up.UnitVectorPowers
theorem _root_.solution (D : Lifts H U X) : IsUnit (Lk D).det := by
  unfold Lk
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact D.Λ_det.map _
end ReciprocityTheory.PGsh.Up.UnitVectorPowers
