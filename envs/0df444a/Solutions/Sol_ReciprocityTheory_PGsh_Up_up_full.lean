-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.up_full
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:16:40.135134+00:00
-- url     : https://prove2.me/submissions/2b27fb1a-9e88-4a72-a72f-353e96a8f7c0

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqMulLeProd
import Definitions.Def_ReciprocityTheory_DualLattices_CokernelsAgreeEquivariantly
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeOfFrobenius
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeOfWdetFrobenius
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Theorems.Thm_ReciprocityTheory_PGsh_Up_idemGen
import Theorems.Thm_ReciprocityTheory_PGsh_Up_killedGen
import Theorems.Thm_ReciprocityTheory_PGsh_Up_lenEx
import Theorems.Thm_ReciprocityTheory_PGsh_Up_unramifiedCokernelLowerBound_of


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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hU7 : UnramifiedCokernelLengthStatement) (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C]
    [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    [Algebra ℤ_[p] R] (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R)
    (hp2 : p ≠ 2) (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) (N : Type) [AddCommGroup N] [Module R N]
    (E : cokE H.Ht U.εT U.εL i (U.cj i) ≃ₗ[R] N) (V1 : NNReal) (hN : HasLen v R N V1) :
    (v (algebraMap R C (p : R)) : ℝ) ^ (((U.r i : ℝ) + U.r (U.cj i)) / (p - 1) - frobSum U i) ≤ V1 := by
  obtain ⟨k, c0, ⟨F0⟩, hc0⟩ := hN
  have h10 := unramifiedCokernelLowerBound_of hU7 lenEx killedGen idemGen
  unfold UnramifiedCokernelLowerBoundStatement at h10
  exact h10 p g C v R O σ cp hp2 hS H U i V1 ⟨k, c0, ⟨E.trans F0⟩, hc0⟩
end ReciprocityTheory.PGsh.Up
