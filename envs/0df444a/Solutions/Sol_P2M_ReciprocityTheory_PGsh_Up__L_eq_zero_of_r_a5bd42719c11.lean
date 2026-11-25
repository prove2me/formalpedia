-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_Up__L_eq_zero_of_r_a5bd42719c11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:43:30.047149+00:00
-- url     : https://prove2.me/submissions/c4aaba3d-30d4-485b-ac00-094dc3579d82

import Definitions.Def_ReciprocityTheory_DualLattices_HasLenLeOfSurj
import Definitions.Def_ReciprocityTheory_DualLattices_MulVecMemPP
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2


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
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (U : UnramData p g v R O σ cp H) {τ : Fin U.m} (h : U.r τ = 0) :
    U.εL τ = 0 := by
  obtain ⟨e⟩ := U.rank τ
  haveI : Subsingleton (Fin (U.r τ) → R) := by rw [h]; infer_instance
  haveI : Subsingleton (LinearMap.range (Matrix.mulVecLin (U.εL τ))) := e.toEquiv.subsingleton
  ext i j
  have h1 : (⟨U.εL τ *ᵥ Pi.single j 1, LinearMap.mem_range_self _ _⟩ :
      LinearMap.range (Matrix.mulVecLin (U.εL τ))) = 0 := Subsingleton.elim _ _
  have h2 := congrArg (fun x : LinearMap.range (Matrix.mulVecLin (U.εL τ)) => (x : Fin g → R) i) h1
  simpa [Matrix.mulVec_single_one] using h2
end ReciprocityTheory.PGsh.Up
