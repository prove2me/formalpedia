-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.mulVec_mem_pP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:31:31.587827+00:00
-- url     : https://prove2.me/submissions/0b6a030d-ba3f-4294-a36c-4201e865eec7

import Definitions.Def_ReciprocityTheory_DualLattices_HasLenLeOfSurj
import Definitions.Def_ReciprocityTheory_DualLattices_MulVecMemPP
import Theorems.Thm_ReciprocityTheory_PGsh_Up_mem_pP

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
omit [Fact p.Prime]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {n n' : ℕ} (M : Matrix (Fin n') (Fin n) R) {w : Fin n → R}
    (hw : w ∈ Ideal.span {(p : R)} • (⊤ : Submodule R (Fin n → R))) :
    M *ᵥ w ∈ Ideal.span {(p : R)} • (⊤ : Submodule R (Fin n' → R)) := by
  obtain ⟨w', rfl⟩ := (mem_pP w).1 hw
  exact (mem_pP _).2 ⟨M *ᵥ w', Matrix.mulVec_smul M (p : R) w'⟩
end ReciprocityTheory.PGsh.Up
