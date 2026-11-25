-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.mem_pP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:24:43.247801+00:00
-- url     : https://prove2.me/submissions/1ab6859e-600c-48d1-b322-751cff9ce92b

import Definitions.Def_ReciprocityTheory_DualLattices_HasLenLeOfSurj
import Definitions.Def_ReciprocityTheory_DualLattices_MulVecMemPP

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
theorem _root_.solution {n : ℕ} (w : Fin n → R) :
    w ∈ Ideal.span {(p : R)} • (⊤ : Submodule R (Fin n → R)) ↔ ∃ w', w = (p : R) • w' := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w', _, hw'⟩
    exact ⟨w', hw'.symm⟩
  · rintro ⟨w', hw'⟩
    exact ⟨w', Submodule.mem_top, hw'.symm⟩
end ReciprocityTheory.PGsh.Up
