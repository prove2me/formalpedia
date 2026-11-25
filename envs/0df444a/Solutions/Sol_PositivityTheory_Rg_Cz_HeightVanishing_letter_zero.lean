-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.HeightVanishing.letter_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:43:37.554556+00:00
-- url     : https://prove2.me/submissions/37b2ba6a-258a-4f1c-b928-e589a6f2c1e6

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PHeight
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_comm_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.HeightVanishing
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable (E : Fin n → Fin n → Module.End ℂ M)
variable {ℓ : M →ₗ[ℂ] ℂ} {ψ : Fin n → Fin n → ℂ} (hE : GlRel E)
  (hψ2 : ∀ a b : Fin n, (a : ℕ) + 1 < b → ψ a b = 0) (hψ : ∀ a b : Fin n, a < b → ℓ ∘ₗ E a b = ψ a b • ℓ)
include hE hψ2 hψ
namespace PositivityTheory.Rg.Cz.HeightVanishing
theorem _root_.solution {k : ℕ} (hQ : ∀ (h : ℤ) (A : Module.End ℂ M), A ∈ W E k h → (k : ℤ) < h → ℓ ∘ₗ A = 0)
    (a b : Fin n) (hab : ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) ≤ 0) {h : ℤ} {A : Module.End ℂ M} (hA : A ∈ W E k h)
    (hk : (k : ℤ) < h + (((b : ℕ) : ℤ) - ((a : ℕ) : ℤ))) : ℓ ∘ₗ (E a b * A) = 0 := by
  have e : E a b * A = A * E a b + (E a b * A - A * E a b) := by abel
  rw [e, LinearMap.comp_add]
  have h1 : ℓ ∘ₗ (A * E a b) = 0 := by
    rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hQ h A hA (by linarith), LinearMap.zero_comp]
  rw [h1, hQ _ _ (comm_mem E hE a b hA) hk, add_zero]
end PositivityTheory.Rg.Cz.HeightVanishing
