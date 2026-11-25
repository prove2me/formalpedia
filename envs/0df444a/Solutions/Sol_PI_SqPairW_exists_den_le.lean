-- Prove2me | solution 1 for PI.SqPairW.exists_den_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:28:46.36626+00:00
-- url     : https://prove2.me/submissions/7f875d68-5e15-450c-b795-b16a0804f448

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_ConjTransposeMemLam
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_ExistsDenLe
import Theorems.Thm_PI_SqPairW_exists_nat_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairW
open Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
namespace PI.SqPairW
theorem _root_.solution {L' L'' : Submodule (𝓞 E) (Fin N → E)} (hfg : L'.FG)
    (hspan : Submodule.span E (L'' : Set (Fin N → E)) = ⊤) :
    ∃ D : ℕ, 0 < D ∧ ∀ w ∈ L', (D : ℤ) • w ∈ L'' := by
  obtain ⟨s, rfl⟩ := hfg
  have hk : ∀ x : s, ∃ k : ℕ, 0 < k ∧ (k : ℤ) • (x : Fin N → E) ∈ L'' :=
    fun x => exists_nat_smul_mem hspan x
  choose k hk0 hkL using hk
  refine ⟨∏ x, k x, Finset.prod_pos (fun x _ => hk0 x), ?_⟩
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm⟩ : k ⟨x, hx⟩ ∣ ∏ y, k y := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
    rw [hm, Nat.cast_mul, mul_comm, mul_smul]
    exact zsmul_mem (hkL ⟨x, hx⟩) _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [smul_comm]
    exact L''.smul_mem c hx
end PI.SqPairW
