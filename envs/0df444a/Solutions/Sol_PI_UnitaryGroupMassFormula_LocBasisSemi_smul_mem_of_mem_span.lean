-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocBasisSemi.smul_mem_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:33.181857+00:00
-- url     : https://prove2.me/submissions/519a8802-07ae-4fc3-b8b7-ccfd241a528b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocBasisSemi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemilocalBasis_SmulMemOfMemSpan
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocBasisSemi_surjK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocBasisSemi
variable (K : Type) [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime]
variable {K p}
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.UnitaryGroupMassFormula.LocBasisSemi
theorem _root_.solution (Y : Submodule (𝓞 K) V) {v : V}
    (hv : v ∈ Submodule.span (A K p) (Y : Set V)) :
    ∃ s : ℕ, Nat.Coprime s p ∧ (s : K) • v ∈ Y := by
  have hnat : ∀ (n : ℕ) {w : V}, w ∈ Y → (n : K) • w ∈ Y := fun n w hw => by
    rw [Nat.cast_smul_eq_nsmul]
    exact Y.nsmul_mem hw n
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.coprime_one_left p, by simpa using hx⟩
  | zero => exact ⟨1, Nat.coprime_one_left p, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
    have e : ((s * t : ℕ) : K) • (x + y) = (t : K) • ((s : K) • x) + (s : K) • ((t : K) • y) := by
      rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (t : K) (s : K)]
    rw [e]
    exact Y.add_mem (hnat t hsx) (hnat s hty)
  | smul a x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, y, hy⟩ := surjK a
    refine ⟨t * s, Nat.Coprime.mul_left ht hs, ?_⟩
    have e : ((t * s : ℕ) : K) • (a • x) = y • ((s : K) • x) := by
      rw [Subalgebra.smul_def, smul_smul, ← algebraMap_smul K y, smul_smul, Nat.cast_mul,
        ← RingOfIntegers.coe_eq_algebraMap, ← hy]
      ring_nf
    rw [e]
    exact Y.smul_mem y hsx
end PI.UnitaryGroupMassFormula.LocBasisSemi
