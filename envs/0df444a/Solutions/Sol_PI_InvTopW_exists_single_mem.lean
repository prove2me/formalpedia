-- Prove2me | solution 1 for PI.InvTopW.exists_single_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:43:28.088921+00:00
-- url     : https://prove2.me/submissions/2cf19918-48cb-404b-990a-0285936c7027

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LatticeOfEntriesIntegral
import Theorems.Thm_PI_InvTopW_exists_nat_den

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
namespace PI.InvTopW
theorem _root_.solution {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (j : Fin n) : ∃ d : ℕ, 1 ≤ d ∧ (d : E) • Pi.single j (1 : E) ∈ L := by
  have hnat : ∀ (d : ℕ) (v : Fin n → E), v ∈ L → (d : E) • v ∈ L := fun d v hv => by
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hv d
  let K : Submodule E (Fin n → E) :=
    { carrier := {x | ∃ d : ℕ, 1 ≤ d ∧ (d : E) • x ∈ L}
      add_mem' := by
        rintro a b ⟨d1, h1, ha⟩ ⟨d2, h2, hb⟩
        refine ⟨d1 * d2, Nat.mul_pos h1 h2, ?_⟩
        have e : ((d1 * d2 : ℕ) : E) • (a + b) = (d2 : E) • ((d1 : E) • a) + (d1 : E) • ((d2 : E) • b) := by
          rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (d2 : E) (d1 : E)]
        rw [e]
        exact add_mem (hnat d2 _ ha) (hnat d1 _ hb)
      zero_mem' := ⟨1, le_rfl, by rw [smul_zero]; exact L.zero_mem⟩
      smul_mem' := by
        rintro r x ⟨d, hd, hx⟩
        obtain ⟨d', hd', hr⟩ := exists_nat_den ({r} : Finset E)
        obtain ⟨s, hs⟩ := RingHom.mem_range.1 (hr r (Finset.mem_singleton_self r))
        refine ⟨d' * d, Nat.mul_pos hd' hd, ?_⟩
        have e : ((d' * d : ℕ) : E) • (r • x) = s • ((d : E) • x) := by
          rw [← algebraMap_smul E s ((d : E) • x), hs, smul_smul, smul_smul, Nat.cast_mul]
          congr 1
          ring
        rw [e]
        exact L.smul_mem s hx }
  have hK : Submodule.span E (L : Set (Fin n → E)) ≤ K := by
    rw [Submodule.span_le]
    intro x hx
    show ∃ d : ℕ, 1 ≤ d ∧ (d : E) • x ∈ L
    exact ⟨1, le_rfl, by rw [Nat.cast_one, one_smul]; exact hx⟩
  have hmem : Pi.single j (1 : E) ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL]
    exact Submodule.mem_top
  exact hK hmem
end PI.InvTopW
