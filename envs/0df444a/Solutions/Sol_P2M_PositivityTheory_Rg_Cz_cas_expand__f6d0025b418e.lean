-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Cz_cas_expand__f6d0025b418e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:07:49.331389+00:00
-- url     : https://prove2.me/submissions/5e6d9916-7953-4e45-ba60-46b7c83326ad

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_ReSwapSumLe
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_Expand
import Theorems.Thm_PositivityTheory_Rg_Cz_tE_zero_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_sum4
import Theorems.Thm_PositivityTheory_Rg_Cz_pair_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
set_option linter.unusedSectionVars false
namespace PositivityTheory.Rg.Cz
section
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
private theorem tE_zero_eq_sum_eAt (S : Finset Q) (a c : Fin n) :
    (tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) a c : Module.End ℂ (TV n ℂ Q)) =
      ∑ p ∈ S, (eAt p a c : Module.End ℂ (TV n ℂ Q)) := by
  apply LinearMap.ext
  intro f
  funext I
  rw [tE_zero_apply]
  simp [LinearMap.sum_apply, Finset.sum_apply]
end
end PositivityTheory.Rg.Cz
end

set_option autoImplicit false
open Finset
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
namespace PositivityTheory.Rg.Cz
theorem _root_.solution (S : Finset Q) :
    (∑ a, ∑ c, tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) a c * tE S 0 c a : Module.End ℂ (TV n ℂ Q)) =
      ((n * S.card : ℕ) : ℂ) • (1 : Module.End ℂ (TV n ℂ Q)) +
        ∑ p ∈ S, ∑ q ∈ S.erase p, pm (Equiv.swap p q) := by
  simp_rw [tE_zero_eq_sum_eAt, Finset.sum_mul_sum]
  apply LinearMap.ext
  intro f
  funext I
  simp only [LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply, Module.End.one_apply]
  rw [sum4]
  simp_rw [pair_apply]
  have hpm : ∀ p q : Q, (pm (Equiv.swap p q) : Module.End ℂ (TV n ℂ Q)) f I = f (I ∘ Equiv.swap p q) := by
    intro p q
    simp [pm]
  simp_rw [hpm]
  have hsplit : ∀ p ∈ S, (∑ q ∈ S, if p = q then (n : ℂ) * f I else f (I ∘ Equiv.swap p q)) =
      (n : ℂ) * f I + ∑ q ∈ S.erase p, f (I ∘ Equiv.swap p q) := by
    intro p hp
    rw [← Finset.add_sum_erase S _ hp]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun q hq => ?_
      rw [if_neg (Finset.ne_of_mem_erase hq).symm]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  simp [Finset.sum_const, nsmul_eq_mul, smul_eq_mul]
  ring
end PositivityTheory.Rg.Cz
