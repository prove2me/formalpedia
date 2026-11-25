-- Prove2me | solution 1 for PI.VolStabS.FFHS.exists_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:50:28.009751+00:00
-- url     : https://prove2.me/submissions/c9e8eea2-c24c-4597-846a-12b616f0a8ce

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFHS
import Theorems.Thm_PI_VolStabS_FFHS_exists_aniso
import Theorems.Thm_PI_VolStabS_FFHS_mem_perp
import Theorems.Thm_PI_VolStabS_FFHS_perp_isHS
import Theorems.Thm_PI_VolStabS_FFHS_finrank_perp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS PI.VolStabS.FFHS
open Module
variable {K : Type} [Field K] {σ : K →+* K}
namespace PI.VolStabS.FFHS
theorem _root_.solution (h2 : (2 : K) ≠ 0) : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V → V → K), IsHS σ h → finrank K V = m →
    ∃ f : Fin m → V, (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧ ∀ i, h (f i) (f i) ≠ 0 := by
  intro m
  induction m with
  | zero => intro V _ _ _ h _ _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    intro V _ _ _ h hs hm
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hm
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨e, he⟩ := exists_aniso h2 hs x hx
    have hq := hs.toIsSq
    have hfr : finrank K (perp hq e) = m := by have := finrank_perp hq e he; omega
    obtain ⟨g, hg1, hg2⟩ := ih (perp hq e) (fun w w' => h w w') (perp_isHS hs e he) hfr
    refine ⟨Fin.cons e (fun i => (g i : V)), ?_, ?_⟩
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => simpa using (mem_perp hq e (g j)).1 (g j).2
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [hq.herm e, (mem_perp hq e (g i)).1 (g i).2, map_zero]
        | succ j =>
          simp only [Fin.cons_succ]
          exact hg1 i j (fun hh => hij (by rw [hh]))
    · intro i
      induction i using Fin.cases with
      | zero => simpa using he
      | succ i => simpa using hg2 i
end PI.VolStabS.FFHS
