-- Prove2me | solution 1 for PI.VolStabSW.FFHS.exists_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:51:24.194083+00:00
-- url     : https://prove2.me/submissions/e3730baf-ff1d-4702-abf2-0141e98482bd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFHS
import Theorems.Thm_PI_VolStabSW_FFHS_exists_aniso
import Theorems.Thm_PI_VolStabSW_FFHS_mem_perp
import Theorems.Thm_PI_VolStabSW_FFHS_perp_isHS
import Theorems.Thm_PI_VolStabSW_FFHS_finrank_perp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FFHS
open Module
variable {K : Type} [Field K] {σ : K →+* K}
namespace PI.VolStabSW.FFHS
theorem _root_.solution (h2 : (2 : K) ≠ 0) : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V → V → K), IsHS σ h → finrank K V = m →
    ∃ f : Fin m → V, (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧ ∀ i, h (f i) (f i) ≠ 0 := by
  intro m
  induction m with
  | zero =>
    intro V _ _ _ h hs hm
    exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro V _ _ _ h hs hm
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < finrank K V)
    obtain ⟨e, he⟩ := exists_aniso h2 hs x hx
    have hp := perp_isHS hs e he
    have hr := finrank_perp hs.toIsSq e he
    obtain ⟨g, hg1, hg2⟩ := ih (perp hs.toIsSq e) (fun w w' => h w w') hp (by omega)
    refine ⟨Fin.cons e (fun i => (g i : V)), ?_, ?_⟩
    · intro i j hij
      induction i using Fin.cases <;> induction j using Fin.cases
      · exact absurd rfl hij
      · simp only [Fin.cons_zero, Fin.cons_succ]
        exact (mem_perp hs.toIsSq e _).1 (g _).2
      · simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hs.herm e, (mem_perp hs.toIsSq e _).1 (g _).2, map_zero]
      · simp only [Fin.cons_succ]
        exact hg1 _ _ (fun h' => hij (by rw [h']))
    · intro i
      induction i using Fin.cases
      · simpa using he
      · simpa using hg2 _
end PI.VolStabSW.FFHS
