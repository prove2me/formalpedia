-- Prove2me | solution 1 for PI.OmLocU.CntFF.exists_orth2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:07:13.826802+00:00
-- url     : https://prove2.me/submissions/8fb513b1-7860-45ff-bd9f-ddff5c9a676f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnitaryOrbits_FFInert2Holds
import Theorems.Thm_PI_OmLocU_CntFF_exists_aniso2
import Theorems.Thm_PI_VolStabSW_FFHS_finrank_perp
import Theorems.Thm_PI_VolStabSW_FFHS_mem_perp
import Theorems.Thm_PI_VolStabSW_FFHS_perp_isHS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmLocU PI.OmLocU.CntFF
open Module PI.VolStabSW PI.VolStabSW.FFHS
namespace PI.OmLocU.CntFF
theorem _root_.solution {K : Type} [Field K] {σ : K →+* K} (h2 : ∃ z : K, z + σ z ≠ 0) :
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V → V → K), IsHS σ h → finrank K V = m →
    ∃ f : Fin m → V, (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧ ∀ i, h (f i) (f i) ≠ 0 := by
  intro m
  induction m with
  | zero =>
    intro V _ _ _ h hs hm
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ m ih =>
    intro V _ _ _ h hs hm
    obtain ⟨x, hx⟩ : ∃ x : V, x ≠ 0 := by
      have : 0 < finrank K V := by omega
      exact finrank_pos_iff_exists_ne_zero.mp this
    obtain ⟨e, he⟩ := exists_aniso2 h2 hs x hx
    obtain ⟨g, hg1, hg2⟩ := ih (perp hs.toIsSq e) (fun w w' => h w w') (perp_isHS hs e he)
      (by have := finrank_perp hs.toIsSq e he; omega)
    refine ⟨Fin.cons e (fun i => (g i : V)), ?_, ?_⟩
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact (mem_perp hs.toIsSq e _).mp (g j).2
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [hs.herm e (g i : V), (mem_perp hs.toIsSq e _).mp (g i).2, map_zero]
        | succ j =>
          simp only [Fin.cons_succ]
          exact hg1 i j (fun h' => hij (by rw [h']))
    · intro i
      cases i using Fin.cases with
      | zero => simpa using he
      | succ i => simpa using hg2 i
end PI.OmLocU.CntFF
