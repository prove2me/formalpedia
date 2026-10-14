-- Prove2me | solution 1 for PersistClust.Count.pullback_birth_strong_lower
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-13T09:22:50.722901+00:00
-- url     : https://prove2.me/submissions/7062398c-4e6c-492f-b103-7afc79d3c695

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

theorem t3_structMap_id {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (t : ℝ) (C : comps stage J t) :
    structMap hLaw le_rfl C = C :=
  Subtype.ext (compRep_spec stage J t C).2

/-- Rung-B (T5a, ψ-mirror of `t5_imageBirthStrongLower`): under square (ii'), the birth-sup
of the pullback cell `ψ_β C` is at least the source's birth-sup minus ε, at any level β ≥ α.
Needed by the kill-pairing (§8.15(b)) and the QSE-sector partner bookkeeping (§8.16.4). -/
theorem solution {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) {α ε : ℝ}
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq2 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (y : comps stageY JY β'),
      ψ β hβ (structMap hLawY hle y) =
        structMap hLawX (show β - ε ≤ β' - ε by linarith) (ψ β' hβ' y))
    {β : ℝ} (hβ : α ≤ β) (C : comps stageY JY β) :
    birthSup hLawY β C - ε ≤ birthSup hLawX (β - ε) (ψ β hβ C) := by
  obtain ⟨s₀, hs₀⟩ := hTameX.2.2
  have hBddX : BddAbove (AncSet hLawX (β - ε) (ψ β hβ C)) := by
    refine ⟨s₀, fun w hw => ?_⟩
    obtain ⟨-, C₂, -⟩ := hw
    have hstage : (stageX w).Nonempty := by
      obtain ⟨x, hx, -⟩ := C₂.property
      exact ⟨x, hx⟩
    by_contra hle
    push_neg at hle
    exact hstage.ne_empty (hs₀ w hle.le)
  have hneY : (AncSet hLawY β C).Nonempty := ⟨β, le_rfl, C, t3_structMap_id hLawY β C⟩
  have hmain : birthSup hLawY β C ≤ birthSup hLawX (β - ε) (ψ β hβ C) + ε := by
    refine csSup_le hneY ?_
    intro u hu
    obtain ⟨huβ, C_u, hCu⟩ := hu
    have hαu : α ≤ u := le_trans hβ huβ
    have hpull : structMap hLawX (show β - ε ≤ u - ε by linarith) (ψ u hαu C_u)
        = ψ β hβ C := by
      have h1 := hSq2 β u hβ hαu huβ C_u
      rw [← hCu]
      exact h1.symm
    have hmemX : (u - ε) ∈ AncSet hLawX (β - ε) (ψ β hβ C) :=
      ⟨show β - ε ≤ u - ε by linarith, ψ u hαu C_u, hpull⟩
    have hle : u - ε ≤ birthSup hLawX (β - ε) (ψ β hβ C) :=
      (rfl : birthSup hLawX (β - ε) (ψ β hβ C)
        = sSup (AncSet hLawX (β - ε) (ψ β hβ C))).symm ▸
        (le_csSup hBddX hmemX)
    linarith
  linarith
