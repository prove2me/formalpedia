-- Prove2me | solution 1 for PersistClust.Count.image_birth_strong_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T18:30:26.460301+00:00
-- url     : https://prove2.me/submissions/c527a5c3-1bb4-4141-a5cf-3cf64eaae1e1

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

/-- Image-birth strong lower bound: under the interleaving square (i'), every
ancestor of the source cell C at a level u >= beta pulls back to an
ancestor of the image cell at level u - eps, so the image's birth-sup is
at least the source's birth-sup minus eps, independent of the probe
level. -/
theorem solution {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameY : IsTameModule stageY JY) {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    {β : ℝ} (hβ : α ≤ β) (C : comps stageX JX β) :
    birthSup hLawX β C - ε ≤ birthSup hLawY (β - ε) (φ β hβ C) := by
  obtain ⟨s₀, hs₀⟩ := hTameY.2.2
  have hBddY : BddAbove (AncSet hLawY (β - ε) (φ β hβ C)) := by
    refine ⟨s₀, fun w hw => ?_⟩
    obtain ⟨-, C₂, -⟩ := hw
    have hstage : (stageY w).Nonempty := by
      obtain ⟨x, hx, -⟩ := C₂.property
      exact ⟨x, hx⟩
    by_contra hle
    push_neg at hle
    exact hstage.ne_empty (hs₀ w hle.le)
  have hneX : (AncSet hLawX β C).Nonempty := ⟨β, le_rfl, C, t3_structMap_id hLawX β C⟩
  have hmain : birthSup hLawX β C ≤ birthSup hLawY (β - ε) (φ β hβ C) + ε := by
    refine csSup_le hneX ?_
    intro u hu
    obtain ⟨huβ, C_u, hCu⟩ := hu
    have hαu : α ≤ u := le_trans hβ huβ
    have hpull : structMap hLawY (show β - ε ≤ u - ε by linarith) (φ u hαu C_u)
        = φ β hβ C := by
      have h1 := hSq1 β u hβ hαu huβ C_u
      rw [← hCu]
      exact h1.symm
    have hmemY : (u - ε) ∈ AncSet hLawY (β - ε) (φ β hβ C) :=
      ⟨show β - ε ≤ u - ε by linarith, φ u hαu C_u, hpull⟩
    have hle : u - ε ≤ birthSup hLawY (β - ε) (φ β hβ C) :=
      (rfl : birthSup hLawY (β - ε) (φ β hβ C)
        = sSup (AncSet hLawY (β - ε) (φ β hβ C))).symm ▸
        (le_csSup hBddY hmemY)
    linarith
  linarith
