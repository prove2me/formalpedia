-- Prove2me | solution 1 for PersistClust.Count.level_le_birth_sup
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T19:53:34.327024+00:00
-- url     : https://prove2.me/submissions/266fccba-d446-4ac0-86e3-cf6efc246420

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

theorem solution {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {t : ℝ} (E : comps stage J t) :
    t ≤ birthSup hLaw t E := by
  obtain ⟨s₀, hs₀⟩ := hTame.2.2
  have hBdd : BddAbove (AncSet hLaw t E) := by
    refine ⟨s₀, fun u hu => ?_⟩
    obtain ⟨-, C₂, -⟩ := hu
    have hstage : (stage u).Nonempty := by
      obtain ⟨x, hx, -⟩ := C₂.property
      exact ⟨x, hx⟩
    by_contra hle
    push_neg at hle
    exact hstage.ne_empty (hs₀ u hle.le)
  exact (rfl : birthSup hLaw t E = sSup (AncSet hLaw t E)).symm ▸
    (le_csSup hBdd ⟨le_rfl, E, t3_structMap_id hLaw t E⟩)
