-- Prove2me | solution 1 for PersistClust.Count.crit_free_descent_injective
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T19:43:59.676418+00:00
-- url     : https://prove2.me/submissions/262d7174-1a54-4ece-99e1-571ad6ed7324

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

theorem solution {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {w w' : ℝ} (hww : w ≤ w')
    (hfree : ∀ τ ∈ critSet hTame, τ < w ∨ w' < τ) {C₁ C₂ : comps stage J w'}
    (h : structMap hLaw hww C₁ = structMap hLaw hww C₂) : C₁ = C₂ := by
  have hspec1 := compRep_spec stage J w' C₁
  have hspec2 := compRep_spec stage J w' C₂
  have hv : (structMap hLaw hww C₁).val = (structMap hLaw hww C₂).val :=
    congrArg Subtype.val h
  rw [structMap_val, structMap_val] at hv
  have hJw : J w (compRep stage J w' C₁) (compRep stage J w' C₂) := by
    have hmem : compRep stage J w' C₂ ∈ {z | J w (compRep stage J w' C₁) z} := by
      rw [hv]
      exact hLaw.refl (hLaw.antitone hww hspec2.1)
    exact hmem
  have hclause := (critSet_spec hTame w w' hww hfree).2
  have hJw' : J w' (compRep stage J w' C₁) (compRep stage J w' C₂) :=
    hclause (compRep stage J w' C₁) hspec1.1 (compRep stage J w' C₂) hspec2.1 hJw
  refine Subtype.ext ?_
  rw [← hspec1.2, ← hspec2.2]
  ext z
  exact ⟨fun hz => hLaw.trans (hLaw.symm hJw') hz, fun hz => hLaw.trans hJw' hz⟩
