-- Prove2me | solution 1 for SensitivityCopyGraphPopulation.copyGraph_independence_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:19:44.244798+00:00
-- url     : https://prove2.me/submissions/af36cac9-e84b-4619-8080-c222db8ae65a

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_CopyGraphPopulation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Fin
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

namespace SensitivityActiveSocketPopulation
end SensitivityActiveSocketPopulation
namespace SensitivityCopyGraphPopulation
end SensitivityCopyGraphPopulation
namespace SensitivityGraphPopulation
end SensitivityGraphPopulation


/-! Disjoint copies of induced conflict graphs, with exact integral edge bounds. -/
open SensitivityCopyGraphPopulation
open scoped Classical BigOperators
open SensitivityGraphPopulation SensitivityActiveSocketPopulation
set_option autoImplicit false
variable {C V : Type} [Fintype C]

theorem solution (G : SimpleGraph V) (sets : C → Finset V)
    (alpha : C → ℕ)
    (hcap : ∀ c, ∀ s ⊆ sets c, G.IsIndepSet s → s.card ≤ alpha c) :
    ∀ vertices : Finset (CopyVertex sets), (copyGraph G sets).IsIndepSet vertices →
      vertices.card ≤ ∑ c, alpha c := by
  intro vertices hind
  have hlocal : ∀ c, (vertices.filter fun v => v.1 = c).card ≤ alpha c := by
    intro c
    let fiber := vertices.filter fun v => v.1 = c
    let image := fiber.image fun v => v.2.val
    have hsub : image ⊆ sets c := by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      have heq := (Finset.mem_filter.mp hw).2
      exact heq ▸ w.2.property
    have hind' : G.IsIndepSet image := by
      intro v hv w hw hne hAdj
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨ha, hac⟩ := Finset.mem_filter.mp ha
      obtain ⟨hb, hbc⟩ := Finset.mem_filter.mp hb
      have hab : a ≠ b := fun heq => hne (congrArg (fun z => z.2.val) heq)
      exact hind ha hb hab ⟨hac.trans hbc.symm, hAdj⟩
    have hcard : image.card = fiber.card := by
      apply Finset.card_image_of_injOn
      intro a ha b hb heq
      obtain ⟨_, hac⟩ := Finset.mem_filter.mp ha
      obtain ⟨_, hbc⟩ := Finset.mem_filter.mp hb
      obtain ⟨ca, va⟩ := a
      obtain ⟨cb, vb⟩ := b
      dsimp at hac hbc heq
      subst ca
      subst cb
      exact congrArg (Sigma.mk c) (Subtype.ext heq)
    exact hcard ▸ hcap c image hsub hind'
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset C)) => hlocal c)
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (s := vertices) (t := (Finset.univ : Finset C)) (f := fun v => v.1)
    (fun _ _ => Finset.mem_univ _)
  rw [← hpartition] at hsum
  exact hsum
