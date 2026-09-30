-- Prove2me | solution 1 for ScenarioReduction.ForwardSelection.forward_first_step
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:15:07.94467+00:00
-- url     : https://prove2.me/submissions/bb9ffa41-b434-4ec2-bc22-20321cac11e7

import Definitions.Def_ScenarioReduction_ForwardSelection_fmCost
import Definitions.Def_ScenarioReduction_ForwardSelection_reductionCost
import Mathlib.Tactic
set_option autoImplicit false
open ScenarioReduction.ForwardSelection Finset

private theorem single_cost {E : Type*} [NormedAddCommGroup E] {N : ℕ}
    (h : ℝ → ℝ) (ω₀ : E) (ω : Fin N → E) (p : Fin N → ℝ) (u : Fin N) :
    reductionCost (scenCost h ω₀ ω) p (univ.erase u) (compl_erase_nonempty _ _) =
      ∑ i, p i * scenCost h ω₀ ω i u := by
  have hz : p u * scenCost h ω₀ ω u u = 0 := by simp [scenCost,fmCost]
  have he := sum_erase_add (s := univ) (f := fun i => p i * scenCost h ω₀ ω i u) (mem_univ u)
  simpa [reductionCost, hz] using he

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {N : ℕ} (h : ℝ → ℝ) (hh : IsGrowthFunction h) (ω₀ : E)
    (ω : Fin N → E) (p : Fin N → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    (∀ u : Fin N, reductionCost (scenCost h ω₀ ω) p (Finset.univ.erase u)
        (compl_erase_nonempty _ _) = ∑ i, p i * scenCost h ω₀ ω i u) ∧
    {x : ℝ | ∃ J : Finset (Fin N), ∃ hJ : Jᶜ.Nonempty, J.card = N - 1 ∧
        x = reductionCost (scenCost h ω₀ ω) p J hJ} =
      Set.range (fun u : Fin N => ∑ i, p i * scenCost h ω₀ ω i u) := by
  refine ⟨single_cost h ω₀ ω p, ?_⟩
  ext x
  constructor
  · rintro ⟨J,hJ,hcard,hx⟩
    have hN : 0 < N := by
      obtain ⟨u,hu⟩ := hJ
      exact lt_of_le_of_lt (Nat.zero_le u.val) u.isLt
    have hcompl : Jᶜ.card = 1 := by
      rw [card_compl,Fintype.card_fin,hcard]
      omega
    obtain ⟨u,hu⟩ := card_eq_one.mp hcompl
    have hJeq : J = univ.erase u := by
      apply compl_injective
      simpa using hu
    subst J
    refine ⟨u,?_⟩
    rw [hx]
    exact (single_cost h ω₀ ω p u).symm
  · rintro ⟨u,rfl⟩
    refine ⟨univ.erase u,compl_erase_nonempty _ _,?_,?_⟩
    · simp
    · exact (single_cost h ω₀ ω p u).symm
