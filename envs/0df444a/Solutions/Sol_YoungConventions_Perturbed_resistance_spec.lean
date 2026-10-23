-- Prove2me | solution 1 for YoungConventions.Perturbed.resistance_spec
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:46:33.387793+00:00
-- url     : https://prove2.me/submissions/7a95ce8b-beda-46a3-aaff-97690f8905fb

import Mathlib
import Definitions.Def_YoungConventions_Perturbed_FiniteChain
import Definitions.Def_YoungConventions_Perturbed_RegularPerturbation

open Filter Topology


namespace YoungConventions.Perturbed

theorem hasRes_unique_core {X : Type*} [Fintype X] [DecidableEq X]
    (P : ℝ → Matrix X X ℝ) (x y : X) (r r' : ℝ)
    (h : HasResistance P x y r) (h' : HasResistance P x y r') (hlt : r < r') : False := by
  obtain ⟨-, c, hc, hT⟩ := h
  obtain ⟨-, c', -, hT'⟩ := h'
  have hpow : Tendsto (fun ε : ℝ => ε ^ (r' - r)) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 (r' - r) (Or.inr (by linarith))).tendsto
    rw [Real.zero_rpow (by linarith)] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hprod := hpow.mul hT'
  rw [zero_mul] at hprod
  have heq : (fun ε : ℝ => ε ^ (r' - r) * (ε ^ (-r') * P ε x y)) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => ε ^ (-r) * P ε x y) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [← mul_assoc, ← Real.rpow_add hε]
    ring_nf
  have h2 := hprod.congr' heq
  have := tendsto_nhds_unique h2 hT
  linarith

theorem resistance_spec_core {X : Type*} [Fintype X] [DecidableEq X]
    (P0 : Matrix X X ℝ) (hP0 : P0 ∈ Matrix.rowStochastic ℝ X)
    (P : ℝ → Matrix X X ℝ) (a : ℝ) (hP : IsRegularPerturbation P0 P a) (x y : X) :
    (∀ r r' : ℝ, HasResistance P x y r → HasResistance P x y r' → r = r') ∧
    ((∃ ε ∈ Set.Ioc 0 a, 0 < P ε x y) → IsEdge P x y) ∧
    (IsEdge P x y → HasResistance P x y (resistance P x y)) ∧
    ((IsEdge P x y ∧ resistance P x y = 0) ↔ 0 < P0 x y) := by
  have huniq : ∀ r r' : ℝ, HasResistance P x y r → HasResistance P x y r' → r = r' := by
    intro r r' h h'
    rcases lt_trichotomy r r' with hl | he | hg
    · exact (hasRes_unique_core P x y r r' h h' hl).elim
    · exact he
    · exact (hasRes_unique_core P x y r' r h' h hg).elim
  have hedge : (∃ ε ∈ Set.Ioc 0 a, 0 < P ε x y) → IsEdge P x y := by
    intro hex
    obtain ⟨r, -, c, hc, hT⟩ := hP.order x y hex
    have hev := hT.eventually_const_lt hc
    filter_upwards [hev, self_mem_nhdsWithin] with ε h1 h2
    have hp : 0 < ε ^ (-r) := Real.rpow_pos_of_pos h2 _
    exact (mul_pos_iff_of_pos_left hp).mp h1
  have hres : IsEdge P x y → HasResistance P x y (resistance P x y) := by
    intro he
    have hex : ∃ ε ∈ Set.Ioc 0 a, 0 < P ε x y := by
      obtain ⟨ε, h1, h2⟩ := (he.and (Ioc_mem_nhdsGT hP.pos)).exists
      exact ⟨ε, h2, h1⟩
    have hr := hP.order x y hex
    unfold resistance
    rw [dif_pos hr]
    exact Classical.choose_spec hr
  refine ⟨huniq, hedge, hres, ?_, ?_⟩
  · rintro ⟨he, h0⟩
    have h := hres he
    rw [h0] at h
    obtain ⟨-, c, hc, hT⟩ := h
    have hT2 : Tendsto (fun ε : ℝ => P ε x y) (𝓝[>] 0) (𝓝 c) := by
      refine hT.congr ?_
      intro ε
      simp
    have := tendsto_nhds_unique (hP.tendsto x y) hT2
    linarith
  · intro hpos
    have he : IsEdge P x y := (hP.tendsto x y).eventually_const_lt hpos
    refine ⟨he, ?_⟩
    have h0 : HasResistance P x y 0 := by
      refine ⟨le_rfl, P0 x y, hpos, ?_⟩
      refine (hP.tendsto x y).congr ?_
      intro ε
      simp
    exact huniq _ _ (hres he) h0

end YoungConventions.Perturbed

open YoungConventions.Perturbed


theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (P0 : Matrix X X ℝ) (hP0 : P0 ∈ Matrix.rowStochastic ℝ X)
    (P : ℝ → Matrix X X ℝ) (a : ℝ) (hP : IsRegularPerturbation P0 P a) (x y : X) :
    (∀ r r' : ℝ, HasResistance P x y r → HasResistance P x y r' → r = r') ∧
    ((∃ ε ∈ Set.Ioc 0 a, 0 < P ε x y) → IsEdge P x y) ∧
    (IsEdge P x y → HasResistance P x y (resistance P x y)) ∧
    ((IsEdge P x y ∧ resistance P x y = 0) ↔ 0 < P0 x y) := by
  exact resistance_spec_core P0 hP0 P a hP x y
