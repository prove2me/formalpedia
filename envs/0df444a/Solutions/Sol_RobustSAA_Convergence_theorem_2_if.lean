-- Prove2me | solution 1 for RobustSAA.Convergence.theorem_2_if
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T20:01:34.241958+00:00
-- url     : https://prove2.me/submissions/29577844-1a42-4935-a3d3-57febda5377f

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped NNReal ENNReal

namespace RSAAIfAux

/-- Countably many bounded continuous test functions determine convergence to a fixed `F`. -/
lemma exists_countable_test {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    [FirstCountableTopology (ProbabilityMeasure Ω)] (F : ProbabilityMeasure Ω) :
    ∃ S : Set (Ω →ᵇ ℝ), S.Countable ∧ ∀ G : ℕ → ProbabilityMeasure Ω,
      (∀ f ∈ S, Tendsto (fun N => ∫ ω, f ω ∂(G N : Measure Ω)) atTop
        (𝓝 (∫ ω, f ω ∂(F : Measure Ω)))) → Tendsto G atTop (𝓝 F) := by
  set L : Filter (ProbabilityMeasure Ω) := ⨅ f : Ω →ᵇ ℝ,
    comap (fun μ : ProbabilityMeasure Ω => ∫ ω, f ω ∂(μ : Measure Ω))
      (𝓝 (∫ ω, f ω ∂(F : Measure Ω))) with hL
  have hLle : L ≤ 𝓝 F := by
    have : Tendsto (id : ProbabilityMeasure Ω → ProbabilityMeasure Ω) L (𝓝 F) := by
      rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
      intro f
      exact tendsto_iInf' f tendsto_comap
    exact this
  obtain ⟨V, hV⟩ := (𝓝 F).exists_antitone_basis
  have hmem : ∀ n, ∃ I : Set (Ω →ᵇ ℝ), I.Finite ∧ ∃ W : I → Set (ProbabilityMeasure Ω),
      (∀ i : I, W i ∈ comap (fun μ : ProbabilityMeasure Ω => ∫ ω, i.1 ω ∂(μ : Measure Ω))
        (𝓝 (∫ ω, i.1 ω ∂(F : Measure Ω)))) ∧ V n = ⋂ i, W i := by
    intro n
    have : V n ∈ L := hLle (hV.mem n)
    exact Filter.mem_iInf.1 this
  choose I hIfin W hW hVeq using hmem
  refine ⟨⋃ n, I n, Set.countable_iUnion fun n => (hIfin n).countable, ?_⟩
  intro G hG
  rw [hV.toHasBasis.tendsto_right_iff]
  intro n _
  rw [hVeq n]
  have : Finite (I n) := (hIfin n).to_subtype
  simp only [Set.mem_iInter]
  rw [Filter.eventually_all]
  intro i
  have h1 := hG i (Set.mem_iUnion.2 ⟨n, i.2⟩)
  have h2 : Tendsto G atTop (comap (fun μ : ProbabilityMeasure Ω =>
      ∫ ω, i.1 ω ∂(μ : Measure Ω)) (𝓝 (∫ ω, i.1 ω ∂(F : Measure Ω)))) :=
    tendsto_comap_iff.2 h1
  exact h2 (hW n i)


end RSAAIfAux

open RSAAIfAux
open RobustSAA.Convergence

lemma expect_bcf {d : ℕ} {Ξ : Set (Pt d)} (G : ProbabilityMeasure ↥Ξ) (f : ↥Ξ →ᵇ ℝ) :
    expect G (fun ξ => f ξ) = ((∫ ξ, f ξ ∂(G : Measure ↥Ξ) : ℝ) : EReal) := by
  unfold expect
  rw [if_pos (f.integrable _)]

/-- If (18) holds for the constant-in-`x` cost `c(x;ξ) = f(ξ)` on `X = {0}`, then no sequence
`G_N ∈ 𝓕_N` (eventually) can have `E_{G_N} f ≥ E_F f + ε` infinitely often. -/
lemma obj_fail {d : ℕ} {Ξ : Set (Pt d)} (𝓕 : DUS Ξ) (F : ProbabilityMeasure ↥Ξ)
    (f : ↥Ξ →ᵇ ℝ) (ω : ℕ → ↥Ξ)
    (hC : Conditions F ({0} : Set (Pt 0)) (fun _ ξ => f ξ) (fun N => 𝓕 N (sample ω N)))
    (G : ℕ → ProbabilityMeasure ↥Ξ) (hfr : ∀ᶠ N in atTop, G N ∈ 𝓕 N (sample ω N))
    (ε : ℝ) (hε : 0 < ε)
    (hfreq : ∃ᶠ N in atTop,
      ∫ ξ, f ξ ∂(F : Measure ↥Ξ) + ε ≤ ∫ ξ, f ξ ∂(G N : Measure ↥Ξ)) : False := by
  have hev := hC.1 {0} subset_rfl isCompact_singleton (ε / 2) (by linarith)
  obtain ⟨N, hN1, hN2, hN3⟩ := (hfreq.and_eventually (hev.and hfr)).exists
  have h0 := (hN2 0 rfl).1
  have hle : expect (G N) (fun ξ => f ξ) ≤ worstCase (𝓕 N (sample ω N)) (fun ξ => f ξ) :=
    le_iSup₂ (f := fun G' (_ : G' ∈ 𝓕 N (sample ω N)) => expect G' (fun ξ => f ξ)) (G N) hN3
  rw [expect_bcf] at hle
  have := hle.trans h0
  rw [EReal.coe_le_coe_iff] at this
  simp only [trueObj] at this
  linarith

theorem solution {d : ℕ} {Ξ : Set (Pt d)} (hΞ : IsClosed Ξ) (𝓕 : DUS Ξ)
    (h𝓕 : ¬ IsUniformlyConsistent 𝓕) :
    ∃ (F : ProbabilityMeasure ↥Ξ) (dx : ℕ) (X : Set (Pt dx)) (c : Pt dx → ↥Ξ → ℝ),
      Standing F X c ∧ Assumption1 X c ∧ Assumption2 F X c ∧ Assumption3 F 𝓕 X c ∧
        ¬ (∀ᵐ ω ∂(dataLaw F), Conditions F X c (fun N => 𝓕 N (sample ω N))) := by
  unfold IsUniformlyConsistent at h𝓕
  obtain ⟨F, hF⟩ := not_forall.1 h𝓕
  obtain ⟨S, hS, hdet⟩ := exists_countable_test F
  by_contra hcon
  have key : ∀ f : ↥Ξ →ᵇ ℝ, ∀ᵐ ω ∂(dataLaw F),
      Conditions F ({0} : Set (Pt 0)) (fun _ ξ => f ξ) (fun N => 𝓕 N (sample ω N)) := by
    intro f
    by_contra hf
    apply hcon
    refine ⟨F, 0, {0}, fun _ ξ => f ξ, ?_, ?_, ?_, ?_, hf⟩
    · exact ⟨isClosed_singleton, fun _ _ => ⟨f.integrable _, f.continuous⟩⟩
    · intro x _ U hU
      exact Filter.Eventually.of_forall (fun _ _ => refl_mem_uniformity hU)
    · exact ⟨isClosed_singleton, Or.inl Bornology.isBounded_singleton⟩
    · refine Or.inr ⟨fun _ => 0, continuous_const, by simp, ?_, ?_⟩
      · refine ae_of_all _ (fun ω => ?_)
        simp [phiDev, sampleMean]
      · intro x _
        refine ⟨‖f‖, 0, fun ξ => ?_⟩
        simpa [Real.norm_eq_abs] using f.norm_coe_le_norm ξ
  set S' : Set (↥Ξ →ᵇ ℝ) := S ∪ (fun f => -f) '' S with hS'
  have hS'c : S'.Countable := hS.union (hS.image _)
  have hall : ∀ᵐ ω ∂(dataLaw F), ∀ f ∈ S',
      Conditions F ({0} : Set (Pt 0)) (fun _ ξ => f ξ) (fun N => 𝓕 N (sample ω N)) :=
    (ae_ball_iff hS'c).2 (fun f _ => key f)
  apply hF
  filter_upwards [hall] with ω hω
  intro G hG
  by_contra hfr
  rw [not_frequently] at hfr
  simp only [not_not] at hfr
  apply hG
  apply hdet
  intro f hfS
  by_contra hnt
  rw [Metric.tendsto_nhds] at hnt
  push Not at hnt
  obtain ⟨ε, hε, hfreq⟩ := hnt
  have hsplit : ∃ᶠ N in atTop,
      ∫ ξ, f ξ ∂(F : Measure ↥Ξ) + ε ≤ ∫ ξ, f ξ ∂(G N : Measure ↥Ξ) ∨
      ∫ ξ, (-f) ξ ∂(F : Measure ↥Ξ) + ε ≤ ∫ ξ, (-f) ξ ∂(G N : Measure ↥Ξ) := by
    refine hfreq.mono (fun N hN => ?_)
    rw [Real.dist_eq] at hN
    simp only [coe_neg, Pi.neg_apply, integral_neg]
    rcases le_abs'.1 hN with h | h
    · right; linarith
    · left; linarith
  rcases frequently_or_distrib.1 hsplit with h | h
  · exact obj_fail 𝓕 F f ω (hω f (Or.inl hfS)) G hfr ε hε h
  · exact obj_fail 𝓕 F (-f) ω (hω (-f) (Or.inr ⟨f, hfS, rfl⟩)) G hfr ε hε h
