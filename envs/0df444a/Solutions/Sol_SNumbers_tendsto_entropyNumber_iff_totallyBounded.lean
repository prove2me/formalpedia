-- Prove2me | solution 1 for SNumbers.tendsto_entropyNumber_iff_totallyBounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:48:58.316031+00:00
-- url     : https://prove2.me/submissions/971826e8-6999-49a5-a84c-e0d3750c6c29

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Entropy
public import Theorems.Thm_SNumbers_entropyNumber_le_of_mem
public import Theorems.Thm_SNumbers_exists_mem_entropySet_lt
public import Theorems.Thm_SNumbers_entropyNumber_nonneg
public import Theorems.Thm_P2M_SNumbers_entropyNumber_antitone__7948be0d85af

set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) :
    Tendsto (entropyNumber S) atTop (𝓝 0) ↔
      TotallyBounded (⇑S '' Metric.closedBall 0 1) := by
  rw [Metric.tendsto_atTop, Metric.totallyBounded_iff]
  constructor
  · intro h ε hε
    obtain ⟨m, hm⟩ := h ε hε
    have hlt : entropyNumber S m < ε := by
      have := hm m le_rfl
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (entropyNumber_nonneg S m)] at this
    obtain ⟨δ, ⟨-, N, -, hcov⟩, hδε⟩ := exists_mem_entropySet_lt hlt
    exact ⟨(N : Set Y), N.finite_toSet,
      hcov.trans (Set.iUnion₂_mono fun y _ => Metric.closedBall_subset_ball hδε)⟩
  · intro h ε hε
    obtain ⟨t, ht_fin, ht_cov⟩ := h (ε / 2) (by positivity)
    have hmem : ε / 2 ∈ entropySet S ht_fin.toFinset.card := by
      refine ⟨by positivity, ht_fin.toFinset, Nat.lt_two_pow_self.le, ?_⟩
      rw [ht_fin.coe_toFinset]
      exact ht_cov.trans (Set.iUnion₂_mono fun y _ => Metric.ball_subset_closedBall)
    refine ⟨ht_fin.toFinset.card, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (entropyNumber_nonneg S n)]
    calc entropyNumber S n ≤ entropyNumber S ht_fin.toFinset.card :=
          entropyNumber_antitone' S hn
      _ ≤ ε / 2 := entropyNumber_le_of_mem hmem
      _ < ε := by linarith
end SNumbers
