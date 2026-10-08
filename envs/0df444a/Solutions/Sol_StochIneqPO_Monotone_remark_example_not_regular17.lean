-- Prove2me | solution 1 for StochIneqPO.Monotone.remark_example_not_regular17
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:55:29.171728+00:00
-- url     : https://prove2.me/submissions/875fc778-f8b2-4263-8582-d570afcf276e

import Mathlib
import Definitions.Def_StochIneqPO_Monotone_Regular17
import Definitions.Def_StochIneqPO_Monotone_RemarkSpace

open StochIneqPO.Monotone Filter Topology
set_option maxHeartbeats 0

private theorem x_limit : Tendsto remarkX atTop (𝓝 remarkZ) := by
  have h : Tendsto (fun k : ℕ => (1 : ℝ) - 1 / ((k : ℝ) + 1)) atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun k : ℕ => (1 : ℝ) - 1 / ((k : ℝ) + 1)) atTop (𝓝 (1 - 0)))
  exact h.prodMk_nhds tendsto_const_nhds

private theorem closed_remark : IsClosed remarkSet := by
  have hx : IsClosed (Set.range remarkX ∪ {remarkZ}) := by
    simpa [Set.union_comm] using x_limit.isCompact_insert_range.isClosed
  have hy : IsClosed (Set.range remarkY) := by
    have hc : IsClosed {p : ℝ × ℝ | p.1 - 1 ∈ Set.range (fun n : ℕ => (n : ℝ)) ∧ p.2 = 1} :=
      (Nat.isClosedEmbedding_coe_real.isClosed_range.preimage (continuous_fst.sub continuous_const)).inter
        (isClosed_eq continuous_snd continuous_const)
    convert hc using 1
    ext p
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨⟨k, by simp [remarkY]⟩, rfl⟩
    · rintro ⟨⟨k, hk⟩, hp⟩
      refine ⟨k, ?_⟩
      apply Prod.ext <;> dsimp [remarkY]
      · linarith
      · exact hp.symm
  exact hx.union hy

private theorem rank_continuous :
    Continuous (fun p : RemarkSpace => remarkRank (p : remarkSet).val) := by
  have hp : ∀ p : RemarkSpace, 0 ≤ (p : remarkSet).val.1 := by
    intro p
    rcases p with ⟨p, hp⟩
    rcases hp with ((⟨k, rfl⟩ | rfl) | ⟨k, rfl⟩)
    · dsimp [remarkX]
      have h : (1 : ℝ) ≤ (k : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
      exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr h)
    · norm_num [remarkZ]
    · dsimp [remarkY]; positivity
  have hf : Continuous (fun p : RemarkSpace => (p : remarkSet).val.1) := continuous_subtype_val.fst
  have hg : Continuous (fun p : RemarkSpace => (p : remarkSet).val.2) := continuous_subtype_val.snd
  have hr : Continuous (fun p : RemarkSpace =>
      (1 - (p : remarkSet).val.2) * (p : remarkSet).val.1 +
      (p : remarkSet).val.2 * (1 - 1 / ((p : remarkSet).val.1 + 1 / 2))) :=
    ((continuous_const.sub hg).mul hf).add
      (hg.mul (continuous_const.sub (continuous_const.div (hf.add continuous_const)
        (fun p => by have := hp p; linarith))))
  convert hr using 1
  funext p
  rcases p with ⟨p, hp⟩
  rcases hp with ((⟨k, rfl⟩ | rfl) | ⟨k, rfl⟩) <;>
    simp [remarkRank, remarkX, remarkY, remarkZ]

private theorem ordering (k : ℕ) :
    RemarkSpace.x k < RemarkSpace.y k ∧ RemarkSpace.y k < RemarkSpace.x (k + 1) ∧
      RemarkSpace.x (k + 1) < RemarkSpace.z := by
  change remarkRank (remarkX k) < remarkRank (remarkY k) ∧
    remarkRank (remarkY k) < remarkRank (remarkX (k + 1)) ∧
    remarkRank (remarkX (k + 1)) < remarkRank remarkZ
  simp only [remarkRank, remarkX, remarkY, remarkZ, if_pos rfl, Nat.cast_add, Nat.cast_one]
  norm_num
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have h1 := one_div_lt_one_div_of_lt (show (0 : ℝ) < (k : ℝ) + 1 by positivity)
    (show (k : ℝ) + 1 < (k : ℝ) + 1 + 1 / 2 by linarith)
  have h2 := one_div_lt_one_div_of_lt (show (0 : ℝ) < (k : ℝ) + 1 + 1 / 2 by positivity)
    (show (k : ℝ) + 1 + 1 / 2 < (k : ℝ) + 1 + 1 by linarith)
  have h3 : (0 : ℝ) < 1 / ((k : ℝ) + 1 + 1) := by positivity
  simp only [one_div] at h1 h2 h3
  constructor
  · linarith
  constructor <;> linarith

theorem solution :
    IsClosed remarkSet ∧ CompleteSpace RemarkSpace ∧
      SecondCountableTopology RemarkSpace ∧ OrderClosedTopology RemarkSpace ∧
      (∀ k : ℕ, RemarkSpace.x k < RemarkSpace.y k ∧ RemarkSpace.y k < RemarkSpace.x (k + 1) ∧
        RemarkSpace.x (k + 1) < RemarkSpace.z) ∧
      ¬ Regular17 RemarkSpace := by
  haveI : CompleteSpace RemarkSpace := closed_remark.completeSpace_coe
  haveI : SecondCountableTopology RemarkSpace := inferInstanceAs (SecondCountableTopology remarkSet)
  haveI : OrderClosedTopology RemarkSpace := by
    constructor
    change IsClosed {p : RemarkSpace × RemarkSpace |
      remarkRank (p.1 : remarkSet).val ≤ remarkRank (p.2 : remarkSet).val}
    exact isClosed_le (rank_continuous.comp continuous_fst) (rank_continuous.comp continuous_snd)
  refine ⟨closed_remark, inferInstance, inferInstance, inferInstance, ordering, ?_⟩
  intro h
  have hx : Tendsto RemarkSpace.x atTop (𝓝 RemarkSpace.z) := tendsto_subtype_rng.mpr x_limit
  have hy := h RemarkSpace.x RemarkSpace.y RemarkSpace.z
    (fun n => ⟨(ordering n).1.le, (ordering n).2.1.le⟩) hx
  have hc : Continuous (fun p : RemarkSpace => (p : remarkSet).val.2) := continuous_subtype_val.snd
  have hlim : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (0 : ℝ)) := hc.tendsto _ |>.comp hy
  have he := tendsto_nhds_unique tendsto_const_nhds hlim
  norm_num at he


#print axioms solution
