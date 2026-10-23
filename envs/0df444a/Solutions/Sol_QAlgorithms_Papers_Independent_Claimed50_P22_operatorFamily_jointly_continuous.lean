-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P22.operatorFamily_jointly_continuous
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:20:09.169984+00:00
-- url     : https://prove2.me/submissions/79e0202d-f545-4cd4-9dff-beeb1d0ebc67

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P22

open Set Filter Topology

universe u v w

namespace X6P22J

/-- Uniform (equicontinuity) estimate for a sequence of operators which is pointwise
bounded, on a Baire domain. -/
lemma equicont
    {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [BaireSpace F]
    {V : Type w} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    (T : ℕ → (F →L[ℝ] V))
    (hbdd : ∀ g : F, Bornology.IsVonNBounded ℝ (Set.range fun n => T n g))
    (W : Set V) (hW : W ∈ 𝓝 (0 : V)) :
    ∃ U ∈ 𝓝 (0 : F), ∀ n, ∀ g ∈ U, T n g ∈ W := by
  obtain ⟨W1, hW1, hW1W⟩ := exists_nhds_zero_half hW
  obtain ⟨W', ⟨hW'n, hW'cl, hW'bal⟩, hW'W1⟩ := (nhds_basis_closed_balanced ℝ V).mem_iff.1 hW1
  let E : Set F := ⋂ n, (T n) ⁻¹' W'
  have hEcl : IsClosed E := isClosed_iInter fun n => hW'cl.preimage (T n).continuous
  let S : ℕ → Set F := fun k => (fun g => ((k : ℝ) + 1)⁻¹ • g) ⁻¹' E
  have hScl : ∀ k, IsClosed (S k) := fun k => hEcl.preimage (continuous_const_smul _)
  have hScov : (⋃ k, S k) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro g
    obtain ⟨r, hr⟩ := absorbs_iff_norm.1 (hbdd g hW'n)
    obtain ⟨k, hk⟩ := exists_nat_ge r
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    simp only [S, E, Set.mem_preimage, Set.mem_iInter]
    intro n
    have hk' : r ≤ ‖((k : ℝ) + 1)‖ := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith
    have := hr _ hk' (Set.mem_range_self n)
    obtain ⟨w, hw, hw'⟩ := Set.mem_smul_set.1 this
    rw [map_smul, ← hw', smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
    exact hw
  obtain ⟨k, hk⟩ := nonempty_interior_of_iUnion_of_closed hScl hScov
  obtain ⟨g0, hg0⟩ := hk
  set c : ℝ := (k : ℝ) + 1
  have hc : c ≠ 0 := by positivity
  let U : Set F := (fun g => c • g + g0) ⁻¹' interior (S k)
  have hU : U ∈ 𝓝 (0 : F) := by
    have hcont : ContinuousAt (fun g : F => c • g + g0) 0 := by fun_prop
    exact hcont.preimage_mem_nhds (isOpen_interior.mem_nhds (by simpa using hg0))
  refine ⟨U, hU, fun n g hg => ?_⟩
  have h1 : T n (c⁻¹ • (c • g + g0)) ∈ W' := by
    have := interior_subset hg
    simp only [S, E, Set.mem_preimage, Set.mem_iInter] at this
    exact this n
  have h2 : T n (c⁻¹ • g0) ∈ W' := by
    have := interior_subset hg0
    simp only [S, E, Set.mem_preimage, Set.mem_iInter] at this
    exact this n
  have h3 : -T n (c⁻¹ • g0) ∈ W' := (hW'bal.neg_mem_iff).2 h2
  have := hW1W _ (hW'W1 h1) _ (hW'W1 h3)
  rwa [smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul, map_add, add_neg_cancel_right] at this

end X6P22J

open X6P22J in
theorem solution
    {X : Type u} [TopologicalSpace X] [FirstCountableTopology X]
    {F : Type v} [AddCommGroup F] [Module ℝ F] [UniformSpace F]
    [IsUniformAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
    [T2Space F] [TopologicalSpace.MetrizableSpace F] [CompleteSpace F]
    {V : Type w} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    (alpha : X → (F →L[ℝ] V))
    (hPointwise : ∀ f : F, Continuous (fun x => alpha x f)) :
    Continuous (fun p : X × F => alpha p.1 p.2) := by
  have : (uniformity F).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : BaireSpace F := inferInstance
  rw [continuous_iff_seqContinuous]
  rintro u ⟨x, f⟩ hu
  have hx : Tendsto (fun n => (u n).1) atTop (𝓝 x) := (continuous_fst.tendsto _).comp hu
  have hf : Tendsto (fun n => (u n).2) atTop (𝓝 f) := (continuous_snd.tendsto _).comp hu
  let T : ℕ → (F →L[ℝ] V) := fun n => alpha (u n).1
  have hT : ∀ g, Tendsto (fun n => T n g) atTop (𝓝 (alpha x g)) := fun g =>
    ((hPointwise g).tendsto x).comp hx
  have hbdd : ∀ g : F, Bornology.IsVonNBounded ℝ (Set.range fun n => T n g) := fun g =>
    (hT g).isVonNBounded_range ℝ
  have hdiff : Tendsto (fun n => T n ((u n).2 - f)) atTop (𝓝 0) := by
    intro W hW
    obtain ⟨U, hU, hUW⟩ := equicont T hbdd W hW
    have : Tendsto (fun n => (u n).2 - f) atTop (𝓝 0) := by
      simpa using hf.sub_const f
    rw [Filter.mem_map]
    filter_upwards [Filter.mem_map.1 (this hU)] with n hn
    exact hUW n _ hn
  have := hdiff.add (hT f)
  simp only [zero_add] at this
  refine this.congr fun n => ?_
  simp only [T, Function.comp, map_sub, sub_add_cancel]
