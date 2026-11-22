-- Prove2me | solution 1 for VectorValuedHolomorphy.exists_isCompact_tsupport_subset_of_isVonNBounded
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:03:29.946467+00:00
-- url     : https://prove2.me/submissions/d6dd1cf4-d6bf-4bf5-81e0-0d328d68f575

import Mathlib
import Definitions.Def_VectorValuedHolomorphy_CompactlySupportedInductiveLimit

open Filter Topology
open scoped CompactlySupported

set_option autoImplicit false

namespace Sol_VectorValuedHolomorphy_exists_isCompact_tsupport_subset_of_isVonNBounded

open Set

/-- In a paracompact space in which every point has a compact neighbourhood, a set contained in
no compact set contains a sequence that visits every compact set only finitely often. -/
theorem exists_seq_finite_preimage_of_not_subset_compact {X : Type*} [TopologicalSpace X]
    [WeaklyLocallyCompactSpace X] [ParacompactSpace X] {S : Set X}
    (hS : ∀ K : Set X, IsCompact K → ¬ S ⊆ K) :
    ∃ x : ℕ → X, (∀ n, x n ∈ S) ∧ ∀ K : Set X, IsCompact K → (x ⁻¹' K).Finite := by
  classical
  choose K hK hxK using fun x : X ↦ exists_compact_mem_nhds x
  obtain ⟨V, _, hcover, hloc, hVK⟩ :=
    precise_refinement (fun x ↦ interior (K x)) (fun _ ↦ isOpen_interior)
      (iUnion_eq_univ_iff.mpr fun x ↦ ⟨x, mem_interior_iff_mem_nhds.mpr (hxK x)⟩)
  let I := {i | (V i ∩ S).Nonempty}
  have hI : I.Infinite := by
    intro hfin
    apply hS (⋃ i ∈ I, K i) (hfin.isCompact_biUnion fun i _ ↦ hK i)
    intro y hy
    obtain ⟨i, hiy⟩ := iUnion_eq_univ_iff.mp hcover y
    exact mem_iUnion₂.mpr ⟨i, ⟨y, hiy, hy⟩, interior_subset (hVK i hiy)⟩
  let e := hI.natEmbedding I
  choose x hxV hxS using fun n : ℕ ↦ (e n).property
  refine ⟨x, hxS, fun L hL ↦ ?_⟩
  have hloc' := hloc.comp_injective (Subtype.val_injective.comp e.injective)
  exact (hloc'.finite_nonempty_inter_compact hL).subset fun n hn ↦ ⟨x n, hxV n, hn⟩

end Sol_VectorValuedHolomorphy_exists_isCompact_tsupport_subset_of_isVonNBounded

open VectorValuedHolomorphy Set in
theorem solution (𝕜 : Type*) [RCLike 𝕜] (X : Type*)
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [ParacompactSpace X] (E : Type*)
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E] (B : Set C_c(X, E))
    (hB : @Bornology.IsVonNBounded 𝕜 C_c(X, E) _ _ _ (compactlySupportedTopology 𝕜 X E) B) :
    ∃ K : Set X, IsCompact K ∧ ∀ f ∈ B, tsupport f ⊆ K := by
  classical
  by_contra hcon
  push Not at hcon
  let S := {x : X | ∃ f ∈ B, f x ≠ 0}
  have hS : ∀ K : Set X, IsCompact K → ¬ S ⊆ K := by
    intro K hK hSK
    obtain ⟨f, hf, hfK⟩ := hcon K hK
    apply hfK
    exact hK.isClosed.closure_subset_iff.mpr fun y hy => hSK ⟨f, hf, hy⟩
  obtain ⟨x, hxS, hx⟩ :=
    Sol_VectorValuedHolomorphy_exists_isCompact_tsupport_subset_of_isVonNBounded.exists_seq_finite_preimage_of_not_subset_compact hS
  choose f hf hfx using hxS
  -- a continuous seminorm on `E` which is at least `n` at `f n (x n)`
  have hsep : ∀ n : ℕ, ∃ q : Seminorm 𝕜 E, Continuous q ∧ (n : ℝ) ≤ q (f n (x n)) := by
    intro n
    obtain ⟨p, hp⟩ := (PolynormableSpace.withSeminorms 𝕜 E).separating_of_T1 _ (hfx n)
    have hpos : 0 < p.1 (f n (x n)) := lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm hp)
    let w : NNReal := ⟨(n : ℝ) / p.1 (f n (x n)), div_nonneg (Nat.cast_nonneg n) hpos.le⟩
    refine ⟨w • p.1, ?_, ?_⟩
    · exact (continuous_const.mul p.2 : Continuous (fun z => (w : ℝ) * p.1 z))
    · change (n : ℝ) ≤ ((n : ℝ) / p.1 (f n (x n))) * p.1 (f n (x n))
      rw [div_mul_cancel₀ _ hpos.ne']
  choose q hq hlarge using hsep
  -- the evaluation sequence of a compactly supported function has finite support
  have hfin : ∀ g : C_c(X, E), (Function.support fun n => q n (g (x n))).Finite := by
    intro g
    refine (hx _ g.hasCompactSupport).subset ?_
    intro n hn
    by_contra h
    apply hn
    simp only [image_eq_zero_of_notMem_tsupport h, map_zero]
  let Q : Seminorm 𝕜 C_c(X, E) := Seminorm.of (fun g => ∑ᶠ n, q n (g (x n)))
    (fun g h => by
      calc ∑ᶠ n, q n ((g + h) (x n)) ≤ ∑ᶠ n, (q n (g (x n)) + q n (h (x n))) := by
            refine finsum_le_finsum' (hfin (g + h)) (((hfin g).union (hfin h)).subset ?_) ?_
            · intro n hn
              by_contra h'
              simp only [mem_union, Function.mem_support, not_or, not_not] at h'
              apply hn
              simp only [h'.1, h'.2, add_zero]
            · intro n
              simp only [CompactlySupportedContinuousMap.add_apply]
              exact map_add_le_add _ _ _
        _ = ∑ᶠ n, q n (g (x n)) + ∑ᶠ n, q n (h (x n)) := finsum_add_distrib (hfin g) (hfin h))
    (fun a g => by
      simp only [CompactlySupportedContinuousMap.smul_apply, map_smul_eq_mul]
      exact (mul_finsum _ _).symm)
  have hQ : ∀ g : C_c(X, E), Q g = ∑ᶠ n, q n (g (x n)) := fun g => rfl
  -- `Q` is continuous on every `C(X, K; E)`
  have hQcont : ContinuousOnSupportedIn 𝕜 X E Q := by
    intro K hK
    let _ : TopologicalSpace {g : C_c(X, E) // tsupport g ⊆ K} :=
      TopologicalSpace.induced (fun g => (g.1 : C(X, E))) ContinuousMap.compactOpen
    let s := (hx K hK).toFinset
    have heq : ∀ g : {g : C_c(X, E) // tsupport g ⊆ K},
        Q g.1 = ∑ n ∈ s, q n (g.1 (x n)) := by
      intro g
      rw [hQ]
      apply finsum_eq_sum_of_support_subset
      intro n hn
      rw [Finite.coe_toFinset]
      by_contra h
      apply hn
      have : g.1 (x n) = 0 := image_eq_zero_of_notMem_tsupport fun h' => h (g.2 h')
      simp only [this, map_zero]
    have hc : Continuous fun g : {g : C_c(X, E) // tsupport g ⊆ K} =>
        ∑ n ∈ s, q n (g.1 (x n)) := by
      refine continuous_finsetSum _ fun n _ => (hq n).comp ?_
      have hev : Continuous fun g : {g : C_c(X, E) // tsupport g ⊆ K} =>
          ((g.1 : C(X, E)) : X → E) (x n) :=
        (continuous_eval_const (x n)).comp
          (continuous_induced_dom (f := fun g : {g : C_c(X, E) // tsupport g ⊆ K} =>
            (g.1 : C(X, E))))
      exact hev
    exact hc.congr fun g => (heq g).symm
  let _ : TopologicalSpace C_c(X, E) := compactlySupportedTopology 𝕜 X E
  have hW : WithSeminorms (compactlySupportedSeminormFamily 𝕜 X E) := ⟨rfl⟩
  obtain ⟨r, _, hr⟩ := hW.isVonNBounded_iff_seminorm_bounded.mp hB ⟨Q, hQcont⟩
  obtain ⟨n, hn⟩ := exists_nat_gt r
  have h1 : q n (f n (x n)) ≤ Q (f n) := by
    rw [hQ]
    exact single_le_finsum n (hfin (f n)) fun j => apply_nonneg _ _
  have h2 : Q (f n) < r := hr (f n) (hf n)
  linarith [hlarge n]
