-- Prove2me | solution 1 for RiemannMasullo.isAcyclicSystem_of_strict_frechet
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:40:56.273688+00:00
-- url     : https://prove2.me/submissions/57023fcc-74d4-4242-8128-caf36112aba3

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec1.lean#L531-L688
import Theorems.Thm_RiemannMasullo_exists_seminorm_extension
import Theorems.Thm_RiemannMasullo_sum_le_directSumSeminorm
import Theorems.Thm_RiemannMasullo_directSumSeminorm_apply
import Theorems.Thm_RiemannMasullo_directSumSeminorm_lof
import Theorems.Thm_RiemannMasullo_directSumDifference_apply
import Definitions.Def_RiemannMasullo_AppC_InductiveLimits

open RiemannMasullo
open Set Filter Topology TopologicalSpace Bornology
open scoped Pointwise DirectSum
variable {E : Type*} [AddCommGroup E] [Module ℂ E] [tE : TopologicalSpace E]
variable {X : ℕ → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
  [∀ k, TopologicalSpace (X k)]

private theorem exists_strictSystem_seminorms
    [∀ k, IsTopologicalAddGroup (X k)] [∀ k, PolynormableSpace ℂ (X k)]
    (j : ∀ k, X k →L[ℂ] X (k+1)) (hj : ∀ k, IsEmbedding (j k))
    (p : ∀ k, Seminorm ℂ (X k)) (hp : ∀ k, Continuous (p k)) :
    ∃ r : ∀ k, Seminorm ℂ (X k), (∀ k, Continuous (r k)) ∧
      ∀ k, (r (k+1)).comp (j k).toLinearMap = r k + p k := by
  choose next hnext hcomp using fun k (s : {s : Seminorm ℂ (X k) // Continuous s}) ↦
    exists_seminorm_extension (f := (j k).toLinearMap) (hj k).isInducing
      (show Continuous (s.val + p k) from s.property.add (hp k))
  let r : ∀ k, {s : Seminorm ℂ (X k) // Continuous s} :=
    Nat.rec ⟨0, continuous_const⟩ (fun k s ↦ ⟨next k s, hnext k s⟩)
  exact ⟨fun k ↦ (r k).val, fun k ↦ (r k).property, fun k ↦ hcomp k (r k)⟩

/-- The difference coordinates after a cutoff bound the input seminorms from the cutoff on.
The restriction identity makes the successive triangle inequalities telescope. -/
private theorem directSumDifference_tail_bound
    (j : ∀ k, X k →L[ℂ] X (k+1)) (p r : ∀ k, Seminorm ℂ (X k))
    (hr : ∀ k, (r (k+1)).comp (j k).toLinearMap = r k + p k)
    (x : ⨁ k, X k) (a : ℕ) [∀ (k : ℕ) (z : X k), Decidable (z ≠ 0)] :
    directSumSeminorm (fun k ↦ if a ≤ k then p k else 0) x + r a (x a) ≤
      directSumSeminorm (fun k ↦ if a < k then r k else 0) (directSumDifference j x) := by
  obtain ⟨b, hb⟩ := Finset.exists_nat_subset_range (insert a x.support)
  have hab : a ≤ b := Nat.le_of_lt (Finset.mem_range.mp (hb (Finset.mem_insert_self _ _)))
  have hs : x.support ⊆ Finset.range b := fun _ hk ↦ hb (Finset.mem_insert_of_mem hk)
  have hxb : x b = 0 := DFinsupp.notMem_support_iff.mp fun h ↦
    (Nat.lt_irrefl b) (Finset.mem_range.mp (hs h))
  let y := directSumDifference j x
  have hstep (k : ℕ) : r k (x k) + p k (x k) ≤ r (k+1) (y (k+1)) + r (k+1) (x (k+1)) := by
    have heq := DFunLike.congr_fun (hr k) (x k)
    change r (k+1) (j k (x k)) = r k (x k) + p k (x k) at heq
    have hdiff : j k (x k) - x (k+1) = -(y (k+1)) := by
      change _ = -(directSumDifference j x (k+1))
      rw [(directSumDifference_apply j x).2 k, neg_sub]
    rw [← heq, add_comm (r (k+1) (y (k+1)))]
    simpa only [hdiff, map_neg_eq_map] using le_map_add_map_sub (r (k+1)) (j k (x k)) (x (k+1))
  have hsum (n : ℕ) (hn : a ≤ n) :
      (∑ k ∈ Finset.Ico a n, p k (x k)) + r a (x a) ≤
        (∑ k ∈ Finset.Ico a n, r (k+1) (y (k+1))) + r n (x n) := by
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top hn, Finset.sum_Ico_succ_top hn]
      linarith only [ih, hstep n]
  have hinput : directSumSeminorm (fun k ↦ if a ≤ k then p k else 0) x =
      ∑ k ∈ Finset.Ico a b, p k (x k) := by
    rw [directSumSeminorm_apply _ _ _ hs]
    simp only [DFunLike.ite_apply, zero_apply, ← Finset.sum_filter]
    congr 1
    ext k
    simp [and_comm]
  have houtput : (∑ k ∈ Finset.Ico a b, r (k+1) (y (k+1))) ≤
      directSumSeminorm (fun k ↦ if a < k then r k else 0) y := by
    rw [Finset.sum_Ico_add' (fun k ↦ r k (y k)) a b 1]
    refine le_trans ?_ (sum_le_directSumSeminorm _ y (Finset.Ico (a+1) (b+1)))
    apply Finset.sum_le_sum
    intro k hk
    simp only [if_pos (Nat.lt_of_succ_le (Finset.mem_Ico.mp hk).1), le_refl]
  rw [hinput]
  exact (hsum b hab).trans (by simpa only [hxb, map_zero, add_zero] using houtput)

theorem solution (hX : ∀ k, IsFrechetTVS (X k))
    (j : ∀ k, X k →L[ℂ] X (k+1)) (hj : ∀ k, IsEmbedding (j k)) : IsAcyclicSystem j := by
  let _ : ∀ (k : ℕ) (z : X k), Decidable (z ≠ 0) := fun _ _ ↦ Classical.propDecidable _
  choose hadd hpoly hmetric _ using hX
  let _ : ∀ k, IsTopologicalAddGroup (X k) := hadd
  let _ : ∀ k, PolynormableSpace ℂ (X k) := hpoly
  let _ : ∀ k, MetrizableSpace (X k) := hmetric
  let D := ⨁ k, X k
  let lof := DirectSum.lof ℂ ℕ X
  let _ : TopologicalSpace D := locallyConvexFinalTopology lof
  let P : SeminormFamily ℂ D {p : Seminorm ℂ D // ∀ k, Continuous (p ∘ lof k)} := Subtype.val
  have hP : WithSeminorms P := ⟨rfl⟩
  let _ : IsTopologicalAddGroup D := hP.topologicalAddGroup
  let _ : PolynormableSpace ℂ D := hP.toPolynormableSpace
  have hlof (k : ℕ) : Continuous (lof k) :=
    hP.continuous_of_continuous_comp _ fun p ↦ p.property k
  have hcontinuous {F : Type _} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
      [PolynormableSpace ℂ F] (f : D →ₗ[ℂ] F) (hf : ∀ k, Continuous (f ∘ lof k)) :
      Continuous f := by
    apply (PolynormableSpace.withSeminorms ℂ F).continuous_of_continuous_comp
    intro p
    exact hP.continuous_seminorm ⟨p.val.comp f, fun k ↦ p.property.comp (hf k)⟩
  have htailContinuous (a : ℕ) (r : ∀ k, Seminorm ℂ (X k)) (hr : ∀ k, Continuous (r k)) :
      Continuous (directSumSeminorm (fun k ↦ if a < k then r k else 0)) := by
    let s (k : ℕ) : Seminorm ℂ (X k) := if a < k then r k else 0
    refine hP.continuous_seminorm ⟨directSumSeminorm s, fun k ↦ ?_⟩
    have heq : (fun z : X k ↦ directSumSeminorm s (lof k z)) = (s k : X k → ℝ) :=
      funext fun z ↦ directSumSeminorm_lof s k z
    change Continuous (fun z : X k ↦ directSumSeminorm s (lof k z))
    rw [heq]
    dsimp only [s]
    split
    · exact hr k
    · exact continuous_zero
  let σ : D →ₗ[ℂ] D := directSumDifference j
  have hσ : Continuous σ := by
    apply hcontinuous
    intro k
    have heq (z : X k) : σ (lof k z) = lof k z - lof (k+1) (j k z) := by
      change directSumDifference j (DirectSum.lof ℂ ℕ X k z) = _
      rw [directSumDifference, LinearMap.sub_apply, LinearMap.id_apply, DirectSum.toModule_lof]
      rfl
    change Continuous (fun z : X k ↦ σ (lof k z))
    simp_rw [heq]
    exact (hlof k).sub ((hlof (k+1)).comp (j k).continuous)
  let coordinate (k : ℕ) : D →ₗ[ℂ] X k := DirectSum.component ℂ ℕ X k
  have hcoordinate (k : ℕ) : Continuous (coordinate k) := by
    apply hcontinuous
    intro i
    by_cases h : i = k
    · subst i
      have heq : coordinate k ∘ lof k = id :=
        funext fun z ↦ DirectSum.component.lof_self ℂ k z
      rw [heq]
      exact continuous_id
    · have hz : coordinate k ∘ lof i = fun _ ↦ 0 :=
        funext fun z ↦ (DirectSum.component.of ℂ k i z).trans (dif_neg h)
      rw [hz]
      exact continuous_const
  let partialSum : ∀ k, D →L[ℂ] X k :=
    Nat.rec ⟨coordinate 0, hcoordinate 0⟩
      (fun k f ↦ (j k).comp f + ⟨coordinate (k+1), hcoordinate (k+1)⟩)
  have hpartialSum (x : D) (k : ℕ) : partialSum k (σ x) = x k := by
    induction k with
    | zero => exact (directSumDifference_apply j x).1
    | succ k ih =>
      change j k (partialSum k (σ x)) + σ x (k+1) = x (k+1)
      rw [ih, (directSumDifference_apply j x).2 k, add_sub_cancel]
  have hinj : Function.Injective σ := fun x y h ↦ DFinsupp.ext fun k ↦ by
    rw [← hpartialSum x k, h, hpartialSum y k]
  change IsClosedEmbedding σ
  constructor
  · let e := LinearEquiv.ofInjective σ hinj
    have he : Continuous e := hσ.subtype_mk _
    have heInv : Continuous e.symm := by
      apply hP.continuous_of_continuous_comp
      intro p
      -- Bound the inverse pullback of each generating seminorm by a continuous seminorm.
      let s (k : ℕ) : Seminorm ℂ (X k) := p.val.comp (lof k)
      obtain ⟨r, hr, hrcomp⟩ := exists_strictSystem_seminorms j hj s p.property
      let q := directSumSeminorm (fun k ↦ if 0 < k then r k else 0)
      have hq : Continuous q := htailContinuous 0 r hr
      have hqsub : Continuous (q.comp σ.range.subtype) := hq.comp continuous_subtype_val
      refine Seminorm.continuous_of_le hqsub fun y ↦ ?_
      let x := e.symm y
      have hx : σ x = (y : D) := congrArg Subtype.val (e.apply_symm_apply y)
      change p.val x ≤ q (y : D)
      rw [← hx]
      have hbound : directSumSeminorm s x ≤ q (σ x) := by
        have hb := directSumDifference_tail_bound j s r hrcomp x 0
        simp only [Nat.zero_le, ite_true] at hb
        exact (le_add_of_nonneg_right (apply_nonneg (r 0) (x 0))).trans hb
      refine le_trans ?_ hbound
      rw [directSumSeminorm_apply _ _ x.support (Finset.Subset.refl _)]
      have hsum := @norm_sum_le ℕ D p.val.toAddGroupSeminorm.toSeminormedAddCommGroup
        x.support (fun k ↦ lof k (x k))
      change p.val (∑ k ∈ x.support, lof k (x k)) ≤ ∑ k ∈ x.support, p.val (lof k (x k)) at hsum
      have hdecomp : (∑ k ∈ x.support, lof k (x k)) = x := DirectSum.sum_support_of x
      rwa [hdecomp] at hsum
    let homeo : D ≃ₜ σ.range := ⟨e.toEquiv, he, heInv⟩
    exact IsEmbedding.subtypeVal.comp homeo.isEmbedding
  · rw [← closure_subset_iff_isClosed]
    intro y hy
    obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range y.support
    -- Every tail seminorm starting after the support vanishes on y.
    have hzero : partialSum n y = 0 := by
      by_contra hne
      obtain ⟨p, hp⟩ := (PolynormableSpace.withSeminorms ℂ (X n)).separating_of_T1 _ hne
      let s (k : ℕ) : Seminorm ℂ (X k) := Pi.single (M := fun k ↦ Seminorm ℂ (X k)) n p.val k
      have hs (k : ℕ) : Continuous (s k) := by
        by_cases h : k = n
        · subst k
          simpa only [s, Pi.single_eq_same] using p.property
        · have hsk : s k = 0 := Pi.single_eq_of_ne h _
          rw [hsk]
          exact continuous_zero
      obtain ⟨r, hr, hrcomp⟩ := exists_strictSystem_seminorms j hj s hs
      let q := directSumSeminorm (fun k ↦ if n < k then r k else 0)
      have hq : Continuous q := htailContinuous n r hr
      have hclosed : IsClosed {z : D | p.val (partialSum n z) ≤ q z} :=
        isClosed_le (p.property.comp (partialSum n).continuous) hq
      have hle : p.val (partialSum n y) ≤ q y := hclosed.closure_subset_iff.mpr (by
        rintro _ ⟨x, rfl⟩
        change p.val (partialSum n (σ x)) ≤ q (σ x)
        rw [hpartialSum]
        have hx := sum_le_directSumSeminorm (fun k ↦ if n ≤ k then s k else 0) x {n}
        simp only [Finset.sum_singleton, le_refl, ite_true, s, Pi.single_eq_same] at hx
        exact hx.trans ((le_add_of_nonneg_right (apply_nonneg (r n) (x n))).trans
          (directSumDifference_tail_bound j s r hrcomp x n))) hy
      have hqy : q y = 0 := by
        rw [directSumSeminorm_apply _ _ _ hn]
        apply Finset.sum_eq_zero
        intro k hk
        simp [not_lt_of_ge (Finset.mem_range.mp hk).le]
      exact hp (le_antisymm (hle.trans_eq hqy) (apply_nonneg p.val _))
    have htail (k : ℕ) (hk : n ≤ k) : partialSum k y = 0 := by
      induction k, hk using Nat.le_induction with
      | base => exact hzero
      | succ k hk ih =>
        have hky : y (k+1) = 0 := DFinsupp.notMem_support_iff.mp fun hm ↦
          (Nat.not_lt_of_ge (Nat.le_succ_of_le hk)) (Finset.mem_range.mp (hn hm))
        change j k (partialSum k y) + y (k+1) = 0
        rw [ih, map_zero, hky, add_zero]
    let x : D := DFinsupp.mk (Finset.range n) (fun k ↦ partialSum k y)
    have hx (k : ℕ) : x k = partialSum k y := by
      change (DFinsupp.mk (Finset.range n) (fun k ↦ partialSum k y)) k = _
      rw [DFinsupp.mk_apply]
      split
      · rfl
      · exact (htail k (Nat.le_of_not_gt fun h ↦ ‹k ∉ Finset.range n›
          (Finset.mem_range.mpr h))).symm
    refine ⟨x, DFinsupp.ext fun k ↦ ?_⟩
    cases k with
    | zero => exact (directSumDifference_apply j x).1.trans (hx 0)
    | succ k =>
      rw [(directSumDifference_apply j x).2 k, hx, hx]
      change j k (partialSum k y) + y (k+1) - j k (partialSum k y) = y (k+1)
      exact add_sub_cancel_left _ _

