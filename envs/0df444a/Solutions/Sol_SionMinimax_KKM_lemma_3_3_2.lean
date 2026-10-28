-- Prove2me | solution 2 for SionMinimax.KKM.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T03:03:06.734258+00:00
-- url     : https://prove2.me/submissions/e84de61b-85b5-4fa0-b91d-7ee9a4e8466c

import Mathlib
import Theorems.Thm_AGT_brouwer_fixed_point

-- carved verbatim out of submission 818ed08f-1f44-45cc-90a9-3239f8bb6e07, lines 1019-1029

section

open Fin.NatCast in
theorem simplex_core (n : ℕ) (A : Fin (n+1) → Set (Fin (n+1) → ℝ)) (hA : ∀ i, IsOpen (A i))
    (hcov : ∀ x ∈ stdSimplex ℝ (Fin (n+1)), ∃ i, x ∈ A i)
    (hC : ∀ i, Convex ℝ (stdSimplex ℝ (Fin (n+1)) \ A i))
    (hv : ∀ i j, i ≠ j → (Pi.single i 1 : Fin (n+1) → ℝ) ∉ A j) :
    ∃ x ∈ stdSimplex ℝ (Fin (n+1)), ∀ i, x ∈ A i := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨i, hi⟩ := hcov _ (single_mem_stdSimplex ℝ (0 : Fin 1))
    exact ⟨_, single_mem_stdSimplex ℝ (0 : Fin 1), fun j => by
      have hj : j = i := Fin.ext (by have := j.2; have := i.2; omega)
      rw [hj]; exact hi⟩
  have : Nontrivial (Fin (n+1)) := Fin.nontrivial_iff_two_le.2 (by omega)
  -- distance functions
  have hne : ∀ i, ((A i)ᶜ).Nonempty := by
    intro i
    obtain ⟨j, hj⟩ := exists_ne i
    exact ⟨_, hv j i hj⟩
  let φ : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ := fun i x => Metric.infDist x (A i)ᶜ
  have hφc : ∀ i, Continuous (φ i) := fun i => Metric.continuous_infDist_pt _
  have hφpos : ∀ i x, 0 < φ i x ↔ x ∈ A i := by
    intro i x
    have := (hA i).isClosed_compl.notMem_iff_infDist_pos (hne i) (x := x)
    simp only [Set.mem_compl_iff, not_not] at this
    exact this.symm
  have hφnn : ∀ i x, 0 ≤ φ i x := fun i x => Metric.infDist_nonneg
  let S : (Fin (n+1) → ℝ) → ℝ := fun x => ∑ i, φ i x
  have hSpos : ∀ x ∈ stdSimplex ℝ (Fin (n+1)), 0 < S x := by
    intro x hx
    obtain ⟨i, hi⟩ := hcov x hx
    exact lt_of_lt_of_le ((hφpos i x).2 hi)
      (Finset.single_le_sum (fun j _ => hφnn j x) (Finset.mem_univ i))
  let sh : Equiv.Perm (Fin (n+1)) := Equiv.subRight (1 : Fin (n+1))
  let T : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) := fun x i => φ (sh i) x / S x
  have hT : ∀ x ∈ stdSimplex ℝ (Fin (n+1)), T x ∈ stdSimplex ℝ (Fin (n+1)) := by
    intro x hx
    refine ⟨fun i => div_nonneg (hφnn _ _) (hSpos x hx).le, ?_⟩
    simp only [T]
    rw [← Finset.sum_div]
    have : ∑ i, φ (sh i) x = S x := Equiv.sum_comp sh (fun j => φ j x)
    rw [this, div_self (hSpos x hx).ne']
  have hTc : ContinuousOn T (stdSimplex ℝ (Fin (n+1))) := by
    refine continuousOn_pi.2 fun i => ?_
    refine ContinuousOn.div (hφc _).continuousOn ?_ (fun x hx => (hSpos x hx).ne')
    exact (continuous_finsetSum _ fun j _ => hφc j).continuousOn
  obtain ⟨x, hx, hfix⟩ := AGT.brouwer_fixed_point (convex_stdSimplex ℝ (Fin (n+1)))
    (isCompact_stdSimplex ℝ (Fin (n+1))) ⟨_, single_mem_stdSimplex ℝ (0 : Fin (n+1))⟩ T hTc hT
  -- face inclusion
  have hface : ∀ j, x j = 0 → x ∉ A j := by
    intro j hj hxA
    have hmem : x ∈ stdSimplex ℝ (Fin (n+1)) \ A j := by
      have hsum : ∑ k ∈ Finset.univ.erase j, x k = 1 := by
        rw [Finset.sum_erase _ hj]; exact hx.2
      have := (hC j).sum_mem (t := Finset.univ.erase j) (w := x) (z := fun k => (Pi.single k 1 : Fin (n+1) → ℝ))
        (fun k _ => hx.1 k) hsum (fun k hk => ⟨single_mem_stdSimplex ℝ k, hv k j (Finset.ne_of_mem_erase hk)⟩)
      convert this using 1
      funext m
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ j)]
      simp [Pi.single_apply, hj]
    exact hmem.2 hxA
  -- supports
  have hxi : ∀ i, x i = φ (sh i) x / S x := fun i => (congrFun hfix i).symm
  have hJ : ∀ j, x ∈ A j → x ∈ A (sh j) := by
    intro j hj
    have h1 : x j ≠ 0 := fun h => hface j h hj
    have h2 : 0 < x j := lt_of_le_of_ne (hx.1 j) (Ne.symm h1)
    rw [hxi j] at h2
    have := (div_pos_iff_of_pos_right (hSpos x hx)).1 h2
    exact (hφpos _ _).1 this
  have hall : ∀ k : ℕ, ∀ j, x ∈ A j → x ∈ A (j - (k : Fin (n+1))) := by
    intro k
    induction k with
    | zero => intro j hj; simpa using hj
    | succ k ih =>
      intro j hj
      have := hJ _ (ih j hj)
      have e : sh (j - (k : Fin (n+1))) = j - ((k+1 : ℕ) : Fin (n+1)) := by
        simp [sh, Equiv.subRight_apply, Nat.cast_succ, sub_sub]
      rw [e] at this; exact this
  obtain ⟨i0, hi0⟩ := hcov x hx
  refine ⟨x, hx, fun i => ?_⟩
  have := hall (i0 - i).val i0 hi0
  rwa [Fin.cast_val_eq_self, sub_sub_cancel] at this

theorem t31_strong {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (n : ℕ) (a : Fin (n + 1) → E)
    (A : Fin (n + 1) → Set E)
    (hA : ∀ i, IsOpen (A i))
    (hcov : convexHull ℝ (Set.range a) ⊆ ⋃ i, A i)
    (hconv : ∀ i, Convex ℝ (convexHull ℝ (Set.range a) \ A i))
    (hv : ∀ i j, i ≠ j → a i ∉ A j) :
    ∃ z ∈ convexHull ℝ (Set.range a), ∀ i, z ∈ A i := by
  classical
  let ψ : (Fin (n+1) → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ a
  have hψ : ∀ x, ψ x = ∑ i, x i • a i := fun x => by
    simp [ψ, Fintype.linearCombination_apply]
  have hψc : Continuous ψ := by
    have : (ψ : (Fin (n+1) → ℝ) → E) = fun x => ∑ i, x i • a i := funext hψ
    rw [this]
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  have hψS : ∀ x ∈ stdSimplex ℝ (Fin (n+1)), ψ x ∈ convexHull ℝ (Set.range a) := by
    intro x hx
    rw [hψ]
    exact (convex_convexHull ℝ _).sum_mem (fun i _ => hx.1 i) hx.2
      (fun i _ => subset_convexHull ℝ _ (Set.mem_range_self i))
  obtain ⟨x, hx, hxA⟩ := simplex_core n (fun i => ψ ⁻¹' A i) (fun i => (hA i).preimage hψc)
    (fun x hx => by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov (hψS x hx))
      exact ⟨i, hi⟩)
    (fun i => by
      have : stdSimplex ℝ (Fin (n+1)) \ ψ ⁻¹' A i
          = stdSimplex ℝ (Fin (n+1)) ∩ (ψ ⁻¹' (convexHull ℝ (Set.range a) \ A i)) := by
        ext x
        simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_preimage]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, hψS x h1, h2⟩
        · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      rw [this]
      exact (convex_stdSimplex ℝ (Fin (n+1))).inter ((hconv i).linear_preimage ψ))
    (fun i j hij => by
      have : ψ (Pi.single i 1) = a i := by
        rw [hψ]
        simp [Pi.single_apply]
      simp only [Set.mem_preimage, this]
      exact hv i j hij)
  exact ⟨ψ x, hψS x hx, fun i => hxA i⟩

theorem usc_open {E : Type*} [TopologicalSpace E] (M : Set E) (g : E → ℝ) (c : ℝ)
    (hu : UpperSemicontinuousOn g M) :
    ∃ V : Set E, IsOpen V ∧ ∀ z ∈ M, (z ∈ V ↔ g z < c) := by
  classical
  have h : ∀ z : E, ∃ U : Set E, IsOpen U ∧ (z ∈ M → g z < c → z ∈ U ∧ ∀ x ∈ U, x ∈ M → g x < c) := by
    intro z
    by_cases hz : z ∈ M ∧ g z < c
    · have := hu z hz.1 c hz.2
      obtain ⟨U, hU, hzU, hsub⟩ := mem_nhdsWithin.1 this
      exact ⟨U, hU, fun _ _ => ⟨hzU, fun x hx hxM => hsub ⟨hx, hxM⟩⟩⟩
    · exact ⟨∅, isOpen_empty, fun h1 h2 => (hz ⟨h1, h2⟩).elim⟩
  choose U hUo hU using h
  refine ⟨⋃ z ∈ {z | z ∈ M ∧ g z < c}, U z, isOpen_biUnion fun z _ => hUo z, fun z hz => ?_⟩
  constructor
  · intro hzV
    obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.1 hzV
    exact (hU w hw.1 hw.2).2 z hzw hz
  · intro hlt
    exact Set.mem_iUnion₂.2 ⟨z, ⟨hz, hlt⟩, (hU z hz hlt).1⟩

theorem l33_core {E ι : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (M : Set E) (hM : Convex ℝ M) (hne : M.Nonempty)
    (Y : Finset ι) (f : E → ι → ℝ) (c : ℝ)
    (hq : ∀ y ∈ Y, QuasiconcaveOn ℝ M (fun μ => f μ y))
    (hu : ∀ y ∈ Y, UpperSemicontinuousOn (fun μ => f μ y) M)
    (hP : ∀ μ ∈ M, ∃ y ∈ Y, f μ y < c)
    (hmin : ∀ Y' : Finset ι, Y' ⊂ Y → ¬ ∀ μ ∈ M, ∃ y ∈ Y', f μ y < c) :
    ∃ μ₀ ∈ M, ∀ y ∈ Y, f μ₀ y < c := by
  classical
  obtain ⟨m0, hm0⟩ := hne
  have hYne : Y.Nonempty := by
    obtain ⟨y, hy, _⟩ := hP m0 hm0
    exact ⟨y, hy⟩
  obtain ⟨n, hn⟩ : ∃ n, Y.card = n + 1 := ⟨Y.card - 1, by have := hYne.card_pos; omega⟩
  let e : Y ≃ Fin (n+1) := Finset.equivFinOfCardEq hn
  let y : Fin (n+1) → ι := fun i => (e.symm i : ι)
  have hyY : ∀ i, y i ∈ Y := fun i => (e.symm i).2
  have hyinj : Function.Injective y := by
    intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  have hyall : ∀ y' ∈ Y, ∃ i, y i = y' := fun y' hy' => ⟨e ⟨y', hy'⟩, by simp [y]⟩
  have hex : ∀ i, ∃ μ ∈ M, ∀ y' ∈ Y.erase (y i), c ≤ f μ y' := by
    intro i
    have := hmin (Y.erase (y i)) (Finset.erase_ssubset (hyY i))
    push_neg at this
    exact this
  choose μ hμM hμ using hex
  have hμi : ∀ i, f (μ i) (y i) < c := by
    intro i
    obtain ⟨y', hy', hlt⟩ := hP (μ i) (hμM i)
    by_cases h : y' = y i
    · rw [← h]; exact hlt
    · exact absurd hlt (not_lt.2 (hμ i y' (Finset.mem_erase.2 ⟨h, hy'⟩)))
  have hμj : ∀ i j, i ≠ j → c ≤ f (μ i) (y j) := by
    intro i j hij
    exact hμ i (y j) (Finset.mem_erase.2 ⟨fun h => hij (hyinj h).symm, hyY j⟩)
  have hV : ∀ i, ∃ V : Set E, IsOpen V ∧ ∀ z ∈ M, (z ∈ V ↔ f z (y i) < c) :=
    fun i => usc_open M _ c (hu (y i) (hyY i))
  choose V hVo hVM using hV
  have hhull : convexHull ℝ (Set.range μ) ⊆ M :=
    convexHull_min (by rintro _ ⟨i, rfl⟩; exact hμM i) hM
  obtain ⟨z, hzh, hz⟩ := t31_strong n μ V hVo
    (by
      intro z hz
      obtain ⟨y', hy', hlt⟩ := hP z (hhull hz)
      obtain ⟨i, rfl⟩ := hyall y' hy'
      exact Set.mem_iUnion.2 ⟨i, (hVM i z (hhull hz)).2 hlt⟩)
    (fun i => by
      have : convexHull ℝ (Set.range μ) \ V i
          = convexHull ℝ (Set.range μ) ∩ {z ∈ M | c ≤ f z (y i)} := by
        ext z
        simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, hhull h1, ?_⟩
          by_contra h
          exact h2 ((hVM i z (hhull h1)).2 (not_le.1 h))
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, fun h => absurd ((hVM i z h2).1 h) (not_lt.2 h3)⟩
      rw [this]
      exact (convex_convexHull ℝ _).inter (hq (y i) (hyY i) c))
    (fun i j hij hmem => by
      have := (hVM j (μ i) (hμM i)).1 hmem
      exact absurd (hμj i j hij) (not_le.2 this))
  refine ⟨z, hhull hzh, fun y' hy' => ?_⟩
  obtain ⟨i, rfl⟩ := hyall y' hy'
  exact (hVM i z (hhull hzh)).1 (hz i)

theorem solution {E ι : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (M : Set E) (hM : Convex ℝ M) (hne : M.Nonempty)
    (Y : Finset ι) (f : E → ι → ℝ) (c : ℝ)
    (hq : ∀ y ∈ Y, QuasiconcaveOn ℝ M (fun μ => f μ y))
    (hu : ∀ y ∈ Y, UpperSemicontinuousOn (fun μ => f μ y) M)
    (hP : ∀ μ ∈ M, ∃ y ∈ Y, f μ y < c)
    (hmin : ∀ Y' : Finset ι, Y' ⊂ Y → ¬ ∀ μ ∈ M, ∃ y ∈ Y', f μ y < c) :
    ∃ μ₀ ∈ M, ∀ y ∈ Y, f μ₀ y < c := by
  exact l33_core M hM hne Y f c hq hu hP hmin

end
