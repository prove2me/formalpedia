-- Prove2me | solution 1 for WhitneyEmbedding.compact_weak_embedding
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T11:46:14.108712+00:00
-- url     : https://prove2.me/submissions/1a94868a-1473-4de3-b8d2-2e59990666d7

/-
Compact weak Whitney embedding, with the exact smoothness/embedding/immersion triple.
The secant and tangent projection argument follows MIT 18.965 Lecture 14,
Theorem 15.1 and Lemma 15.2. Hausdorff dimension replaces the small-dimensional
case of Sard: chart images of C1 maps cannot increase dimension.
-/
import Mathlib
open Function Filter Module Set Topology
open scoped Manifold ContDiff
noncomputable section

private theorem dimH_image_le_finrank_of_contDiffAt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {s : Set E} (hf : ∀ x ∈ s, ContDiffAt ℝ 1 f x) :
    dimH (f '' s) ≤ finrank ℝ E := by
  calc
    dimH (f '' s) ≤ dimH s := dimH_image_le_of_locally_lipschitzOn fun x hx => by
      obtain ⟨K, t, ht, hK⟩ := (hf x hx).exists_lipschitzOnWith
      exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩
    _ ≤ dimH (univ : Set E) := dimH_mono (subset_univ _)
    _ = finrank ℝ E := Real.dimH_univ_eq_finrank E

private theorem slope_of_projection_zero
    {F : Type*} [AddCommGroup F] [Module ℝ F]
    (v : F) (z : F × ℝ) (hz : z ≠ 0) (hp : z.1 - z.2 • v = 0) :
    z.2 ≠ 0 ∧ z.2⁻¹ • z.1 = v := by
  have he : z.1 = z.2 • v := sub_eq_zero.mp hp
  have h2 : z.2 ≠ 0 := by
    intro h
    apply hz
    ext
    · simpa [h] using he
    · exact h
  exact ⟨h2, by rw [he, inv_smul_smul₀ h2]⟩

private theorem avoid_secants_tangents
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [Countable ι]
    (U : ι → Set E) (f : ι → E → F × ℝ)
    (hU : ∀ i, IsOpen (U i)) (hf : ∀ i, ContDiffOn ℝ 2 (f i) (U i))
    (hdim : 2 * finrank ℝ E < finrank ℝ F) :
    ∃ v : F,
      (∀ i j, ∀ x ∈ U i, ∀ y ∈ U j,
        f i x - f j y ≠ 0 →
          (f i x - f j y).1 - (f i x - f j y).2 • v ≠ 0) ∧
      (∀ i, ∀ x ∈ U i, ∀ w : E,
        fderiv ℝ (f i) x w ≠ 0 →
          (fderiv ℝ (f i) x w).1 - (fderiv ℝ (f i) x w).2 • v ≠ 0) := by
  let sec (i j : ι) (p : E × E) : F × ℝ := f i p.1 - f j p.2
  let tan (i : ι) (p : E × E) : F × ℝ := fderiv ℝ (f i) p.1 p.2
  let S (i j : ι) : Set (E × E) := {p | p.1 ∈ U i ∧ p.2 ∈ U j ∧ (sec i j p).2 ≠ 0}
  let T (i : ι) : Set (E × E) := {p | p.1 ∈ U i ∧ (tan i p).2 ≠ 0}
  let slope (z : F × ℝ) : F := z.2⁻¹ • z.1
  have hsec (i j : ι) : dimH ((slope ∘ sec i j) '' S i j) ≤
      (2 * finrank ℝ E : ℕ) := by
    have h := dimH_image_le_finrank_of_contDiffAt (s := S i j)
      (f := slope ∘ sec i j) (fun p hp => ?_)
    · simpa [Module.finrank_prod, two_mul, Nat.cast_add] using h
    have hfi := ((hf i).contDiffAt ((hU i).mem_nhds hp.1)).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    have hfj := ((hf j).contDiffAt ((hU j).mem_nhds hp.2.1)).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    have hs : ContDiffAt ℝ 1 (sec i j) p :=
      (hfi.comp p contDiffAt_fst).sub (hfj.comp p contDiffAt_snd)
    exact (hs.snd.inv hp.2.2).smul hs.fst
  have htan (i : ι) : dimH ((slope ∘ tan i) '' T i) ≤
      (2 * finrank ℝ E : ℕ) := by
    have h := dimH_image_le_finrank_of_contDiffAt (s := T i)
      (f := slope ∘ tan i) (fun p hp => ?_)
    · simpa [Module.finrank_prod, two_mul, Nat.cast_add] using h
    have hfi : ContDiffAt ℝ 1 (fderiv ℝ (f i)) p.1 :=
      ((hf i).contDiffAt ((hU i).mem_nhds hp.1)).fderiv_right (by norm_num)
    have ht : ContDiffAt ℝ 1 (tan i) p :=
      (hfi.comp p contDiffAt_fst).clm_apply contDiffAt_snd
    exact (ht.snd.inv hp.2).smul ht.fst
  let B : Set F := (⋃ i, ⋃ j, (slope ∘ sec i j) '' S i j) ∪
    (⋃ i, (slope ∘ tan i) '' T i)
  have hB : dimH B ≤ (2 * finrank ℝ E : ℕ) := by
    simp only [B, dimH_union, dimH_iUnion, max_le_iff, iSup_le_iff]
    exact ⟨hsec, htan⟩
  obtain ⟨v, hv⟩ := (dense_compl_of_dimH_lt_finrank
    (hB.trans_lt (Nat.cast_lt.mpr hdim))).nonempty
  refine ⟨v, ?_, ?_⟩
  · intro i j x hx y hy hne hp
    obtain ⟨h2, hs⟩ := slope_of_projection_zero v (f i x - f j y) hne hp
    apply hv
    exact Or.inl (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j,
      ⟨(x, y), ⟨hx, hy, h2⟩, hs⟩⟩⟩)
  · intro i x hx w hne hp
    obtain ⟨h2, hs⟩ := slope_of_projection_zero v (fderiv ℝ (f i) x w) hne hp
    apply hv
    exact Or.inr (mem_iUnion.mpr ⟨i, ⟨(x, w), ⟨hx, h2⟩, hs⟩⟩)



set_option backward.isDefEq.respectTransparency false in
private theorem exists_projection_injective_immersion
    {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [SecondCountableTopology M]
    (e : M → F × ℝ) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F × ℝ) ∞ e)
    (hei : Injective e) (hed : ∀ x, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F × ℝ) e x))
    (hdim : 2 * finrank ℝ E < finrank ℝ F) :
    ∃ P : (F × ℝ) →L[ℝ] F,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (P ∘ e) ∧ Injective (P ∘ e) ∧
      ∀ x, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (P ∘ e) x) := by
  obtain ⟨c, hc, hcover⟩ := countable_cover_nhds (fun x : M => chart_source_mem_nhds E x)
  have : Countable c := hc.to_subtype
  let U (i : c) : Set E := (extChartAt 𝓘(ℝ, E) i.1).target
  let f (i : c) : E → F × ℝ := e ∘ (extChartAt 𝓘(ℝ, E) i.1).symm
  have hf (i : c) : ContDiffOn ℝ 2 (f i) (U i) := by
    exact ((he.comp_contMDiffOn (contMDiffOn_extChartAt_symm i.1 )).contDiffOn).of_le (by decide)
  obtain ⟨v, hsec, htan⟩ := avoid_secants_tangents U f
    (fun i => isOpen_extChartAt_target i.1) hf hdim
  let P : (F × ℝ) →L[ℝ] F := ContinuousLinearMap.fst ℝ F ℝ -
    (ContinuousLinearMap.toSpanSingleton ℝ v).comp (ContinuousLinearMap.snd ℝ F ℝ)
  have hP (z : F × ℝ) : P z = z.1 - z.2 • v := rfl
  have hcov (x : M) : ∃ i : c, x ∈ (extChartAt 𝓘(ℝ, E) i.1).source := by
    have hx : x ∈ ⋃ i ∈ c, (chartAt E i).source := by rw [hcover]; trivial
    obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp hx
    exact ⟨⟨i, hi⟩, by simpa only [extChartAt_source] using hx⟩
  have hsmooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (P ∘ e) := P.contMDiff.comp he
  refine ⟨P, hsmooth, ?_, ?_⟩
  · intro x y hxy
    obtain ⟨i, hix⟩ := hcov x
    obtain ⟨j, hjy⟩ := hcov y
    by_contra hne
    have hexy : f i (extChartAt 𝓘(ℝ, E) i.1 x) -
        f j (extChartAt 𝓘(ℝ, E) j.1 y) = e x - e y := by
      simp only [f, comp_apply, (extChartAt 𝓘(ℝ, E) i.1).left_inv hix,
        (extChartAt 𝓘(ℝ, E) j.1).left_inv hjy]
    have hz := hsec i j _ ((extChartAt 𝓘(ℝ, E) i.1).map_source hix)
      _ ((extChartAt 𝓘(ℝ, E) j.1).map_source hjy)
    rw [hexy] at hz
    apply hz (sub_ne_zero.mpr (fun h => hne (hei h)))
    change P (e x - e y) = 0
    rw [map_sub, sub_eq_zero]
    exact hxy
  · intro x
    apply (injective_iff_map_eq_zero (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (P ∘ e) x)).mpr
    intro w hw
    obtain ⟨i, hix⟩ := hcov x
    let a := extChartAt 𝓘(ℝ, E) i.1
    have ha : a x ∈ a.target := a.map_source hix
    let w' := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) a x w
    have hcomp : fderiv ℝ (f i) (a x) w' = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F × ℝ) e x w := by
      have hsym : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) a.symm (a x) :=
        ((contMDiffOn_extChartAt_symm (n := ∞) i.1) _ ha).contMDiffAt
          ((isOpen_extChartAt_target i.1).mem_nhds ha) |>.mdifferentiableAt (by simp)
      have hd : fderiv ℝ (f i) (a x) =
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F × ℝ) e x).comp
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) a.symm (a x)) := by
        have hd0 : fderiv ℝ (f i) (a x) =
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F × ℝ) e (a.symm (a x))).comp
              (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) a.symm (a x)) := by
          exact (mfderiv_eq_fderiv (f := f i)).symm.trans
            (mfderiv_comp_of_eq (he.mdifferentiable (by simp) x) hsym (a.left_inv hix))
        have hde : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F × ℝ) e (a.symm (a x)) : E →L[ℝ] F × ℝ) =
            mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F × ℝ) e x :=
          by
            let D : M → (E →L[ℝ] F × ℝ) := fun y => by
              exact mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F × ℝ) e y
            exact congrArg D (a.left_inv hix)
        exact hd0.trans (congrArg (fun L : E →L[ℝ] F × ℝ => L.comp
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) a.symm (a x))) hde)
      rw [hd]
      change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F × ℝ) e x)
        ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) a.symm (a x)) w') = _
      have hi := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
        (I := 𝓘(ℝ, E)) (x := i.1) (y := x) hix
      simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hi
      have hiw := DFunLike.congr_fun hi w
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) a.symm (a x) w' = w at hiw
      rw [hiw]
    have hpzero : P (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F × ℝ) e x w) = 0 := by
      rwa [mfderiv_comp _ (P.mdifferentiable _) (he.mdifferentiable (by simp) _),
        P.mfderiv_eq] at hw
    have hzero : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F × ℝ) e x w = 0 := by
      by_contra hne
      have h := htan i (a x) ha w'
      rw [hcomp] at h
      exact h hne hpzero
    exact (hed x) (hzero.trans (map_zero _).symm)


private theorem linear_postcompose_injective_immersion
    {E V W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [TopologicalSpace M] [ChartedSpace E M]
    (e : M → V) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ e)
    (hei : Injective e) (hed : ∀ x, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, V) e x))
    (L : V →L[ℝ] W) (hL : Injective L) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, W) ∞ (L ∘ e) ∧ Injective (L ∘ e) ∧
      ∀ x, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, W) (L ∘ e) x) := by
  refine ⟨L.contMDiff.comp he, hL.comp hei, fun x => ?_⟩
  rw [mfderiv_comp _ (L.mdifferentiable _) (he.mdifferentiable (by simp) _), L.mfderiv_eq]
  exact hL.comp (hed x)

private theorem reduce_ambient (n N : ℕ)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [SecondCountableTopology M]
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 n) (𝓡 N) ∞ e)
    (hei : Injective e) (hed : ∀ x, Injective (mfderiv (𝓡 n) (𝓡 N) e x)) :
    ∃ g : M → EuclideanSpace ℝ (Fin (2 * n + 1)),
      ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ g ∧ Injective g ∧
      ∀ x, Injective (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) g x) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hN : N ≤ 2 * n + 1
    · let A : (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin (2 * n + 1 - N))) ≃L[ℝ]
          EuclideanSpace ℝ (Fin (2 * n + 1)) :=
        ContinuousLinearEquiv.ofFinrankEq (by
          simp only [Module.finrank_prod, finrank_euclideanSpace_fin]
          omega)
      let L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n + 1)) :=
        A.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ _ _)
      refine ⟨L ∘ e, linear_postcompose_injective_immersion e he hei hed L ?_⟩
      exact A.injective.comp (fun _ _ h => congrArg Prod.fst h)
    · cases N with
      | zero => omega
      | succ k =>
        let A : EuclideanSpace ℝ (Fin (k + 1)) ≃L[ℝ] (EuclideanSpace ℝ (Fin k) × ℝ) :=
          ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
        obtain ⟨hAe, hAi, hAd⟩ := linear_postcompose_injective_immersion e he hei hed
          A.toContinuousLinearMap A.injective
        obtain ⟨P, hPe, hPi, hPd⟩ := exists_projection_injective_immersion (A ∘ e)
          hAe hAi hAd (by
            simp only [finrank_euclideanSpace_fin]
            omega)
        exact ih k (Nat.lt_succ_self k) (P ∘ A ∘ e) hPe hPi hPd

theorem solution (n : ℕ)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * n + 1)),
      ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ e ∧ IsClosedEmbedding e ∧
      ∀ x, Injective (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) e x) := by
  obtain ⟨N, e, he, hei, hed⟩ := exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  obtain ⟨g, hg, hgi, hgd⟩ := reduce_ambient n N e he hei.injective hed
  exact ⟨g, hg, hg.continuous.isClosedEmbedding hgi, hgd⟩

#print axioms solution
