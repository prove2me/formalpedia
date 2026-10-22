-- Prove2me | solution 1 for WhitneyEmbedding.exists_uniform_dim_immersion_on_compacts
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T02:58:15.389977+00:00
-- url     : https://prove2.me/submissions/1f2f36be-5938-4f6f-b3f5-a98a95526919

import Mathlib

open Function Filter Module Set Topology
open MeasureTheory
open scoped Manifold ContDiff

namespace WhitneyUniformAux

/-- The image of an open set under a map differentiable on it, from a space of dimension
smaller than `N`, is Lebesgue-null in `ℝ^N`. -/
theorem null_image {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    {N : ℕ} (h : A → EuclideanSpace ℝ (Fin N)) {U : Set A} (hU : IsOpen U)
    (hd : DifferentiableOn ℝ h U) (hdim : finrank ℝ A < N) :
    volume (h '' U) = 0 := by
  let C := EuclideanSpace ℝ (Fin (N - finrank ℝ A))
  have hrank : finrank ℝ (A × C) = finrank ℝ (EuclideanSpace ℝ (Fin N)) := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]; omega
  let L : (A × C) ≃L[ℝ] EuclideanSpace ℝ (Fin N) := ContinuousLinearEquiv.ofFinrankEq hrank
  let S : Submodule ℝ (EuclideanSpace ℝ (Fin N)) :=
    (LinearMap.range (LinearMap.inl ℝ A C)).map (L : (A × C) →ₗ[ℝ] EuclideanSpace ℝ (Fin N))
  have hS : S ≠ ⊤ := by
    intro hS
    have hpos : 0 < N - finrank ℝ A := by omega
    let c : C := EuclideanSpace.single ⟨0, hpos⟩ 1
    have hc : c ≠ 0 := by
      intro h0
      have := congrArg (fun z : C => z ⟨0, hpos⟩) h0
      simp [c] at this
    have hmem : L (0, c) ∈ S := hS ▸ Submodule.mem_top
    obtain ⟨y, ⟨a, rfl⟩, hy⟩ := hmem
    have h2 := L.injective hy
    simp only [LinearMap.inl_apply, Prod.mk.injEq] at h2
    exact hc h2.2.symm
  have hsub : L '' (U ×ˢ {0}) ⊆ (S : Set (EuclideanSpace ℝ (Fin N))) := by
    rintro _ ⟨⟨a, c⟩, ⟨-, hc⟩, rfl⟩
    simp only [mem_singleton_iff] at hc
    subst hc
    exact ⟨(a, 0), ⟨a, rfl⟩, rfl⟩
  have hnull : volume (L '' (U ×ˢ {0})) = 0 :=
    measure_mono_null hsub (Measure.addHaar_submodule volume S hS)
  let f : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) := fun z => h (L.symm z).1
  have himg : f '' (L '' (U ×ˢ {0})) = h '' U := by
    ext z
    constructor
    · rintro ⟨_, ⟨⟨a, c⟩, ⟨ha, -⟩, rfl⟩, rfl⟩
      exact ⟨a, ha, by simp [f]⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨L (a, 0), ⟨(a, 0), ⟨ha, rfl⟩, rfl⟩, by simp [f]⟩
  rw [← himg]
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ hnull
  rintro _ ⟨⟨a, c⟩, ⟨ha, -⟩, rfl⟩
  have h1 : DifferentiableAt ℝ h (L.symm (L (a, c))).1 := by
    simpa using hd.differentiableAt (hU.mem_nhds ha)
  have h2 : DifferentiableAt ℝ (fun z => (L.symm z).1) (L (a, c)) :=
    ((ContinuousLinearMap.fst ℝ A C).comp (L.symm : EuclideanSpace ℝ (Fin N) →L[ℝ] A × C)).differentiableAt
  exact (h1.comp (L (a, c)) h2).differentiableWithinAt

section PiTangent

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [T2Space M] [Fintype ι] {s : Set M} (f : SmoothBumpCovering ι I M s)

open SmoothBumpCovering


/-- Smooth embedding of `M` into `(E × ℝ) ^ ι`. -/
noncomputable def embPT : C^∞⟮I, M; 𝓘(ℝ, ι → E × ℝ), ι → E × ℝ⟯ where
  val x i := (f i x • extChartAt I (f.c i) x, f i x)
  property :=
    contMDiff_pi_space.2 fun i =>
      ((f i).contMDiff_smul contMDiffOn_extChartAt).prodMk_space (f i).contMDiff

@[local simp]
theorem embPT_coe :
    ⇑(embPT f) = fun x i => (f i x • extChartAt I (f.c i) x, f i x) :=
  (rfl)

theorem embPT_injOn : InjOn (embPT f) s := by
  intro x hx y _ h
  simp only [embPT_coe, funext_iff] at h
  obtain ⟨h₁, h₂⟩ := Prod.mk_inj.1 (h (f.ind x hx))
  rw [f.apply_ind x hx] at h₂
  rw [← h₂, f.apply_ind x hx, one_smul, one_smul] at h₁
  have := f.mem_extChartAt_source_of_eq_one h₂.symm
  exact (extChartAt I (f.c _)).injOn (f.mem_extChartAt_ind_source x hx) this h₁

theorem comp_embPT_mfderiv (x : M) (hx : x ∈ s) :
    ((ContinuousLinearMap.fst ℝ E ℝ).comp
            (@ContinuousLinearMap.proj ℝ _ ι (fun _ => E × ℝ) _ _ (fun _ => inferInstance)
              (f.ind x hx))).comp
        (mfderiv I 𝓘(ℝ, ι → E × ℝ) (embPT f) x) =
      mfderiv% (chartAt H (f.c (f.ind x hx))) x := by
  set L :=
    (ContinuousLinearMap.fst ℝ E ℝ).comp
      (@ContinuousLinearMap.proj ℝ _ ι (fun _ => E × ℝ) _ _ (fun _ => inferInstance) (f.ind x hx))
  have := L.hasMFDerivAt.comp x
    ((embPT f).contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt
  convert! hasMFDerivAt_unique this _
  refine (hasMFDerivAt_extChartAt (f.mem_chartAt_ind_source x hx)).congr_of_eventuallyEq ?_
  refine (f.eventuallyEq_one x hx).mono fun y hy => ?_
  simp only [L, embPT_coe, ContinuousLinearMap.coe_comp, (· ∘ ·),
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.proj_apply]
  rw [hy, Pi.one_apply, one_smul]

theorem embPT_ker_mfderiv (x : M) (hx : x ∈ s) :
    (mfderiv I 𝓘(ℝ, ι → E × ℝ) (embPT f) x).ker = ⊥ := by
  apply bot_unique
  rw [← (mdifferentiable_chart (f.c (f.ind x hx))).ker_mfderiv_eq_bot
      (f.mem_chartAt_ind_source x hx),
    ← comp_embPT_mfderiv f]
  exact LinearMap.ker_le_ker_comp _ _

theorem embPT_injective_mfderiv (x : M) (hx : x ∈ s) :
    Injective (mfderiv I 𝓘(ℝ, ι → E × ℝ) (embPT f) x) :=
  LinearMap.ker_eq_bot.1 (embPT_ker_mfderiv f x hx)

end PiTangent

variable (n : ℕ) {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]

/-- A smooth map into `ℝ^N` which is injective on `K` and an immersion at points of `K`. -/
def Good (K : Set M) (N : ℕ) : Prop :=
  ∃ g : M → EuclideanSpace ℝ (Fin N), ContMDiff (𝓡 n) (𝓡 N) ∞ g ∧ InjOn g K ∧
    ∀ x ∈ K, Injective (mfderiv (𝓡 n) (𝓡 N) g x)

theorem good_comp (K : Set M) {N N' : ℕ}
    (L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N'))
    (g : M → EuclideanSpace ℝ (Fin N)) (hg : ContMDiff (𝓡 n) (𝓡 N) ∞ g)
    (hinj : InjOn (L ∘ g) K)
    (himm : ∀ x ∈ K, ∀ w, L (mfderiv (𝓡 n) (𝓡 N) g x w) = 0 → w = 0) : Good n K N' := by
  refine ⟨L ∘ g, L.contMDiff.comp hg, hinj, fun x hx => ?_⟩
  rw [mfderiv_comp x L.mdifferentiableAt (hg.mdifferentiableAt (by simp)), L.mfderiv_eq]
  intro w₁ w₂ hw
  refine sub_eq_zero.mp (himm x hx _ ?_)
  exact (congrArg L (map_sub (mfderiv (𝓡 n) (𝓡 N) g x) w₁ w₂)).trans
    ((map_sub L _ _).trans (sub_eq_zero.mpr hw))

theorem pad (K : Set M) {N N' : ℕ} (hNN : N ≤ N') : Good n K N → Good n K N' := by
  rintro ⟨g, hg, hinj, himm⟩
  let C := EuclideanSpace ℝ (Fin (N' - N))
  have hrank : finrank ℝ (EuclideanSpace ℝ (Fin N) × C) =
      finrank ℝ (EuclideanSpace ℝ (Fin N')) := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin,
      finrank_euclideanSpace_fin]; omega
  let Lq : (EuclideanSpace ℝ (Fin N) × C) ≃L[ℝ] EuclideanSpace ℝ (Fin N') :=
    ContinuousLinearEquiv.ofFinrankEq hrank
  let L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N') :=
    (Lq : _ →L[ℝ] _).comp (ContinuousLinearMap.inl ℝ _ C)
  have hL : Injective L := by
    intro a b hab
    have := Lq.injective hab
    simpa using this
  refine good_comp n K L g hg (hL.comp_injOn hinj) (fun x hx w hw => himm x hx ?_)
  rw [map_zero]
  exact hL (hw.trans (map_zero L).symm)

theorem reduce (K : Set M) (hK : IsCompact K) (N : ℕ) (hN : 2 * n + 1 ≤ N)
    (hgood : Good n K (N + 1)) : Good n K N := by
  obtain ⟨g, hg, hinj, himm⟩ := hgood
  obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover
    (fun x => (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (fun x _ => chart_source_mem_nhds _ x)
  let φ : M → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) := fun a =>
    chartAt (EuclideanSpace ℝ (Fin n)) a
  let hh : M → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (N + 1)) := fun a =>
    g ∘ (φ a).symm
  have hhC : ∀ a, ContDiffOn ℝ ∞ (hh a) (φ a).target := fun a =>
    contMDiffOn_iff_contDiffOn.1 (hg.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓡 n)))
  have hhDa : ∀ a, ∀ u ∈ (φ a).target, DifferentiableAt ℝ (hh a) u := fun a u hu =>
    ((hhC a).differentiableOn (by simp)).differentiableAt ((φ a).open_target.mem_nhds hu)
  have hhFa : ∀ a, ∀ u ∈ (φ a).target, DifferentiableAt ℝ (fun y => fderiv ℝ (hh a) y) u :=
    fun a u hu => (((hhC a).fderiv_of_isOpen (φ a).open_target (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableOn
      (by simp)).differentiableAt ((φ a).open_target.mem_nhds hu)
  let σ : M × M → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ →
      EuclideanSpace ℝ (Fin (N + 1)) := fun p q => q.2.2 • (hh p.1 q.1 - hh p.2 q.2.1)
  let τ : M → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin (N + 1)) := fun a q => fderiv ℝ (hh a) q.1 q.2
  let Sec := ⋃ p ∈ (t ×ˢ t : Set (M × M)),
    σ p '' ((φ p.1).target ×ˢ (φ p.2).target ×ˢ univ)
  let Tan := ⋃ a ∈ (t : Set M), τ a '' ((φ a).target ×ˢ univ)
  have hSec : volume Sec = 0 := by
    refine (measure_biUnion_null_iff ((t.finite_toSet.prod t.finite_toSet).countable)).2 ?_
    intro p _
    refine null_image _ ((φ p.1).open_target.prod ((φ p.2).open_target.prod isOpen_univ)) ?_ ?_
    · intro q hq
      have h1 := hhDa p.1 q.1 hq.1
      have h2 := hhDa p.2 q.2.1 hq.2.1
      refine DifferentiableAt.differentiableWithinAt ?_
      have h1' : DifferentiableAt ℝ (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ =>
          hh p.1 q.1) q :=
        DifferentiableAt.comp (g := hh p.1) (f := fun q => q.1) q h1 differentiableAt_fst
      have h2' : DifferentiableAt ℝ (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ =>
          hh p.2 q.2.1) q := by
        have hf : DifferentiableAt ℝ
            (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ => q.2.1) q := by
          fun_prop
        exact DifferentiableAt.comp (g := hh p.2) (f := fun q => q.2.1) q h2 hf
      have h3 : DifferentiableAt ℝ (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ =>
          q.2.2) q := by fun_prop
      exact h3.smul (h1'.sub h2')
    · simp only [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self]
      omega
  have hTan : volume Tan = 0 := by
    refine (measure_biUnion_null_iff t.finite_toSet.countable).2 ?_
    intro a _
    refine null_image _ ((φ a).open_target.prod isOpen_univ) ?_ ?_
    · intro q hq
      have h1 := hhFa a q.1 hq.1
      refine DifferentiableAt.differentiableWithinAt ?_
      exact DifferentiableAt.clm_apply (h1.comp q differentiableAt_fst) differentiableAt_snd
    · simp only [Module.finrank_prod, finrank_euclideanSpace_fin]
      omega
  have hBad : volume (Sec ∪ Tan ∪ {0}) = 0 :=
    measure_union_null (measure_union_null hSec hTan) (measure_singleton _)
  obtain ⟨v, hv⟩ : ∃ v, v ∉ Sec ∪ Tan ∪ {0} := by
    by_contra hcon
    push Not at hcon
    rw [eq_univ_of_forall hcon] at hBad
    exact (NeZero.ne (volume : Measure (EuclideanSpace ℝ (Fin (N + 1)))))
      (Measure.measure_univ_eq_zero.mp hBad)
  have hv0 : v ≠ 0 := fun h => hv (Or.inr h)
  let P : Submodule ℝ (EuclideanSpace ℝ (Fin (N + 1))) := ℝ ∙ v
  have hfr : finrank ℝ (EuclideanSpace ℝ (Fin (N + 1)) ⧸ P) =
      finrank ℝ (EuclideanSpace ℝ (Fin N)) := by
    have := Submodule.finrank_quotient_add_finrank P
    rw [finrank_span_singleton hv0, finrank_euclideanSpace_fin] at this
    rw [finrank_euclideanSpace_fin]
    omega
  let e := LinearEquiv.ofFinrankEq _ _ hfr
  let π : EuclideanSpace ℝ (Fin (N + 1)) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
    LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ P.mkQ)
  have hπ : ∀ w, π w = 0 → ∃ c : ℝ, w = c • v := by
    intro w hw
    have h1 : P.mkQ w = 0 := e.injective (by
      rw [map_zero]
      exact hw)
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton] at h1
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, hc.symm⟩
  refine good_comp n K π g hg ?_ ?_
  · intro x hx y hy hxy
    obtain ⟨c, hc⟩ := hπ (g x - g y) (by
      rw [map_sub]
      exact sub_eq_zero.mpr hxy)
    by_cases hc0 : c = 0
    · subst hc0
      rw [zero_smul] at hc
      exact hinj hx hy (sub_eq_zero.mp hc)
    · exfalso
      obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp (hcov hx)
      obtain ⟨b, hb, hyb⟩ := mem_iUnion₂.mp (hcov hy)
      apply hv
      refine Or.inl (Or.inl (mem_iUnion₂.mpr ⟨(a, b), mk_mem_prod ha hb,
        ((φ a) x, (φ b) y, c⁻¹), ⟨(φ a).map_source hxa, (φ b).map_source hyb, trivial⟩, ?_⟩))
      simp only [σ, hh, comp_apply, (φ a).left_inv hxa, (φ b).left_inv hyb, hc, smul_smul,
        inv_mul_cancel₀ hc0, one_smul]
  · intro x hx w hw
    obtain ⟨c, hc⟩ := hπ _ hw
    by_contra hw0
    by_cases hc0 : c = 0
    · subst hc0
      rw [zero_smul] at hc
      exact hw0 (himm x hx (hc.trans (map_zero _).symm))
    · obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp (hcov hx)
      have heq : g =ᶠ[𝓝 x] hh a ∘ φ a := by
        filter_upwards [(φ a).open_source.mem_nhds hxa] with y hy
        simp only [hh, comp_apply, (φ a).left_inv hy]
      have hφ : MDifferentiableAt (𝓡 n) (𝓡 n) (φ a) x :=
        mdifferentiableAt_atlas (chart_mem_atlas _ a) hxa
      have hhm : MDifferentiableAt (𝓡 n) (𝓡 (N + 1)) (hh a) (φ a x) :=
        (hhDa a _ ((φ a).map_source hxa)).mdifferentiableAt
      have hchain : mfderiv (𝓡 n) (𝓡 (N + 1)) g x =
          (fderiv ℝ (hh a) (φ a x)).comp (mfderiv (𝓡 n) (𝓡 n) (φ a) x) := by
        rw [heq.mfderiv_eq, mfderiv_comp x hhm hφ, mfderiv_eq_fderiv]; rfl
      apply hv
      refine Or.inl (Or.inr (mem_iUnion₂.mpr ⟨a, ha,
        ((φ a) x, mfderiv (𝓡 n) (𝓡 n) (φ a) x (c⁻¹ • w)), ⟨(φ a).map_source hxa, trivial⟩, ?_⟩))
      show fderiv ℝ (hh a) (φ a x) (mfderiv (𝓡 n) (𝓡 n) (φ a) x (c⁻¹ • w)) = v
      have h5 : mfderiv (𝓡 n) (𝓡 (N + 1)) g x (c⁻¹ • w) = v := by
        have h6 : c⁻¹ • (c • v) = v := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
        rw [map_smul, hc]
        exact h6
      rw [hchain] at h5
      exact h5

theorem reduce_all (K : Set M) (hK : IsCompact K) :
    ∀ k : ℕ, Good n K (2 * n + 1 + k) → Good n K (2 * n + 1) := by
  intro k
  induction k with
  | zero => exact id
  | succ k ih => exact fun h => ih (reduce n K hK (2 * n + 1 + k) (by omega) h)

theorem exists_good [T2Space M] [SecondCountableTopology M] (K : Set M) (hK : IsCompact K) :
    ∃ N, Good n K N := by
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  have : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  rcases SmoothBumpCovering.exists_isSubordinate (𝓡 n) hK.isClosed (fun x _ => univ_mem) with
    ⟨ι, f, -⟩
  have hfin : Finite ι := by
    have h := f.locallyFinite.finite_nonempty_inter_compact hK
    exact Set.finite_univ_iff.mp
      (h.subset fun i _ => ⟨f.c i, (f i).c_mem_support, f.c_mem' i⟩)
  cases nonempty_fintype ι
  let F := EuclideanSpace ℝ (Fin <| finrank ℝ (ι → EuclideanSpace ℝ (Fin n) × ℝ))
  let eEF : (ι → EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] F :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  refine ⟨_, eEF ∘ embPT f,
    eEF.toDiffeomorph.contMDiff.comp (embPT f).contMDiff,
    eEF.injective.comp_injOn (embPT_injOn f), fun x hx => ?_⟩
  rw [mfderiv_comp _ eEF.differentiableAt.mdifferentiableAt
      ((embPT f).contMDiff.mdifferentiableAt (by simp)),
    eEF.mfderiv_eq]
  exact eEF.injective.comp (embPT_injective_mfderiv f _ hx)

end WhitneyUniformAux

theorem solution (n : ℕ)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M] :
    ∃ m : ℕ, ∀ K : Set M, IsCompact K →
      ∃ g : M → EuclideanSpace ℝ (Fin m),
        ContMDiff (𝓡 n) (𝓡 m) ∞ g ∧ InjOn g K ∧
        ∀ x ∈ K, Injective (mfderiv (𝓡 n) (𝓡 m) g x) := by
  refine ⟨2 * n + 1, fun K hK => ?_⟩
  obtain ⟨N, hN⟩ := WhitneyUniformAux.exists_good n K hK
  exact WhitneyUniformAux.reduce_all n K hK N
    (WhitneyUniformAux.pad n K (by omega : N ≤ 2 * n + 1 + N) hN)
