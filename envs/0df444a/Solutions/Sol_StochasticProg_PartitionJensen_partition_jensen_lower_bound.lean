-- Prove2me | solution 1 for StochasticProg.PartitionJensen.partition_jensen_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T21:53:14.162241+00:00
-- url     : https://prove2.me/submissions/c93305cb-b073-4429-ab97-608972dd7a0d

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace PJAux

/-- Subgradient of a convex function at an interior point of its (convex) domain. -/
theorem subgrad_interior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {C : Set E} {g : E → ℝ} (hg : ConvexOn ℝ C g) {m : E}
    (hm : m ∈ interior C) :
    ∃ φ : StrongDual ℝ E, ∀ y ∈ C, g m + φ (y - m) ≤ g y := by
  set U : Set (E × ℝ) := (interior C ×ˢ Set.univ) ∩ (fun p => p.2 - g p.1) ⁻¹' Set.Ioi 0 with hU
  have hUo : IsOpen U := by
    refine ContinuousOn.isOpen_inter_preimage ?_ (isOpen_interior.prod isOpen_univ) isOpen_Ioi
    refine continuous_snd.continuousOn.sub ?_
    exact hg.continuousOn_interior.comp continuous_fst.continuousOn
      (fun p hp => (Set.mem_prod.1 hp).1)
  have hUc : Convex ℝ U := by
    rw [convex_iff_forall_pos]
    rintro p ⟨⟨hp1, -⟩, hp2⟩ q ⟨⟨hq1, -⟩, hq2⟩ a b ha hb hab
    simp only [Set.mem_preimage, Set.mem_Ioi, sub_pos] at hp2 hq2
    refine ⟨⟨hg.1.interior hp1 hq1 ha.le hb.le hab, Set.mem_univ _⟩, ?_⟩
    simp only [Set.mem_preimage, Set.mem_Ioi, sub_pos, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have h1 := hg.2 (interior_subset hp1) (interior_subset hq1) ha.le hb.le hab
    simp only [smul_eq_mul] at h1
    have h2 : a * g p.1 < a * p.2 := mul_lt_mul_of_pos_left hp2 ha
    have h3 : b * g q.1 < b * q.2 := mul_lt_mul_of_pos_left hq2 hb
    linarith
  have hnot : (m, g m) ∉ U := by
    rintro ⟨-, h⟩
    simp at h
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hUc hUo hnot
  set c : ℝ := f (0, 1) with hc
  set φ0 : StrongDual ℝ E := f.comp (ContinuousLinearMap.inl ℝ E ℝ) with hφ0
  have hdec : ∀ (y : E) (t : ℝ), f (y, t) = φ0 y + t * c := by
    intro y t
    have : ((y, t) : E × ℝ) = (y, 0) + t • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
    rfl
  have hcneg : c < 0 := by
    have hmem : (m, g m + 1) ∈ U := by
      refine ⟨⟨hm, Set.mem_univ _⟩, ?_⟩
      simp
    have := hf _ hmem
    rw [hdec, hdec] at this
    linarith
  set φ : StrongDual ℝ E := (-c)⁻¹ • φ0 with hφ
  have hφapp : ∀ y, φ (y - m) = (φ0 m - φ0 y) / c := by
    intro y
    rw [hφ, smul_apply, map_sub, smul_eq_mul]
    have hc0 : c ≠ 0 := hcneg.ne
    field_simp
    ring
  have hint : ∀ y ∈ interior C, g m + φ (y - m) ≤ g y := by
    intro y hy
    rw [hφapp]
    by_contra hcon
    push Not at hcon
    set K := g m + (φ0 m - φ0 y) / c with hK
    have hmem : (y, K) ∈ U := by
      refine ⟨⟨hy, Set.mem_univ _⟩, ?_⟩
      simp only [Set.mem_preimage, Set.mem_Ioi, sub_pos]
      exact hcon
    have := hf _ hmem
    rw [hdec, hdec] at this
    have hc0 : c ≠ 0 := hcneg.ne
    have hKc : K * c = g m * c + (φ0 m - φ0 y) := by
      rw [hK, add_mul, div_mul_cancel₀ _ hc0]
    linarith
  refine ⟨φ, fun y hy => ?_⟩
  have hz : (1 / 2 : ℝ) • m + (1 / 2 : ℝ) • y ∈ interior C :=
    hg.1.combo_interior_closure_mem_interior hm (subset_closure hy) (by norm_num) (by norm_num)
      (by norm_num)
  have h1 := hint _ hz
  have h2 := hg.2 (interior_subset hm) hy (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hzm : (1 / 2 : ℝ) • m + (1 / 2 : ℝ) • y - m = (1 / 2 : ℝ) • (y - m) := by
    module
  rw [hzm, map_smul, smul_eq_mul] at h1
  simp only [smul_eq_mul] at h2
  linarith

/-- A nonzero functional bounded above on `C` by its value at `m`, when `m ∉ interior C`
and `C` is nonempty and `ν`-full. -/
theorem exists_support_functional {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (ν : Measure E)
    [IsProbabilityMeasure ν] (hint : Integrable (fun y => y) ν) {C : Set E} (hC : Convex ℝ C)
    (hCν : ν Cᶜ = 0) (hm : (∫ y, y ∂ν) ∉ interior C) :
    ∃ φ : StrongDual ℝ E, φ ≠ 0 ∧ ∀ y ∈ C, φ y ≤ φ (∫ y, y ∂ν) := by
  set m := ∫ y, y ∂ν with hmdef
  have hCae : ∀ᵐ y ∂ν, y ∈ C := ae_iff.2 (measure_mono_null (fun y hy => hy) hCν)
  have hCne : C.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [hcon, Set.compl_empty] at hCν
    simp at hCν
  by_cases hne : (interior C).Nonempty
  · obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hC.interior isOpen_interior hm
    refine ⟨f, ?_, ?_⟩
    · rintro rfl
      obtain ⟨a, ha⟩ := hne
      simpa using hf a ha
    · intro y hy
      have hcl : y ∈ closure (interior C) := by
        rw [hC.closure_interior_eq_closure_of_nonempty_interior hne]
        exact subset_closure hy
      have : closure (interior C) ⊆ {a | f a ≤ f m} :=
        closure_minimal (fun a ha => (hf a ha).le) (isClosed_le f.continuous continuous_const)
      exact this hcl
  · have hspan : affineSpan ℝ C ≠ ⊤ := fun h =>
      hne (hC.interior_nonempty_iff_affineSpan_eq_top.2 h)
    have hdir : (affineSpan ℝ C).direction ≠ ⊤ := by
      intro h
      apply hspan
      rwa [AffineSubspace.direction_eq_top_iff_of_nonempty] at h
      exact hCne.mono (subset_affineSpan ℝ C)
    obtain ⟨f, hf0, hfk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hdir)
    let φ : StrongDual ℝ E := LinearMap.toContinuousLinearMap f
    obtain ⟨c0, hc0⟩ := hCne
    have hconst : ∀ y ∈ C, φ y = φ c0 := by
      intro y hy
      have hd : y -ᵥ c0 ∈ (affineSpan ℝ C).direction :=
        AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ C hy) (subset_affineSpan ℝ C hc0)
      have := hfk hd
      rw [LinearMap.mem_ker, vsub_eq_sub, map_sub] at this
      change f y = f c0
      linarith
    have hφm : φ m = φ c0 := by
      rw [hmdef, ← ContinuousLinearMap.integral_comp_comm φ hint]
      rw [integral_congr_ae (hCae.mono fun y hy => hconst y hy)]
      simp
    refine ⟨φ, ?_, fun y hy => by rw [hconst y hy, hφm]⟩
    intro h
    apply hf0
    ext v
    have := congrArg (fun F : StrongDual ℝ E => F v) h
    simpa [φ] using this

/-- Jensen with a supporting affine minorant, by strong induction on the dimension. -/
theorem jensen_affine (n : ℕ) : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E], Module.finrank ℝ E = n →
    ∀ (ν : Measure E) [IsProbabilityMeasure ν], Integrable (fun y => y) ν →
    ∀ (C : Set E) (g : E → ℝ), ν Cᶜ = 0 → ConvexOn ℝ C g →
    (∫ y, y ∂ν) ∈ C ∧ ∃ φ : StrongDual ℝ E,
      ∀ᵐ y ∂ν, g (∫ y, y ∂ν) + φ (y - ∫ y, y ∂ν) ≤ g y := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E _ _ _ _ _ hn ν _ hint C g hCν hg
  set m := ∫ y, y ∂ν with hmdef
  have hCae : ∀ᵐ y ∂ν, y ∈ C := ae_iff.2 (measure_mono_null (fun y hy => hy) hCν)
  by_cases hm : m ∈ interior C
  · obtain ⟨φ, hφ⟩ := subgrad_interior hg hm
    exact ⟨interior_subset hm, φ, hCae.mono fun y hy => hφ y hy⟩
  obtain ⟨φ, hφ0, hφC⟩ := exists_support_functional ν hint hg.1 hCν hm
  -- `φ = φ m` almost everywhere
  have hφint : ∫ y, φ y ∂ν = φ m := by
    rw [hmdef, ContinuousLinearMap.integral_comp_comm φ hint]
  have hH : ∀ᵐ y ∂ν, φ y = φ m := by
    have hnn : 0 ≤ᵐ[ν] fun y => φ m - φ y :=
      hCae.mono fun y hy => sub_nonneg.2 (hφC y hy)
    have hfi : Integrable (fun y => φ m - φ y) ν :=
      (integrable_const _).sub (φ.integrable_comp hint)
    have h0 : ∫ y, (φ m - φ y) ∂ν = 0 := by
      rw [integral_sub (integrable_const _) (φ.integrable_comp hint), hφint]
      simp
    have := (integral_eq_zero_iff_of_nonneg_ae hnn hfi).1 h0
    exact this.mono fun y hy => by simp only [Pi.zero_apply, sub_eq_zero] at hy; exact hy.symm
  -- a vector with `φ w0 = 1`
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφ0 (ContinuousLinearMap.ext hcon)
  set w0 : E := (φ v)⁻¹ • v with hw0
  have hφw0 : φ w0 = 1 := by
    rw [hw0, map_smul, smul_eq_mul, inv_mul_cancel₀ hv]
  set W : Submodule ℝ E := LinearMap.ker (φ : E →ₗ[ℝ] ℝ) with hW
  have hWlt : Module.finrank ℝ W < n := by
    rw [← hn]
    apply Submodule.finrank_lt
    intro htop
    apply hv
    have : v ∈ W := by rw [htop]; exact Submodule.mem_top
    exact this
  set P0 : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - φ.smulRight w0 with hP0
  have hP0mem : ∀ y, P0 y ∈ W := by
    intro y
    simp [hW, hP0, hφw0]
  set P : E →L[ℝ] W := P0.codRestrict W hP0mem with hP
  have hPapp : ∀ y, (P y : E) = y - φ y • w0 := by
    intro y
    rfl
  set T : E → W := fun y => P (y - m) with hT
  have hTc : Continuous T := P.continuous.comp (continuous_id.sub continuous_const)
  have hTm : Measurable T := hTc.measurable
  have hTH : ∀ y, φ y = φ m → (T y : E) + m = y := by
    intro y hy
    rw [show (T y : E) = (y - m) - φ (y - m) • w0 from hPapp _, map_sub, hy, sub_self,
      zero_smul, sub_zero, sub_add_cancel]
  set ν' : Measure W := ν.map T with hν'
  have : IsProbabilityMeasure ν' := Measure.isProbabilityMeasure_map hTm.aemeasurable
  have hTint : Integrable T ν := P.integrable_comp (hint.sub (integrable_const m))
  have hint' : Integrable (fun w => w) ν' := by
    show Integrable id ν'
    rw [hν', integrable_map_measure aestronglyMeasurable_id hTm.aemeasurable]
    exact hTint
  have hmean' : (∫ w, w ∂ν') = 0 := by
    show ∫ w, id w ∂ν' = 0
    rw [hν', integral_map hTm.aemeasurable aestronglyMeasurable_id]
    have hi2 : Integrable (fun y => y - m) ν := hint.sub (integrable_const m)
    show ∫ y, P (y - m) ∂ν = 0
    rw [ContinuousLinearMap.integral_comp_comm P hi2,
      integral_sub hint (integrable_const m), ← hmdef]
    simp
  -- the restricted problem on `W`
  set A : W →ᵃ[ℝ] E := W.subtype.toAffineMap + AffineMap.const ℝ W m with hA
  have hAapp : ∀ w, A w = (w : E) + m := fun w => rfl
  set C' : Set W := A ⁻¹' C with hC'
  have hg' : ConvexOn ℝ C' (g ∘ A) := hg.comp_affineMap A
  set Nset := toMeasurable ν Cᶜ with hN
  have hNm : MeasurableSet Nset := measurableSet_toMeasurable _ _
  have hN0 : ν Nset = 0 := by rw [hN, measure_toMeasurable]; exact hCν
  have hAc : Continuous A := by
    have : (A : W → E) = fun w : W => (w : E) + m := funext hAapp
    rw [this]; exact continuous_subtype_val.add continuous_const
  have hCν' : ν' C'ᶜ = 0 := by
    have hsub : C'ᶜ ⊆ A ⁻¹' Nset := by
      intro w hw
      exact subset_toMeasurable ν Cᶜ hw
    refine measure_mono_null hsub ?_
    rw [hν', Measure.map_apply hTm (hAc.measurable hNm)]
    refine measure_mono_null ?_ (measure_union_null (ae_iff.1 hH) hN0)
    intro y hy
    by_cases hyH : φ y = φ m
    · right
      have : A (T y) = y := by rw [hAapp]; exact hTH y hyH
      simpa [this] using hy
    · left; exact hyH
  obtain ⟨hmem, ψ, hψ⟩ := ih _ hWlt W rfl ν' hint' C' (g ∘ A) hCν' hg'
  rw [hmean'] at hmem hψ
  have hmC : m ∈ C := by
    have : A 0 = m := by rw [hAapp]; simp
    rw [← this]; exact hmem
  refine ⟨hmC, ψ.comp P, ?_⟩
  have hψ2 : ∀ᵐ y ∂ν, (g ∘ A) 0 + ψ (T y - 0) ≤ (g ∘ A) (T y) := ae_of_ae_map hTm.aemeasurable hψ
  filter_upwards [hψ2, hH] with y hy1 hy2
  have hA0 : A 0 = m := by rw [hAapp]; simp
  have hAT : A (T y) = y := by rw [hAapp]; exact hTH y hy2
  simp only [Function.comp_apply, hA0, hAT, sub_zero] at hy1
  simpa [hT] using hy1

end PJAux

open MeasureTheory in
theorem solution {N ν : ℕ} {X : Type*}
    (μ : Measure (EuclideanSpace ℝ (Fin N))) [IsProbabilityMeasure μ]
    (hξ : Integrable (fun ξ => ξ) μ)
    (S : Fin ν → Set (EuclideanSpace ℝ (Fin N))) (hSm : ∀ l, MeasurableSet (S l))
    (hSd : Pairwise (Function.onFun Disjoint S)) (hSc : μ (⋃ l, S l)ᶜ = 0)
    (g : X → EuclideanSpace ℝ (Fin N) → ℝ) (D : Set X)
    (C : X → Set (EuclideanSpace ℝ (Fin N))) (hCμ : ∀ x ∈ D, μ (C x)ᶜ = 0)
    (hg : ∀ x ∈ D, ConvexOn ℝ (C x) (g x)) :
    ∀ x ∈ D,
      (∫⁻ ξ, ENNReal.ofReal (-g x ξ) ∂μ) ≠ ⊤ ∧
        ((∑ l, μ.real (S l) * g x (⨍ ξ in S l, ξ ∂μ) : ℝ) : EReal) ≤
          ((∫⁻ ξ, ENNReal.ofReal (g x ξ) ∂μ : ENNReal) : EReal) -
            ((∫⁻ ξ, ENNReal.ofReal (-g x ξ) ∂μ : ENNReal) : EReal) := by
  intro x hx
  set G := g x with hG
  have hconv := hg x hx
  have hCx := hCμ x hx
  set mm : Fin ν → EuclideanSpace ℝ (Fin N) := fun l => ⨍ ξ in S l, ξ ∂μ with hmm
  have cell : ∀ l, ∃ φ : StrongDual ℝ (EuclideanSpace ℝ (Fin N)),
      μ (S l) ≠ 0 → ∀ᵐ y ∂μ, y ∈ S l → G (mm l) + φ (y - mm l) ≤ G y := by
    intro l
    by_cases h0 : μ (S l) = 0
    · exact ⟨0, fun h => absurd h0 h⟩
    · haveI : NeZero (μ.restrict (S l)) := ⟨by rwa [Ne, Measure.restrict_eq_zero]⟩
      set c : ENNReal := (μ.restrict (S l) Set.univ)⁻¹ with hc
      have hcne : c ≠ 0 := ENNReal.inv_ne_zero.2 (measure_ne_top _ _)
      have hctop : c ≠ ⊤ := by
        rw [hc, Ne, ENNReal.inv_eq_top, Measure.restrict_apply_univ]; exact h0
      set ρ : Measure (EuclideanSpace ℝ (Fin N)) := c • μ.restrict (S l) with hρ
      have : IsProbabilityMeasure ρ := isProbabilityMeasureSMul
      have hρint : Integrable (fun y => y) ρ := (hξ.restrict).smul_measure hctop
      have hρC : ρ (C x)ᶜ = 0 := by
        rw [hρ, Measure.smul_apply, Measure.restrict_apply' (hSm l), smul_eq_mul]
        rw [measure_mono_null Set.inter_subset_left hCx, mul_zero]
      obtain ⟨-, φ, hφ⟩ := PJAux.jensen_affine _ (EuclideanSpace ℝ (Fin N)) rfl ρ hρint (C x) G hρC
        hconv
      have hmean : (∫ y, y ∂ρ) = mm l := rfl
      rw [hmean] at hφ
      refine ⟨φ, fun _ => ?_⟩
      have h1 := ae_iff.1 hφ
      rw [hρ, Measure.smul_apply, smul_eq_mul, mul_eq_zero] at h1
      exact (ae_restrict_iff' (hSm l)).1 (ae_iff.2 (h1.resolve_left hcne))
  choose φ hφ using cell
  set a : Fin ν → EuclideanSpace ℝ (Fin N) → ℝ := fun l y => G (mm l) + φ l (y - mm l) with ha
  set h : EuclideanSpace ℝ (Fin N) → ℝ := fun y => ∑ l, (S l).indicator (a l) y with hh
  have haint : ∀ l, Integrable (a l) μ := fun l =>
    (integrable_const _).add ((φ l).integrable_comp (hξ.sub (integrable_const _)))
  have hint : Integrable h μ :=
    integrable_finsetSum _ (fun l _ => (haint l).indicator (hSm l))
  have hle : ∀ᵐ y ∂μ, h y ≤ G y := by
    have h1 : ∀ᵐ y ∂μ, ∀ l, y ∈ S l → a l y ≤ G y := by
      rw [ae_all_iff]
      intro l
      by_cases h0 : μ (S l) = 0
      · refine ae_iff.2 (measure_mono_null (fun y hy => ?_) h0)
        by_contra hcon
        exact hy (fun h' => absurd h' hcon)
      · exact hφ l h0
    have h2 : ∀ᵐ y ∂μ, y ∈ ⋃ l, S l := ae_iff.2 (measure_mono_null (fun y hy => hy) hSc)
    filter_upwards [h1, h2] with y hy1 hy2
    obtain ⟨l0, hl0⟩ := Set.mem_iUnion.1 hy2
    have : h y = a l0 y := by
      simp only [hh]
      rw [Finset.sum_eq_single l0]
      · exact Set.indicator_of_mem hl0 _
      · intro b _ hb
        apply Set.indicator_of_notMem
        exact fun hb' => Set.disjoint_left.1 (hSd hb) hb' hl0
      · intro hcon; exact absurd (Finset.mem_univ _) hcon
    rw [this]
    exact hy1 l0 hl0
  have hval : ∫ y, h y ∂μ = ∑ l, μ.real (S l) * G (mm l) := by
    simp only [hh]
    rw [integral_finsetSum _ (fun l _ => (haint l).indicator (hSm l))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_indicator (hSm l)]
    simp only [ha]
    have hi1 : IntegrableOn (fun y => φ l (y - mm l)) (S l) μ :=
      ((φ l).integrable_comp (hξ.sub (integrable_const (mm l)))).integrableOn
    have hi2 : Integrable (fun y => y - mm l) (μ.restrict (S l)) :=
      (hξ.sub (integrable_const (mm l))).integrableOn
    rw [integral_add (integrable_const _) hi1,
      setIntegral_const, ContinuousLinearMap.integral_comp_comm _ hi2,
      integral_sub hξ.integrableOn (integrable_const _).integrableOn, setIntegral_const]
    have hsa : μ.real (S l) • mm l = ∫ y in S l, y ∂μ :=
      measure_smul_setAverage _ (measure_ne_top _ _)
    rw [← hsa, sub_self, map_zero, add_zero, smul_eq_mul]
  have hnegle : (∫⁻ ξ, ENNReal.ofReal (-G ξ) ∂μ) ≤ ∫⁻ ξ, ENNReal.ofReal (-h ξ) ∂μ :=
    lintegral_mono_ae (hle.mono fun y hy => ENNReal.ofReal_le_ofReal (by linarith))
  have hposle : (∫⁻ ξ, ENNReal.ofReal (h ξ) ∂μ) ≤ ∫⁻ ξ, ENNReal.ofReal (G ξ) ∂μ :=
    lintegral_mono_ae (hle.mono fun y hy => ENNReal.ofReal_le_ofReal hy)
  have hnegfin : (∫⁻ ξ, ENNReal.ofReal (-h ξ) ∂μ) ≠ ⊤ := hint.neg.lintegral_lt_top.ne
  have hposfin : (∫⁻ ξ, ENNReal.ofReal (h ξ) ∂μ) ≠ ⊤ := hint.lintegral_lt_top.ne
  refine ⟨ne_top_of_le_ne_top hnegfin hnegle, ?_⟩
  have hsum : (∑ l, μ.real (S l) * g x (⨍ ξ in S l, ξ ∂μ) : ℝ) = ∫ y, h y ∂μ := hval.symm
  rw [hsum, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint, EReal.coe_sub,
    EReal.coe_ennreal_toReal hposfin, EReal.coe_ennreal_toReal hnegfin]
  exact EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.2 hposle)
    (EReal.coe_ennreal_le_coe_ennreal_iff.2 hnegle)
