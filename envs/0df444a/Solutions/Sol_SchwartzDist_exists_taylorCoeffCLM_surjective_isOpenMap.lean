-- Prove2me | solution 1 for SchwartzDist.exists_taylorCoeffCLM_surjective_isOpenMap
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:12:28.995845+00:00
-- url     : https://prove2.me/submissions/991f7032-3efd-413c-af47-2ae12e97a47d

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_open_mapping_LF
import Theorems.Thm_MasulloGRH_isLF_of_isFrechet
import Theorems.Thm_MasulloGRH_schwartz_space_euclidean_nuclear
import Theorems.Thm_MeasureTheory_exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero

open SchwartzMap LineDeriv Topology Filter

set_option autoImplicit false

namespace Sol_SchwartzDist_exists_taylorCoeffCLM_surjective_isOpenMap

open MasulloGRH

theorem isCompleteTVS_of_completeSpace (E : Type*) [AddCommGroup E] [Module ℂ E] [UniformSpace E]
    [IsUniformAddGroup E] [CompleteSpace E] [T2Space E] : IsCompleteTVS E := by
  refine ⟨inferInstance, fun f hf => ?_⟩
  obtain ⟨hne, hU⟩ := hf
  have hc : Cauchy f := by
    refine ⟨hne, ?_⟩
    rw [uniformity_eq_comap_nhds_zero]
    intro s hs
    obtain ⟨U, hU0, hUs⟩ := mem_comap.1 hs
    obtain ⟨A, hA, hAU⟩ := hU U hU0
    exact mem_of_superset (prod_mem_prod hA hA) (fun p hp => hUs (hAU _ hp.2 _ hp.1))
  exact CompleteSpace.complete hc

theorem isFrechet_pi : IsFrechet (ℕ → ℂ) := by
  refine ⟨⟨(Σ _ : ℕ, Fin 1), ⟨⟨0, 0⟩⟩, _, withSeminorms_pi (fun _ => norm_withSeminorms ℂ ℂ)⟩,
    isCompleteTVS_of_completeSpace _, inferInstance⟩

theorem isFrechet_induced {E F : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup F]
    [Module ℂ F] [tF : TopologicalSpace F] (e : E ≃ₗ[ℂ] F) (hF : IsFrechet F) :
    @IsFrechet E _ _ (TopologicalSpace.induced e tF) := by
  let tE : TopologicalSpace E := TopologicalSpace.induced e tF
  obtain ⟨⟨ι, hι, p, hp⟩, ⟨hT2, hcompl⟩, hmet⟩ := hF
  have hemb : IsEmbedding (e : E → F) := ⟨⟨rfl⟩, e.injective⟩
  refine ⟨⟨ι, hι, p.comp (e : E →ₗ[ℂ] F), (e : E →ₗ[ℂ] F).withSeminorms_induced hp⟩,
    ⟨hemb.t2Space, ?_⟩, hemb.metrizableSpace⟩
  rintro f ⟨hne, hf⟩
  have hcF : IsCauchyFilter (f.map e) := by
    refine ⟨inferInstance, fun U hU => ?_⟩
    have h0 : (e : E → F) ⁻¹' U ∈ 𝓝 (0 : E) := by
      rw [hemb.toIsInducing.nhds_eq_comap, map_zero]
      exact preimage_mem_comap hU
    obtain ⟨A, hA, hAU⟩ := hf _ h0
    refine ⟨e '' A, image_mem_map hA, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := hAU a ha b hb
    simpa [map_sub] using this
  obtain ⟨y, hy⟩ := hcompl _ hcF
  refine ⟨e.symm y, ?_⟩
  rw [hemb.toIsInducing.nhds_eq_comap, e.apply_symm_apply]
  exact map_le_iff_le_comap.1 hy

/-- The real line as `EuclideanSpace ℝ (Fin 1)`. -/
noncomputable def euc1 : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  (EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)

noncomputable def schwA : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin 1), ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ euc1

noncomputable def schwB : 𝓢(EuclideanSpace ℝ (Fin 1), ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ euc1.symm

theorem schwB_schwA (f : 𝓢(ℝ, ℂ)) : schwB (schwA f) = f := by
  ext x; simp [schwA, schwB]

theorem schwA_schwB (f : 𝓢(EuclideanSpace ℝ (Fin 1), ℂ)) : schwA (schwB f) = f := by
  ext x; simp [schwA, schwB]

noncomputable def schwL : (⊤ : Submodule ℂ 𝓢(ℝ, ℂ)) ≃ₗ[ℂ] 𝓢(EuclideanSpace ℝ (Fin 1), ℂ) :=
  Submodule.topEquiv.trans
    (ContinuousLinearEquiv.equivOfInverse schwA schwB schwB_schwA schwA_schwB).toLinearEquiv

theorem schwartz_cover :
    ∃ (X : ℕ → Submodule ℂ 𝓢(ℝ, ℂ)) (τ : ∀ n, TopologicalSpace (X n)), Monotone X ∧
      (∀ x : 𝓢(ℝ, ℂ), ∃ n, x ∈ X n) ∧ (∀ n, @IsFrechet (X n) _ _ (τ n)) ∧
      ∀ n, @Continuous (X n) 𝓢(ℝ, ℂ) (τ n) _ Subtype.val := by
  refine ⟨fun _ => ⊤, fun _ => TopologicalSpace.induced schwL inferInstance, monotone_const,
    fun x => ⟨0, Submodule.mem_top⟩,
    fun _ => isFrechet_induced schwL (schwartz_space_euclidean_nuclear 1).2.1, fun _ => ?_⟩
  have hval : (Subtype.val : (⊤ : Submodule ℂ 𝓢(ℝ, ℂ)) → 𝓢(ℝ, ℂ)) = schwB ∘ schwL := by
    funext x
    simp [schwL, schwB_schwA]
  rw [hval]
  exact @Continuous.comp _ _ _ (TopologicalSpace.induced schwL inferInstance) _ _ _ _
    schwB.continuous continuous_induced_dom

/-- Evaluation at the origin. -/
noncomputable def ev0 : 𝓢(ℝ, ℂ) →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ 0).comp (toBoundedContinuousFunctionCLM ℂ ℝ ℂ)

theorem derivCLM_pow_apply (k : ℕ) (f : 𝓢(ℝ, ℂ)) :
    (((derivCLM ℂ ℂ) ^ k) f : ℝ → ℂ) = iteratedDeriv k (f : ℝ → ℂ) := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    show (((derivCLM ℂ ℂ) ^ k) (derivCLM ℂ ℂ f) : ℝ → ℂ) = _
    rw [ih, iteratedDeriv_succ']
    congr 1

noncomputable def taylorJ : 𝓢(ℝ, ℂ) →L[ℂ] (ℕ → ℂ) :=
  ContinuousLinearMap.pi fun k => ((k.factorial : ℂ)⁻¹) • (ev0.comp ((derivCLM ℂ ℂ) ^ k))

theorem taylorJ_apply (f : 𝓢(ℝ, ℂ)) (k : ℕ) :
    taylorJ f k = iteratedDeriv k (f : ℝ → ℂ) 0 / (k.factorial : ℂ) := by
  simp only [taylorJ, ContinuousLinearMap.pi_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [div_eq_inv_mul]
  congr 1
  show (((derivCLM ℂ ℂ) ^ k) f : ℝ → ℂ) 0 = _
  rw [derivCLM_pow_apply]

/-- Borel's lemma on the line, from the parametrized version with a zero-dimensional parameter
space. -/
theorem exists_smooth_iteratedDeriv (c : ℕ → ℂ) :
    ∃ g : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) g ∧ ∀ m, iteratedDeriv m g 0 = (m.factorial : ℂ) * c m := by
  obtain ⟨B, hB, hT⟩ :=
    MeasureTheory.exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero
      (E := Fin 0 → ℝ) (F := ℂ) Set.univ Set.subsingleton_univ.isCompact
      (fun k _ => (k.factorial : ℂ) * c k) (fun _ => contDiff_const)
      (fun _ e he => absurd (Set.mem_univ e) he)
  let ι : ℝ →L[ℝ] (Fin 0 → ℝ) × ℝ := ContinuousLinearMap.inr ℝ (Fin 0 → ℝ) ℝ
  refine ⟨B ∘ ι, hB.comp ι.contDiff, fun m => ?_⟩
  let P : ℝ → ℂ := fun t =>
    ∑ k ∈ Finset.range (m + 1), (t ^ k / (k.factorial : ℝ)) • ((k.factorial : ℂ) * c k)
  have hPc : ContDiff ℝ (⊤ : ℕ∞) P := by
    refine ContDiff.sum fun k _ => ?_
    exact ((contDiff_id.pow k).div_const _).smul contDiff_const
  set D : (Fin 0 → ℝ) × ℝ → ℂ := fun p => B p -
      ∑ k ∈ Finset.range (m + 1),
        (p.2 ^ k / (k.factorial : ℝ)) • (fun (k : ℕ) (_ : Fin 0 → ℝ) => (k.factorial : ℂ) * c k) k p.1
    with hDdef
  have hD : ContDiff ℝ (⊤ : ℕ∞) D := by
    refine hB.sub (ContDiff.sum fun k _ => ?_)
    exact ((contDiff_snd.pow k).div_const _).smul contDiff_const
  have h1 := hT m m le_rfl 0
  have h2 := ι.iteratedFDeriv_comp_right hD 0 (i := m) (by exact_mod_cast le_top)
  have hι0 : ι 0 = ((0 : Fin 0 → ℝ), (0 : ℝ)) := rfl
  rw [hι0, h1] at h2
  have h3 : iteratedDeriv m (fun t => (B ∘ ι) t - P t) 0 = 0 := by
    have hfun : (fun t => (B ∘ ι) t - P t) = D ∘ ι := rfl
    rw [hfun, iteratedDeriv_eq_iteratedFDeriv, h2]
    simp
  rw [iteratedDeriv_fun_sub ((hB.comp ι.contDiff).contDiffAt.of_le (by exact_mod_cast le_top))
    (hPc.contDiffAt.of_le (by exact_mod_cast le_top)), sub_eq_zero] at h3
  rw [h3]
  simp only [P]
  rw [iteratedDeriv_fun_sum (fun k _ =>
    ((((contDiff_id.pow k).div_const _).smul contDiff_const).contDiffAt.of_le
      (by exact_mod_cast le_top)))]
  rw [Finset.sum_eq_single m]
  · rw [iteratedDeriv_smul_const ((((contDiff_id.pow m).div_const _)).contDiffAt.of_le
      (by exact_mod_cast le_top))]
    rw [iteratedDeriv_div_const, iteratedDeriv_fun_pow_zero, if_pos rfl,
      div_self (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)), one_smul]
  · intro k _ hk
    rw [iteratedDeriv_smul_const ((((contDiff_id.pow k).div_const _)).contDiffAt.of_le
      (by exact_mod_cast le_top))]
    rw [iteratedDeriv_div_const, iteratedDeriv_fun_pow_zero, if_neg (Ne.symm hk), Nat.cast_zero, zero_div,
      zero_smul]
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_self m)) h

theorem exists_schwartz_taylor (c : ℕ → ℂ) :
    ∃ f : 𝓢(ℝ, ℂ), ∀ m, iteratedDeriv m (f : ℝ → ℂ) 0 = (m.factorial : ℂ) * c m := by
  obtain ⟨g, hg, hgd⟩ := exists_smooth_iteratedDeriv c
  let φ : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have hs : HasCompactSupport (fun t => φ t • g t) := φ.hasCompactSupport.smul_right
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t => φ t • g t) := φ.contDiff.smul hg
  refine ⟨hs.toSchwartzMap hc, fun m => ?_⟩
  have heq : (fun t => φ t • g t) =ᶠ[𝓝 0] g := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with t ht
    rw [φ.one_of_mem_closedBall (Metric.ball_subset_closedBall ht), one_smul]
  rw [← hgd m]
  exact heq.iteratedDeriv_eq m

theorem taylorJ_surjective : Function.Surjective taylorJ := by
  intro c
  obtain ⟨f, hf⟩ := exists_schwartz_taylor c
  refine ⟨f, funext fun k => ?_⟩
  rw [taylorJ_apply, hf k]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k))

end Sol_SchwartzDist_exists_taylorCoeffCLM_surjective_isOpenMap

open Sol_SchwartzDist_exists_taylorCoeffCLM_surjective_isOpenMap in
theorem solution :
    ∃ J : 𝓢(ℝ, ℂ) →L[ℂ] (ℕ → ℂ),
      (∀ (f : 𝓢(ℝ, ℂ)) (k : ℕ), J f k = iteratedDeriv k (f : ℝ → ℂ) 0 / (k.factorial : ℂ)) ∧
      Function.Surjective J ∧ IsOpenMap J := by
  refine ⟨taylorJ, taylorJ_apply, taylorJ_surjective, ?_⟩
  exact MasulloGRH.open_mapping_LF (ℕ → ℂ) 𝓢(ℝ, ℂ)
    (MasulloGRH.isLF_of_isFrechet _ isFrechet_pi) schwartz_cover
    (taylorJ : 𝓢(ℝ, ℂ) →ₗ[ℂ] (ℕ → ℂ)) taylorJ.continuous taylorJ_surjective
