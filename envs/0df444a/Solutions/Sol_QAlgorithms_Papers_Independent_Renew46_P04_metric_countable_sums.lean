-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P04.metric_countable_sums
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:02:50.942993+00:00
-- url     : https://prove2.me/submissions/37da4cdd-28ae-47f6-bad8-a0c53a9b83a7

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P04

noncomputable section

open Filter Set
open scoped Topology ENNReal

namespace X7CSums

open QAlgorithms.Papers.Independent.Renew46.P04

variable {K : Type*} [RCLike K]

theorem X7_mp_le {F : Type*} [NormedAddCommGroup F] [NormedSpace K F] (h : MetricPi K F)
    (T : Finset F) (hT : ∀ t ∈ T, ‖t‖ ≤ 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Q : F →L[K] F, Q.comp Q = Q ∧ ‖Q‖ ≤ 1 ∧ FiniteDimensional K Q.range ∧
      ∀ t ∈ T, ∃ w ∈ Q.range, ‖t - w‖ < δ := by
  classical
  obtain ⟨Q, h1, h2, h3, h4⟩ := h δ hδ
    ((T.filter (fun t => t ≠ 0)).image (fun t => ((‖t‖⁻¹ : ℝ) : K) • t)) (by
      intro u hu
      simp only [Finset.mem_image, Finset.mem_filter] at hu
      obtain ⟨t, ⟨_, ht0⟩, rfl⟩ := hu
      rw [norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr ht0)])
  refine ⟨Q, h1, h2, h3, fun t ht => ?_⟩
  by_cases ht0 : t = 0
  · exact ⟨0, Submodule.zero_mem _, by simpa [ht0] using hδ⟩
  obtain ⟨w, hw, hlt⟩ := h4 _ (Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, ht0⟩, rfl⟩)
  refine ⟨((‖t‖ : ℝ) : K) • w, Submodule.smul_mem _ _ hw, ?_⟩
  have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
  have : t - ((‖t‖ : ℝ) : K) • w = ((‖t‖ : ℝ) : K) • (((‖t‖⁻¹ : ℝ) : K) • t - w) := by
    rw [smul_sub, smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ htpos.ne', RCLike.ofReal_one,
      one_smul]
  rw [this, norm_smul, RCLike.norm_ofReal, abs_norm]
  calc ‖t‖ * ‖((‖t‖⁻¹ : ℝ) : K) • t - w‖ ≤ 1 * ‖((‖t‖⁻¹ : ℝ) : K) • t - w‖ := by
        gcongr; exact hT t ht
    _ < δ := by rw [one_mul]; exact hlt

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace K (E n)]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- finite sum of singles -/
def sumS (p : ℝ≥0∞) (N : ℕ) (v : ∀ k, E k) : lp E p :=
  ∑ k ∈ Finset.range N, lp.single p k (v k)

omit [∀ n, NormedSpace K (E n)] [Fact (1 ≤ p)] in
theorem sumS_apply (N : ℕ) (v : ∀ k, E k) (j : ℕ) :
    (sumS p N v : ∀ k, E k) j = if j < N then v j else 0 := by
  unfold sumS
  rw [lp.coeFn_sum, Finset.sum_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single j]
    · exact lp.single_apply_self p j (v j)
    · intro b _ hb; exact lp.single_apply_ne p b (v b) (Ne.symm hb)
    · intro hj; exact absurd (Finset.mem_range.mpr h) hj
  · apply Finset.sum_eq_zero
    intro k hk
    refine lp.single_apply_ne p k (v k) ?_
    intro hjk; subst hjk; exact h (Finset.mem_range.mp hk)

/-- block projection -/
def Pg (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ) (Q : ∀ k, E k →L[K] E k) : lp E p →L[K] lp E p :=
  ∑ k ∈ Finset.range N,
    (lp.singleContinuousLinearMap K E p k).comp ((Q k).comp (lp.evalCLM K E p k))

theorem Pg_eq (N : ℕ) (Q : ∀ k, E k →L[K] E k) (x : lp E p) :
    Pg p N Q x = sumS p N (fun k => Q k (x k)) := by
  simp only [Pg, sumS, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    lp.singleContinuousLinearMap_apply]
  rfl

theorem Pg_apply (N : ℕ) (Q : ∀ k, E k →L[K] E k) (x : lp E p) (j : ℕ) :
    (Pg p N Q x : ∀ k, E k) j = if j < N then Q j (x j) else 0 := by
  rw [Pg_eq, sumS_apply]

theorem Pg_norm (N : ℕ) (Q : ∀ k, E k →L[K] E k) (hQ : ∀ k, ‖Q k‖ ≤ 1) :
    ‖Pg p N Q‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  have hp : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  refine lp.norm_mono hp fun j => ?_
  rw [Pg_apply]
  split_ifs
  · simpa using (Q j).le_of_opNorm_le (hQ j) (x j)
  · simp

theorem Pg_idem (N : ℕ) (Q : ∀ k, E k →L[K] E k) (hQ : ∀ k, (Q k).comp (Q k) = Q k) :
    (Pg p N Q).comp (Pg p N Q) = Pg p N Q := by
  ext1 x; apply lp.ext; funext j
  simp only [ContinuousLinearMap.comp_apply, Pg_apply]
  split_ifs
  · exact congrArg (fun T : E j →L[K] E j => T (x j)) (hQ j)
  · rfl

theorem Pg_fd (N : ℕ) (Q : ∀ k, E k →L[K] E k) (hQ : ∀ k, FiniteDimensional K (Q k).range) :
    FiniteDimensional K (Pg p N Q).range := by
  let S : ℕ → Submodule K (lp E p) := fun k =>
    ((Q k).range).map (lp.singleContinuousLinearMap K E p k : E k →ₗ[K] lp E p)
  have hS : ∀ k, FiniteDimensional K (S k) := fun k => by
    haveI := hQ k; infer_instance
  have hle : (Pg p N Q).range ≤ (Finset.range N).sup S := by
    rintro _ ⟨x, rfl⟩
    show Pg p N Q x ∈ _
    rw [Pg_eq]
    refine Submodule.sum_mem _ fun k hk => ?_
    refine Finset.le_sup (f := S) hk ?_
    exact Submodule.mem_map_of_mem (LinearMap.mem_range_self _ _)
  exact Submodule.finiteDimensional_of_le hle

theorem X7_main (h : ∀ n, MetricPi K (E n)) (s : Finset (lp E p)) (hs : ∀ x ∈ s, ‖x‖ ≤ 1)
    (eps : ℝ) (heps : 0 < eps) (N : ℕ)
    (hN : ∀ x ∈ s, ‖x - sumS p N (fun k => x k)‖ < eps / 2) :
    ∃ Q : ∀ k, E k →L[K] E k, (∀ k, (Q k).comp (Q k) = Q k) ∧ (∀ k, ‖Q k‖ ≤ 1) ∧
      (∀ k, FiniteDimensional K (Q k).range) ∧
      ∀ x ∈ s, ∃ y ∈ (Pg p N Q).range, ‖x - y‖ < eps := by
  classical
  have hp : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hp' : 0 < p := pos_iff_ne_zero.mpr hp
  set δ : ℝ := eps / (2 * ((N : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hex : ∀ k, ∃ Q : E k →L[K] E k, Q.comp Q = Q ∧ ‖Q‖ ≤ 1 ∧ FiniteDimensional K Q.range ∧
      ∀ t ∈ s.image (fun x : lp E p => (x : ∀ k, E k) k), ∃ w ∈ Q.range, ‖t - w‖ < δ := fun k =>
    X7_mp_le (h k) _ (by
      intro t ht
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
      exact (lp.norm_apply_le_norm hp x k).trans (hs x hx)) δ hδpos
  choose Q hQ1 hQ2 hQ3 hQ4 using hex
  refine ⟨Q, hQ1, hQ2, hQ3, fun x hx => ?_⟩
  have hv : ∀ k, ∃ w ∈ (Q k).range, ‖x k - w‖ < δ := fun k =>
    hQ4 k _ (Finset.mem_image_of_mem _ hx)
  choose v hvr hvn using hv
  refine ⟨sumS p N v, ?_, ?_⟩
  · refine ⟨sumS p N v, ?_⟩
    change Pg p N Q (sumS p N v) = sumS p N v
    apply lp.ext; funext j
    rw [Pg_apply, sumS_apply]
    split_ifs
    · obtain ⟨w, hw⟩ := hvr j
      rw [← hw]
      exact congrArg (fun T : E j →L[K] E j => T w) (hQ1 j)
    · rfl
  · have hdec : x - sumS p N v = (x - sumS p N (fun k => x k)) + sumS p N (fun k => x k - v k) := by
      simp only [sumS, lp.single_sub, Finset.sum_sub_distrib]
      abel
    rw [hdec]
    refine lt_of_le_of_lt (norm_add_le _ _) ?_
    have h2 : ‖sumS p N (fun k => x k - v k)‖ ≤ N * δ := by
      unfold sumS
      refine (norm_sum_le _ _).trans ?_
      calc ∑ k ∈ Finset.range N, ‖lp.single p k (x k - v k)‖
          ≤ ∑ _k ∈ Finset.range N, δ := by
            refine Finset.sum_le_sum fun k _ => ?_
            rw [lp.norm_single hp']
            exact (hvn k).le
        _ = N * δ := by simp
    have h3 : (N : ℝ) * δ < eps / 2 := by
      rw [hδ]
      have : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith [hN x hx]

theorem X7_lp (h : ∀ n, MetricPi K (E n)) (hpt : p < ⊤) : MetricPi K (lp E p) := by
  intro eps heps s hs
  have hev : ∀ x ∈ s, ∀ᶠ N in atTop, ‖x - sumS p N (fun k => x k)‖ < eps / 2 := by
    intro x _
    have ht := (lp.hasSum_single hpt.ne x).tendsto_sum_nat
    have ht2 := (tendsto_const_nhds (x := x)).sub ht
    rw [sub_self] at ht2
    filter_upwards [ht2.norm.eventually (gt_mem_nhds (show ‖(0 : lp E p)‖ < eps / 2 by rw [norm_zero]; exact half_pos heps))] with N hN
    simpa [sumS] using hN
  obtain ⟨N, hN⟩ := ((eventually_all_finset s).2 hev).exists
  obtain ⟨Q, hQ1, hQ2, hQ3, hQ4⟩ :=
    X7_main h s (fun x hx => (hs x hx).le) eps heps N hN
  exact ⟨Pg p N Q, Pg_idem N Q hQ1, Pg_norm N Q hQ2, Pg_fd N Q hQ3, hQ4⟩

omit [Fact (1 ≤ p)] in
theorem X7_span_fin (z : lp E ⊤)
    (hz : z ∈ Submodule.span K {v : lp E ⊤ | ∃ (n : ℕ) (x : E n), v = lp.single ⊤ n x}) :
    ∃ N0 : ℕ, ∀ j ≥ N0, (z : ∀ k, E k) j = 0 := by
  induction hz using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨n, x, rfl⟩ := hv
    exact ⟨n + 1, fun j hj => lp.single_apply_ne ⊤ n x (by omega)⟩
  | zero => exact ⟨0, fun j _ => rfl⟩
  | add a b _ _ ha hb =>
    obtain ⟨A, hA⟩ := ha
    obtain ⟨B, hB⟩ := hb
    refine ⟨max A B, fun j hj => ?_⟩
    rw [lp.coeFn_add, Pi.add_apply, hA j (le_of_max_le_left hj), hB j (le_of_max_le_right hj),
      add_zero]
  | smul c a _ ha =>
    obtain ⟨A, hA⟩ := ha
    exact ⟨A, fun j hj => by rw [lp.coeFn_smul, Pi.smul_apply, hA j hj, smul_zero]⟩

theorem X7_c0_tail (x : lp E ⊤) (hx : x ∈ CZeroSum (K := K) (E := E)) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ‖x - sumS ⊤ N (fun k => x k)‖ < ε := by
  have hx' : x ∈ closure ((Submodule.span K
      {v : lp E ⊤ | ∃ (n : ℕ) (x : E n), v = lp.single ⊤ n x} : Submodule K (lp E ⊤)) :
        Set (lp E ⊤)) := hx
  obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.mp hx' ε hε
  obtain ⟨N0, hN0⟩ := X7_span_fin z hz
  refine ⟨N0, fun N hN => lt_of_le_of_lt ?_ (by rwa [dist_eq_norm] at hxz)⟩
  refine lp.norm_mono (by simp) fun j => ?_
  rw [lp.coeFn_sub, Pi.sub_apply, sumS_apply, lp.coeFn_sub, Pi.sub_apply]
  split_ifs with hj
  · simp
  · rw [hN0 j (by omega), sub_zero]

theorem X7_c0 (h : ∀ n, MetricPi K (E n)) : MetricPi K (CZeroSum (K := K) (E := E)) := by
  classical
  intro eps heps s hs
  have hev : ∀ x ∈ s.image Subtype.val, ∀ᶠ N in atTop,
      ‖x - sumS ⊤ N (fun k => x k)‖ < eps / 2 := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨N0, hN0⟩ := X7_c0_tail y.1 y.2 (eps / 2) (half_pos heps)
    exact eventually_atTop.2 ⟨N0, hN0⟩
  obtain ⟨N, hN⟩ := ((eventually_all_finset _).2 hev).exists
  obtain ⟨Q, hQ1, hQ2, hQ3, hQ4⟩ := X7_main h (s.image Subtype.val)
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact (hs y hy).le) eps heps N hN
  set P := Pg ⊤ N Q with hP
  have hmem : ∀ z : lp E ⊤, P z ∈ CZeroSum (K := K) (E := E) := by
    intro z
    apply Submodule.le_topologicalClosure
    rw [hP, Pg_eq]
    refine Submodule.sum_mem _ fun k _ => Submodule.subset_span ⟨k, _, rfl⟩
  let Pr : CZeroSum (K := K) (E := E) →L[K] CZeroSum (K := K) (E := E) :=
    P.restrict (fun z _ => hmem z)
  have hPr : ∀ z, (Pr z : lp E ⊤) = P z := fun z => rfl
  refine ⟨Pr, ?_, ?_, ?_, ?_⟩
  · ext1 z; apply Subtype.ext
    show P (P z) = P z
    exact congrArg (fun T : lp E ⊤ →L[K] lp E ⊤ => T z) (Pg_idem N Q hQ1)
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
    show ‖P z‖ ≤ 1 * ‖(z : lp E ⊤)‖
    exact (Pg_norm N Q hQ2).trans_eq' rfl |> fun h => P.le_of_opNorm_le h z
  · let g : Pr.range →ₗ[K] lp E ⊤ :=
      (CZeroSum (K := K) (E := E)).subtype.comp (Pr.range).subtype
    have hg : Function.Injective g := fun a b hab => Subtype.ext (Subtype.ext hab)
    have hrg : LinearMap.range g ≤ P.range := by
      rintro _ ⟨⟨_, ⟨z, rfl⟩⟩, rfl⟩
      exact ⟨z, rfl⟩
    haveI : FiniteDimensional K P.range := Pg_fd N Q hQ3
    haveI : FiniteDimensional K (LinearMap.range g) := Submodule.finiteDimensional_of_le hrg
    exact LinearEquiv.finiteDimensional (LinearEquiv.ofInjective g hg).symm
  · intro x hx
    obtain ⟨y, ⟨z, hz⟩, hxy⟩ := hQ4 x.1 (Finset.mem_image_of_mem _ hx)
    have hyP : P y = y := by
      rw [← hz]
      exact congrArg (fun T : lp E ⊤ →L[K] lp E ⊤ => T z) (Pg_idem N Q hQ1)
    have hyS : y ∈ CZeroSum (K := K) (E := E) := hyP ▸ hmem y
    refine ⟨⟨y, hyS⟩, ⟨⟨y, hyS⟩, Subtype.ext hyP⟩, ?_⟩
    exact hxy

end X7CSums

universe u v

variable {K : Type*} [RCLike K]

open QAlgorithms.Papers.Independent.Renew46.P04 X7CSums in
theorem solution (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)]
    [∀ n, NormedSpace K (E n)] [∀ n, CompleteSpace (E n)] (h : ∀ n, MetricPi K (E n)) :
    MetricPi K (CZeroSum (K := K) (E := E)) ∧
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p < ⊤ → MetricPi K (lp E p) :=
  ⟨X7_c0 h, fun _ _ hp => X7_lp h hp⟩
