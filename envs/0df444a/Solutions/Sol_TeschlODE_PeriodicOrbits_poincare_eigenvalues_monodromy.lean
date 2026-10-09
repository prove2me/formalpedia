-- Prove2me | solution 1 for TeschlODE.PeriodicOrbits.poincare_eigenvalues_monodromy
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T00:31:15.83158+00:00
-- url     : https://prove2.me/submissions/6c402bcf-0a9b-47d6-80b9-1e1fda2ffe72

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow
import Definitions.Def_TeschlODE_PeriodicOrbits_IsRegularPeriodicPoint
import Definitions.Def_TeschlODE_PeriodicOrbits_IsTransversalSection
import Definitions.Def_TeschlODE_PeriodicOrbits_IsReturnTime
import Definitions.Def_TeschlODE_PeriodicOrbits_IsPoincareDerivative

set_option autoImplicit false

open Set Metric Filter Topology NNReal TeschlODE.Shared

namespace FA7570

section Flow
variable {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)} {M : Set (Fin n → ℝ)}
  {I : (Fin n → ℝ) → Set ℝ} {Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)}

theorem shift_curve (hΦ : IsMaximalFlow f M I Φ) {x : Fin n → ℝ} (hx : x ∈ M) (c : ℝ) :
    IsIntegralCurve f M {s | s + c ∈ I x} (fun s => Φ (s + c) x) := by
  obtain ⟨⟨h1, h2, h3, h4⟩, -⟩ := hΦ x hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h1.preimage (continuous_id.add continuous_const)
  · refine ⟨fun a ha b hb t ht => ?_⟩
    exact h2.out ha hb ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro t ht
    exact h3 (t + c) ht
  · intro t ht
    exact (h4 (t + c) ht).comp_add_const t c

theorem flow_shift (hΦ : IsMaximalFlow f M I Φ) {x : Fin n → ℝ} (hx : x ∈ M) {t : ℝ}
    (ht : t ∈ I x) {s : ℝ} (hs : s + t ∈ I x) :
    s ∈ I (Φ t x) ∧ Φ s (Φ t x) = Φ (s + t) x := by
  have hm : Φ t x ∈ M := (hΦ x hx).1.2.2.1 t ht
  have h := (hΦ _ hm).2.2.2 _ _ (shift_curve hΦ hx t) (by simpa using ht) (by simp)
  exact ⟨h.1 hs, (h.2 s hs).symm⟩

theorem flow_shift_inv (hΦ : IsMaximalFlow f M I Φ) {x : Fin n → ℝ} (hx : x ∈ M) {t : ℝ}
    (ht : t ∈ I x) {s : ℝ} (hs : s ∈ I (Φ t x)) : s + t ∈ I x := by
  have h0 : (0:ℝ) ∈ I x := (hΦ x hx).2.1
  have hm : Φ t x ∈ M := (hΦ x hx).1.2.2.1 t ht
  obtain ⟨hmt, hback⟩ := flow_shift hΦ hx ht (s := -t) (by simpa using h0)
  have hback' : Φ (-t) (Φ t x) = x := by rw [hback, neg_add_cancel, (hΦ x hx).2.2.1]
  have := (flow_shift hΦ hm hmt (s := s + t) (by simpa using hs)).1
  rwa [hback'] at this

end Flow

open ODE in
theorem exists_sol_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {a L K : ℝ≥0}
    (hg : IsPicardLindelof g t₀ x₀ a 0 L K) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ (∀ t, α t ∈ closedBall x₀ a) ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (g t (α t)) (Icc tmin tmax) t := by
  obtain ⟨α, hα⟩ := FunSpace.exists_isFixedPt_next hg (mem_closedBall_self le_rfl)
  refine ⟨α.compProj, ?_, fun t => α.compProj_mem_closedBall hg.mul_max_le, fun t ht ↦ ?_⟩
  · rw [FunSpace.compProj_val, ← hα, FunSpace.next_apply₀]
  · apply hasDerivWithinAt_picard_Icc t₀.2 hg.continuousOn_uncurry
      α.continuous_compProj.continuousOn (fun _ ht' ↦ α.compProj_mem_closedBall hg.mul_max_le)
      x₀ ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [FunSpace.compProj_of_mem ht', FunSpace.next_apply]

theorem unif_diff {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)} {M S : Set (Fin n → ℝ)}
    (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M) (hS : IsCompact S) (hSc : Convex ℝ S)
    (hSM : S ⊆ M) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ p ∈ S, ∀ q ∈ S, ‖p - q‖ < δ →
      ‖f p - f q - fderiv ℝ f q (p - q)‖ ≤ η * ‖p - q‖ := by
  have hcont : ContinuousOn (fderiv ℝ f) S :=
    (hf.continuousOn_fderiv_of_isOpen hM le_rfl).mono hSM
  have huc := hS.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc η hη
  refine ⟨δ, hδ, fun p hp q hq hpq => ?_⟩
  have hseg : segment ℝ q p ⊆ S := hSc.segment_subset hq hp
  refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := f) (f' := fderiv ℝ f)
    (fun c hc => ((hf.differentiableOn one_ne_zero c (hSM (hseg hc))).differentiableAt
      (hM.mem_nhds (hSM (hseg hc)))).hasFDerivAt.hasFDerivWithinAt)
    (fun c hc => ?_) (convex_segment q p) (left_mem_segment ℝ q p) (right_mem_segment ℝ q p)
  have hcq : dist c q < δ := by
    have h1 : dist c q ≤ dist q p := segment_subset_closedBall_left q p hc
    rw [dist_comm q p, dist_eq_norm p q] at h1
    linarith
  have := hδ' c (hseg hc) q hq hcq
  rw [dist_eq_norm] at this
  exact this.le

theorem uniform_local {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)} {M : Set (Fin n → ℝ)}
    {I : (Fin n → ℝ) → Set ℝ} {Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)} (hM : IsOpen M)
    (hf : ContDiffOn ℝ 1 f M) (hΦ : IsMaximalFlow f M I Φ) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKM : K ⊆ M) :
    ∃ a > (0:ℝ), ∃ B C ε : ℝ, 0 < ε ∧ 0 ≤ B ∧ 0 ≤ C ∧ 2 * C * ε ≤ 1 ∧
      cthickening (3 * a) K ⊆ M ∧
      (∀ p ∈ cthickening (3 * a) K, ‖f p‖ ≤ B ∧ ‖fderiv ℝ f p‖ ≤ C) ∧
      ∀ y ∈ cthickening (2 * a) K, ∀ s ∈ Ioo (-(2 * ε)) (2 * ε),
        s ∈ I y ∧ Φ s y ∈ closedBall y a := by
  obtain ⟨δ, hδ, hδM⟩ := hK.exists_cthickening_subset_open hM hKM
  set a : ℝ := δ / 3 with ha_def
  have ha : 0 < a := by positivity
  have h3a : 3 * a = δ := by rw [ha_def]; ring
  have hKc : IsCompact (cthickening δ K) := hK.cthickening
  obtain ⟨B0, hB0⟩ := hKc.exists_bound_of_continuousOn (hf.continuousOn.mono hδM)
  obtain ⟨C0, hC0⟩ := hKc.exists_bound_of_continuousOn
    ((hf.continuousOn_fderiv_of_isOpen hM le_rfl).mono hδM)
  set B : ℝ := max B0 0
  set C : ℝ := max C0 0
  have hB : 0 ≤ B := le_max_right _ _
  have hC : 0 ≤ C := le_max_right _ _
  set ε : ℝ := min a 1 / (4 * (B + C + 1)) with hε_def
  have hε : 0 < ε := by positivity
  have hmin1 : min a 1 ≤ 1 := min_le_right _ _
  have hmina : min a 1 ≤ a := min_le_left _ _
  have hBCpos : 0 < 4 * (B + C + 1) := by positivity
  have hCε : 2 * C * ε ≤ 1 := by
    rw [hε_def, mul_div_assoc', div_le_one hBCpos]
    nlinarith [min_le_right a 1, le_min ha.le zero_le_one]
  have hBε : B * (2 * ε) ≤ a := by
    have : B * (2 * ε) = (2 * B) * min a 1 / (4 * (B + C + 1)) := by rw [hε_def]; ring
    rw [this, div_le_iff₀ hBCpos]
    have hm0 : 0 ≤ min a 1 := le_min ha.le zero_le_one
    nlinarith
  refine ⟨a, ha, B, C, ε, hε, hB, hC, hCε, by rw [h3a]; exact hδM, fun p hp => ?_, ?_⟩
  · rw [h3a] at hp
    exact ⟨(hB0 p hp).trans (le_max_left _ _), (hC0 p hp).trans (le_max_left _ _)⟩
  intro y hy
  have hball : closedBall y a ⊆ cthickening δ K := by
    refine (closedBall_subset_cthickening hy a).trans ?_
    refine (cthickening_cthickening_subset ha.le (by positivity) K).trans ?_
    rw [← h3a]; apply cthickening_mono; linarith
  have hyM : y ∈ M := hδM (hball (mem_closedBall_self ha.le))
  have hdiff : ∀ p ∈ closedBall y a, HasFDerivWithinAt f (fderiv ℝ f p) (closedBall y a) p :=
    fun p hp => ((hf.differentiableOn one_ne_zero p (hδM (hball hp))).differentiableAt
      (hM.mem_nhds (hδM (hball hp)))).hasFDerivAt.hasFDerivWithinAt
  have hlip : LipschitzOnWith C.toNNReal f (closedBall y a) :=
    (convex_closedBall y a).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le hdiff
      (fun p hp => by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal C hC]
        exact (hC0 p (hball hp)).trans (le_max_left _ _))
  have hPL : IsPicardLindelof (fun _ => f) (tmin := -(2 * ε)) (tmax := 2 * ε)
      ⟨0, by constructor <;> linarith⟩ y a.toNNReal 0 B.toNNReal C.toNNReal := by
    apply IsPicardLindelof.of_time_independent
    · intro p hp
      rw [Real.coe_toNNReal a ha.le] at hp
      rw [Real.coe_toNNReal B hB]
      exact (hB0 p (hball hp)).trans (le_max_left _ _)
    · rw [Real.coe_toNNReal a ha.le]; exact hlip
    · simp only [Real.coe_toNNReal B hB, Real.coe_toNNReal a ha.le, NNReal.coe_zero, sub_zero,
        zero_sub, neg_neg, max_self]
      exact hBε
  obtain ⟨α, hα0, hαmem, hαd⟩ := exists_sol_mem hPL
  have hcurve : IsIntegralCurve f M (Ioo (-(2 * ε)) (2 * ε)) α := by
    refine ⟨isOpen_Ioo, ordConnected_Ioo, fun t _ => hδM (hball (by simpa [Real.coe_toNNReal a ha.le] using hαmem t)), fun t ht => ?_⟩
    exact (hαd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have h0 : (0:ℝ) ∈ Ioo (-(2 * ε)) (2 * ε) := ⟨by linarith, by linarith⟩
  have hmax := (hΦ y hyM).2.2.2 _ α hcurve h0 hα0
  intro s hs
  refine ⟨hmax.1 hs, ?_⟩
  rw [← hmax.2 s hs]
  have := hαmem s
  rwa [Real.coe_toNNReal a ha.le] at this

end FA7570

namespace FA7570

theorem gronwall_scale (K e x : ℝ) : gronwallBound 0 K e x = e * gronwallBound 0 K 1 x := by
  unfold gronwallBound; split_ifs <;> ring

theorem local_hasFDeriv {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)} {M : Set (Fin n → ℝ)}
    {I : (Fin n → ℝ) → Set ℝ} {Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)} (hM : IsOpen M)
    (hf : ContDiffOn ℝ 1 f M) (hΦ : IsMaximalFlow f M I Φ) {K : Set (Fin n → ℝ)}
    {a B C ε : ℝ} (ha : 0 < a) (hε : 0 < ε) (hC : 0 ≤ C) (hCε : 2 * C * ε ≤ 1)
    (hKM : cthickening (3 * a) K ⊆ M)
    (hbd : ∀ p ∈ cthickening (3 * a) K, ‖f p‖ ≤ B ∧ ‖fderiv ℝ f p‖ ≤ C)
    (hloc : ∀ y ∈ cthickening (2 * a) K, ∀ s ∈ Ioo (-(2 * ε)) (2 * ε),
        s ∈ I y ∧ Φ s y ∈ closedBall y a)
    {y : Fin n → ℝ} (hy : y ∈ cthickening a K) {s : ℝ} (hs : s ∈ Icc 0 ε) :
    ∃ D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ), HasFDerivAt (Φ s) D y := by
  have hball2 : closedBall y (2 * a) ⊆ cthickening (3 * a) K := by
    refine (closedBall_subset_cthickening hy (2 * a)).trans ?_
    refine (cthickening_cthickening_subset (by positivity) ha.le K).trans ?_
    apply cthickening_mono; linarith
  have hy2 : ∀ w ∈ closedBall y a, w ∈ cthickening (2 * a) K := by
    intro w hw
    have := ((closedBall_subset_cthickening hy a).trans
      (cthickening_cthickening_subset ha.le ha.le K)) hw
    exact cthickening_mono (by linarith) K this
  have hyM : y ∈ M := hKM (hball2 (mem_closedBall_self (by positivity)))
  have hsol : ∀ w ∈ closedBall y a, ∀ r ∈ Ioo (-(2 * ε)) (2 * ε),
      Φ r w ∈ closedBall y (2 * a) ∧ HasDerivAt (fun r => Φ r w) (f (Φ r w)) r := by
    intro w hw r hr
    obtain ⟨hrI, hrb⟩ := hloc w (hy2 w hw) r hr
    have hwM : w ∈ M := hKM (hball2 (closedBall_subset_closedBall (by linarith) hw))
    refine ⟨?_, (hΦ w hwM).1.2.2.2 r hrI⟩
    rw [mem_closedBall] at hw hrb ⊢
    linarith [dist_triangle (Φ r w) w y]
  have hdiff : ∀ p ∈ closedBall y (2 * a), HasFDerivAt f (fderiv ℝ f p) p :=
    fun p hp => ((hf.differentiableOn one_ne_zero p (hKM (hball2 hp))).differentiableAt
      (hM.mem_nhds (hKM (hball2 hp)))).hasFDerivAt
  have hlip : LipschitzOnWith C.toNNReal f (closedBall y (2 * a)) :=
    (convex_closedBall y (2 * a)).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun p hp => (hdiff p hp).hasFDerivWithinAt)
      (fun p hp => by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal C hC]
        exact (hbd p (hball2 hp)).2)
  have hyb : y ∈ closedBall y a := mem_closedBall_self ha.le
  have hIcc : ∀ r ∈ Icc 0 ε, r ∈ Ioo (-(2 * ε)) (2 * ε) :=
    fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩
  set u : ℝ → (Fin n → ℝ) := fun r => Φ r y with hu
  set A : ℝ → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) := fun r => fderiv ℝ f (u r) with hA
  have hAc : ContinuousOn A (Icc 0 ε) := by
    have h1 := hf.continuousOn_fderiv_of_isOpen hM le_rfl
    have h2 : ContinuousOn u (Icc 0 ε) := fun r hr =>
      (hsol y hyb r (hIcc r hr)).2.continuousAt.continuousWithinAt
    exact h1.comp h2 (fun r hr => hKM (hball2 (hsol y hyb r (hIcc r hr)).1))
  have hAb : ∀ r ∈ Icc 0 ε, ‖A r‖ ≤ C :=
    fun r hr => (hbd _ (hball2 (hsol y hyb r (hIcc r hr)).1)).2
  have hPL : IsPicardLindelof (fun r (J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) => (A r).comp J)
      (tmin := 0) (tmax := ε) ⟨0, ⟨le_rfl, hε.le⟩⟩ (ContinuousLinearMap.id ℝ _)
      1 0 (2 * C).toNNReal C.toNNReal := by
    refine { lipschitzOnWith := ?_, continuousOn := ?_, norm_le := ?_, mul_max_le := ?_ }
    · intro r hr
      rw [lipschitzOnWith_iff_norm_sub_le]
      intro J1 _ J2 _
      rw [← ContinuousLinearMap.comp_sub, Real.coe_toNNReal C hC]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hAb r hr) (norm_nonneg _))
    · intro J _
      exact hAc.clm_comp continuousOn_const
    · intro r hr J hJ
      have hJ' : ‖J‖ ≤ 2 := by
        rw [mem_closedBall, dist_eq_norm, NNReal.coe_one] at hJ
        have h1 := norm_sub_norm_le J (ContinuousLinearMap.id ℝ (Fin n → ℝ))
        have h2 := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Fin n → ℝ)
        linarith
      rw [Real.coe_toNNReal _ (by positivity)]
      calc ‖(A r).comp J‖ ≤ ‖A r‖ * ‖J‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ C * 2 := mul_le_mul (hAb r hr) hJ' (norm_nonneg _) hC
        _ = 2 * C := by ring
    · rw [Real.coe_toNNReal _ (by positivity)]
      norm_num [max_eq_left hε.le]
      linarith
  obtain ⟨J, hJ0, -, hJd⟩ := exists_sol_mem hPL
  have hJ0' : J 0 = ContinuousLinearMap.id ℝ _ := hJ0
  have hJc : ContinuousOn J (Icc 0 ε) := fun r hr => (hJd r hr).continuousWithinAt
  refine ⟨J s, ?_⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  set G : ℝ := gronwallBound 0 C 1 s with hG
  set E0 : ℝ := Real.exp (C * ε) with hE0def
  have hE0 : 0 < E0 := Real.exp_pos _
  set η : ℝ := c / (E0 * (|G| + 1)) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨δ₁, hδ₁, hUD⟩ := unif_diff hM hf (isCompact_closedBall y (2 * a))
    (convex_closedBall y (2 * a)) (fun p hp => hKM (hball2 hp)) hη
  have hρ : 0 < min a (δ₁ / E0) := lt_min ha (div_pos hδ₁ hE0)
  filter_upwards [Metric.ball_mem_nhds (0 : Fin n → ℝ) hρ] with h hh
  rw [mem_ball_zero_iff] at hh
  have hha : ‖h‖ < a := lt_of_lt_of_le hh (min_le_left _ _)
  have hhδ : ‖h‖ * E0 < δ₁ := by
    have := lt_of_lt_of_le hh (min_le_right _ _)
    rwa [lt_div_iff₀ hE0] at this
  have hyh : y + h ∈ closedBall y a := by
    rw [mem_closedBall, dist_eq_norm]; simpa using hha.le
  have hyhM : y + h ∈ M := hKM (hball2 (closedBall_subset_closedBall (by linarith) hyh))
  set v : ℝ → (Fin n → ℝ) := fun r => Φ r (y + h) with hv
  have hsε : Icc 0 s ⊆ Icc 0 ε := Icc_subset_Icc_right hs.2
  have hv0 : v 0 = y + h := (hΦ _ hyhM).2.2.1
  have hu0 : u 0 = y := (hΦ _ hyM).2.2.1
  have hdist : ∀ r ∈ Icc 0 s, dist (v r) (u r) ≤ dist (y + h) y * Real.exp (C * (r - 0)) := by
    have := dist_le_of_trajectories_ODE_of_mem (v := fun _ => f)
      (s := fun _ => closedBall y (2 * a)) (K := C.toNNReal) (f := v) (g := u)
      (a := 0) (b := s) (δ := dist (y + h) y)
      (fun _ _ => hlip)
      (fun r hr => (hsol _ hyh r (hIcc r (hsε hr))).2.continuousAt.continuousWithinAt)
      (fun r hr => (hsol _ hyh r (hIcc r (hsε (Ico_subset_Icc_self hr)))).2.hasDerivWithinAt)
      (fun r hr => (hsol _ hyh r (hIcc r (hsε (Ico_subset_Icc_self hr)))).1)
      (fun r hr => (hsol _ hyb r (hIcc r (hsε hr))).2.continuousAt.continuousWithinAt)
      (fun r hr => (hsol _ hyb r (hIcc r (hsε (Ico_subset_Icc_self hr)))).2.hasDerivWithinAt)
      (fun r hr => (hsol _ hyb r (hIcc r (hsε (Ico_subset_Icc_self hr)))).1)
      (by rw [hv0, hu0])
    intro r hr
    simpa [Real.coe_toNNReal C hC] using this r hr
  have hvu : ∀ r ∈ Icc 0 s, ‖v r - u r‖ ≤ ‖h‖ * E0 := by
    intro r hr
    have h1 := hdist r hr
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, sub_zero] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [hE0def]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hr.2.trans hs.2) hC)
  have hR := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun r => v r - u r - J r h)
    (f' := fun r => f (v r) - f (u r) - (A r) (J r h)) (δ := 0) (K := C)
    (ε := η * (‖h‖ * E0)) (a := 0) (b := s) ?_ ?_ ?_ ?_ s ⟨hs.1, le_rfl⟩
  · rw [sub_zero, gronwall_scale] at hR
    have hR' : ‖Φ s (y + h) - Φ s y - (J s) h‖ ≤ η * (‖h‖ * E0) * G := hR
    have hG' : G ≤ |G| := le_abs_self G
    have hkey : η * (E0 * (|G| + 1)) = c := by
      rw [hηdef]; field_simp
    have hpos : 0 ≤ η * (‖h‖ * E0) := by positivity
    calc ‖Φ s (y + h) - Φ s y - (J s) h‖ ≤ η * (‖h‖ * E0) * G := hR'
      _ ≤ η * (‖h‖ * E0) * (|G| + 1) := by
          apply mul_le_mul_of_nonneg_left _ hpos; linarith
      _ = (η * (E0 * (|G| + 1))) * ‖h‖ := by ring
      _ = c * ‖h‖ := by rw [hkey]
  · have hvc : ContinuousOn v (Icc 0 s) := fun r hr =>
      (hsol _ hyh r (hIcc r (hsε hr))).2.continuousAt.continuousWithinAt
    have huc : ContinuousOn u (Icc 0 s) := fun r hr =>
      (hsol _ hyb r (hIcc r (hsε hr))).2.continuousAt.continuousWithinAt
    exact (hvc.sub huc).sub ((hJc.mono hsε).clm_apply continuousOn_const)
  · intro r hr
    have hrε : r ∈ Ico 0 ε := ⟨hr.1, lt_of_lt_of_le hr.2 hs.2⟩
    have hrI : r ∈ Icc 0 ε := Ico_subset_Icc_self hrε
    have hJr : HasDerivWithinAt J ((A r).comp (J r)) (Ici r) r :=
      (hJd r hrI).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hrε)
    have hJh : HasDerivWithinAt (fun r => J r h) ((A r) (J r h)) (Ici r) r := by
      have := hJr.clm_apply (hasDerivWithinAt_const r (Ici r) h)
      simpa using this
    exact (((hsol _ hyh r (hIcc r hrI)).2.hasDerivWithinAt).sub
      ((hsol _ hyb r (hIcc r hrI)).2.hasDerivWithinAt)).sub hJh
  · simp [hv0, hu0, hJ0']
  · intro r hr
    have hrI : r ∈ Icc 0 s := Ico_subset_Icc_self hr
    have hrε : r ∈ Icc 0 ε := hsε hrI
    have e : f (v r) - f (u r) - (A r) (J r h) =
        (f (v r) - f (u r) - (A r) (v r - u r)) + (A r) (v r - u r - J r h) := by
      simp only [map_sub]; abel
    rw [e]
    have hvb := (hsol _ hyh r (hIcc r hrε)).1
    have hub := (hsol _ hyb r (hIcc r hrε)).1
    have h1 : ‖f (v r) - f (u r) - (A r) (v r - u r)‖ ≤ η * (‖h‖ * E0) := by
      have := hUD (v r) hvb (u r) hub (lt_of_le_of_lt (hvu r hrI) hhδ)
      exact this.trans (mul_le_mul_of_nonneg_left (hvu r hrI) hη.le)
    have h2 : ‖(A r) (v r - u r - J r h)‖ ≤ C * ‖v r - u r - J r h‖ :=
      ((A r).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hAb r hrε) (norm_nonneg _))
    calc _ ≤ ‖f (v r) - f (u r) - (A r) (v r - u r)‖ + ‖(A r) (v r - u r - J r h)‖ :=
          norm_add_le _ _
      _ ≤ C * ‖v r - u r - J r h‖ + η * (‖h‖ * E0) := by linarith

end FA7570

namespace FA7570

theorem flow_diff_forward {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)} {M : Set (Fin n → ℝ)}
    {I : (Fin n → ℝ) → Set ℝ} {Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)} (hM : IsOpen M)
    (hf : ContDiffOn ℝ 1 f M) (hΦ : IsMaximalFlow f M I Φ)
    {x : Fin n → ℝ} (hx : x ∈ M) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ∈ I x) :
    (∀ᶠ y in 𝓝 x, y ∈ M ∧ t ∈ I y) ∧ DifferentiableAt ℝ (Φ t) x := by
  obtain ⟨⟨hIo, hIc, hmem, hder⟩, h0, hΦ0, -⟩ := hΦ x hx
  have hsub : Icc 0 t ⊆ I x := hIc.out h0 ht
  have hcont : ContinuousOn (fun r => Φ r x) (Icc 0 t) :=
    fun r hr => (hder r (hsub hr)).continuousAt.continuousWithinAt
  set K := (fun r => Φ r x) '' Icc 0 t with hKdef
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hcont
  have hKM : K ⊆ M := by
    rintro _ ⟨r, hr, rfl⟩; exact hmem r (hsub hr)
  obtain ⟨a, ha, B, C, ε, hε, hB, hC, hCε, hKM', hbd, hloc⟩ :=
    uniform_local hM hf hΦ hK hKM
  let P : ℝ → Prop := fun r => (∀ᶠ y in 𝓝 x, y ∈ M ∧ r ∈ I y) ∧ DifferentiableAt ℝ (Φ r) x
  have hP0 : P 0 := by
    have hev : ∀ᶠ y in 𝓝 x, y ∈ M := hM.mem_nhds hx
    refine ⟨hev.mono fun y hy => ⟨hy, (hΦ y hy).2.1⟩, ?_⟩
    have heq : (Φ 0) =ᶠ[𝓝 x] id := hev.mono fun y hy => (hΦ y hy).2.2.1
    exact differentiableAt_id.congr_of_eventuallyEq heq
  have hstep : ∀ N : ℕ, ∀ r ∈ Icc 0 t, r ≤ N * ε → P r := by
    intro N
    induction N with
    | zero =>
      intro r hr hrN
      have : r = 0 := le_antisymm (by simpa using hrN) hr.1
      rw [this]; exact hP0
    | succ N ih =>
      intro r hr hrN
      by_cases hle : r ≤ N * ε
      · exact ih r hr hle
      rw [not_le] at hle
      have hN0 : (0:ℝ) ≤ N * ε := by positivity
      set r₁ : ℝ := N * ε with hr₁
      have hr₁t : r₁ ∈ Icc 0 t := ⟨hN0, by linarith [hr.2]⟩
      obtain ⟨hev₁, hd₁⟩ := ih r₁ hr₁t le_rfl
      set σ : ℝ := r - r₁ with hσ
      have hσ0 : 0 ≤ σ := by linarith
      have hσε : σ ≤ ε := by push_cast at hrN; linarith
      have hz : Φ r₁ x ∈ K := ⟨r₁, hr₁t, rfl⟩
      have hthick : thickening a K ∈ 𝓝 (Φ r₁ x) :=
        isOpen_thickening.mem_nhds (self_subset_thickening ha K hz)
      have hev₂ : ∀ᶠ y in 𝓝 x, Φ r₁ y ∈ thickening a K :=
        hd₁.continuousAt.preimage_mem_nhds hthick
      have hgood : ∀ᶠ y in 𝓝 x, y ∈ M ∧ r ∈ I y ∧ Φ r y = Φ σ (Φ r₁ y) := by
        filter_upwards [hev₁, hev₂] with y hy1 hy2
        obtain ⟨hyM, hr₁y⟩ := hy1
        have hc2 : Φ r₁ y ∈ cthickening (2 * a) K :=
          cthickening_mono (by linarith) K (thickening_subset_cthickening a K hy2)
        have hσI : σ ∈ I (Φ r₁ y) :=
          (hloc _ hc2 σ ⟨by linarith, by linarith⟩).1
        have hrI : σ + r₁ ∈ I y := flow_shift_inv hΦ hyM hr₁y hσI
        have hσr : σ + r₁ = r := by rw [hσ]; ring
        rw [hσr] at hrI
        refine ⟨hyM, hrI, ?_⟩
        have := (flow_shift hΦ hyM hr₁y (s := σ) (by rw [hσr]; exact hrI)).2
        rw [this, hσr]
      refine ⟨hgood.mono fun y hy => ⟨hy.1, hy.2.1⟩, ?_⟩
      have hzc : Φ r₁ x ∈ cthickening a K := self_subset_cthickening K hz
      obtain ⟨D, hD⟩ := local_hasFDeriv hM hf hΦ ha hε hC hCε hKM' hbd hloc hzc ⟨hσ0, hσε⟩
      have hcomp : DifferentiableAt ℝ (fun y => Φ σ (Φ r₁ y)) x :=
        hD.differentiableAt.comp x hd₁
      exact hcomp.congr_of_eventuallyEq (hgood.mono fun y hy => hy.2.2)
  obtain ⟨N, hN⟩ := exists_nat_ge (t / ε)
  have : t ≤ N * ε := by rwa [div_le_iff₀ hε] at hN
  exact hstep N t ⟨ht0, le_rfl⟩ this

end FA7570

namespace FA7570

theorem abs_le_of_mem_uIcc0 {s r : ℝ} (hr : r ∈ uIcc 0 s) : |r| ≤ |s| := by
  rcases Set.mem_uIcc.1 hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
  · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith

theorem joint_at_zero {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)} {M : Set (Fin n → ℝ)}
    {I : (Fin n → ℝ) → Set ℝ} {Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)} (hM : IsOpen M)
    (hf : ContDiffOn ℝ 1 f M) (hΦ : IsMaximalFlow f M I Φ) {z : Fin n → ℝ} (hz : z ∈ M) :
    HasFDerivAt (fun q : ℝ × (Fin n → ℝ) => Φ q.1 q.2)
      ((ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)).smulRight (f z) +
        ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)) ((0 : ℝ), z) := by
  obtain ⟨a, ha, B, C, ε, hε, hB, hC, -, hKM, hbd, hloc⟩ :=
    uniform_local hM hf hΦ isCompact_singleton (singleton_subset_iff.2 hz)
  have hw2 : ∀ w ∈ closedBall z a, w ∈ cthickening (2 * a) ({z} : Set (Fin n → ℝ)) := by
    intro w hw
    rw [cthickening_singleton _ (by positivity)]
    exact closedBall_subset_closedBall (by linarith) hw
  have hwM : ∀ w ∈ closedBall z a, w ∈ M := by
    intro w hw
    apply hKM
    rw [cthickening_singleton _ (by positivity)]
    exact closedBall_subset_closedBall (by linarith) hw
  have hsol : ∀ w ∈ closedBall z a, ∀ r ∈ Ioo (-(2 * ε)) (2 * ε),
      ‖f (Φ r w)‖ ≤ B ∧ HasDerivAt (fun r => Φ r w) (f (Φ r w)) r := by
    intro w hw r hr
    obtain ⟨hrI, hrb⟩ := hloc w (hw2 w hw) r hr
    have hb3 : Φ r w ∈ cthickening (3 * a) ({z} : Set (Fin n → ℝ)) := by
      rw [cthickening_singleton _ (by positivity)]
      rw [mem_closedBall] at hw hrb ⊢
      linarith [dist_triangle (Φ r w) w z]
    exact ⟨(hbd _ hb3).1, (hΦ w (hwM w hw)).1.2.2.2 r hrI⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hfc : ContinuousAt f z := hf.continuousOn.continuousAt (hM.mem_nhds hz)
  rw [Metric.continuousAt_iff] at hfc
  obtain ⟨δ, hδ, hδf⟩ := hfc c hc
  set e : ℝ := δ / (2 * (B + 1)) with he_def
  have he : 0 < e := by positivity
  have he2 : e * (2 * (B + 1)) = δ := by rw [he_def]; field_simp
  have hρ : 0 < min (min a ε) e := lt_min (lt_min ha hε) he
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ × (Fin n → ℝ)) hρ] with q hq
  obtain ⟨s, h⟩ := q
  rw [mem_ball_zero_iff] at hq
  have hs' : ‖s‖ < min (min a ε) e := lt_of_le_of_lt (norm_fst_le (s, h)) hq
  have hh' : ‖h‖ < min (min a ε) e := lt_of_le_of_lt (norm_snd_le (s, h)) hq
  rw [Real.norm_eq_abs] at hs'
  have hsε : |s| < ε := lt_of_lt_of_le hs' ((min_le_left _ _).trans (min_le_right _ _))
  have hse : |s| < e := lt_of_lt_of_le hs' (min_le_right _ _)
  have hha : ‖h‖ < a := lt_of_lt_of_le hh' ((min_le_left _ _).trans (min_le_left _ _))
  have hhe : ‖h‖ < e := lt_of_lt_of_le hh' (min_le_right _ _)
  set w : Fin n → ℝ := z + h with hw_def
  have hw : w ∈ closedBall z a := by
    rw [mem_closedBall, dist_eq_norm, hw_def]; simpa using hha.le
  have hIoo : ∀ r ∈ uIcc 0 s, r ∈ Ioo (-(2 * ε)) (2 * ε) := by
    intro r hr
    have := abs_le_of_mem_uIcc0 hr
    rw [abs_le] at this
    constructor <;> cases abs_cases s <;> linarith [abs_nonneg s]
  have hw0 : Φ 0 w = w := (hΦ w (hwM w hw)).2.2.1
  have hz0 : Φ 0 z = z := (hΦ z hz).2.2.1
  -- speed bound
  have hspeed : ∀ r ∈ uIcc 0 s, ‖Φ r w - w‖ ≤ B * |r| := by
    intro r hr
    have hsub : uIcc 0 r ⊆ uIcc 0 s := uIcc_subset_uIcc left_mem_uIcc hr
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun r => Φ r w)
      (f' := fun r => f (Φ r w)) (C := B) (s := uIcc 0 r) (x := 0) (y := r)
      (fun x hx => (hsol w hw x (hIoo x (hsub hx))).2.hasDerivWithinAt)
      (fun x hx => (hsol w hw x (hIoo x (hsub hx))).1) (convex_uIcc 0 r) left_mem_uIcc right_mem_uIcc
    simpa [hw0, Real.norm_eq_abs] using this
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun r => Φ r w - r • f z) (f' := fun r => f (Φ r w) - f z) (C := c) (s := uIcc 0 s)
    (x := 0) (y := s)
    (fun x hx => by
      have h1 := (hsol w hw x (hIoo x hx)).2
      have h2 := (hasDerivAt_id' x).smul_const (f z)
      have h3 := h1.sub h2
      rw [one_smul] at h3
      exact h3.hasDerivWithinAt)
    (fun x hx => by
      have hxs := abs_le_of_mem_uIcc0 hx
      have h1 := hspeed x hx
      have hd : dist (Φ x w) z < δ := by
        rw [dist_eq_norm]
        have : Φ x w - z = (Φ x w - w) + h := by rw [hw_def]; abel
        rw [this]
        have hBx : B * |x| ≤ B * e := mul_le_mul_of_nonneg_left (hxs.trans hse.le) hB
        calc ‖(Φ x w - w) + h‖ ≤ ‖Φ x w - w‖ + ‖h‖ := norm_add_le _ _
          _ < B * e + e := by linarith
          _ = δ / 2 := by rw [← he2]; ring
          _ < δ := by linarith
      have := hδf hd
      rw [dist_eq_norm] at this
      exact this.le)
    (convex_uIcc 0 s) left_mem_uIcc right_mem_uIcc
  simp only [Prod.fst_add, Prod.snd_add, zero_add, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd']
  have heq : Φ s (z + h) - Φ 0 z - (s • f z + h) = (Φ s w - s • f z) - (Φ 0 w - (0:ℝ) • f z) := by
    rw [hw0, hz0, hw_def, zero_smul, sub_zero]; abel
  rw [heq]
  refine hmain.trans ?_
  rw [sub_zero]
  exact mul_le_mul_of_nonneg_left (norm_fst_le (s, h)) hc.le

theorem poincare_hasFDeriv {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)} {M : Set (Fin n → ℝ)}
    {I : (Fin n → ℝ) → Set ℝ} {Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)} (hM : IsOpen M)
    (hf : ContDiffOn ℝ 1 f M) (hΦ : IsMaximalFlow f M I Φ) {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ M)
    {T : ℝ} (hT0 : 0 ≤ T) (hTI : T ∈ I x₀) (hper : Φ T x₀ = x₀)
    {τ : (Fin n → ℝ) → ℝ} {dτ : (Fin n → ℝ) →L[ℝ] ℝ} (hτd : HasFDerivAt τ dτ x₀)
    (hτx : τ x₀ = T) (hτI : ∀ᶠ y in 𝓝 x₀, τ y ∈ I y) :
    HasFDerivAt (fun y => Φ (τ y) y)
      (((ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)).smulRight (f x₀) +
        ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)).comp (dτ.prod (fderiv ℝ (Φ T) x₀))) x₀ := by
  obtain ⟨hev, hdT⟩ := flow_diff_forward hM hf hΦ hx₀ hT0 hTI
  have hF : HasFDerivAt (fun y => (τ y - T, Φ T y)) (dτ.prod (fderiv ℝ (Φ T) x₀)) x₀ :=
    (hτd.sub_const T).prodMk hdT.hasFDerivAt
  have hG := joint_at_zero hM hf hΦ hx₀
  have hF0 : (τ x₀ - T, Φ T x₀) = ((0:ℝ), x₀) := by rw [hτx, hper, sub_self]
  have hG' : HasFDerivAt (fun q : ℝ × (Fin n → ℝ) => Φ q.1 q.2)
      ((ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)).smulRight (f x₀) +
        ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)) (τ x₀ - T, Φ T x₀) := by
    rw [hF0]; exact hG
  have hcomp := hG'.comp x₀ hF
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hev, hτI] with y hy1 hy2
  have := (flow_shift hΦ hy1.1 hy1.2 (s := τ y - T) (by rwa [sub_add_cancel])).2
  simp only [Function.comp_apply]
  rw [this, sub_add_cancel]

theorem fderiv_flow_field {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)} {M : Set (Fin n → ℝ)}
    {I : (Fin n → ℝ) → Set ℝ} {Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)} (hM : IsOpen M)
    (hf : ContDiffOn ℝ 1 f M) (hΦ : IsMaximalFlow f M I Φ) {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ M)
    {T : ℝ} (hT0 : 0 ≤ T) (hTI : T ∈ I x₀) (hper : Φ T x₀ = x₀) :
    fderiv ℝ (Φ T) x₀ (f x₀) = f x₀ := by
  obtain ⟨-, hdT⟩ := flow_diff_forward hM hf hΦ hx₀ hT0 hTI
  obtain ⟨⟨hIo, -, -, hder⟩, h0, hΦ0, -⟩ := hΦ x₀ hx₀
  have hd0 : HasDerivAt (fun s => Φ s x₀) (f x₀) 0 := by
    have := hder 0 h0
    simpa only [hΦ0] using this
  have hl : HasFDerivAt (Φ T) (fderiv ℝ (Φ T) x₀) ((fun s => Φ s x₀) 0) := by
    simp only [hΦ0]; exact hdT.hasFDerivAt
  have h1 := hl.comp_hasDerivAt (0:ℝ) hd0
  have hev : ∀ᶠ s in 𝓝 (0:ℝ), s ∈ I x₀ ∧ T + s ∈ I x₀ := by
    have e1 : ∀ᶠ s in 𝓝 (0:ℝ), s ∈ I x₀ := hIo.mem_nhds h0
    have e2 : ∀ᶠ s in 𝓝 (0:ℝ), T + s ∈ I x₀ := by
      have hc : Continuous fun s : ℝ => T + s := continuous_const.add continuous_id
      have := hc.continuousAt (x := 0) |>.preimage_mem_nhds (by simpa using hIo.mem_nhds hTI)
      exact this
    exact e1.and e2
  have h2 : HasDerivAt (fun s => Φ s x₀) (fderiv ℝ (Φ T) x₀ (f x₀)) 0 := by
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hev] with s hs
    have a1 := (flow_shift hΦ hx₀ hs.1 (s := T) hs.2).2
    have a2 := (flow_shift hΦ hx₀ hTI (s := s) (by rw [add_comm]; exact hs.2)).2
    rw [hper] at a2
    simp only [Function.comp_apply]
    rw [a1, a2, add_comm]
  exact h2.unique hd0

end FA7570

namespace FA7570

open Module in
theorem charpoly_split {n : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (v₀ : Fin n → ℝ) (hv₀ : A v₀ = v₀)
    (ℓ : (Fin n → ℝ) →ₗ[ℝ] ℝ) (hℓ : ℓ v₀ ≠ 0) (L : Module.End ℝ (LinearMap.ker ℓ))
    (hL : ∀ w : LinearMap.ker ℓ, ∃ c : ℝ, (L w : Fin n → ℝ) = A w + c • v₀) :
    A.charpoly = (Polynomial.X - 1) * L.charpoly := by
  let φ : (ℝ × LinearMap.ker ℓ) →ₗ[ℝ] (Fin n → ℝ) := (LinearMap.toSpanSingleton ℝ _ v₀).coprod (LinearMap.ker ℓ).subtype
  have hφ : ∀ p : ℝ × LinearMap.ker ℓ, φ p = p.1 • v₀ + (p.2 : Fin n → ℝ) := fun p => by
    simp [φ, LinearMap.coprod_apply]
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hφ] at hp
    have h1 : ℓ (p.1 • v₀ + (p.2 : Fin n → ℝ)) = 0 := by rw [hp, map_zero]
    rw [map_add, map_smul, LinearMap.mem_ker.1 p.2.2, add_zero, smul_eq_mul] at h1
    have hc : p.1 = 0 := (mul_eq_zero.1 h1).resolve_right hℓ
    rw [hc, zero_smul, zero_add] at hp
    exact Prod.ext hc (by simpa using hp)
  have hsurj : Function.Surjective φ := by
    intro x
    refine ⟨(ℓ x / ℓ v₀, ⟨x - (ℓ x / ℓ v₀) • v₀, ?_⟩), ?_⟩
    · rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hℓ, sub_self]
    · rw [hφ]; simp
  let e : (ℝ × LinearMap.ker ℓ) ≃ₗ[ℝ] (Fin n → ℝ) := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have he : ∀ p, e p = p.1 • v₀ + (p.2 : Fin n → ℝ) := fun p => hφ p
  set B : Module.End ℝ (ℝ × LinearMap.ker ℓ) := e.symm.conj A with hB
  have hBapp : ∀ p, B p = e.symm (A (e p)) := fun p => by
    simp [hB, LinearEquiv.conj_apply]
  have hB1 : B (1, 0) = (1, 0) := by
    rw [hBapp, LinearEquiv.symm_apply_eq, he]
    simp [hv₀]
  have hB2 : ∀ w : LinearMap.ker ℓ, (B (0, w)).2 = L w := by
    intro w
    obtain ⟨c, hc⟩ := hL w
    have : B (0, w) = (-c, L w) := by
      rw [hBapp, LinearEquiv.symm_apply_eq, he, he]
      simp only [zero_smul, zero_add, neg_smul]
      rw [hc]; abel
    rw [this]
  have hchar : A.charpoly = B.charpoly := by
    rw [hB, LinearEquiv.charpoly_conj]
  rw [hchar]
  let bW := Module.Free.chooseBasis ℝ (LinearMap.ker ℓ)
  let b := (Basis.singleton (Fin 1) ℝ).prod bW
  rw [← LinearMap.charpoly_toMatrix B b, ← Matrix.fromBlocks_toBlocks (LinearMap.toMatrix b b B)]
  have h21 : (LinearMap.toMatrix b b B).toBlocks₂₁ = 0 := by
    ext i j
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply, LinearMap.toMatrix_apply]
    have hbj : b (Sum.inl j) = (1, 0) := by
      ext
      · simp [b, Basis.prod_apply_inl_fst]
      · simp [b, Basis.prod_apply_inl_snd]
    rw [hbj, hB1, Basis.prod_repr_inr]
    simp
  have h11 : (LinearMap.toMatrix b b B).toBlocks₁₁ = 1 := by
    ext i j
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, LinearMap.toMatrix_apply]
    have hbj : b (Sum.inl j) = (1, 0) := by
      ext
      · simp [b, Basis.prod_apply_inl_fst]
      · simp [b, Basis.prod_apply_inl_snd]
    rw [hbj, hB1, Basis.prod_repr_inl]
    have hij : i = j := Subsingleton.elim i j
    subst hij
    simp
  have h22 : (LinearMap.toMatrix b b B).toBlocks₂₂ = LinearMap.toMatrix bW bW L := by
    ext i j
    simp only [Matrix.toBlocks₂₂, Matrix.of_apply, LinearMap.toMatrix_apply]
    have hbj : b (Sum.inr j) = (0, bW j) := by
      ext
      · simp [b, Basis.prod_apply_inr_fst]
      · simp [b, Basis.prod_apply_inr_snd]
    rw [hbj, Basis.prod_repr_inr, hB2]
  rw [h21, h11, h22, Matrix.charpoly_fromBlocks_zero₂₁, Matrix.charpoly_one,
    LinearMap.charpoly_toMatrix]
  simp

end FA7570

namespace FA7570

theorem shift_down {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (M : Set (Fin n → ℝ)) (I : (Fin n → ℝ) → Set ℝ) (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (hΦ : IsMaximalFlow f M I Φ) (x : Fin n → ℝ) (hx : x ∈ M) (S : ℝ)
    (hSI : S ∈ I x) (hper : Φ S x = x) :
    ∀ s : ℝ, s + S ∈ I x → s ∈ I x := by
  obtain ⟨⟨hopen, hord, hmem, hder⟩, _h0, _hΦ0, huniq⟩ := hΦ x hx
  have key := huniq ((fun s => s + S) ⁻¹' I x) (fun s => Φ (s + S) x) ?_ ?_ ?_
  · intro s hs
    exact key.1 hs
  · refine ⟨hopen.preimage (continuous_id.add continuous_const), ?_, ?_, ?_⟩
    · refine ⟨fun a ha b hb c hc => ?_⟩
      have := hord.out ha hb
      exact this ⟨by simp only [Set.mem_Icc] at hc ⊢; linarith [hc.1],
        by simp only [Set.mem_Icc] at hc ⊢; linarith [hc.2]⟩
    · intro t ht
      exact hmem _ ht
    · intro t ht
      have h := hder _ ht
      exact h.comp_add_const t S
  · simpa using hSI
  · simpa using hper

theorem global_interval {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (M : Set (Fin n → ℝ))
    (I : (Fin n → ℝ) → Set ℝ) (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (hΦ : IsMaximalFlow f M I Φ) (x : Fin n → ℝ) (hx : x ∈ M) (T : ℝ)
    (hT0 : 0 < T) (hTI : T ∈ I x) (hper : Φ T x = x) :
    I x = Set.univ := by
  obtain ⟨⟨_hopen, hord, _hmem, _hder⟩, h0, hΦ0, huniq⟩ := hΦ x hx
  have down := shift_down f M I Φ hΦ x hx T hTI hper
  have hmT : -T ∈ I x := down (-T) (by simpa using h0)
  have hmTper : Φ (-T) x = x := by
    have := (huniq ((fun s => s + T) ⁻¹' I x) (fun s => Φ (s + T) x) ?_ ?_ ?_).2 (-T) ?_
    · simpa [hΦ0] using this.symm
    · obtain ⟨⟨hopen, hord, hmem, hder⟩, _, _, _⟩ := hΦ x hx
      refine ⟨hopen.preimage (continuous_id.add continuous_const), ?_, ?_, ?_⟩
      · refine ⟨fun a ha b hb c hc => ?_⟩
        have := hord.out ha hb
        exact this ⟨by simp only [Set.mem_Icc] at hc ⊢; linarith [hc.1],
          by simp only [Set.mem_Icc] at hc ⊢; linarith [hc.2]⟩
      · intro t ht
        exact hmem _ ht
      · intro t ht
        exact (hder _ ht).comp_add_const t T
    · simpa using hTI
    · simpa using hper
    · simpa using h0
  have up := shift_down f M I Φ hΦ x hx (-T) hmT hmTper
  have hk : ∀ k : ℕ, (k : ℝ) * T ∈ I x ∧ -((k : ℝ) * T) ∈ I x := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      refine ⟨up _ ?_, down _ ?_⟩
      · have : ((k + 1 : ℕ) : ℝ) * T + -T = (k : ℝ) * T := by push_cast; ring
        rw [this]; exact ih.1
      · have : -(((k + 1 : ℕ) : ℝ) * T) + T = -((k : ℝ) * T) := by push_cast; ring
        rw [this]; exact ih.2
  ext y
  simp only [Set.mem_univ, iff_true]
  obtain ⟨k, hk'⟩ := Archimedean.arch |y| hT0
  have hy := hk k
  rw [nsmul_eq_mul] at hk'
  exact hord.out hy.2 hy.1 ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩

theorem charpoly_comp_comm {n : ℕ} (F G : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    (F ∘ₗ G).charpoly = (G ∘ₗ F).charpoly := by
  let b := Pi.basisFun ℝ (Fin n)
  rw [← LinearMap.charpoly_toMatrix (F ∘ₗ G) b, ← LinearMap.charpoly_toMatrix (G ∘ₗ F) b,
    LinearMap.toMatrix_comp b b b, LinearMap.toMatrix_comp b b b, Matrix.charpoly_mul_comm]

theorem monodromy_charpoly {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)} {M : Set (Fin n → ℝ)}
    {I : (Fin n → ℝ) → Set ℝ} {Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)} (hM : IsOpen M)
    (hf : ContDiffOn ℝ 1 f M) (hΦ : IsMaximalFlow f M I Φ) {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ M)
    {T : ℝ} (hT : 0 < T) (hTI : T ∈ I x₀) (hper : Φ T x₀ = x₀) (t₀ : ℝ) :
    LinearMap.charpoly (fderiv ℝ (Φ T) (Φ t₀ x₀) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) =
      LinearMap.charpoly (fderiv ℝ (Φ T) x₀ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) := by
  have hIu : I x₀ = univ := global_interval f M I Φ hΦ x₀ hx₀ T hT hTI hper
  have hperiodic : Function.Periodic (fun t => Φ t x₀) T := by
    intro t
    have := (flow_shift hΦ hx₀ hTI (s := t) (by rw [hIu]; trivial)).2
    rw [hper] at this
    exact this.symm
  set a : ℝ := toIcoMod hT 0 t₀ with ha_def
  have ha : a ∈ Ico 0 T := by simpa using toIcoMod_mem_Ico hT 0 t₀
  have hta : Φ t₀ x₀ = Φ a x₀ := by
    rw [ha_def, ← self_sub_toIcoDiv_zsmul]
    exact (hperiodic.sub_zsmul_eq _).symm
  rw [hta]
  set z := Φ a x₀ with hz_def
  have haI : a ∈ I x₀ := by rw [hIu]; trivial
  have hzM : z ∈ M := (hΦ x₀ hx₀).1.2.2.1 a haI
  have hIz : ∀ s : ℝ, s ∈ I z := fun s =>
    (flow_shift hΦ hx₀ haI (s := s) (by rw [hIu]; trivial)).1
  have hzx : Φ (T - a) z = x₀ := by
    rw [hz_def, (flow_shift hΦ hx₀ haI (s := T - a) (by rw [hIu]; trivial)).2, sub_add_cancel,
      hper]
  obtain ⟨hevA, hdA⟩ := flow_diff_forward hM hf hΦ hx₀ ha.1 haI
  obtain ⟨hevT, -⟩ := flow_diff_forward hM hf hΦ hx₀ hT.le hTI
  have hTa0 : 0 ≤ T - a := by linarith [ha.2]
  obtain ⟨hevB, hdB⟩ := flow_diff_forward hM hf hΦ hzM hTa0 (hIz _)
  obtain ⟨hevTz, -⟩ := flow_diff_forward hM hf hΦ hzM hT.le (hIz _)
  -- near x₀ : Φ T = Φ (T - a) ∘ Φ a
  have heq1 : (fun y => Φ (T - a) (Φ a y)) =ᶠ[𝓝 x₀] Φ T := by
    filter_upwards [hevA, hevT] with y h1 h2
    rw [(flow_shift hΦ h1.1 h1.2 (s := T - a) (by rw [sub_add_cancel]; exact h2.2)).2,
      sub_add_cancel]
  have heq2 : (fun w => Φ a (Φ (T - a) w)) =ᶠ[𝓝 z] Φ T := by
    filter_upwards [hevB, hevTz] with w h1 h2
    rw [(flow_shift hΦ h1.1 h1.2 (s := a) (by rw [add_sub_cancel]; exact h2.2)).2,
      add_sub_cancel]
  have hdB' : DifferentiableAt ℝ (Φ (T - a)) (Φ a x₀) := hdB
  have hdA' : DifferentiableAt ℝ (Φ a) (Φ (T - a) z) := by rw [hzx]; exact hdA
  have hD1 : fderiv ℝ (Φ T) x₀ = (fderiv ℝ (Φ (T - a)) z).comp (fderiv ℝ (Φ a) x₀) := by
    rw [← heq1.fderiv_eq]
    exact (hdB'.hasFDerivAt.comp x₀ hdA.hasFDerivAt).fderiv
  have hD2 : fderiv ℝ (Φ T) z = (fderiv ℝ (Φ a) x₀).comp (fderiv ℝ (Φ (T - a)) z) := by
    rw [← heq2.fderiv_eq]
    have := (hdA'.hasFDerivAt.comp z hdB.hasFDerivAt).fderiv
    rw [hzx] at this
    exact this
  rw [hD1, hD2]
  exact charpoly_comp_comm (fderiv ℝ (Φ a) x₀ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (fderiv ℝ (Φ (T - a)) z)

end FA7570

open TeschlODE.PeriodicOrbits in
theorem solution {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (M : Set (Fin n → ℝ)) (hM : IsOpen M) (k : ℕ) (hk : 1 ≤ k) (hf : ContDiffOn ℝ k f M)
    (I : (Fin n → ℝ) → Set ℝ) (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (hΦ : TeschlODE.Shared.IsMaximalFlow f M I Φ)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ M) (T : ℝ) (hper : IsRegularPeriodicPoint I Φ x₀ T)
    (U : Set (Fin n → ℝ)) (S : (Fin n → ℝ) → ℝ) (hsec : IsTransversalSection f M k U S)
    (hx₀U : x₀ ∈ U) (hSx₀ : S x₀ = 0)
    (τ : (Fin n → ℝ) → ℝ) (hτ : IsReturnTime I Φ k U S x₀ T τ) :
    ∃ L : Module.End ℝ (LinearMap.ker (fderiv ℝ S x₀ : (Fin n → ℝ) →ₗ[ℝ] ℝ)),
      IsPoincareDerivative Φ τ S x₀ L ∧
      ∀ t₀ : ℝ,
        LinearMap.charpoly (fderiv ℝ (Φ T) (Φ t₀ x₀) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) =
          (Polynomial.X - 1) * L.charpoly := by
  have hk0 : (k : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hf1 : ContDiffOn ℝ 1 f M := hf.of_le (by exact_mod_cast hk)
  obtain ⟨hT0, hTI, hTx, -⟩ := hper
  obtain ⟨V, hVo, hx₀V, hτc, hτx, hτV⟩ := hτ
  obtain ⟨hUo, hSc, hsec'⟩ := hsec
  have hτd : DifferentiableAt ℝ τ x₀ :=
    (hτc.differentiableOn hk0 x₀ hx₀V).differentiableAt (hVo.mem_nhds hx₀V)
  have hτI : ∀ᶠ y in 𝓝 x₀, τ y ∈ I y :=
    Filter.mem_of_superset (hVo.mem_nhds hx₀V) fun y hy => (hτV y hy).1
  have hP := FA7570.poincare_hasFDeriv hM hf1 hΦ hx₀ hT0.le hTI hTx hτd.hasFDerivAt hτx hτI
  set DT := fderiv ℝ (Φ T) x₀ with hDT
  set DP := ((ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)).smulRight (f x₀) +
        ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)).comp ((fderiv ℝ τ x₀).prod DT) with hDP
  have hDPapp : ∀ v, DP v = (fderiv ℝ τ x₀ v) • f x₀ + DT v := by
    intro v; simp [hDP]
  have hSd : DifferentiableAt ℝ S x₀ :=
    (hSc.differentiableOn hk0 x₀ hx₀U).differentiableAt (hUo.mem_nhds hx₀U)
  set ℓ := fderiv ℝ S x₀ with hℓ
  have hPx : (fun y => Φ (τ y) y) x₀ = x₀ := by simp only [hτx, hTx]
  have hSP : HasFDerivAt (fun y => S (Φ (τ y) y)) (ℓ.comp DP) x₀ := by
    have hS' : HasFDerivAt S ℓ ((fun y => Φ (τ y) y) x₀) := by rw [hPx]; exact hSd.hasFDerivAt
    exact HasFDerivAt.comp (g := S) (f := fun y => Φ (τ y) y) x₀ hS' hP
  have hSP0 : HasFDerivAt (fun y => S (Φ (τ y) y)) (0 : (Fin n → ℝ) →L[ℝ] ℝ) x₀ := by
    refine (hasFDerivAt_const (0:ℝ) x₀).congr_of_eventuallyEq ?_
    filter_upwards [hVo.mem_nhds hx₀V] with y hy
    exact (hτV y hy).2.2
  have hzero : ℓ.comp DP = 0 := hSP.unique hSP0
  have hmaps : ∀ v ∈ LinearMap.ker (ℓ : (Fin n → ℝ) →ₗ[ℝ] ℝ),
      (DP : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) v ∈ LinearMap.ker (ℓ : (Fin n → ℝ) →ₗ[ℝ] ℝ) := by
    intro v _
    rw [LinearMap.mem_ker]
    have := congrArg (fun F : (Fin n → ℝ) →L[ℝ] ℝ => F v) hzero
    simpa using this
  set L := (DP : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)).restrict hmaps with hL
  refine ⟨L, ?_, ?_⟩
  · intro v
    rw [hP.fderiv]
    rfl
  · have hv₀ : (DT : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (f x₀) = f x₀ :=
      FA7570.fderiv_flow_field hM hf1 hΦ hx₀ hT0.le hTI hTx
    have hℓv : (ℓ : (Fin n → ℝ) →ₗ[ℝ] ℝ) (f x₀) ≠ 0 := (hsec' x₀ hx₀U hSx₀).2.2
    have hLw : ∀ w : LinearMap.ker (ℓ : (Fin n → ℝ) →ₗ[ℝ] ℝ), ∃ c : ℝ,
        (L w : Fin n → ℝ) = (DT : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) w + c • f x₀ := by
      intro w
      refine ⟨fderiv ℝ τ x₀ w, ?_⟩
      have : (L w : Fin n → ℝ) = DP w := rfl
      rw [this, hDPapp, add_comm]
      rfl
    have h0 := FA7570.charpoly_split (DT : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (f x₀) hv₀
      (ℓ : (Fin n → ℝ) →ₗ[ℝ] ℝ) hℓv L hLw
    intro t₀
    rw [FA7570.monodromy_charpoly hM hf1 hΦ hx₀ hT0 hTI hTx t₀]
    exact h0
