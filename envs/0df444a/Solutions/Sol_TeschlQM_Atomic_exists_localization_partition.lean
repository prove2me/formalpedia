-- Prove2me | solution 1 for TeschlQM.Atomic.exists_localization_partition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T03:39:43.971327+00:00
-- url     : https://prove2.me/submissions/399ea557-cb25-448d-a1c7-3b820882ea3b

import Mathlib
import Definitions.Def_TeschlQM_Atomic_mulOp
import Definitions.Def_TeschlQM_Atomic_freeHamiltonian
import Definitions.Def_TeschlQM_Atomic_atomicHamiltonian

set_option autoImplicit false

open Filter Topology
open scoped ContDiff

namespace HVZPart

variable {N : ℕ} {C : ℝ}

lemma elec_smul (s : ℝ) (x : EuclideanSpace ℝ (Fin N × Fin 3)) (k : Fin N) :
    TeschlQM.Atomic.electron (s • x) k = s • TeschlQM.Atomic.electron x k := by
  ext a
  simp [TeschlQM.Atomic.electron]

lemma norm_sq_eq_sum (x : EuclideanSpace ℝ (Fin N × Fin 3)) :
    ‖x‖ ^ 2 = ∑ k, ‖TeschlQM.Atomic.electron x k‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  simp [TeschlQM.Atomic.electron]

lemma contDiff_elec_sq (k : Fin N) :
    ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin N × Fin 3) => ‖TeschlQM.Atomic.electron x k‖ ^ 2) := by
  have h : (fun x : EuclideanSpace ℝ (Fin N × Fin 3) => ‖TeschlQM.Atomic.electron x k‖ ^ 2) =
      fun x => ∑ a : Fin 3, (EuclideanSpace.proj (𝕜 := ℝ) (k, a) x) ^ 2 := by
    funext x
    rw [EuclideanSpace.norm_sq_eq]
    simp [TeschlQM.Atomic.electron]
  rw [h]
  exact ContDiff.sum fun a _ => ((EuclideanSpace.proj (𝕜 := ℝ) (k, a)).contDiff).pow 2

noncomputable def ρ (x : EuclideanSpace ℝ (Fin N × Fin 3)) : ℝ :=
  ‖x‖ ^ 2 + Real.smoothTransition (1 - 4 * ‖x‖ ^ 2)

noncomputable def bb (x : EuclideanSpace ℝ (Fin N × Fin 3)) : ℝ :=
  Real.smoothTransition (1 - 4 * ‖x‖ ^ 2)

noncomputable def u (k : Fin N) (x : EuclideanSpace ℝ (Fin N × Fin 3)) : ℝ :=
  ‖TeschlQM.Atomic.electron x k‖ ^ 2 / ρ x

noncomputable def g (N : ℕ) (C t : ℝ) : ℝ :=
  Real.smoothTransition ((t - C ^ 2) / (1 / (N : ℝ) - C ^ 2))

noncomputable def a (C : ℝ) (k : Fin N) (x : EuclideanSpace ℝ (Fin N × Fin 3)) : ℝ :=
  g N C (u k x) + bb x / N

noncomputable def S (C : ℝ) (x : EuclideanSpace ℝ (Fin N × Fin 3)) : ℝ :=
  ∑ k, (a C k x) ^ 2

noncomputable def φ (C : ℝ) (j : Fin N) (x : EuclideanSpace ℝ (Fin N × Fin 3)) : ℝ :=
  a C j x / Real.sqrt (S C x)

lemma ρ_pos (x : EuclideanSpace ℝ (Fin N × Fin 3)) : 0 < ρ x := by
  unfold ρ
  have h2 := sq_nonneg ‖x‖
  by_cases h : 0 < 1 - 4 * ‖x‖ ^ 2
  · have := Real.smoothTransition.pos_of_pos h
    linarith
  · push Not at h
    have := Real.smoothTransition.nonneg (1 - 4 * ‖x‖ ^ 2)
    nlinarith

lemma ρ_eq {x : EuclideanSpace ℝ (Fin N × Fin 3)} (hx : 1 ≤ 4 * ‖x‖ ^ 2) : ρ x = ‖x‖ ^ 2 := by
  unfold ρ
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

lemma bb_eq {x : EuclideanSpace ℝ (Fin N × Fin 3)} (hx : 1 ≤ 4 * ‖x‖ ^ 2) : bb x = 0 := by
  unfold bb
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

lemma a_nonneg (k : Fin N) (x : EuclideanSpace ℝ (Fin N × Fin 3)) : 0 ≤ a C k x :=
  add_nonneg (Real.smoothTransition.nonneg _)
    (div_nonneg (Real.smoothTransition.nonneg _) (Nat.cast_nonneg _))

lemma S_pos (hN : 0 < N) (hD : 0 < 1 / (N : ℝ) - C ^ 2) (x : EuclideanSpace ℝ (Fin N × Fin 3)) :
    0 < S C x := by
  have hsingle : ∀ k, (a C k x) ^ 2 ≤ S C x := fun k =>
    Finset.single_le_sum (f := fun k => (a C k x) ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ k)
  by_cases h : 0 < 1 - 4 * ‖x‖ ^ 2
  · have hb : 0 < bb x := Real.smoothTransition.pos_of_pos h
    have ha : 0 < a C ⟨0, hN⟩ x := by
      unfold a g
      have := Real.smoothTransition.nonneg ((u ⟨0, hN⟩ x - C ^ 2) / (1 / (N : ℝ) - C ^ 2))
      have : 0 < bb x / N := div_pos hb (Nat.cast_pos.2 hN)
      linarith
    exact lt_of_lt_of_le (by positivity) (hsingle ⟨0, hN⟩)
  · push Not at h
    have h4 : 1 ≤ 4 * ‖x‖ ^ 2 := by linarith
    have hx : 0 < ‖x‖ ^ 2 := by nlinarith
    have hsum : ∑ k, u k x = 1 := by
      simp only [u, ρ_eq h4]
      rw [← Finset.sum_div, ← norm_sq_eq_sum, div_self hx.ne']
    have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
    obtain ⟨k, -, hk⟩ := Finset.exists_le_of_sum_le (s := Finset.univ) ⟨⟨0, hN⟩, Finset.mem_univ _⟩
      (f := fun _ => (1 : ℝ) / N) (g := fun k => u k x) (by
        rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_one_div_cancel hNr.ne'])
    have hg : g N C (u k x) = 1 := by
      unfold g
      apply Real.smoothTransition.one_of_one_le
      rw [le_div_iff₀ hD]
      linarith
    have ha : 1 ≤ a C k x := by
      unfold a
      rw [hg]
      have : 0 ≤ bb x / N := div_nonneg (Real.smoothTransition.nonneg _) (Nat.cast_nonneg _)
      linarith
    exact lt_of_lt_of_le (by nlinarith) (hsingle k)

lemma contDiff_ρ : ContDiff ℝ ∞ (ρ (N := N)) := by
  show ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin N × Fin 3) =>
    ‖x‖ ^ 2 + Real.smoothTransition (1 - 4 * ‖x‖ ^ 2))
  exact (contDiff_norm_sq ℝ).add (Real.smoothTransition.contDiff.comp
    (contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ))))

lemma contDiff_bb : ContDiff ℝ ∞ (bb (N := N)) := by
  show ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin N × Fin 3) =>
    Real.smoothTransition (1 - 4 * ‖x‖ ^ 2))
  exact Real.smoothTransition.contDiff.comp
    (contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ)))

lemma contDiff_u (k : Fin N) : ContDiff ℝ ∞ (u k) := by
  show ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin N × Fin 3) =>
    ‖TeschlQM.Atomic.electron x k‖ ^ 2 / ρ x)
  exact (contDiff_elec_sq k).div contDiff_ρ (fun x => (ρ_pos x).ne')

lemma contDiff_a (k : Fin N) : ContDiff ℝ ∞ (a C k) := by
  show ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin N × Fin 3) =>
    Real.smoothTransition ((u k x - C ^ 2) / (1 / (N : ℝ) - C ^ 2)) + bb x / N)
  exact (Real.smoothTransition.contDiff.comp (((contDiff_u k).sub contDiff_const).div_const _)).add
    (contDiff_bb.div_const _)

lemma contDiff_S : ContDiff ℝ ∞ (S (N := N) C) := by
  show ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin N × Fin 3) => ∑ k, (a C k x) ^ 2)
  exact ContDiff.sum fun k _ => (contDiff_a k).pow 2

lemma contDiff_φ (hN : 0 < N) (hD : 0 < 1 / (N : ℝ) - C ^ 2) (j : Fin N) :
    ContDiff ℝ ∞ (φ C j) := by
  show ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin N × Fin 3) => a C j x / Real.sqrt (S C x))
  exact (contDiff_a j).div (contDiff_S.sqrt (fun x => (S_pos hN hD x).ne'))
    (fun x => (Real.sqrt_pos.2 (S_pos hN hD x)).ne')

lemma φ_mem (hN : 0 < N) (hD : 0 < 1 / (N : ℝ) - C ^ 2) (j : Fin N)
    (x : EuclideanSpace ℝ (Fin N × Fin 3)) : φ C j x ∈ Set.Icc (0 : ℝ) 1 := by
  have hS := S_pos hN hD x
  have hsq : (a C j x) ^ 2 ≤ S C x :=
    Finset.single_le_sum (f := fun k => (a C k x) ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  have hle : a C j x ≤ Real.sqrt (S C x) := (le_abs_self _).trans (Real.abs_le_sqrt hsq)
  exact ⟨div_nonneg (a_nonneg j x) (Real.sqrt_nonneg _), (div_le_one (Real.sqrt_pos.2 hS)).2 hle⟩

lemma φ_sum (hN : 0 < N) (hD : 0 < 1 / (N : ℝ) - C ^ 2) (x : EuclideanSpace ℝ (Fin N × Fin 3)) :
    ∑ j, φ C j x ^ 2 = 1 := by
  have hS := S_pos hN hD x
  simp only [φ, div_pow, Real.sq_sqrt hS.le]
  rw [← Finset.sum_div]
  exact div_self hS.ne'

lemma φ_tsupport (hC0 : 0 < C) (hD : 0 < 1 / (N : ℝ) - C ^ 2) (j : Fin N) :
    tsupport (φ C j) ∩ {x | 1 ≤ ‖x‖} ⊆ {x | C * ‖x‖ ≤ ‖TeschlQM.Atomic.electron x j‖} := by
  have hF : tsupport (φ C j) ⊆ {x | C ^ 2 * ρ x ≤ ‖TeschlQM.Atomic.electron x j‖ ^ 2} ∪
      {x | 0 ≤ 1 - 4 * ‖x‖ ^ 2} := by
    apply closure_minimal _ (IsClosed.union
      (isClosed_le (continuous_const.mul contDiff_ρ.continuous) (contDiff_elec_sq j).continuous)
      (isClosed_le continuous_const (continuous_const.sub (continuous_const.mul (continuous_norm.pow 2)))))
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hcon
    have hc1 : ‖TeschlQM.Atomic.electron x j‖ ^ 2 < C ^ 2 * ρ x := not_le.1 fun h => hcon (Or.inl h)
    have hc2 : 1 - 4 * ‖x‖ ^ 2 < 0 := not_le.1 fun h => hcon (Or.inr h)
    apply hx
    have hu : u j x ≤ C ^ 2 := by
      unfold u
      rw [div_le_iff₀ (ρ_pos x)]
      linarith [hc1]
    have hg : g N C (u j x) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hD.le)
    have hb : bb x = 0 := Real.smoothTransition.zero_of_nonpos hc2.le
    simp only [φ, a, hg, hb]
    simp
  intro x ⟨hx1, hx2⟩
  simp only [Set.mem_setOf_eq] at hx2 ⊢
  rcases hF hx1 with h | h
  · simp only [Set.mem_setOf_eq] at h
    have h4 : 1 ≤ 4 * ‖x‖ ^ 2 := by nlinarith
    rw [ρ_eq h4] at h
    have : (C * ‖x‖) ^ 2 ≤ ‖TeschlQM.Atomic.electron x j‖ ^ 2 := by rw [mul_pow]; exact h
    exact (pow_le_pow_iff_left₀ (mul_nonneg hC0.le (norm_nonneg _)) (norm_nonneg _)
      two_ne_zero).1 this
  · simp only [Set.mem_setOf_eq] at h
    exfalso
    nlinarith

lemma φ_smul (s : ℝ) (hs : 1 ≤ s) (w : EuclideanSpace ℝ (Fin N × Fin 3)) (hw : 1 ≤ 4 * ‖w‖ ^ 2)
    (j : Fin N) : φ C j (s • w) = φ C j w := by
  have hs0 : 0 < s := by linarith
  have hnorm : ‖s • w‖ = s * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
  have hsw : 1 ≤ 4 * ‖s • w‖ ^ 2 := by
    rw [hnorm, mul_pow]
    have : 1 ≤ s ^ 2 := by nlinarith
    nlinarith [sq_nonneg ‖w‖]
  have hu : ∀ k, u k (s • w) = u k w := by
    intro k
    unfold u
    rw [ρ_eq hsw, ρ_eq hw, elec_smul, hnorm, norm_smul, Real.norm_eq_abs, abs_of_pos hs0,
      mul_pow, mul_pow]
    exact mul_div_mul_left _ _ (pow_pos hs0 2).ne'
  have hb : bb (s • w) = bb w := by rw [bb_eq hsw, bb_eq hw]
  have ha : ∀ k, a C k (s • w) = a C k w := fun k => by unfold a; rw [hu k, hb]
  unfold φ S
  simp only [ha]

lemma fderiv_bound (j : Fin N) (hφ : ContDiff ℝ ∞ (φ C j)) :
    ∃ M, ∀ y : EuclideanSpace ℝ (Fin N × Fin 3), 1 ≤ ‖y‖ → ‖fderiv ℝ (φ C j) y‖ ≤ M / ‖y‖ := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin N × Fin 3)) 1).exists_bound_of_continuousOn
    ((hφ.continuous_fderiv (by simp)).continuousOn)
  refine ⟨M, fun y hy => ?_⟩
  have hs0 : 0 < ‖y‖ := by linarith
  let z : EuclideanSpace ℝ (Fin N × Fin 3) := ‖y‖⁻¹ • y
  have hz : ‖z‖ = 1 := by
    simp only [z, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hs0.ne'
  have hyz : ‖y‖ • z = y := by
    simp only [z, smul_smul]
    rw [mul_inv_cancel₀ hs0.ne', one_smul]
  have hd : DifferentiableAt ℝ (φ C j) y := (hφ.differentiable (by simp)) y
  have hψ : HasFDerivAt (fun w => φ C j (‖y‖ • w))
      ((fderiv ℝ (φ C j) y).comp (‖y‖ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin N × Fin 3)))) z := by
    have h1 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin N × Fin 3) => ‖y‖ • w)
        (‖y‖ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin N × Fin 3))) z :=
      (hasFDerivAt_id z).const_smul ‖y‖
    have h2 : HasFDerivAt (φ C j) (fderiv ℝ (φ C j) y) (‖y‖ • z) := by
      rw [hyz]; exact hd.hasFDerivAt
    exact h2.comp z h1
  have heq : (fun w => φ C j (‖y‖ • w)) =ᶠ[𝓝 z] φ C j := by
    have hev : ∀ᶠ w in 𝓝 z, (1 / 2 : ℝ) < ‖w‖ :=
      (continuous_norm.tendsto z).eventually (lt_mem_nhds (by rw [hz]; norm_num))
    filter_upwards [hev] with w hw
    exact φ_smul ‖y‖ hy w (by nlinarith) j
  have hfd : fderiv ℝ (φ C j) z =
      (fderiv ℝ (φ C j) y).comp (‖y‖ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin N × Fin 3))) := by
    rw [← heq.fderiv_eq]
    exact hψ.fderiv
  have hnorm : ‖fderiv ℝ (φ C j) z‖ = ‖y‖ * ‖fderiv ℝ (φ C j) y‖ := by
    rw [hfd, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id, norm_smul, norm_norm]
  have hMz := hM z (by simp [hz])
  rw [le_div_iff₀ hs0, mul_comm, ← hnorm]
  exact hMz

lemma fderiv_tendsto (j : Fin N) (hφ : ContDiff ℝ ∞ (φ C j)) :
    Tendsto (fun x => ‖fderiv ℝ (φ C j) x‖) (cocompact _) (𝓝 0) := by
  obtain ⟨M, hM⟩ := fderiv_bound j hφ
  have h1 : Tendsto (fun y : EuclideanSpace ℝ (Fin N × Fin 3) => M * ‖y‖⁻¹) (cocompact _) (𝓝 0) := by
    have := (tendsto_norm_cocompact_atTop (E := EuclideanSpace ℝ (Fin N × Fin 3))).inv_tendsto_atTop.const_mul M
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h1
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop 1] with y hy
  rw [← div_eq_mul_inv]
  exact hM y hy

end HVZPart

open Filter Topology TeschlQM.Atomic ContDiff in
theorem solution (N : ℕ) (C : ℝ) (hC0 : 0 < C)
    (hC : C < 1 / Real.sqrt N) :
    ∃ φ : Fin N → EuclideanSpace ℝ (Fin N × Fin 3) → ℝ,
      (∀ j, ContDiff ℝ ∞ (φ j)) ∧ (∀ j x, φ j x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x, ∑ j, φ j x ^ 2 = 1) ∧
      (∀ j, tsupport (φ j) ∩ {x | 1 ≤ ‖x‖} ⊆ {x | C * ‖x‖ ≤ ‖electron x j‖}) ∧
      (∀ j, Tendsto (fun x => ‖fderiv ℝ (φ j) x‖) (cocompact _) (𝓝 0)) := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h
      simp at hC
      linarith
    · exact h
  have hD : 0 < 1 / (N : ℝ) - C ^ 2 := by
    have hs : (1 / Real.sqrt N) ^ 2 = 1 / (N : ℝ) := by
      rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    have : C ^ 2 < (1 / Real.sqrt N) ^ 2 := pow_lt_pow_left₀ hC hC0.le two_ne_zero
    linarith
  exact ⟨HVZPart.φ C, fun j => HVZPart.contDiff_φ hN hD j, fun j x => HVZPart.φ_mem hN hD j x,
    fun x => HVZPart.φ_sum hN hD x, fun j => HVZPart.φ_tsupport hC0 hD j,
    fun j => HVZPart.fderiv_tendsto j (HVZPart.contDiff_φ hN hD j)⟩
