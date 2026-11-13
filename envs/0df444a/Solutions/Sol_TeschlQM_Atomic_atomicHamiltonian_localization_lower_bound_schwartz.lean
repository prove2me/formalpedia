-- Prove2me | solution 1 for TeschlQM.Atomic.atomicHamiltonian_localization_lower_bound_schwartz
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T08:14:38.704708+00:00
-- url     : https://prove2.me/submissions/0b160eda-a3a0-40ca-8664-c344bb107ac4

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_Atomic_mulOp
import Definitions.Def_TeschlQM_Atomic_freeHamiltonian
import Definitions.Def_TeschlQM_Atomic_atomicHamiltonian

section SecX

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
theorem hvzPartSolution (N : ℕ) (C : ℝ) (hC0 : 0 < C)
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

namespace HVZFar
open HVZPart TeschlQM.Atomic

variable {N : ℕ}

noncomputable def far (γ r : ℝ) (j : Fin N) (x : EuclideanSpace ℝ (Fin N × Fin 3)) : ℝ :=
  if r ≤ ‖electron x j‖ then γ / ‖electron x j‖ else 0

lemma far_meas (γ r : ℝ) (j : Fin N) : Measurable (far γ r j) := by
  have hm : Measurable (fun x : EuclideanSpace ℝ (Fin N × Fin 3) => ‖electron x j‖) := by
    unfold electron; fun_prop
  exact Measurable.ite (measurableSet_le measurable_const hm) (measurable_const.div hm) measurable_const

lemma far_nonneg (γ r : ℝ) (hγ : 0 ≤ γ) (j : Fin N) (x : EuclideanSpace ℝ (Fin N × Fin 3)) :
    0 ≤ far γ r j x := by
  unfold far; split_ifs
  · positivity
  · exact le_rfl

lemma far_bdd (γ r : ℝ) (hγ : 0 ≤ γ) (hr : 0 < r) (j : Fin N) :
    ∃ C, ∀ x, |far γ r j x| ≤ C := by
  refine ⟨γ / r, fun x => ?_⟩
  rw [abs_of_nonneg (far_nonneg γ r hγ j x)]
  unfold far; split_ifs with h
  · exact div_le_div_of_nonneg_left hγ hr h
  · positivity

lemma far_tendsto (γ r C : ℝ) (hγ : 0 ≤ γ) (hN : 0 < N) (hC0 : 0 < C)
    (hD : 0 < 1 / (N : ℝ) - C ^ 2) (j : Fin N) :
    Tendsto (fun x => far γ r j x * φ C j x ^ 2) (cocompact _) (𝓝 0) := by
  have h1 : Tendsto (fun y : EuclideanSpace ℝ (Fin N × Fin 3) => γ / C * ‖y‖⁻¹) (cocompact _) (𝓝 0) := by
    have := (tendsto_norm_cocompact_atTop (E := EuclideanSpace ℝ (Fin N × Fin 3))).inv_tendsto_atTop.const_mul (γ / C)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun x => mul_nonneg (far_nonneg γ r hγ j x) (sq_nonneg _))
    ?_ h1
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop 1] with x hx
  have hx0 : 0 < ‖x‖ := lt_of_lt_of_le one_pos hx
  have hb : 0 ≤ γ / C * ‖x‖⁻¹ := by positivity
  by_cases hφ0 : φ C j x = 0
  · rw [hφ0]; simpa using hb
  have hts : x ∈ tsupport (φ C j) ∩ {x | 1 ≤ ‖x‖} := ⟨subset_tsupport _ hφ0, hx⟩
  have hel : C * ‖x‖ ≤ ‖electron x j‖ := φ_tsupport hC0 hD j hts
  have hm := φ_mem hN hD j x
  have hφ1 : φ C j x ^ 2 ≤ 1 := by nlinarith [hm.1, hm.2]
  have hfar : far γ r j x ≤ γ / C * ‖x‖⁻¹ := by
    unfold far; split_ifs
    · rw [show γ / C * ‖x‖⁻¹ = γ / (C * ‖x‖) by field_simp]
      exact div_le_div_of_nonneg_left hγ (by positivity) hel
    · exact hb
  calc far γ r j x * φ C j x ^ 2 ≤ γ / C * ‖x‖⁻¹ * 1 :=
        mul_le_mul hfar hφ1 (sq_nonneg _) hb
    _ = γ / C * ‖x‖⁻¹ := mul_one _

end HVZFar


/-! P3 fiber lemma pieces for 7ab9d8bf D3c (IMS lower bound). -/

set_option autoImplicit false

open MeasureTheory SchwartzMap FourierTransform LineDeriv
open scoped ContDiff InnerProductSpace ComplexConjugate Topology
open Filter

namespace HVZFib

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem integral_norm_sq_lineDeriv (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) (m : EuclideanSpace ℝ ι) :
    ∫ x, ‖fderiv ℝ f x m‖ ^ 2 =
      ∫ ξ, (2 * Real.pi * inner ℝ ξ m) ^ 2 * ‖𝓕 f ξ‖ ^ 2 := by
  have h1 := integral_norm_sq_fourier (∂_{m} f)
  rw [fourier_lineDerivOp_eq] at h1
  have hg : (inner ℝ · m : EuclideanSpace ℝ ι → ℝ).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  rw [← integral_congr_ae (Filter.Eventually.of_forall fun x => by
      rw [← lineDerivOp_apply_eq_fderiv] : ∀ᵐ x ∂volume, ‖(∂_{m} f) x‖ ^ 2 = ‖fderiv ℝ f x m‖ ^ 2),
    ← h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_apply, smulLeftCLM_apply_apply hg, norm_smul, Complex.norm_mul,
    Complex.norm_I, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

lemma sq_fourier_lineDeriv (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) (m ξ : EuclideanSpace ℝ ι) :
    ‖𝓕 (∂_{m} f) ξ‖ ^ 2 = (2 * Real.pi * inner ℝ ξ m) ^ 2 * ‖𝓕 f ξ‖ ^ 2 := by
  have hg : (inner ℝ · m : EuclideanSpace ℝ ι → ℝ).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  rw [fourier_lineDerivOp_eq]
  simp only [smul_apply, smulLeftCLM_apply_apply hg, norm_smul, Complex.norm_mul,
    Complex.norm_I, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring


open TeschlQM.Atomic in
/-- Schwartz functions lie in `𝔇(H₀)` and `re⟪g, H₀ g⟫ = ∑ᵢ ∫ |∂ᵢ g|²`. -/
theorem kin_schwartz (g : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    ∃ hg : g.toLp 2 (volume : Measure (EuclideanSpace ℝ ι)) ∈ (freeHamiltonian ι).domain,
      (⟪g.toLp 2 (volume : Measure (EuclideanSpace ℝ ι)), freeHamiltonian ι ⟨_, hg⟩⟫_ℂ).re =
        ∑ i, ∫ x, ‖fderiv ℝ (⇑g) x (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
  let U := Lp.fourierTransformₗᵢ (EuclideanSpace ℝ ι) ℂ
  let w : EuclideanSpace ℝ ι → ℂ := fun ξ => ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)
  have hU : U (g.toLp 2 (volume : Measure (EuclideanSpace ℝ ι))) = (𝓕 g).toLp 2 (volume : Measure (EuclideanSpace ℝ ι)) := SchwartzMap.toLp_fourier_eq g
  have hT : w.HasTemperateGrowth :=
    Function.HasTemperateGrowth.comp Complex.ofRealCLM.hasTemperateGrowth
      ((Function.HasTemperateGrowth.const (4 * Real.pi ^ 2)).mul (Function.hasTemperateGrowth_norm_sq (EuclideanSpace ℝ ι)))
  let h : 𝓢(EuclideanSpace ℝ ι, ℂ) := smulLeftCLM ℂ w (𝓕 g)
  have hh : ∀ ξ, h ξ = w ξ * 𝓕 g ξ := fun ξ => smulLeftCLM_apply_apply hT (𝓕 g) ξ
  have hae : ∀ᵐ ξ ∂(volume : Measure (EuclideanSpace ℝ ι)),
      w ξ * (U (g.toLp 2 (volume : Measure (EuclideanSpace ℝ ι))) : EuclideanSpace ℝ ι → ℂ) ξ = h ξ := by
    filter_upwards [(𝓕 g).coeFn_toLp 2 volume] with ξ hξ
    rw [hU, hξ, hh]
  have hdom : MemLp (fun ξ : EuclideanSpace ℝ ι =>
      w ξ * (U (g.toLp 2 (volume : Measure (EuclideanSpace ℝ ι))) : EuclideanSpace ℝ ι → ℂ) ξ) 2 volume :=
    (h.memLp 2).ae_eq (hae.mono fun ξ hξ => hξ.symm)
  have hmem : g.toLp 2 (volume : Measure (EuclideanSpace ℝ ι)) ∈ (freeHamiltonian ι).domain :=
    Submodule.mem_comap.2 hdom
  refine ⟨hmem, ?_⟩
  have hval : freeHamiltonian ι ⟨_, hmem⟩ = U.symm (hdom.toLp _) := rfl
  rw [hval, ← U.inner_map_map, LinearIsometryEquiv.apply_symm_apply, L2.inner_def]
  have hre := integral_re (𝕜 := ℂ) (L2.integrable_inner (U (g.toLp 2 (volume : Measure (EuclideanSpace ℝ ι)))) (hdom.toLp _))
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  have hint2 : ∀ i : ι, Integrable (fun ξ : EuclideanSpace ℝ ι =>
      (2 * Real.pi * inner ℝ ξ (EuclideanSpace.single i (1 : ℝ))) ^ 2 * ‖𝓕 g ξ‖ ^ 2) := by
    intro i
    set k := 𝓕 (∂_{EuclideanSpace.single i (1 : ℝ)} g)
    have := (memLp_two_iff_integrable_sq_norm k.continuous.aestronglyMeasurable).1 (k.memLp 2)
    refine this.congr (Filter.Eventually.of_forall fun ξ => ?_)
    exact sq_fourier_lineDeriv g _ ξ
  have hpt : ∀ ξ : EuclideanSpace ℝ ι, 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 * ‖𝓕 g ξ‖ ^ 2 =
      ∑ i, (2 * Real.pi * inner ℝ ξ (EuclideanSpace.single i (1 : ℝ))) ^ 2 * ‖𝓕 g ξ‖ ^ 2 := by
    intro ξ
    rw [← Finset.sum_mul, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [EuclideanSpace.inner_single_right]
    simp only [Real.norm_eq_abs, sq_abs, one_mul, conj_trivial]
    ring
  rw [Finset.sum_congr rfl fun i _ => integral_norm_sq_lineDeriv g _,
    ← integral_finsetSum _ fun i _ => hint2 i]
  refine integral_congr_ae ?_
  filter_upwards [hdom.coeFn_toLp, (𝓕 g).coeFn_toLp 2 volume] with ξ h1 h2
  rw [h1, RCLike.inner_apply', hU, h2, ← hpt ξ]
  have : (starRingEnd ℂ) (𝓕 g ξ) * (w ξ * 𝓕 g ξ) =
      ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 * ‖𝓕 g ξ‖ ^ 2 : ℝ) : ℂ) := by
    simp only [w]; rw [mul_left_comm, Complex.conj_mul']; push_cast; ring
  rw [this, Complex.ofReal_re]

open TeschlQM.Atomic TeschlQM.Shared in
/-- `H^{(M)} ≥ λ` in form on Schwartz functions (given `g ∈ 𝔇(V)`). -/
theorem form_schwartz (γne γee lam : ℝ) (M : ℕ)
    (hlam : IsBoundedBelowBy (atomicHamiltonian γne γee M) lam)
    (g : 𝓢(EuclideanSpace ℝ (Fin M × Fin 3), ℂ))
    (hV : g.toLp 2 (volume : Measure (EuclideanSpace ℝ (Fin M × Fin 3))) ∈
      (mulOp volume (fun x => ((atomicPotential γne γee M x : ℝ) : ℂ))).domain) :
    lam * ∫ x, ‖g x‖ ^ 2 ≤
      (∑ i, ∫ x, ‖fderiv ℝ (⇑g) x (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) +
        ∫ x, atomicPotential γne γee M x * ‖g x‖ ^ 2 := by
  obtain ⟨h0, hk⟩ := kin_schwartz g
  have hdom : g.toLp 2 (volume : Measure (EuclideanSpace ℝ (Fin M × Fin 3))) ∈
      (atomicHamiltonian γne γee M).domain := Submodule.mem_inf.2 ⟨h0, hV⟩
  have hl := hlam ⟨_, hdom⟩
  have hval : atomicHamiltonian γne γee M ⟨_, hdom⟩ =
      freeHamiltonian (Fin M × Fin 3) ⟨_, h0⟩ +
        mulOp volume (fun x => ((atomicPotential γne γee M x : ℝ) : ℂ)) ⟨_, hV⟩ :=
    LinearPMap.add_apply _ _ ⟨_, hdom⟩
  rw [hval, inner_add_right, Complex.add_re, hk] at hl
  have hBv : mulOp volume (fun x => ((atomicPotential γne γee M x : ℝ) : ℂ)) ⟨_, hV⟩ =
      MemLp.toLp _ hV := rfl
  have hB : (⟪g.toLp 2 (volume : Measure (EuclideanSpace ℝ (Fin M × Fin 3))),
      mulOp volume (fun x => ((atomicPotential γne γee M x : ℝ) : ℂ)) ⟨_, hV⟩⟫_ℂ).re =
      ∫ x, atomicPotential γne γee M x * ‖g x‖ ^ 2 := by
    rw [hBv, L2.inner_def]
    have hre := integral_re (𝕜 := ℂ) (L2.integrable_inner
      (g.toLp 2 (volume : Measure (EuclideanSpace ℝ (Fin M × Fin 3)))) (MemLp.toLp _ hV))
    simp only [RCLike.re_to_complex] at hre
    rw [← hre]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hV, g.coeFn_toLp 2 volume] with x h1 h2
    rw [h1, RCLike.inner_apply']
    simp only [h2]
    have : (starRingEnd ℂ) (g x) * (((atomicPotential γne γee M x : ℝ) : ℂ) * g x) =
        ((atomicPotential γne γee M x * ‖g x‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_left_comm, Complex.conj_mul']; push_cast; ring
    rw [this, Complex.ofReal_re]
  have hn : ‖g.toLp 2 (volume : Measure (EuclideanSpace ℝ (Fin M × Fin 3)))‖ ^ 2 =
      ∫ x, ‖g x‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
    refine integral_congr_ae ?_
    filter_upwards [g.coeFn_toLp 2 volume] with x hx
    simp only [inner_self_eq_norm_sq_to_K, hx]; norm_cast
  rw [hB] at hl
  rw [← hn]
  exact hl

end HVZFib

namespace HVZFib
open TeschlQM.Atomic TeschlQM.Shared

abbrev A (M : ℕ) := EuclideanSpace ℝ (Fin M × Fin 3)
abbrev B := EuclideanSpace ℝ (Fin 3)

/-- drop electron `e`. -/
noncomputable def drop {M : ℕ} (e : Fin (M + 1)) (x : A (M + 1)) : A M :=
  WithLp.toLp 2 (fun p : Fin M × Fin 3 => x (e.succAbove p.1, p.2))

lemma electron_drop {M : ℕ} (e : Fin (M + 1)) (x : A (M + 1)) (j : Fin M) :
    electron (drop e x) j = electron x (e.succAbove j) := rfl

noncomputable def Lmap (M : ℕ) (e : Fin (M + 1)) : A (M + 1) →ₗ[ℝ] WithLp 2 (A M × B) where
  toFun x := WithLp.toLp 2 (drop e x, electron x e)
  map_add' x y := rfl
  map_smul' c x := rfl

theorem Lmap_norm (M : ℕ) (e : Fin (M + 1)) (x : A (M + 1)) : ‖Lmap M e x‖ = ‖x‖ := by
  have h : ‖Lmap M e x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp only [EuclideanSpace.norm_sq_eq]
    conv_rhs => rw [Fintype.sum_prod_type, Fin.sum_univ_succAbove _ e]
    rw [Fintype.sum_prod_type]
    simp [Lmap, drop, electron]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

noncomputable def Liso (M : ℕ) (e : Fin (M + 1)) : A (M + 1) ≃ₗᵢ[ℝ] WithLp 2 (A M × B) :=
  LinearIsometry.toLinearIsometryEquiv ⟨Lmap M e, fun x => Lmap_norm M e x⟩ (by
    rw [finrank_euclideanSpace, (WithLp.linearEquiv 2 ℝ (A M × B)).finrank_eq,
      Module.finrank_prod, finrank_euclideanSpace, finrank_euclideanSpace]
    simp
    ring)

noncomputable def emap (M : ℕ) (e : Fin (M + 1)) : A (M + 1) ≃ᵐ A M × B :=
  (Liso M e).toHomeomorph.toMeasurableEquiv.trans (MeasurableEquiv.toLp 2 _).symm

theorem emap_apply (M : ℕ) (e : Fin (M + 1)) (x : A (M + 1)) :
    emap M e x = (drop e x, electron x e) := rfl

theorem emap_mp (M : ℕ) (e : Fin (M + 1)) : MeasurePreserving (emap M e) :=
  (WithLp.volume_preserving_symm_measurableEquiv_toLp_prod _ _).comp (Liso M e).measurePreserving

noncomputable def P (M : ℕ) (e : Fin (M + 1)) : (A M × B) ≃L[ℝ] A (M + 1) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (A M) B).symm.trans
    (Liso M e).symm.toContinuousLinearEquiv

lemma emap_symm_eq (M : ℕ) (e : Fin (M + 1)) (p : A M × B) : (emap M e).symm p = P M e p := rfl

lemma emap_P (M : ℕ) (e : Fin (M + 1)) (w : A M) (y : B) : emap M e (P M e (w, y)) = (w, y) :=
  (emap M e).apply_symm_apply _

lemma drop_P (M : ℕ) (e : Fin (M + 1)) (w : A M) (y : B) : drop e (P M e (w, y)) = w := by
  have h := emap_P M e w y
  rw [emap_apply] at h
  exact congrArg Prod.fst h

lemma electron_P (M : ℕ) (e : Fin (M + 1)) (w : A M) (y : B) : electron (P M e (w, y)) e = y := by
  have h := emap_P M e w y
  rw [emap_apply] at h
  exact congrArg Prod.snd h

lemma P_single (M : ℕ) (e : Fin (M + 1)) (i : Fin M × Fin 3) :
    P M e (EuclideanSpace.single i (1 : ℝ), 0) = EuclideanSpace.single (e.succAbove i.1, i.2) 1 := by
  apply (emap M e).injective
  rw [emap_P, emap_apply]
  ext p
  · obtain ⟨j, k⟩ := p
    simp only [drop, EuclideanSpace.single_apply, Prod.mk.injEq, Fin.succAbove_right_inj]
    simp [Prod.ext_iff]
  · simp only [electron, EuclideanSpace.single_apply, Prod.mk.injEq, PiLp.zero_apply]
    simp [(Fin.succAbove_ne e i.1).symm]

theorem fub (M : ℕ) (e : Fin (M + 1)) (F : A (M + 1) → ℝ) (hF : Integrable F) :
    Integrable (fun y : B => ∫ w : A M, F (P M e (w, y))) ∧
      ∫ x, F x = ∫ y : B, ∫ w : A M, F (P M e (w, y)) := by
  have hmp := MeasurePreserving.symm _ (emap_mp M e)
  have hG : Integrable (fun p : A M × B => F (P M e p)) ((volume : Measure (A M)).prod volume) :=
    (hmp.integrable_comp_emb (emap M e).symm.measurableEmbedding).2 hF
  refine ⟨hG.integral_prod_right, ?_⟩
  rw [← integral_prod_symm _ hG]
  exact (hmp.integral_comp' F).symm

lemma closedEmb (M : ℕ) (e : Fin (M + 1)) (y : B) :
    Topology.IsClosedEmbedding (fun w : A M => P M e (w, y)) := by
  have h1 : Topology.IsClosedEmbedding (fun w : A M => (w, y)) :=
    { toIsEmbedding := isEmbedding_prodMkLeft y
      isClosed_range := by
        convert isClosed_univ.prod (isClosed_singleton (x := y)) using 1
        ext ⟨a, b⟩; simp [eq_comm] }
  exact (P M e).toHomeomorph.isClosedEmbedding.comp h1

lemma fderiv_slice (M : ℕ) (e : Fin (M + 1)) (f : A (M + 1) → ℂ) (hf : ContDiff ℝ ∞ f) (y : B)
    (w v : A M) :
    fderiv ℝ (fun w : A M => f (P M e (w, y))) w v = fderiv ℝ f (P M e (w, y)) (P M e (v, 0)) := by
  have hd : HasFDerivAt (fun w : A M => P M e (w, y))
      ((P M e : (A M × B) →L[ℝ] A (M + 1)).comp
        ((ContinuousLinearMap.id ℝ (A M)).prod (0 : A M →L[ℝ] B))) w :=
    (P M e : (A M × B) →L[ℝ] A (M + 1)).hasFDerivAt.comp w
      ((hasFDerivAt_id w).prodMk (hasFDerivAt_const y w))
  have hfd := ((hf.differentiable (by simp)).differentiableAt (x := P M e (w, y))).hasFDerivAt.comp w hd
  exact congrArg (fun L => L v) hfd.fderiv

/-- P3 fiber lemma for electron `e`. -/
theorem fiber (γne γee lam : ℝ) (M : ℕ) (e : Fin (M + 1))
    (hlam : IsBoundedBelowBy (atomicHamiltonian γne γee M) lam)
    (hVdom : ∀ g : 𝓢(A M, ℂ), g.toLp 2 (volume : Measure (A M)) ∈
      (mulOp volume (fun x => ((atomicPotential γne γee M x : ℝ) : ℂ))).domain)
    (f : A (M + 1) → ℂ) (hf : ContDiff ℝ ∞ f) (hcs : HasCompactSupport f)
    (hVint : Integrable (fun x => atomicPotential γne γee M (drop e x) * ‖f x‖ ^ 2)) :
    lam * ∫ x, ‖f x‖ ^ 2 ≤
      (∑ i : Fin M × Fin 3,
        ∫ x, ‖fderiv ℝ f x (EuclideanSpace.single (e.succAbove i.1, i.2) (1 : ℝ))‖ ^ 2) +
        ∫ x, atomicPotential γne γee M (drop e x) * ‖f x‖ ^ 2 := by
  simp only [← P_single]
  have hfc : Continuous f := hf.continuous
  have hfdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hc1 : HasCompactSupport (fun x => ‖f x‖ ^ 2) :=
    hcs.mono fun x hx h0 => hx (by simp [h0])
  have hI1 : Integrable (fun x => ‖f x‖ ^ 2) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hc1
  have hcd : HasCompactSupport (fderiv ℝ f) := hcs.fderiv (𝕜 := ℝ)
  have hI2 : ∀ i : Fin M × Fin 3, Integrable
      (fun x => ‖fderiv ℝ f x (P M e (EuclideanSpace.single i (1 : ℝ), 0))‖ ^ 2) := by
    intro i
    have hc2 : HasCompactSupport
        (fun x => ‖fderiv ℝ f x (P M e (EuclideanSpace.single i (1 : ℝ), 0))‖ ^ 2) :=
      hcd.mono fun x hx h0 => hx (by simp [h0])
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop) hc2
  obtain ⟨hJ1, hE1⟩ := fub M e _ hI1
  obtain ⟨hJ3, hE3⟩ := fub M e _ hVint
  have hJ2 := fun i => (fub M e _ (hI2 i)).1
  have hE2 := fun i => (fub M e _ (hI2 i)).2
  rw [hE1, hE3, Finset.sum_congr rfl fun i _ => hE2 i, ← integral_finsetSum _ fun i _ => hJ2 i,
    ← integral_const_mul, ← integral_add (integrable_finsetSum _ fun i _ => hJ2 i) hJ3]
  refine integral_mono (hJ1.const_mul lam) ((integrable_finsetSum _ fun i _ => hJ2 i).add hJ3) ?_
  intro y
  have hsd : ContDiff ℝ ∞ (fun w : A M => f (P M e (w, y))) :=
    hf.comp ((P M e : (A M × B) →L[ℝ] A (M + 1)).contDiff.comp (contDiff_id.prodMk contDiff_const))
  have hsc : HasCompactSupport (fun w : A M => f (P M e (w, y))) :=
    hcs.comp_isClosedEmbedding (closedEmb M e y)
  let g : 𝓢(A M, ℂ) := hsc.toSchwartzMap hsd
  have hg : ∀ w, g w = f (P M e (w, y)) := fun w => rfl
  have key := form_schwartz γne γee lam M hlam g (hVdom g)
  have hgf : (⇑g) = fun w : A M => f (P M e (w, y)) := funext hg
  simp only [hgf, fderiv_slice M e f hf y] at key
  simp only [drop_P]
  exact key

/-- dropping electron `e` only removes nonnegative repulsions and one attraction. -/
theorem pot_drop (γne γee : ℝ) (hee : 0 ≤ γee) (M : ℕ) (e : Fin (M + 1)) (x : A (M + 1)) :
    atomicPotential γne γee M (drop e x) - γne / ‖electron x e‖ ≤
      atomicPotential γne γee (M + 1) x := by
  have h1 : 0 ≤ ∑ k : Fin M, if e < e.succAbove k then
      γee / ‖electron x e - electron x (e.succAbove k)‖ else 0 :=
    Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
  have h2 : 0 ≤ ∑ i : Fin M, if e.succAbove i < e then
      γee / ‖electron x (e.succAbove i) - electron x e‖ else 0 :=
    Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
  unfold atomicPotential
  simp only [Finset.sum_filter, electron_drop]
  rw [Fin.sum_univ_succAbove (fun j => γne / ‖electron x j‖) e, Fin.sum_univ_succAbove _ e]
  simp only [Fin.sum_univ_succAbove _ e, lt_irrefl, if_false, Fin.succAbove_lt_succAbove_iff,
    Finset.sum_add_distrib, zero_add]
  linarith

end HVZFib

namespace HVZFib
open TeschlQM.Atomic

theorem pot_meas (γne γee : ℝ) (N : ℕ) : Measurable (atomicPotential γne γee N) := by
  unfold atomicPotential electron
  refine (Finset.measurable_sum _ fun j _ => ?_).neg.add
    (Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_) <;> fun_prop

lemma div_le_add_div_sq (F t : ℝ) (hF : 0 ≤ F) (ht : 0 ≤ t) : F / t ≤ F + F / t ^ 2 := by
  rcases ht.eq_or_lt with h | h
  · subst h; simp [hF]
  · rcases le_or_gt 1 t with h1 | h1
    · have := div_le_self hF h1
      have : 0 ≤ F / t ^ 2 := by positivity
      linarith
    · have h2 : F / t ≤ F / t ^ 2 := div_le_div_of_nonneg_left hF (by positivity) (by nlinarith)
      linarith

lemma pot_abs_mul_le (γne γee : ℝ) (N : ℕ) (x : A N) (F : ℝ) (hF : 0 ≤ F) :
    |atomicPotential γne γee N x| * F ≤
      (∑ j, |γne| * (F + F / ‖electron x j‖ ^ 2)) +
        ∑ j, ∑ k ∈ Finset.univ.filter (fun k : Fin N => j < k),
          |γee| * (F + F / ‖electron x j - electron x k‖ ^ 2) := by
  have hA : |atomicPotential γne γee N x| ≤ (∑ j, |γne| / ‖electron x j‖) +
      ∑ j, ∑ k ∈ Finset.univ.filter (fun k : Fin N => j < k),
        |γee| / ‖electron x j - electron x k‖ := by
    unfold atomicPotential
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_neg]
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (le_of_eq (Finset.sum_congr rfl fun j _ => by rw [abs_div, abs_norm]))
    · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ =>
        (Finset.abs_sum_le_sum_abs _ _).trans
          (le_of_eq (Finset.sum_congr rfl fun k _ => by rw [abs_div, abs_norm])))
  refine (mul_le_mul_of_nonneg_right hA hF).trans ?_
  simp only [add_mul, Finset.sum_mul]
  refine add_le_add (Finset.sum_le_sum fun j _ => ?_)
    (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_) <;>
  · rw [div_mul_eq_mul_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_add_div_sq F _ hF (norm_nonneg _)) (abs_nonneg _)

theorem int_pot {X : Type*} [MeasurableSpace X] {μ : Measure X} (γne γee : ℝ) (N : ℕ)
    (y : X → A N) (hy : Measurable y) (G : X → ℝ) (hG0 : ∀ x, 0 ≤ G x) (hG : Integrable G μ)
    (h1 : ∀ j, Integrable (fun x => G x / ‖electron (y x) j‖ ^ 2) μ)
    (h2 : ∀ j k, j < k → Integrable (fun x => G x / ‖electron (y x) j - electron (y x) k‖ ^ 2) μ) :
    Integrable (fun x => atomicPotential γne γee N (y x) * G x) μ := by
  refine Integrable.mono' (g := fun x => (∑ j, |γne| * (G x + G x / ‖electron (y x) j‖ ^ 2)) +
      ∑ j, ∑ k ∈ Finset.univ.filter (fun k : Fin N => j < k),
        |γee| * (G x + G x / ‖electron (y x) j - electron (y x) k‖ ^ 2)) ?_ ?_ ?_
  · exact (integrable_finsetSum _ fun j _ => (hG.add (h1 j)).const_mul _).add
      (integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k hk =>
        (hG.add (h2 j k (Finset.mem_filter.1 hk).2)).const_mul _)
  · exact ((pot_meas γne γee N).comp hy).aestronglyMeasurable.mul hG.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hG0 x)]
      exact pot_abs_mul_le _ _ _ _ _ (hG0 x)

/-- Hardy-type hypotheses on Schwartz functions (proved in D0). -/
def HardyS (N : ℕ) : Prop :=
  ∀ (g : 𝓢(A N, ℂ)) (j : Fin N), Integrable (fun x => ‖g x‖ ^ 2 / ‖electron x j‖ ^ 2) ∧
    ∫ x, ‖g x‖ ^ 2 / ‖electron x j‖ ^ 2 ≤
      4 * ∑ p : Fin N × Fin 3, ∫ x, ‖fderiv ℝ (⇑g) x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2

def HardyP (N : ℕ) : Prop :=
  ∀ (g : 𝓢(A N, ℂ)) (j k : Fin N), j ≠ k →
    Integrable (fun x => ‖g x‖ ^ 2 / ‖electron x j - electron x k‖ ^ 2)

theorem int_pot_drop (γne γee : ℝ) (M : ℕ) (e : Fin (M + 1)) (hS : HardyS (M + 1))
    (hP : HardyP (M + 1)) (g : 𝓢(A (M + 1), ℂ)) :
    Integrable (fun x => atomicPotential γne γee M (drop e x) * ‖g x‖ ^ 2) := by
  have hG : Integrable (fun x => ‖g x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm g.continuous.aestronglyMeasurable).1 (g.memLp 2)
  refine int_pot γne γee M (drop e) ?_ (fun x => ‖g x‖ ^ 2) (fun x => by positivity) hG ?_ ?_
  · exact (emap M e).measurable.fst
  · intro j
    simpa only [electron_drop] using (hS g (e.succAbove j)).1
  · intro j k hjk
    simpa only [electron_drop] using hP g _ _ ((Fin.succAbove_right_injective (p := e)).ne hjk.ne)

theorem int_pot_self (γne γee : ℝ) (N : ℕ) (hS : HardyS N) (hP : HardyP N) (g : 𝓢(A N, ℂ)) :
    Integrable (fun x => atomicPotential γne γee N x * ‖g x‖ ^ 2) := by
  have hG : Integrable (fun x => ‖g x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm g.continuous.aestronglyMeasurable).1 (g.memLp 2)
  exact int_pot γne γee N id measurable_id (fun x => ‖g x‖ ^ 2) (fun x => by positivity) hG
    (fun j => (hS g j).1) (fun j k hjk => hP g j k hjk.ne)

end HVZFib

namespace HVZFib
open TeschlQM.Atomic TeschlQM.Shared

lemma K_split (M : ℕ) (e : Fin (M + 1)) (h : Fin (M + 1) × Fin 3 → ℝ) :
    ∑ p, h p = ∑ a, h (e, a) + ∑ i : Fin M × Fin 3, h (e.succAbove i.1, i.2) := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_succAbove _ e, Fintype.sum_prod_type]

lemma near_le (γ r t F : ℝ) (hγ : 0 ≤ γ) (hr : 0 < r) (ht : 0 ≤ t) (hF : 0 ≤ F) :
    (if r ≤ t then 0 else γ / t) * F ≤ γ * r * (F / t ^ 2) := by
  split_ifs with h
  · simp only [zero_mul]; positivity
  · rcases ht.eq_or_lt with h0 | h0
    · subst h0; simp
    · have h' : t < r := lt_of_not_ge h
      have e1 : γ / t * F = γ * r * (F / t ^ 2) * (t / r) := by field_simp <;> ring
      rw [e1]
      exact mul_le_of_le_one_right (by positivity) ((div_le_one hr).2 h'.le)

/-- Per-electron bound: `g` localized where electron `e` is the far one. -/
theorem elec_bound (γne γee lam δ r : ℝ) (hne : 0 ≤ γne) (hee : 0 ≤ γee) (hr : 0 < r)
    (hrδ : 4 * γne * r ≤ δ) (M : ℕ) (e : Fin (M + 1))
    (hlam : IsBoundedBelowBy (atomicHamiltonian γne γee M) lam)
    (hVdom : ∀ g : 𝓢(A M, ℂ), g.toLp 2 (volume : Measure (A M)) ∈
      (mulOp volume (fun x => ((atomicPotential γne γee M x : ℝ) : ℂ))).domain)
    (hS : HardyS (M + 1)) (hP : HardyP (M + 1))
    (g : A (M + 1) → ℂ) (hg : ContDiff ℝ ∞ g) (hcs : HasCompactSupport g) :
    (lam * ∫ x, ‖g x‖ ^ 2)
      - (∫ x, (if r ≤ ‖electron x e‖ then γne / ‖electron x e‖ else 0) * ‖g x‖ ^ 2)
      - δ * ∑ p, ∫ x, ‖fderiv ℝ g x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2 ≤
      (∑ p, ∫ x, ‖fderiv ℝ g x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2) +
        ∫ x, atomicPotential γne γee (M + 1) x * ‖g x‖ ^ 2 := by
  let G : 𝓢(A (M + 1), ℂ) := hcs.toSchwartzMap hg
  have hGg : (⇑G : A (M + 1) → ℂ) = g := rfl
  have hF : Integrable (fun x => ‖g x‖ ^ 2) := by
    rw [← hGg]
    exact (memLp_two_iff_integrable_sq_norm G.continuous.aestronglyMeasurable).1 (G.memLp 2)
  have hVd := int_pot_drop γne γee M e hS hP G
  have hVs := int_pot_self γne γee (M + 1) hS hP G
  rw [hGg] at hVd hVs
  have hfib := fiber γne γee lam M e hlam hVdom g hg hcs hVd
  obtain ⟨hH1, hH2⟩ := hS G e
  rw [hGg] at hH1 hH2
  have ht : Measurable (fun x : A (M + 1) => ‖electron x e‖) := (emap M e).measurable.snd.norm
  have hfar_m : Measurable (fun x : A (M + 1) => if r ≤ ‖electron x e‖ then γne / ‖electron x e‖ else 0) :=
    Measurable.ite (measurableSet_le measurable_const ht) (measurable_const.div ht) measurable_const
  have hnear_m : Measurable (fun x : A (M + 1) => if r ≤ ‖electron x e‖ then 0 else γne / ‖electron x e‖) :=
    Measurable.ite (measurableSet_le measurable_const ht) measurable_const (measurable_const.div ht)
  have hgm : Measurable (fun x => ‖g x‖ ^ 2) := hg.continuous.measurable.norm.pow_const 2
  have hfar : Integrable (fun x => (if r ≤ ‖electron x e‖ then γne / ‖electron x e‖ else 0) * ‖g x‖ ^ 2) := by
    refine Integrable.mono' (hF.const_mul (γne / r)) (hfar_m.mul hgm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖g x‖ ^ 2)]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    split_ifs with h
    · rw [abs_of_nonneg (by positivity)]
      exact div_le_div_of_nonneg_left hne hr h
    · simp only [abs_zero]; positivity
  have hnear_le : ∀ x, (if r ≤ ‖electron x e‖ then 0 else γne / ‖electron x e‖) * ‖g x‖ ^ 2 ≤
      γne * r * (‖g x‖ ^ 2 / ‖electron x e‖ ^ 2) := fun x =>
    near_le γne r _ _ hne hr (norm_nonneg _) (by positivity)
  have hnear : Integrable (fun x => (if r ≤ ‖electron x e‖ then 0 else γne / ‖electron x e‖) * ‖g x‖ ^ 2) := by
    refine Integrable.mono' (hH1.const_mul (γne * r)) (hnear_m.mul hgm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by split_ifs <;> positivity)]
    exact hnear_le x
  have hsplit : ∀ x, γne / ‖electron x e‖ * ‖g x‖ ^ 2 =
      (if r ≤ ‖electron x e‖ then γne / ‖electron x e‖ else 0) * ‖g x‖ ^ 2 +
        (if r ≤ ‖electron x e‖ then 0 else γne / ‖electron x e‖) * ‖g x‖ ^ 2 := fun x => by
    split_ifs <;> ring
  have hpot : ∫ x, atomicPotential γne γee M (drop e x) * ‖g x‖ ^ 2 ≤
      (∫ x, atomicPotential γne γee (M + 1) x * ‖g x‖ ^ 2) +
        ((∫ x, (if r ≤ ‖electron x e‖ then γne / ‖electron x e‖ else 0) * ‖g x‖ ^ 2) +
          ∫ x, (if r ≤ ‖electron x e‖ then 0 else γne / ‖electron x e‖) * ‖g x‖ ^ 2) := by
    have hfn : Integrable (fun x => (if r ≤ ‖electron x e‖ then γne / ‖electron x e‖ else 0) * ‖g x‖ ^ 2 +
        (if r ≤ ‖electron x e‖ then 0 else γne / ‖electron x e‖) * ‖g x‖ ^ 2) := hfar.add hnear
    rw [← integral_add hfar hnear, ← integral_add hVs hfn]
    refine integral_mono hVd (hVs.add hfn) fun x => ?_
    have h1 := mul_le_mul_of_nonneg_right (pot_drop γne γee hee M e x)
      (by positivity : (0 : ℝ) ≤ ‖g x‖ ^ 2)
    have h2 := hsplit x
    rw [sub_mul] at h1
    linarith
  have hnearI : ∫ x, (if r ≤ ‖electron x e‖ then 0 else γne / ‖electron x e‖) * ‖g x‖ ^ 2 ≤
      γne * r * (4 * ∑ p, ∫ x, ‖fderiv ℝ g x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2) := by
    refine (integral_mono hnear (hH1.const_mul (γne * r)) hnear_le).trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hH2 (by positivity)
  have hK0 : 0 ≤ ∑ p, ∫ x, ‖fderiv ℝ g x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2 :=
    Finset.sum_nonneg fun p _ => integral_nonneg fun x => by positivity
  have hKe : 0 ≤ ∑ a, ∫ x, ‖fderiv ℝ g x (EuclideanSpace.single (e, a) (1 : ℝ))‖ ^ 2 :=
    Finset.sum_nonneg fun p _ => integral_nonneg fun x => by positivity
  have hKs : ∑ p, ∫ x, ‖fderiv ℝ g x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2 =
      (∑ a, ∫ x, ‖fderiv ℝ g x (EuclideanSpace.single (e, a) (1 : ℝ))‖ ^ 2) +
        ∑ i : Fin M × Fin 3, ∫ x, ‖fderiv ℝ g x (EuclideanSpace.single (e.succAbove i.1, i.2) (1 : ℝ))‖ ^ 2 :=
    K_split M e (fun p => ∫ x, ‖fderiv ℝ g x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2)
  have hδK : γne * r * (4 * ∑ p, ∫ x, ‖fderiv ℝ g x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2) ≤
      δ * ∑ p, ∫ x, ‖fderiv ℝ g x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hrδ hK0
    linarith
  linarith

end HVZFib


/-! P2 IMS identity for 7ab9d8bf D3c. -/

set_option autoImplicit false

open MeasureTheory
open scoped ContDiff ComplexConjugate

namespace HVZIms

lemma nsq (a b : ℝ) (F G : ℂ) :
    ‖(a : ℂ) * F + (b : ℂ) * G‖ ^ 2 =
      a ^ 2 * ‖F‖ ^ 2 + b ^ 2 * ‖G‖ ^ 2 + 2 * (a * b) * (F * conj G).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι]

lemma fderiv_ofReal_mul (φ : E → ℝ) (f : E → ℂ) (x v : E) (hφ : DifferentiableAt ℝ φ x)
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun y => (φ y : ℂ) * f y) x v =
      ((fderiv ℝ φ x v : ℝ) : ℂ) * f x + (φ x : ℂ) * fderiv ℝ f x v := by
  have hc : HasFDerivAt (fun y => (φ y : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ φ x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hφ.hasFDerivAt
  have h := hc.mul hf.hasFDerivAt
  rw [show (fun y => (φ y : ℂ) * f y) = (fun y => (φ y : ℂ)) * f from rfl, h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  ring

lemma sum_mul_fderiv_zero (φ : ι → E → ℝ) (x v : E) (hφ : ∀ e, DifferentiableAt ℝ (φ e) x)
    (hsum : ∀ y, ∑ e, φ e y ^ 2 = 1) : ∑ e, fderiv ℝ (φ e) x v * φ e x = 0 := by
  have h1 : HasFDerivAt (fun y => ∑ e, φ e y ^ 2)
      (∑ e, ((2 : ℕ) * φ e x ^ (2 - 1)) • fderiv ℝ (φ e) x) x := by
    have := HasFDerivAt.fun_sum (u := Finset.univ) (fun e _ => (hφ e).hasFDerivAt.pow 2)
    simpa using this
  have h2 : HasFDerivAt (fun y => ∑ e, φ e y ^ 2) (0 : E →L[ℝ] ℝ) x := by
    rw [show (fun y => ∑ e, φ e y ^ 2) = fun _ => (1 : ℝ) from funext hsum]
    exact hasFDerivAt_const 1 x
  have h3 := congrArg (fun L : E →L[ℝ] ℝ => L v) (h1.unique h2)
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.zero_apply] at h3
  have h4 : ∑ e, fderiv ℝ (φ e) x v * φ e x = (1 / 2) * ∑ e, (2 : ℕ) * φ e x ^ (2 - 1) * fderiv ℝ (φ e) x v := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by push_cast; ring
  rw [h4, h3, mul_zero]

/-- Pointwise IMS identity. -/
theorem ims_pt (φ : ι → E → ℝ) (f : E → ℂ) (x v : E) (hφ : ∀ e, DifferentiableAt ℝ (φ e) x)
    (hf : DifferentiableAt ℝ f x) (hsum : ∀ y, ∑ e, φ e y ^ 2 = 1) :
    ∑ e, ‖fderiv ℝ (fun y => (φ e y : ℂ) * f y) x v‖ ^ 2 =
      ‖fderiv ℝ f x v‖ ^ 2 + (∑ e, (fderiv ℝ (φ e) x v) ^ 2) * ‖f x‖ ^ 2 := by
  have h0 := sum_mul_fderiv_zero φ x v hφ hsum
  simp only [fun e => fderiv_ofReal_mul (φ e) f x v (hφ e) hf, nsq]
  have hs := hsum x
  calc ∑ e, ((fderiv ℝ (φ e) x v) ^ 2 * ‖f x‖ ^ 2 + φ e x ^ 2 * ‖fderiv ℝ f x v‖ ^ 2 +
        2 * (fderiv ℝ (φ e) x v * φ e x) * (f x * conj (fderiv ℝ f x v)).re)
      = (∑ e, (fderiv ℝ (φ e) x v) ^ 2) * ‖f x‖ ^ 2 + (∑ e, φ e x ^ 2) * ‖fderiv ℝ f x v‖ ^ 2 +
        2 * (∑ e, fderiv ℝ (φ e) x v * φ e x) * (f x * conj (fderiv ℝ f x v)).re := by
        rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    _ = _ := by rw [hs, h0]; ring

/-- Integrated IMS identity for a smooth compactly supported `f`. -/
theorem ims_int [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)]
    (φ : ι → E → ℝ) (hφ : ∀ e, ContDiff ℝ ∞ (φ e)) (hsum : ∀ y, ∑ e, φ e y ^ 2 = 1)
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (hcs : HasCompactSupport f) (v : E) :
    ∑ e, ∫ x, ‖fderiv ℝ (fun y => (φ e y : ℂ) * f y) x v‖ ^ 2 =
      (∫ x, ‖fderiv ℝ f x v‖ ^ 2) + ∫ x, (∑ e, (fderiv ℝ (φ e) x v) ^ 2) * ‖f x‖ ^ 2 := by
  have hφc : ∀ e, ContDiff ℝ ∞ (fun y => (φ e y : ℂ) * f y) := fun e =>
    (Complex.ofRealCLM.contDiff.comp (hφ e)).mul hf
  have hI : ∀ e, Integrable (fun x => ‖fderiv ℝ (fun y => (φ e y : ℂ) * f y) x v‖ ^ 2) := by
    intro e
    have hcs' : HasCompactSupport (fun y => (φ e y : ℂ) * f y) := hcs.mul_left
    have hcd := hcs'.fderiv (𝕜 := ℝ)
    have hcont := (hφc e).continuous_fderiv (by simp)
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (hcd.mono fun x hx h0 => hx (by simp [h0]))
  have hI1 : Integrable (fun x => ‖fderiv ℝ f x v‖ ^ 2) := by
    have hcont := hf.continuous_fderiv (by simp)
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
      ((hcs.fderiv (𝕜 := ℝ)).mono fun x hx h0 => hx (by simp [h0]))
  have hI2 : Integrable (fun x => (∑ e, (fderiv ℝ (φ e) x v) ^ 2) * ‖f x‖ ^ 2) := by
    have hcont : ∀ e, Continuous (fderiv ℝ (φ e)) := fun e => (hφ e).continuous_fderiv (by simp)
    have hfc := hf.continuous
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (hcs.mono fun x hx h0 => hx (by simp [h0]))
  rw [← integral_finsetSum _ fun e _ => hI e, ← integral_add hI1 hI2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact ims_pt φ f x v (fun e => ((hφ e).differentiable (by simp)).differentiableAt)
    ((hf.differentiable (by simp)).differentiableAt) hsum

end HVZIms

namespace HVZAsm
open HVZIms

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {ι : Type*} [Fintype ι]

/-- kinetic form `∑ₚ ∫ |∂ₚ g|²`. -/
noncomputable def kin (g : EuclideanSpace ℝ κ → ℂ) : ℝ :=
  ∑ p, ∫ x, ‖fderiv ℝ g x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2

/-- localization error `W = (1+δ) ∑ₚ∑ₑ (∂ₚ φₑ)² + ∑ₑ farₑ φₑ²`. -/
noncomputable def Wfun (δ : ℝ) (φ : ι → EuclideanSpace ℝ κ → ℝ) (far : ι → EuclideanSpace ℝ κ → ℝ)
    (x : EuclideanSpace ℝ κ) : ℝ :=
  (1 + δ) * ∑ p, ∑ e, (fderiv ℝ (φ e) x (EuclideanSpace.single p (1 : ℝ))) ^ 2 +
    ∑ e, far e x * φ e x ^ 2

lemma int_cs (f : EuclideanSpace ℝ κ → ℂ) (hcs : HasCompactSupport f) (h : EuclideanSpace ℝ κ → ℝ)
    (hc : Continuous h) (hz : ∀ x, f x = 0 → h x = 0) : Integrable h :=
  hc.integrable_of_hasCompactSupport (hcs.mono fun x hx h0 => hx (hz x h0))

theorem assemble (lam δ : ℝ) (φ : ι → EuclideanSpace ℝ κ → ℝ) (hφ : ∀ e, ContDiff ℝ ∞ (φ e))
    (hsum : ∀ y, ∑ e, φ e y ^ 2 = 1)
    (far : ι → EuclideanSpace ℝ κ → ℝ) (hfm : ∀ e, Measurable (far e))
    (hfb : ∀ e, ∃ C, ∀ x, |far e x| ≤ C) (V : EuclideanSpace ℝ κ → ℝ)
    (hVi : ∀ g : EuclideanSpace ℝ κ → ℂ, ContDiff ℝ ∞ g → HasCompactSupport g →
      Integrable (fun x => V x * ‖g x‖ ^ 2))
    (hEB : ∀ (e : ι) (g : EuclideanSpace ℝ κ → ℂ), ContDiff ℝ ∞ g → HasCompactSupport g →
      (lam * ∫ x, ‖g x‖ ^ 2) - (∫ x, far e x * ‖g x‖ ^ 2) - δ * kin g ≤
        kin g + ∫ x, V x * ‖g x‖ ^ 2)
    (f : EuclideanSpace ℝ κ → ℂ) (hf : ContDiff ℝ ∞ f) (hcs : HasCompactSupport f) :
    (lam * ∫ x, ‖f x‖ ^ 2) - δ * kin f - (∫ x, Wfun δ φ far x * ‖f x‖ ^ 2) ≤
      kin f + ∫ x, V x * ‖f x‖ ^ 2 := by
  classical
  set g : ι → EuclideanSpace ℝ κ → ℂ := fun e y => (φ e y : ℂ) * f y with hg
  have hgc : ∀ e, ContDiff ℝ ∞ (g e) := fun e => (Complex.ofRealCLM.contDiff.comp (hφ e)).mul hf
  have hgs : ∀ e, HasCompactSupport (g e) := fun e => hcs.mul_left
  have hn : ∀ e x, ‖g e x‖ ^ 2 = φ e x ^ 2 * ‖f x‖ ^ 2 := by
    intro e x
    simp only [hg, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hfc := hf.continuous
  have hφc : ∀ e, Continuous (φ e) := fun e => (hφ e).continuous
  have hdc : ∀ e, Continuous (fderiv ℝ (φ e)) := fun e => (hφ e).continuous_fderiv (by simp)
  have hA : Integrable (fun x => ‖f x‖ ^ 2) :=
    int_cs f hcs _ (by fun_prop) fun x h0 => by simp [h0]
  have hAe : ∀ e, Integrable (fun x => ‖g e x‖ ^ 2) := fun e =>
    int_cs f hcs _ (by simp only [hn]; fun_prop) fun x h0 => by simp [hn, h0]
  have hFe : ∀ e, Integrable (fun x => far e x * ‖g e x‖ ^ 2) := by
    intro e
    obtain ⟨C, hC⟩ := hfb e
    refine ((hAe e).const_mul C).mono' ((hfm e).aestronglyMeasurable.mul (hAe e).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    show ‖far e x * ‖g e x‖ ^ 2‖ ≤ C * ‖g e x‖ ^ 2
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖g e x‖)]
    exact mul_le_mul_of_nonneg_right (hC x) (sq_nonneg _)
  have hDp : ∀ p : κ, Integrable (fun x =>
      (∑ e, (fderiv ℝ (φ e) x (EuclideanSpace.single p (1 : ℝ))) ^ 2) * ‖f x‖ ^ 2) := fun p =>
    int_cs f hcs _ (by fun_prop) fun x h0 => by simp [h0]
  -- mass
  have hmass : ∑ e, ∫ x, ‖g e x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    rw [← integral_finsetSum _ fun e _ => hAe e]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hn, ← Finset.sum_mul, hsum, one_mul]
  -- potential
  have hpot : ∑ e, ∫ x, V x * ‖g e x‖ ^ 2 = ∫ x, V x * ‖f x‖ ^ 2 := by
    rw [← integral_finsetSum _ fun e _ => hVi (g e) (hgc e) (hgs e)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hn]
    rw [← Finset.mul_sum, ← Finset.sum_mul, hsum, one_mul]
  -- kinetic (IMS)
  have hkin : ∑ e, kin (g e) = kin f + ∑ p : κ, ∫ x,
      (∑ e, (fderiv ℝ (φ e) x (EuclideanSpace.single p (1 : ℝ))) ^ 2) * ‖f x‖ ^ 2 := by
    simp only [kin]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    exact ims_int φ hφ hsum f hf hcs _
  -- W
  have hW : ∫ x, Wfun δ φ far x * ‖f x‖ ^ 2 =
      (1 + δ) * (∑ p : κ, ∫ x,
        (∑ e, (fderiv ℝ (φ e) x (EuclideanSpace.single p (1 : ℝ))) ^ 2) * ‖f x‖ ^ 2) +
      ∑ e, ∫ x, far e x * ‖g e x‖ ^ 2 := by
    rw [← integral_finsetSum _ fun p _ => hDp p, ← integral_finsetSum _ fun e _ => hFe e,
      ← integral_const_mul, ← integral_add ((integrable_finsetSum _ fun p _ => hDp p).const_mul _)
        (integrable_finsetSum _ fun e _ => hFe e)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Wfun, hn, Finset.sum_mul, add_mul, mul_assoc]
  have hS := Finset.sum_le_sum (s := Finset.univ) fun e _ => hEB e (g e) (hgc e) (hgs e)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hS
  rw [hmass, hpot, hkin] at hS
  rw [hW]
  nlinarith [hS]

end HVZAsm

namespace HVZAsm
open Filter Topology

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {ι : Type*} [Fintype ι]

lemma ev_R {P : EuclideanSpace ℝ κ → Prop} (h : ∀ᶠ x in cocompact (EuclideanSpace ℝ κ), P x) :
    ∃ R : ℝ, ∀ x, R ≤ ‖x‖ → P x := by
  obtain ⟨t, ht, hts⟩ := Filter.mem_cocompact.1 h
  obtain ⟨R, hR⟩ := ht.isBounded.subset_closedBall 0
  refine ⟨R + 1, fun x hx => hts fun hxt => ?_⟩
  have := hR hxt
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith

lemma bdd_of_tendsto (h : EuclideanSpace ℝ κ → ℝ) (hc : Continuous h)
    (ht : Tendsto h (cocompact _) (𝓝 0)) : ∃ C : ℝ, ∀ x, |h x| ≤ C := by
  obtain ⟨R, hR⟩ := ev_R ((Metric.tendsto_nhds.1 ht) 1 one_pos)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ κ) R).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 1, fun x => ?_⟩
  by_cases hx : R ≤ ‖x‖
  · have := hR x hx
    rw [Real.dist_eq, sub_zero] at this
    exact le_trans this.le (le_max_right _ _)
  · have := hC x (by rw [Metric.mem_closedBall, dist_zero_right]; linarith)
    rw [Real.norm_eq_abs] at this
    exact le_trans this (le_max_left _ _)

theorem Wprops (δ : ℝ) (φ : ι → EuclideanSpace ℝ κ → ℝ) (hφ : ∀ e, ContDiff ℝ ∞ (φ e))
    (hsum : ∀ y, ∑ e, φ e y ^ 2 = 1)
    (hdt : ∀ e, Tendsto (fun x => ‖fderiv ℝ (φ e) x‖) (cocompact _) (𝓝 0))
    (far : ι → EuclideanSpace ℝ κ → ℝ) (hfm : ∀ e, Measurable (far e))
    (hfb : ∀ e, ∃ C, ∀ x, |far e x| ≤ C)
    (hft : ∀ e, Tendsto (fun x => far e x * φ e x ^ 2) (cocompact _) (𝓝 0)) :
    Measurable (Wfun δ φ far) ∧ (∃ C : ℝ, ∀ x, |Wfun δ φ far x| ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x, R ≤ ‖x‖ → |Wfun δ φ far x| ≤ ε) := by
  classical
  have hφc : ∀ e, Continuous (φ e) := fun e => (hφ e).continuous
  have hdc : ∀ e, Continuous (fderiv ℝ (φ e)) := fun e => (hφ e).continuous_fderiv (by simp)
  set D : EuclideanSpace ℝ κ → ℝ := fun x =>
    ∑ p, ∑ e, (fderiv ℝ (φ e) x (EuclideanSpace.single p (1 : ℝ))) ^ 2 with hD
  set F : EuclideanSpace ℝ κ → ℝ := fun x => ∑ e, far e x * φ e x ^ 2 with hF
  have hWe : Wfun δ φ far = fun x => (1 + δ) * D x + F x := rfl
  have hDc : Continuous D := by simp only [hD]; fun_prop
  have hFm : Measurable F := Finset.measurable_sum _ fun e _ =>
    (hfm e).mul ((hφc e).measurable.pow_const 2)
  have hdv : ∀ e (v : EuclideanSpace ℝ κ),
      Tendsto (fun x => fderiv ℝ (φ e) x v) (cocompact _) (𝓝 0) := by
    intro e v
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h2 := (hdt e).mul_const ‖v‖
    rw [zero_mul] at h2
    exact squeeze_zero (fun _ => norm_nonneg _) (fun x => (fderiv ℝ (φ e) x).le_opNorm v) h2
  have hDt : Tendsto D (cocompact _) (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset κ) fun p _ =>
      tendsto_finset_sum (Finset.univ : Finset ι) fun e _ =>
        (hdv e (EuclideanSpace.single p (1 : ℝ))).pow 2
    simpa [hD] using this
  have hFt : Tendsto F (cocompact _) (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset ι) fun e _ => hft e
    simpa [hF] using this
  have hWt : Tendsto (Wfun δ φ far) (cocompact _) (𝓝 0) := by
    have := (hDt.const_mul (1 + δ)).add hFt
    rw [mul_zero, add_zero] at this
    rw [hWe]; exact this
  refine ⟨?_, ?_, ?_⟩
  · rw [hWe]; exact (hDc.measurable.const_mul _).add hFm
  · obtain ⟨CD, hCD⟩ := bdd_of_tendsto D hDc hDt
    choose Cf hCf using hfb
    have hφ1 : ∀ e x, φ e x ^ 2 ≤ 1 := fun e x => by
      rw [← hsum x]
      exact Finset.single_le_sum (f := fun e => φ e x ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ e)
    refine ⟨|1 + δ| * CD + ∑ e, Cf e, fun x => ?_⟩
    rw [hWe]
    have h1 : |F x| ≤ ∑ e, Cf e := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun e _ => ?_)
      rw [abs_mul, abs_of_nonneg (sq_nonneg (φ e x))]
      have h0 : 0 ≤ Cf e := le_trans (abs_nonneg _) (hCf e x)
      calc |far e x| * φ e x ^ 2 ≤ Cf e * 1 :=
            mul_le_mul (hCf e x) (hφ1 e x) (sq_nonneg _) h0
        _ = Cf e := mul_one _
    calc |(1 + δ) * D x + F x| ≤ |(1 + δ) * D x| + |F x| := abs_add_le _ _
      _ ≤ |1 + δ| * CD + ∑ e, Cf e := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left (hCD x) (abs_nonneg _)) h1
  · intro ε hε
    obtain ⟨R, hR⟩ := ev_R ((Metric.tendsto_nhds.1 hWt) ε hε)
    refine ⟨R, fun x hx => ?_⟩
    have := hR x hx
    rw [Real.dist_eq, sub_zero] at this
    exact this.le

end HVZAsm

namespace HVZX
open TeschlQM.Atomic TeschlQM.Shared HVZFib HVZAsm HVZFar

theorem ccbound_of (γne γee : ℝ) (hne : 0 < γne) (hee : 0 < γee) (M : ℕ) (lam δ : ℝ) (hδ : 0 < δ)
    (hlam : IsBoundedBelowBy (atomicHamiltonian γne γee M) lam)
    (hVdom : ∀ g : 𝓢(A M, ℂ), g.toLp 2 (volume : Measure (A M)) ∈
      (mulOp volume (fun x => ((atomicPotential γne γee M x : ℝ) : ℂ))).domain)
    (hS : HardyS (M + 1)) (hP : HardyP (M + 1)) :
    ∃ W : A (M + 1) → ℝ, Measurable W ∧ (∃ C : ℝ, ∀ x, |W x| ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x, R ≤ ‖x‖ → |W x| ≤ ε) ∧
      ∀ f : A (M + 1) → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
        (lam * ∫ x, ‖f x‖ ^ 2) - δ * kin f - (∫ x, W x * ‖f x‖ ^ 2) ≤
          kin f + ∫ x, atomicPotential γne γee (M + 1) x * ‖f x‖ ^ 2 := by
  set r : ℝ := δ / (4 * γne) with hr_def
  have hr : 0 < r := by positivity
  have hrδ : 4 * γne * r ≤ δ := by rw [hr_def]; field_simp; exact le_rfl
  set n : ℝ := ((M + 1 : ℕ) : ℝ) with hn_def
  have hn : 1 ≤ n := by rw [hn_def]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le M)
  set C : ℝ := 1 / (2 * n) with hC_def
  have hC0 : 0 < C := by positivity
  have hD : 0 < 1 / n - C ^ 2 := by
    have : C ^ 2 < 1 / n := by
      rw [hC_def, div_pow, one_pow, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hN0 : 0 < M + 1 := Nat.succ_pos M
  have hφ : ∀ e, ContDiff ℝ ∞ (HVZPart.φ (N := M + 1) C e) := fun e => HVZPart.contDiff_φ hN0 hD e
  have hsum : ∀ y, ∑ e, HVZPart.φ (N := M + 1) C e y ^ 2 = 1 := fun y => HVZPart.φ_sum hN0 hD y
  obtain ⟨hWm, hWb, hWt⟩ := Wprops δ (HVZPart.φ (N := M + 1) C) hφ hsum
    (fun e => HVZPart.fderiv_tendsto e (hφ e)) (far (N := M + 1) γne r) (fun e => far_meas γne r e)
    (fun e => far_bdd γne r hne.le hr e) (fun e => far_tendsto γne r C hne.le hN0 hC0 hD e)
  refine ⟨Wfun δ (HVZPart.φ (N := M + 1) C) (far (N := M + 1) γne r), hWm, hWb, hWt, fun f hf hcs => ?_⟩
  have h := assemble lam δ (HVZPart.φ (N := M + 1) C) hφ hsum (far (N := M + 1) γne r)
    (fun e => far_meas γne r e) (fun e => far_bdd γne r hne.le hr e) (atomicPotential γne γee (M + 1))
    (fun g hg hgs => int_pot_self γne γee (M + 1) hS hP (hgs.toSchwartzMap hg))
    (fun e g hg hgs => elec_bound γne γee lam δ r hne.le hee.le hr hrδ M e hlam hVdom hS hP g hg hgs)
    f hf hcs
  exact h

end HVZX

end SecX

section SecHS

/-! Grandchild D0 of 7ab9d8bf (HVZ), child of the essential-spectrum identity: H^N is symmetric,
has a real resolvent point, is bounded below, and controls the kinetic form.
Hardy's inequality in each electron coordinate (dilation argument on Schwartz functions, Plancherel for
derivatives, density of Schwartz functions in the graph norm of H0, Fatou) + Coulomb AM-GM bound. -/

set_option autoImplicit false

/-! Hardy inequality pieces for 7ab9d8bf (HVZ C1). -/


open MeasureTheory SchwartzMap FourierTransform LineDeriv

namespace HVZHardy

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- H2: Plancherel for a directional derivative of a Schwartz function. -/
theorem integral_norm_sq_lineDeriv (f : 𝓢(V, ℂ)) (m : V) :
    ∫ x, ‖fderiv ℝ f x m‖ ^ 2 =
      ∫ ξ, (2 * Real.pi * inner ℝ ξ m) ^ 2 * ‖𝓕 f ξ‖ ^ 2 := by
  have h1 := integral_norm_sq_fourier (∂_{m} f)
  rw [fourier_lineDerivOp_eq] at h1
  have hg : (inner ℝ · m : V → ℝ).HasTemperateGrowth := ((innerSL ℝ).flip m).hasTemperateGrowth
  rw [← integral_congr_ae (Filter.Eventually.of_forall fun x => by
      rw [← lineDerivOp_apply_eq_fderiv] : ∀ᵐ x ∂volume, ‖(∂_{m} f) x‖ ^ 2 = ‖fderiv ℝ f x m‖ ^ 2),
    ← h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_apply, smulLeftCLM_apply_apply hg, norm_smul, Complex.norm_mul,
    Complex.norm_I, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- H1a scaling: in dimension 3, `∫ |f(s y)|²/|y|² = s⁻¹ ∫ |f|²/|y|²`. -/
theorem integral_scale (hV : Module.finrank ℝ V = 3) (f : V → ℂ) {s : ℝ} (hs : 0 < s) :
    ∫ y, ‖f (s • y)‖ ^ 2 / ‖y‖ ^ 2 = s⁻¹ * ∫ y, ‖f y‖ ^ 2 / ‖y‖ ^ 2 := by
  have h := Measure.integral_comp_smul (volume : Measure V) (fun y => ‖f y‖ ^ 2 / ‖y‖ ^ 2) s
  rw [hV] at h
  have e : ∀ y : V, ‖f (s • y)‖ ^ 2 / ‖y‖ ^ 2 = s ^ 2 * (‖f (s • y)‖ ^ 2 / ‖s • y‖ ^ 2) := by
    intro y
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    rcases eq_or_ne ‖y‖ 0 with hy | hy
    · simp [hy]
    · field_simp
  simp_rw [e]
  rw [integral_const_mul, h, smul_eq_mul, abs_of_pos (by positivity)]
  field_simp

/-- Radial integrability in a 3-dimensional space: `‖x‖^s e^{-b‖x‖}` for `s > -3`. -/
lemma integrable_radial (hV : Module.finrank ℝ V = 3) (s : ℝ) (hs : -3 < s) (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : V => ‖x‖ ^ s * Real.exp (-(b * ‖x‖))) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hV]; norm_num)
  refine (integrable_fun_norm_addHaar volume (f := fun y : ℝ => y ^ s * Real.exp (-(b * y)))).2 ?_
  refine (integrableOn_rpow_mul_exp_neg_mul_rpow (s := s + 2) (p := 1) (by linarith) one_pos hb).congr_fun
    (fun y hy => ?_) measurableSet_Ioi
  have hy' : 0 < y := hy
  beta_reduce
  rw [hV, Real.rpow_one, Real.rpow_add hy', Real.rpow_two, smul_eq_mul]
  norm_num
  ring

/-- `‖y‖^s (1+‖y‖)^{-4}` is integrable in dimension 3 for `-3 < s ≤ 0`. -/
lemma integrable_rpow_decay (hV : Module.finrank ℝ V = 3) (s : ℝ) (hs : -3 < s) (hs0 : s ≤ 0) :
    Integrable (fun y : V => ‖y‖ ^ s * ((1 + ‖y‖) ^ 4)⁻¹) := by
  have h1 := (integrable_radial hV s hs 1 one_pos).const_mul (Real.exp 1)
  have h2 : Integrable (fun y : V => (1 + ‖y‖) ^ (-(4:ℝ))) :=
    integrable_one_add_norm (by rw [hV]; norm_num)
  refine (h1.add h2).mono' (Measurable.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun y => ?_)
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
  have e4 : (1 + ‖y‖) ^ (-(4:ℝ)) = ((1 + ‖y‖) ^ 4)⁻¹ := by
    rw [Real.rpow_neg (by positivity)]; norm_cast
  have hs' : 0 ≤ ‖y‖ ^ s := Real.rpow_nonneg hy0 s
  have hinv0 : 0 ≤ ((1 + ‖y‖) ^ 4)⁻¹ := by positivity
  simp only [Pi.add_apply, e4]
  rw [Real.norm_of_nonneg (by positivity)]
  rcases le_or_gt ‖y‖ 1 with h | h
  · have hinv : ((1 + ‖y‖) ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    have he : 1 ≤ Real.exp 1 * Real.exp (-(1 * ‖y‖)) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    calc ‖y‖ ^ s * ((1 + ‖y‖) ^ 4)⁻¹ ≤ ‖y‖ ^ s * 1 := mul_le_mul_of_nonneg_left hinv hs'
      _ ≤ ‖y‖ ^ s * (Real.exp 1 * Real.exp (-(1 * ‖y‖))) := mul_le_mul_of_nonneg_left he hs'
      _ ≤ _ := le_add_of_le_of_nonneg (le_of_eq (by ring)) hinv0
  · have hle : ‖y‖ ^ s ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h.le hs0
    refine le_add_of_nonneg_of_le (by positivity) ?_
    calc ‖y‖ ^ s * ((1 + ‖y‖) ^ 4)⁻¹ ≤ 1 * ((1 + ‖y‖) ^ 4)⁻¹ := mul_le_mul_of_nonneg_right hle hinv0
      _ = _ := one_mul _

/-- Schwartz decay with an explicit power of `1 + ‖x‖`. -/
lemma exists_decay {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (g : 𝓢(D, F)) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x, (1 + ‖x‖) ^ k * ‖g x‖ ≤ C := by
  have h : ∀ x, (1 + ‖x‖) ^ k * ‖g x‖ ≤
      2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g := fun x => by
    simpa [norm_iteratedFDeriv_zero] using
      one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl g x
  exact ⟨_, le_trans (by positivity) (h 0), h⟩

lemma inv_one_add_smul_le (y : V) {s : ℝ} (hs : 1 / 2 < s) :
    ((1 + ‖s • y‖) ^ 4)⁻¹ ≤ 16 * ((1 + ‖y‖) ^ 4)⁻¹ := by
  have hle : (1 + ‖y‖) / 2 ≤ 1 + ‖s • y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
    nlinarith [norm_nonneg y]
  have h4 : ((1 + ‖y‖) / 2) ^ 4 ≤ (1 + ‖s • y‖) ^ 4 := pow_le_pow_left₀ (by positivity) hle 4
  calc ((1 + ‖s • y‖) ^ 4)⁻¹ ≤ (((1 + ‖y‖) / 2) ^ 4)⁻¹ := inv_anti₀ (by positivity) h4
    _ = 16 * ((1 + ‖y‖) ^ 4)⁻¹ := by rw [div_pow, inv_div, div_eq_mul_inv]; norm_num

lemma sq_le_decay (a C r : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r) (h : (1 + r) ^ 2 * a ≤ C) :
    a ^ 2 ≤ C ^ 2 * ((1 + r) ^ 4)⁻¹ := by
  have h0 : 0 ≤ (1 + r) ^ 2 * a := by positivity
  have := pow_le_pow_left₀ h0 h 2
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  nlinarith [this]

lemma mul_le_decay (a b C D r : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (h : (1 + r) ^ 2 * a ≤ C) (h' : (1 + r) ^ 2 * b ≤ D) :
    a * b ≤ C * D * ((1 + r) ^ 4)⁻¹ := by
  have := mul_le_mul h h' (by positivity) (le_trans (by positivity) h)
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  nlinarith [this]

/-- H1a: Hardy's inequality in a 3-dimensional space, for a function with explicit decay. -/
theorem hardy3_of_decay (hV : Module.finrank ℝ V = 3) (f : V → ℂ) (hd : Differentiable ℝ f)
    (hDc : Continuous (fun y => fderiv ℝ f y)) (C1 C2 : ℝ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (h1 : ∀ x, (1 + ‖x‖) ^ 2 * ‖f x‖ ≤ C1) (h2 : ∀ x, (1 + ‖x‖) ^ 2 * ‖fderiv ℝ f x‖ ≤ C2) :
    Integrable (fun y : V => ‖f y‖ ^ 2 / ‖y‖ ^ 2) ∧
    ∫ y, ‖f y‖ ^ 2 / ‖y‖ ^ 2 ≤ 4 * ∫ y, ‖fderiv ℝ f y‖ ^ 2 := by
  have hfc : Continuous (fun y => f y) := hd.continuous
  -- integrability of the two sides
  have hI : Integrable (fun y : V => ‖f y‖ ^ 2 / ‖y‖ ^ 2) := by
    refine ((integrable_rpow_decay hV (-2) (by norm_num) (by norm_num)).const_mul (C1 ^ 2)).mono'
      (Measurable.aestronglyMeasurable (by fun_prop)) (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg (norm_nonneg y), Real.rpow_two]
    have := sq_le_decay _ _ _ (norm_nonneg _) (norm_nonneg y) (h1 y)
    calc ‖f y‖ ^ 2 / ‖y‖ ^ 2 = ‖f y‖ ^ 2 * (‖y‖ ^ 2)⁻¹ := div_eq_mul_inv _ _
      _ ≤ C1 ^ 2 * ((1 + ‖y‖) ^ 4)⁻¹ * (‖y‖ ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by ring
  have hJ : Integrable (fun y : V => ‖fderiv ℝ f y‖ ^ 2) := by
    refine ((integrable_rpow_decay hV 0 (by norm_num) le_rfl).const_mul (C2 ^ 2)).mono'
      (Measurable.aestronglyMeasurable (by fun_prop)) (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_zero, one_mul]
    exact sq_le_decay _ _ _ (norm_nonneg _) (norm_nonneg y) (h2 y)
  -- differentiate the dilation family at s = 1
  set I := ∫ y, ‖f y‖ ^ 2 / ‖y‖ ^ 2 with hIdef
  let F : ℝ → V → ℝ := fun s y => ‖f (s • y)‖ ^ 2 / ‖y‖ ^ 2
  let F' : ℝ → V → ℝ := fun s y => 2 * inner ℝ (f (s • y)) (fderiv ℝ f (s • y) y) / ‖y‖ ^ 2
  let bound : V → ℝ := fun y => 32 * C1 * C2 * (‖y‖ ^ (-1:ℝ) * ((1 + ‖y‖) ^ 4)⁻¹)
  have hbound : Integrable bound :=
    (integrable_rpow_decay hV (-1) (by norm_num) (by norm_num)).const_mul _
  have hF'meas : AEStronglyMeasurable (F' 1) volume := by
    refine Measurable.aestronglyMeasurable ?_
    have : Continuous (fun y : V => 2 * inner ℝ (f ((1:ℝ) • y)) (fderiv ℝ f ((1:ℝ) • y) y)) := by
      fun_prop
    exact this.measurable.div (by fun_prop)
  obtain ⟨hF'int, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := F) (F' := F') (x₀ := (1:ℝ)) (bound := bound) (Ioi_mem_nhds (by norm_num : (1/2:ℝ) < 1))
    (Filter.Eventually.of_forall fun s => Measurable.aestronglyMeasurable
      (((hfc.comp (continuous_const_smul s)).measurable.norm.pow_const 2).div
        (measurable_norm.pow_const 2)))
    (by simpa only [F, one_smul] using hI) hF'meas
    (Filter.Eventually.of_forall fun y s hs => by
      have hs' : (1/2:ℝ) < s := hs
      simp only [F', bound]
      rcases eq_or_ne y 0 with hy | hy
      · subst hy; simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, div_zero, norm_zero]
        have : (0:ℝ) ^ (-1:ℝ) = 0 := by rw [Real.zero_rpow (by norm_num)]
        rw [this]; simp
      have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy
      have hin : |inner ℝ (f (s • y)) (fderiv ℝ f (s • y) y)| ≤
          ‖f (s • y)‖ * (‖fderiv ℝ f (s • y)‖ * ‖y‖) :=
        (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left ((fderiv ℝ f (s • y)).le_opNorm y) (norm_nonneg _))
      have hfd := mul_le_decay _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
        (h1 (s • y)) (h2 (s • y))
      have h16 := inv_one_add_smul_le y hs'
      rw [Real.rpow_neg_one, Real.norm_eq_abs, abs_div, abs_mul, abs_two,
        abs_of_pos (by positivity : (0:ℝ) < ‖y‖ ^ 2), div_le_iff₀ (by positivity)]
      have hP : ‖f (s • y)‖ * ‖fderiv ℝ f (s • y)‖ ≤ C1 * C2 * (16 * ((1 + ‖y‖) ^ 4)⁻¹) :=
        hfd.trans (mul_le_mul_of_nonneg_left h16 (by positivity))
      have e : 32 * C1 * C2 * (‖y‖⁻¹ * ((1 + ‖y‖) ^ 4)⁻¹) * ‖y‖ ^ 2 =
          2 * (C1 * C2 * (16 * ((1 + ‖y‖) ^ 4)⁻¹)) * ‖y‖ := by
        field_simp; ring
      rw [e]
      have := mul_le_mul_of_nonneg_right hP hr.le
      nlinarith [hin, this])
    hbound
    (Filter.Eventually.of_forall fun y s _ => by
      have hc : HasDerivAt (fun s : ℝ => s • y) y s := by
        simpa using (hasDerivAt_id s).smul_const y
      have hf : HasDerivAt (fun s => f (s • y)) (fderiv ℝ f (s • y) y) s :=
        ((hd _).hasFDerivAt).comp_hasDerivAt s hc
      exact hf.norm_sq.div_const _)
  have hG : HasDerivAt (fun s : ℝ => s⁻¹ * I) (-I) 1 := by
    simpa using (hasDerivAt_inv one_ne_zero).mul_const I
  have heq : (fun s => ∫ y, F s y) =ᶠ[nhds 1] fun s => s⁻¹ * I := by
    filter_upwards [lt_mem_nhds one_pos] with s hs
    exact integral_scale hV f hs
  have hval : ∫ y, F' 1 y = -I := hderiv.unique (hG.congr_of_eventuallyEq heq)
  refine ⟨hI, ?_⟩
  have hpt : ∀ y, -F' 1 y ≤ ‖f y‖ ^ 2 / ‖y‖ ^ 2 / 2 + 2 * ‖fderiv ℝ f y‖ ^ 2 := by
    intro y
    simp only [F', one_smul]
    rcases eq_or_ne y 0 with hy | hy
    · subst hy; simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, div_zero, neg_zero, zero_div, zero_add]
      positivity
    have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hin : -inner ℝ (f y) (fderiv ℝ f y y) ≤ ‖f y‖ * (‖fderiv ℝ f y‖ * ‖y‖) :=
      (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left ((fderiv ℝ f y).le_opNorm y) (norm_nonneg _)))
    have e : ‖f y‖ ^ 2 / ‖y‖ ^ 2 / 2 + 2 * ‖fderiv ℝ f y‖ ^ 2 =
        (‖f y‖ ^ 2 / 2 + 2 * ‖fderiv ℝ f y‖ ^ 2 * ‖y‖ ^ 2) / ‖y‖ ^ 2 := by
      field_simp
    rw [e, ← neg_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [sq_nonneg (‖f y‖ - 2 * ‖fderiv ℝ f y‖ * ‖y‖)]
  have hle := integral_mono hF'int.neg ((hI.div_const 2).add (hJ.const_mul 2)) hpt
  simp only [Pi.neg_apply, Pi.add_apply] at hle
  rw [integral_neg, hval, neg_neg, integral_add (hI.div_const 2) (hJ.const_mul 2), integral_div,
    integral_const_mul] at hle
  linarith

/-- H1a for Schwartz functions. -/
theorem hardy3 (hV : Module.finrank ℝ V = 3) (f : 𝓢(V, ℂ)) :
    Integrable (fun y : V => ‖f y‖ ^ 2 / ‖y‖ ^ 2) ∧
    ∫ y, ‖f y‖ ^ 2 / ‖y‖ ^ 2 ≤ 4 * ∫ y, ‖fderiv ℝ f y‖ ^ 2 := by
  obtain ⟨C1, hC1, h1⟩ := exists_decay f 2
  obtain ⟨C2, hC2, h2⟩ := exists_decay (fderivCLM ℝ V ℂ f) 2
  simp only [fderivCLM_apply] at h2
  have hDc : Continuous (fun y => fderiv ℝ (⇑f) y) := by
    have := (fderivCLM ℝ V ℂ f).continuous
    simpa only [funext (fderivCLM_apply (𝕜 := ℝ) f)] using this
  exact hardy3_of_decay hV f f.differentiable hDc C1 C2 hC1 hC2 h1 h2

/-- Hardy along an isometric affine 3-dimensional slice of a Schwartz function. -/
theorem hardy_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hV : Module.finrank ℝ V = 3) (φ : 𝓢(E, ℂ)) (L : V →L[ℝ] E) (hL : ∀ y, ‖L y‖ = ‖y‖) (c : E) :
    Integrable (fun y : V => ‖φ (c + L y)‖ ^ 2 / ‖y‖ ^ 2) ∧
    Integrable (fun y : V => ‖fderiv ℝ (⇑φ) (c + L y)‖ ^ 2) ∧
    ∫ y, ‖φ (c + L y)‖ ^ 2 / ‖y‖ ^ 2 ≤ 4 * ∫ y, ‖fderiv ℝ (⇑φ) (c + L y)‖ ^ 2 := by
  obtain ⟨C1, hC1, h1⟩ := exists_decay φ 2
  obtain ⟨C2, hC2, h2⟩ := exists_decay (fderivCLM ℝ E ℂ φ) 2
  simp only [fderivCLM_apply] at h2
  have hDφ : Continuous (fun x => fderiv ℝ (⇑φ) x) := by
    have := (fderivCLM ℝ E ℂ φ).continuous
    simpa only [funext (fderivCLM_apply (𝕜 := ℝ) φ)] using this
  have hgd : ∀ y, HasFDerivAt (fun y => φ (c + L y)) ((fderiv ℝ (⇑φ) (c + L y)).comp L) y :=
    fun y => (φ.differentiableAt.hasFDerivAt).comp y (L.hasFDerivAt.const_add c)
  have hfd : ∀ y, fderiv ℝ (fun y => φ (c + L y)) y = (fderiv ℝ (⇑φ) (c + L y)).comp L :=
    fun y => (hgd y).fderiv
  have hLn : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (fun y => by rw [hL, one_mul])
  have hcomp : ∀ y, ‖(fderiv ℝ (⇑φ) (c + L y)).comp L‖ ≤ ‖fderiv ℝ (⇑φ) (c + L y)‖ := fun y =>
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa using mul_le_mul_of_nonneg_left hLn (norm_nonneg (fderiv ℝ (⇑φ) (c + L y))))
  have hgrow : ∀ y : V, (1 + ‖y‖) ^ 2 ≤ (1 + ‖c‖) ^ 2 * (1 + ‖c + L y‖) ^ 2 := by
    intro y
    have h3 : ‖y‖ ≤ ‖c + L y‖ + ‖c‖ := by
      rw [← hL y]
      calc ‖L y‖ = ‖(c + L y) - c‖ := by simp
        _ ≤ _ := norm_sub_le _ _
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity)
      (by nlinarith [mul_nonneg (norm_nonneg c) (norm_nonneg (c + L y))]) 2
  have h1' : ∀ y : V, (1 + ‖y‖) ^ 2 * ‖φ (c + L y)‖ ≤ (1 + ‖c‖) ^ 2 * C1 := fun y => calc
      (1 + ‖y‖) ^ 2 * ‖φ (c + L y)‖ ≤ (1 + ‖c‖) ^ 2 * (1 + ‖c + L y‖) ^ 2 * ‖φ (c + L y)‖ :=
        mul_le_mul_of_nonneg_right (hgrow y) (norm_nonneg _)
      _ = (1 + ‖c‖) ^ 2 * ((1 + ‖c + L y‖) ^ 2 * ‖φ (c + L y)‖) := by ring
      _ ≤ (1 + ‖c‖) ^ 2 * C1 := mul_le_mul_of_nonneg_left (h1 _) (by positivity)
  have hD' : ∀ y : V, (1 + ‖y‖) ^ 2 * ‖fderiv ℝ (⇑φ) (c + L y)‖ ≤ (1 + ‖c‖) ^ 2 * C2 := fun y => calc
      (1 + ‖y‖) ^ 2 * ‖fderiv ℝ (⇑φ) (c + L y)‖ ≤
          (1 + ‖c‖) ^ 2 * (1 + ‖c + L y‖) ^ 2 * ‖fderiv ℝ (⇑φ) (c + L y)‖ :=
        mul_le_mul_of_nonneg_right (hgrow y) (norm_nonneg _)
      _ = (1 + ‖c‖) ^ 2 * ((1 + ‖c + L y‖) ^ 2 * ‖fderiv ℝ (⇑φ) (c + L y)‖) := by ring
      _ ≤ (1 + ‖c‖) ^ 2 * C2 := mul_le_mul_of_nonneg_left (h2 _) (by positivity)
  have h2' : ∀ y : V, (1 + ‖y‖) ^ 2 * ‖fderiv ℝ (fun y => φ (c + L y)) y‖ ≤ (1 + ‖c‖) ^ 2 * C2 :=
    fun y => by
      rw [hfd]
      exact le_trans (mul_le_mul_of_nonneg_left (hcomp y) (by positivity)) (hD' y)
  have hgc : Continuous (fun y => fderiv ℝ (fun y => φ (c + L y)) y) := by
    simp_rw [hfd]
    exact (hDφ.comp (continuous_const.add L.continuous)).clm_comp continuous_const
  obtain ⟨hI, hle⟩ := hardy3_of_decay hV (fun y => φ (c + L y)) (fun y => (hgd y).differentiableAt)
    hgc _ _ (by positivity) (by positivity) h1' h2'
  have hJ : Integrable (fun y : V => ‖fderiv ℝ (⇑φ) (c + L y)‖ ^ 2) := by
    have hc : Continuous (fun y : V => ‖fderiv ℝ (⇑φ) (c + L y)‖ ^ 2) :=
      ((hDφ.comp (continuous_const.add L.continuous)).norm).pow 2
    refine ((integrable_rpow_decay hV 0 (by norm_num) le_rfl).const_mul
      (((1 + ‖c‖) ^ 2 * C2) ^ 2)).mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_zero, one_mul]
    exact sq_le_decay _ _ _ (norm_nonneg _) (norm_nonneg y) (hD' y)
  refine ⟨hI, hJ, hle.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))⟩
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by positivity) hJ
    (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [hfd]
  exact pow_le_pow_left₀ (norm_nonneg _) (hcomp y) 2

end HVZHardy

/-! ## H1b: lift to the electron coordinate of `ℝ^{3N}` -/

namespace HVZHardy

variable {N : ℕ} (j : Fin N)

/-- The coordinates not belonging to electron `j`. -/
abbrev Kj := {p : Fin N × Fin 3 // p.1 ≠ j}

/-- Split the coordinates into those of electron `j` and the rest. -/
def splitEquiv : Fin N × Fin 3 ≃ Kj j ⊕ Fin 3 where
  toFun p := if h : p.1 = j then Sum.inr p.2 else Sum.inl ⟨p, h⟩
  invFun := Sum.elim Subtype.val (fun a => (j, a))
  left_inv p := by
    by_cases h : p.1 = j
    · simp only [dif_pos h, Sum.elim_inr]; exact Prod.ext h.symm rfl
    · simp only [dif_neg h, Sum.elim_inl]
  right_inv s := by
    rcases s with ⟨p, hp⟩ | a
    · exact dif_neg hp
    · exact dif_pos rfl

/-- Insert the electron-`j` coordinates `y` into the rest `w`. -/
noncomputable def ins (w : Kj j → ℝ) (y : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin N × Fin 3) :=
  WithLp.toLp 2 (fun p => if h : p.1 = j then y p.2 else w ⟨p, h⟩)

noncomputable def insE : (Kj j → ℝ) × EuclideanSpace ℝ (Fin 3) ≃ᵐ EuclideanSpace ℝ (Fin N × Fin 3) :=
  ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Kj j ⊕ Fin 3 => ℝ)).symm).trans
    ((MeasurableEquiv.arrowCongr' (splitEquiv j).symm (MeasurableEquiv.refl ℝ)).trans
      (MeasurableEquiv.toLp 2 (Fin N × Fin 3 → ℝ)))

lemma insE_apply (w : Kj j → ℝ) (y : EuclideanSpace ℝ (Fin 3)) : insE j (w, y) = ins j w y := by
  ext p
  simp [insE, ins, MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr, splitEquiv,
    MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi]
  split_ifs <;> rfl

lemma insE_mp : MeasurePreserving (insE j) := by
  have h1 : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Kj j → ℝ))
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm) (volume.prod volume) (volume.prod volume) :=
    (MeasurePreserving.id volume).prod (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3))
  have h2 : MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi (fun _ : Kj j ⊕ Fin 3 => ℝ)).symm
      (volume.prod volume) volume :=
    measurePreserving_sumPiEquivProdPi_symm (fun _ => volume)
  have h3 : MeasurePreserving (MeasurableEquiv.arrowCongr' (splitEquiv j).symm (MeasurableEquiv.refl ℝ)) :=
    volume_preserving_arrowCongr' _ _ (MeasurePreserving.id volume)
  have h4 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin N × Fin 3 → ℝ)) :=
    MeasurePreserving.symm _ (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin N × Fin 3))
  exact h4.comp (h3.comp (h2.comp h1))

lemma ins_split (w : Kj j → ℝ) (y : EuclideanSpace ℝ (Fin 3)) : ins j w y = ins j w 0 + ins j 0 y := by
  ext p
  simp only [ins, PiLp.add_apply]
  split_ifs <;> simp

/-- The linear isometric embedding of the electron-`j` coordinates. -/
noncomputable def insL : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin N × Fin 3) :=
  LinearMap.toContinuousLinearMap
    { toFun := ins j 0
      map_add' := fun a b => by ext p; simp only [ins, PiLp.add_apply]; split_ifs <;> simp
      map_smul' := fun r a => by ext p; simp only [ins, PiLp.smul_apply]; split_ifs <;> simp }

lemma insL_apply (y : EuclideanSpace ℝ (Fin 3)) : insL j y = ins j 0 y := rfl

lemma norm_insL (y : EuclideanSpace ℝ (Fin 3)) : ‖insL j y‖ = ‖y‖ := by
  rw [insL_apply, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fintype.sum_prod_type]
  congr 1
  simp [ins]

/-- H1b: Hardy's inequality in the electron-`j` coordinate for a Schwartz function on `ℝ^{3N}`. -/
theorem hardy_electron (φ : 𝓢(EuclideanSpace ℝ (Fin N × Fin 3), ℂ)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin N × Fin 3) =>
      ‖φ x‖ ^ 2 / ‖(WithLp.toLp 2 (fun a => x (j, a)) : EuclideanSpace ℝ (Fin 3))‖ ^ 2) ∧
    ∫ x : EuclideanSpace ℝ (Fin N × Fin 3),
      ‖φ x‖ ^ 2 / ‖(WithLp.toLp 2 (fun a => x (j, a)) : EuclideanSpace ℝ (Fin 3))‖ ^ 2 ≤
      4 * ∫ x, ‖fderiv ℝ (⇑φ) x‖ ^ 2 := by
  have hV : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  set F : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ := fun x =>
    ‖φ x‖ ^ 2 / ‖(WithLp.toLp 2 (fun a => x (j, a)) : EuclideanSpace ℝ (Fin 3))‖ ^ 2 with hF
  set D : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ := fun x => ‖fderiv ℝ (⇑φ) x‖ ^ 2 with hDdef
  have hmp := insE_mp j
  have hel : ∀ w y, (WithLp.toLp 2 (fun a => (ins j w y) (j, a)) : EuclideanSpace ℝ (Fin 3)) = y := by
    intro w y; ext a; simp [ins]
  have hFslice : ∀ w y, F (insE j (w, y)) = ‖φ (ins j w 0 + insL j y)‖ ^ 2 / ‖y‖ ^ 2 := by
    intro w y; simp only [hF, insE_apply, hel, insL_apply, ← ins_split]
  have hDslice : ∀ w y, D (insE j (w, y)) = ‖fderiv ℝ (⇑φ) (ins j w 0 + insL j y)‖ ^ 2 := by
    intro w y; simp only [hDdef, insE_apply, insL_apply, ← ins_split]
  -- integrability of D on ℝ^{3N}
  obtain ⟨C2, hC2, h2⟩ := exists_decay (fderivCLM ℝ _ ℂ φ) 0
  simp only [fderivCLM_apply, pow_zero, one_mul] at h2
  have hDφ : Continuous (fun x => fderiv ℝ (⇑φ) x) := by
    have := (fderivCLM ℝ (EuclideanSpace ℝ (Fin N × Fin 3)) ℂ φ).continuous
    simpa only [funext (fderivCLM_apply (𝕜 := ℝ) φ)] using this
  have hDint : Integrable D := by
    have hi := ((fderivCLM ℝ (EuclideanSpace ℝ (Fin N × Fin 3)) ℂ φ).integrable (μ := volume)).norm.const_mul C2
    refine hi.mono' (hDφ.norm.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    show ‖fderiv ℝ (⇑φ) x‖ ^ 2 ≤ _
    rw [sq, fderivCLM_apply]
    exact mul_le_mul_of_nonneg_right (h2 x) (norm_nonneg _)
  have hFm : Measurable F := by
    have : Measurable (fun x : EuclideanSpace ℝ (Fin N × Fin 3) => ‖φ x‖ ^ 2) :=
      (φ.continuous.norm.pow 2).measurable
    refine this.div ((Continuous.measurable ?_).pow_const 2)
    fun_prop
  have hDP : Integrable (D ∘ insE j) := (hmp.integrable_comp_emb (insE j).measurableEmbedding).2 hDint
  have hGm : AEStronglyMeasurable (F ∘ insE j) (volume.prod volume) :=
    (hFm.comp (insE j).measurable).aestronglyMeasurable
  have hsl := fun w : Kj j → ℝ => hardy_slice hV φ (insL j) (norm_insL j) (ins j w 0)
  have hGP : Integrable (F ∘ insE j) (volume.prod volume) := by
    refine (integrable_prod_iff hGm).2 ⟨Filter.Eventually.of_forall fun w => ?_, ?_⟩
    · simpa only [Function.comp, hFslice] using (hsl w).1
    · refine (hDP.integral_prod_left.const_mul 4).mono' hGm.norm.integral_prod_right'
        (Filter.Eventually.of_forall fun w => ?_)
      simp only [Function.comp, hFslice, hDslice]
      rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
      simp only [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ ‖φ (ins j w 0 + insL j _)‖ ^ 2 / ‖_‖ ^ 2)]
      exact (hsl w).2.2
  refine ⟨(hmp.integrable_comp_emb (insE j).measurableEmbedding).1 hGP, ?_⟩
  rw [← hmp.integral_comp' (g := F), ← hmp.integral_comp' (g := D)]
  change ∫ q, (F ∘ insE j) q ∂(volume.prod volume) ≤ 4 * ∫ q, (D ∘ insE j) q ∂(volume.prod volume)
  rw [integral_prod _ hGP, integral_prod _ hDP, ← integral_const_mul]
  refine integral_mono hGP.integral_prod_left (hDP.integral_prod_left.const_mul 4) fun w => ?_
  simp only [Function.comp, hFslice, hDslice]
  exact (hsl w).2.2


/-- Hardy in the relative coordinate `x_j - x_k` of two electrons (translate the `x_j`-slice). -/
theorem hardy_pair (k : Fin N) (hkj : k ≠ j) (φ : 𝓢(EuclideanSpace ℝ (Fin N × Fin 3), ℂ)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin N × Fin 3) =>
      ‖φ x‖ ^ 2 / ‖(WithLp.toLp 2 (fun a => x (j, a)) : EuclideanSpace ℝ (Fin 3)) -
        WithLp.toLp 2 (fun a => x (k, a))‖ ^ 2) ∧
    ∫ x : EuclideanSpace ℝ (Fin N × Fin 3),
      ‖φ x‖ ^ 2 / ‖(WithLp.toLp 2 (fun a => x (j, a)) : EuclideanSpace ℝ (Fin 3)) -
        WithLp.toLp 2 (fun a => x (k, a))‖ ^ 2 ≤
      4 * ∫ x, ‖fderiv ℝ (⇑φ) x‖ ^ 2 := by
  have hV : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  let F : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ := fun x =>
    ‖φ x‖ ^ 2 / ‖(WithLp.toLp 2 (fun a => x (j, a)) : EuclideanSpace ℝ (Fin 3)) -
        WithLp.toLp 2 (fun a => x (k, a))‖ ^ 2
  let D : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ := fun x => ‖fderiv ℝ (⇑φ) x‖ ^ 2
  have hmp := insE_mp j
  let av : (Kj j → ℝ) → EuclideanSpace ℝ (Fin 3) := fun w =>
    WithLp.toLp 2 (fun b => w ⟨(k, b), hkj⟩)
  have hel : ∀ w y, (WithLp.toLp 2 (fun a => (ins j w y) (j, a)) : EuclideanSpace ℝ (Fin 3)) = y := by
    intro w y; ext a; simp [ins]
  have helk : ∀ w y, (WithLp.toLp 2 (fun a => (ins j w y) (k, a)) : EuclideanSpace ℝ (Fin 3)) = av w := by
    intro w y; ext a; simp [ins, av, hkj]
  have hFslice : ∀ w y, F (insE j (w, y)) = ‖φ (ins j w 0 + insL j y)‖ ^ 2 / ‖y - av w‖ ^ 2 := by
    intro w y; simp only [F, insE_apply, hel, helk, insL_apply, ← ins_split]
  have hDslice : ∀ w y, D (insE j (w, y)) = ‖fderiv ℝ (⇑φ) (ins j w 0 + insL j y)‖ ^ 2 := by
    intro w y; simp only [D, insE_apply, insL_apply, ← ins_split]
  have hS : ∀ w, Integrable (fun y => F (insE j (w, y))) ∧
      ∫ y, F (insE j (w, y)) ≤ 4 * ∫ y, D (insE j (w, y)) := by
    intro w
    have hsl := hardy_slice hV φ (insL j) (norm_insL j) (ins j w 0 + insL j (av w))
    have hc : ∀ y, ins j w 0 + insL j (av w) + insL j (y - av w) = ins j w 0 + insL j y := by
      intro y; rw [map_sub]; abel
    have e1 : (fun y => F (insE j (w, y))) = fun y =>
        (fun y' => ‖φ (ins j w 0 + insL j (av w) + insL j y')‖ ^ 2 / ‖y'‖ ^ 2) (y - av w) := by
      funext y; rw [hFslice]; exact congrArg (fun p => ‖φ p‖ ^ 2 / ‖y - av w‖ ^ 2) (hc y).symm
    have e2 : (fun y => D (insE j (w, y))) = fun y =>
        (fun y' => ‖fderiv ℝ (⇑φ) (ins j w 0 + insL j (av w) + insL j y')‖ ^ 2) (y - av w) := by
      funext y; rw [hDslice]; exact congrArg (fun p => ‖fderiv ℝ (⇑φ) p‖ ^ 2) (hc y).symm
    refine ⟨e1 ▸ hsl.1.comp_sub_right (av w), ?_⟩
    have i1 := integral_sub_right_eq_self (μ := volume)
      (fun y' => ‖φ (ins j w 0 + insL j (av w) + insL j y')‖ ^ 2 / ‖y'‖ ^ 2) (av w)
    have i2 := integral_sub_right_eq_self (μ := volume)
      (fun y' => ‖fderiv ℝ (⇑φ) (ins j w 0 + insL j (av w) + insL j y')‖ ^ 2) (av w)
    rw [e1, e2]
    calc _ = _ := i1
      _ ≤ _ := hsl.2.2
      _ = _ := (congrArg (fun t => 4 * t) i2).symm
  have hF0 : ∀ x, 0 ≤ F x := fun x => by positivity
  -- integrability of D on ℝ^{3N}
  obtain ⟨C2, hC2, h2⟩ := exists_decay (fderivCLM ℝ _ ℂ φ) 0
  simp only [fderivCLM_apply, pow_zero, one_mul] at h2
  have hDφ : Continuous (fun x => fderiv ℝ (⇑φ) x) := by
    have := (fderivCLM ℝ (EuclideanSpace ℝ (Fin N × Fin 3)) ℂ φ).continuous
    simpa only [funext (fderivCLM_apply (𝕜 := ℝ) φ)] using this
  have hDint : Integrable D := by
    have hi := ((fderivCLM ℝ (EuclideanSpace ℝ (Fin N × Fin 3)) ℂ φ).integrable (μ := volume)).norm.const_mul C2
    refine hi.mono' (hDφ.norm.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    show ‖fderiv ℝ (⇑φ) x‖ ^ 2 ≤ _
    rw [sq, fderivCLM_apply]
    exact mul_le_mul_of_nonneg_right (h2 x) (norm_nonneg _)
  have hFm : Measurable F := by
    have : Measurable (fun x : EuclideanSpace ℝ (Fin N × Fin 3) => ‖φ x‖ ^ 2) :=
      (φ.continuous.norm.pow 2).measurable
    refine this.div ((Continuous.measurable ?_).pow_const 2)
    fun_prop
  have hDP : Integrable (D ∘ insE j) := (hmp.integrable_comp_emb (insE j).measurableEmbedding).2 hDint
  have hGm : AEStronglyMeasurable (F ∘ insE j) (volume.prod volume) :=
    (hFm.comp (insE j).measurable).aestronglyMeasurable
  have hGP : Integrable (F ∘ insE j) (volume.prod volume) := by
    refine (integrable_prod_iff hGm).2 ⟨Filter.Eventually.of_forall fun w => (hS w).1, ?_⟩
    refine (hDP.integral_prod_left.const_mul 4).mono' hGm.norm.integral_prod_right'
      (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
    simp only [Function.comp_apply, Real.norm_of_nonneg (hF0 _)]
    exact (hS w).2
  refine ⟨(hmp.integrable_comp_emb (insE j).measurableEmbedding).1 hGP, ?_⟩
  rw [← hmp.integral_comp' (g := F), ← hmp.integral_comp' (g := D)]
  change ∫ q, (F ∘ insE j) q ∂(volume.prod volume) ≤ 4 * ∫ q, (D ∘ insE j) q ∂(volume.prod volume)
  rw [integral_prod _ hGP, integral_prod _ hDP, ← integral_const_mul]
  exact integral_mono hGP.integral_prod_left (hDP.integral_prod_left.const_mul 4) fun w => (hS w).2

end HVZHardy


/-! H2-sum and H3 density for the Hardy step of 7ab9d8bf (HVZ C1). -/


open MeasureTheory SchwartzMap FourierTransform LineDeriv
open scoped ContDiff InnerProductSpace ComplexConjugate Topology
open Filter

namespace HVZDens

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- copied from 7ab9d8bf_hardy.lean -/
theorem integral_norm_sq_lineDeriv (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) (m : EuclideanSpace ℝ ι) :
    ∫ x, ‖fderiv ℝ f x m‖ ^ 2 =
      ∫ ξ, (2 * Real.pi * inner ℝ ξ m) ^ 2 * ‖𝓕 f ξ‖ ^ 2 := by
  have h1 := integral_norm_sq_fourier (∂_{m} f)
  rw [fourier_lineDerivOp_eq] at h1
  have hg : (inner ℝ · m : EuclideanSpace ℝ ι → ℝ).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  rw [← integral_congr_ae (Filter.Eventually.of_forall fun x => by
      rw [← lineDerivOp_apply_eq_fderiv] : ∀ᵐ x ∂volume, ‖(∂_{m} f) x‖ ^ 2 = ‖fderiv ℝ f x m‖ ^ 2),
    ← h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_apply, smulLeftCLM_apply_apply hg, norm_smul, Complex.norm_mul,
    Complex.norm_I, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

lemma sq_fourier_lineDeriv (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) (m ξ : EuclideanSpace ℝ ι) :
    ‖𝓕 (∂_{m} f) ξ‖ ^ 2 = (2 * Real.pi * inner ℝ ξ m) ^ 2 * ‖𝓕 f ξ‖ ^ 2 := by
  have hg : (inner ℝ · m : EuclideanSpace ℝ ι → ℝ).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  rw [fourier_lineDerivOp_eq]
  simp only [smul_apply, smulLeftCLM_apply_apply hg, norm_smul, Complex.norm_mul,
    Complex.norm_I, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

lemma opNorm_sq_le_sum (L : EuclideanSpace ℝ ι →L[ℝ] ℂ) :
    ‖L‖ ^ 2 ≤ ∑ i, ‖L (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
  set S := ∑ i, ‖L (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 with hS
  have hS0 : 0 ≤ S := by positivity
  have hb : ‖L‖ ≤ Real.sqrt S := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
    have hv : L v = ∑ i, v i • L (EuclideanSpace.single i (1 : ℝ)) := by
      conv_lhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr v]
      simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
    rw [hv]
    calc ‖∑ i, v i • L (EuclideanSpace.single i (1 : ℝ))‖
        ≤ ∑ i, ‖v i‖ * ‖L (EuclideanSpace.single i (1 : ℝ))‖ := by
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          simp only [norm_smul]
      _ ≤ Real.sqrt (∑ i, ‖v i‖ ^ 2) * Real.sqrt S := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = Real.sqrt S * ‖v‖ := by rw [EuclideanSpace.norm_eq, mul_comm]
  calc ‖L‖ ^ 2 ≤ Real.sqrt S ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = S := Real.sq_sqrt hS0


end HVZDens

namespace HVZHS
open TeschlQM.Atomic

theorem hardyS_of (N : ℕ) (g : 𝓢(EuclideanSpace ℝ (Fin N × Fin 3), ℂ)) (j : Fin N) :
    Integrable (fun x => ‖g x‖ ^ 2 / ‖electron x j‖ ^ 2) ∧
      ∫ x, ‖g x‖ ^ 2 / ‖electron x j‖ ^ 2 ≤
        4 * ∑ p : Fin N × Fin 3, ∫ x, ‖fderiv ℝ (⇑g) x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := HVZHardy.hardy_electron j g
  have hI : Integrable (fun x => ‖fderiv ℝ (⇑g) x‖ ^ 2) := by
    have := (memLp_two_iff_integrable_sq_norm
      (SchwartzMap.fderivCLM ℝ _ _ g).continuous.aestronglyMeasurable).1 ((SchwartzMap.fderivCLM ℝ _ _ g).memLp 2)
    simpa [SchwartzMap.fderivCLM_apply] using this
  have hc : Continuous (fun x => fderiv ℝ (⇑g) x) := by
    exact (SchwartzMap.fderivCLM ℝ _ _ g).continuous
  have hIp : ∀ v : EuclideanSpace ℝ (Fin N × Fin 3),
      Integrable (fun x => ‖fderiv ℝ (⇑g) x v‖ ^ 2) := fun v =>
    (hI.mul_const (‖v‖ ^ 2)).mono' (((hc.clm_apply continuous_const).norm.pow 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) ((fderiv ℝ (⇑g) x).le_opNorm v) 2)
  refine ⟨h1, h2.trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [← integral_finsetSum _ fun p _ => hIp _]
  exact integral_mono hI (integrable_finsetSum _ fun p _ => hIp _)
    (fun x => HVZDens.opNorm_sq_le_sum _)

theorem hardyP_of (N : ℕ) (g : 𝓢(EuclideanSpace ℝ (Fin N × Fin 3), ℂ)) (j k : Fin N) (hjk : j ≠ k) :
    Integrable (fun x => ‖g x‖ ^ 2 / ‖electron x j - electron x k‖ ^ 2) :=
  (HVZHardy.hardy_pair j k hjk.symm g).1

end HVZHS

end SecHS

section XFinal
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff SchwartzMap

namespace HVZVD
open TeschlQM.Atomic

lemma pot_sq_le (γne γee : ℝ) (N : ℕ) (x : EuclideanSpace ℝ (Fin N × Fin 3)) :
    atomicPotential γne γee N x ^ 2 ≤
      2 * N * ∑ j, (γne / ‖electron x j‖) ^ 2 +
        2 * N * N * ∑ j, ∑ k ∈ Finset.univ.filter (fun k : Fin N => j < k),
          (γee / ‖electron x j - electron x k‖) ^ 2 := by
  unfold atomicPotential
  set a := ∑ j : Fin N, γne / ‖electron x j‖
  set c : Fin N → ℝ := fun j => ∑ k ∈ Finset.univ.filter (fun k : Fin N => j < k),
      γee / ‖electron x j - electron x k‖ with hc
  have h1 : (-a + ∑ j, c j) ^ 2 ≤ 2 * a ^ 2 + 2 * (∑ j, c j) ^ 2 := by
    nlinarith [sq_nonneg (a + ∑ j, c j)]
  have h2 : a ^ 2 ≤ N * ∑ j : Fin N, (γne / ‖electron x j‖) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin N)))
      (f := fun j => γne / ‖electron x j‖)
    simpa [Finset.card_univ, Fintype.card_fin] using this
  have h3 : (∑ j, c j) ^ 2 ≤ N * ∑ j : Fin N, c j ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin N))) (f := c)
    simpa [Finset.card_univ, Fintype.card_fin] using this
  have h4 : ∀ j, c j ^ 2 ≤ N * ∑ k ∈ Finset.univ.filter (fun k : Fin N => j < k),
      (γee / ‖electron x j - electron x k‖) ^ 2 := by
    intro j
    refine (sq_sum_le_card_mul_sum_sq (s := Finset.univ.filter (fun k : Fin N => j < k))
      (f := fun k => γee / ‖electron x j - electron x k‖)).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun k _ => sq_nonneg _)
    have := Finset.card_filter_le (Finset.univ : Finset (Fin N)) (fun k : Fin N => j < k)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have h5 : ∑ j : Fin N, c j ^ 2 ≤ N * ∑ j, ∑ k ∈ Finset.univ.filter (fun k : Fin N => j < k),
      (γee / ‖electron x j - electron x k‖) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun j _ => h4 j
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h6 := mul_le_mul_of_nonneg_left h5 hN
  nlinarith [h1, h2, h3, h6]

theorem vdom (γne γee : ℝ) (M : ℕ) (g : 𝓢(EuclideanSpace ℝ (Fin M × Fin 3), ℂ)) :
    g.toLp 2 (volume : Measure (EuclideanSpace ℝ (Fin M × Fin 3))) ∈
      (mulOp volume (fun x => ((atomicPotential γne γee M x : ℝ) : ℂ))).domain := by
  show MemLp (fun x => ((atomicPotential γne γee M x : ℝ) : ℂ) *
    ((g.toLp 2 (volume : Measure (EuclideanSpace ℝ (Fin M × Fin 3))) :
      EuclideanSpace ℝ (Fin M × Fin 3) → ℂ) x)) 2 volume
  have hae := g.coeFn_toLp 2 (volume : Measure (EuclideanSpace ℝ (Fin M × Fin 3)))
  have hVm : Measurable (fun x => ((atomicPotential γne γee M x : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (HVZFib.pot_meas γne γee M)
  have hmeas : AEStronglyMeasurable (fun x => ((atomicPotential γne γee M x : ℝ) : ℂ) * g x) volume :=
    hVm.aestronglyMeasurable.mul g.continuous.aestronglyMeasurable
  refine MemLp.ae_eq (f := fun x => ((atomicPotential γne γee M x : ℝ) : ℂ) * g x) ?_ ?_
  · filter_upwards [hae] with x hx
    rw [hx]
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hS := fun j => (HVZHS.hardyS_of M g j).1
  have hP := fun j k (h : j < k) => HVZHS.hardyP_of M g j k h.ne
  refine Integrable.mono' (g := fun x =>
      2 * M * ∑ j, γne ^ 2 * (‖g x‖ ^ 2 / ‖electron x j‖ ^ 2) +
        2 * M * M * ∑ j, ∑ k ∈ Finset.univ.filter (fun k : Fin M => j < k),
          γee ^ 2 * (‖g x‖ ^ 2 / ‖electron x j - electron x k‖ ^ 2)) ?_ ?_ ?_
  · exact ((integrable_finsetSum _ fun j _ => (hS j).const_mul _).const_mul _).add
      ((integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k hk =>
        (hP j k (Finset.mem_filter.1 hk).2).const_mul _).const_mul _)
  · exact (hmeas.norm.pow 2)
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs]
    have hF : 0 ≤ ‖g x‖ ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right (pot_sq_le γne γee M x) hF
    refine this.trans (le_of_eq ?_)
    have h1 : (∑ j, (γne / ‖electron x j‖) ^ 2) * ‖g x‖ ^ 2 =
        ∑ j, γne ^ 2 * (‖g x‖ ^ 2 / ‖electron x j‖ ^ 2) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [div_pow]; ring
    have h2 : (∑ j, ∑ k ∈ Finset.univ.filter (fun k : Fin M => j < k),
          (γee / ‖electron x j - electron x k‖) ^ 2) * ‖g x‖ ^ 2 =
        ∑ j, ∑ k ∈ Finset.univ.filter (fun k : Fin M => j < k),
          γee ^ 2 * (‖g x‖ ^ 2 / ‖electron x j - electron x k‖ ^ 2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by rw [div_pow]; ring
    linear_combination (2 * (M : ℝ)) * h1 + (2 * (M : ℝ) * M) * h2

end HVZVD

namespace HVZXF
open TeschlQM.Atomic TeschlQM.Shared

theorem smooth_bound (γne γee : ℝ) (hne : 0 < γne) (hee : 0 < γee)
    (N : ℕ) (hN : 1 ≤ N) (lam : ℝ)
    (hlam : TeschlQM.Shared.IsBoundedBelowBy (atomicHamiltonian γne γee (N - 1)) lam) (δ : ℝ) (hδ : 0 < δ) :
    ∃ W : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ, Measurable W ∧ (∃ C : ℝ, ∀ x, |W x| ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x, R ≤ ‖x‖ → |W x| ≤ ε) ∧
      ∀ f : EuclideanSpace ℝ (Fin N × Fin 3) → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
        (lam * ∫ x, ‖f x‖ ^ 2)
          - δ * (∑ p : Fin N × Fin 3, ∫ x, ‖fderiv ℝ f x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2)
          - (∫ x, W x * ‖f x‖ ^ 2) ≤
        (∑ p : Fin N × Fin 3, ∫ x, ‖fderiv ℝ f x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2)
          + ∫ x, atomicPotential γne γee N x * ‖f x‖ ^ 2 := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hlam
  exact HVZX.ccbound_of γne γee hne hee M lam δ hδ hlam (fun g => HVZVD.vdom γne γee M g)
    (fun g j => HVZHS.hardyS_of _ g j) (fun g j k h => HVZHS.hardyP_of _ g j k h)

end HVZXF
end XFinal


section SecY1all

/-! Y1 for 7ab9d8bf D3c: the C_c^∞ form inequality extends to Schwartz functions by a smooth cutoff
`χ(x/R) • g` and dominated convergence. Generic (no atomic content). -/

section SecY1

set_option autoImplicit false

open MeasureTheory SchwartzMap LineDeriv Filter Metric
open scoped ContDiff Topology

namespace HVZY1

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sq_int (g : 𝓢(EuclideanSpace ℝ ι, ℂ)) : Integrable (fun x => ‖g x‖ ^ 2) :=
  (memLp_two_iff_integrable_sq_norm g.continuous.aestronglyMeasurable).1 (g.memLp 2)

lemma dsq_int (g : 𝓢(EuclideanSpace ℝ ι, ℂ)) (m : EuclideanSpace ℝ ι) :
    Integrable (fun x => ‖fderiv ℝ g x m‖ ^ 2) := by
  have := sq_int (∂_{m} g)
  simpa only [lineDerivOp_apply_eq_fderiv] using this

/-- The fixed cutoff: `1` on the unit ball, supported in the ball of radius 2. -/
noncomputable def bump : ContDiffBump (0 : EuclideanSpace ℝ ι) := ⟨1, 2, one_pos, one_lt_two⟩

lemma bump_rIn : (bump : ContDiffBump (0 : EuclideanSpace ℝ ι)).rIn = 1 := rfl

lemma bump_deriv_bound :
    ∃ M, ∀ y, ‖fderiv ℝ (bump : ContDiffBump (0 : EuclideanSpace ℝ ι)) y‖ ≤ M :=
  ((bump.contDiff (n := 1)).continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (bump.hasCompactSupport.fderiv (𝕜 := ℝ))

/-- The cut-off function `χ(x/R) • g x`. -/
noncomputable def cut (R : ℝ) (g : 𝓢(EuclideanSpace ℝ ι, ℂ)) : EuclideanSpace ℝ ι → ℂ :=
  fun x => (bump : ContDiffBump (0 : EuclideanSpace ℝ ι)) (R⁻¹ • x) • g x

lemma cut_smooth (n : ℕ∞) (R : ℝ) (g : 𝓢(EuclideanSpace ℝ ι, ℂ)) : ContDiff ℝ n (cut R g) :=
  (bump.contDiff.comp (contDiff_const_smul R⁻¹)).smul (g.smooth n)

lemma cut_supp (R : ℝ) (hR : R ≠ 0) (g : 𝓢(EuclideanSpace ℝ ι, ℂ)) : HasCompactSupport (cut R g) :=
  (bump.hasCompactSupport.comp_smul (inv_ne_zero hR)).smul_right

lemma cut_norm_le (R : ℝ) (g : 𝓢(EuclideanSpace ℝ ι, ℂ)) (x : EuclideanSpace ℝ ι) :
    ‖cut R g x‖ ≤ ‖g x‖ := by
  unfold cut
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg bump.nonneg]
  exact mul_le_of_le_one_left (norm_nonneg _) bump.le_one

lemma cut_eq (R : ℝ) (hR : 0 < R) (g : 𝓢(EuclideanSpace ℝ ι, ℂ)) (x : EuclideanSpace ℝ ι)
    (hx : ‖x‖ < R) : cut R g =ᶠ[𝓝 x] g := by
  have : ∀ᶠ y in 𝓝 x, ‖y‖ < R := (continuous_norm.tendsto x).eventually (gt_mem_nhds hx)
  filter_upwards [this] with y hy
  have h1 : (bump : ContDiffBump (0 : EuclideanSpace ℝ ι)) (R⁻¹ • y) = 1 := by
    apply bump.one_of_mem_closedBall
    rw [bump_rIn, mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hR, inv_mul_le_iff₀ hR]
    linarith
  simp [cut, h1]

lemma cut_fderiv_bound (M : ℝ)
    (hM : ∀ y, ‖fderiv ℝ (bump : ContDiffBump (0 : EuclideanSpace ℝ ι)) y‖ ≤ M)
    (R : ℝ) (hR : 1 ≤ R) (g : 𝓢(EuclideanSpace ℝ ι, ℂ)) (x m : EuclideanSpace ℝ ι) (hm : ‖m‖ ≤ 1) :
    ‖fderiv ℝ (cut R g) x m‖ ≤ ‖fderiv ℝ g x m‖ + M * ‖g x‖ := by
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ ι => R⁻¹ • y)
      (R⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)) x :=
    (hasFDerivAt_id x).const_smul R⁻¹
  have hc : HasFDerivAt (fun y => (bump : ContDiffBump (0 : EuclideanSpace ℝ ι)) (R⁻¹ • y))
      ((fderiv ℝ (bump : ContDiffBump (0 : EuclideanSpace ℝ ι)) (R⁻¹ • x)).comp
        (R⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι))) x :=
    ((bump.contDiff (n := 1)).differentiable (by norm_num) (R⁻¹ • x)).hasFDerivAt.comp x h1
  have hcut := hc.smul g.differentiableAt.hasFDerivAt
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rw [show cut R g = (fun y => (bump : ContDiffBump (0 : EuclideanSpace ℝ ι)) (R⁻¹ • y)) • ⇑g
    from rfl, hcut.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg bump.nonneg]
    exact mul_le_of_le_one_left (norm_nonneg _) bump.le_one
  · rw [norm_smul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc ‖fderiv ℝ (bump : ContDiffBump (0 : EuclideanSpace ℝ ι)) (R⁻¹ • x) (R⁻¹ • m)‖
        ≤ ‖fderiv ℝ (bump : ContDiffBump (0 : EuclideanSpace ℝ ι)) (R⁻¹ • x)‖ * ‖R⁻¹ • m‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * 1 := by
        apply mul_le_mul (hM _) _ (norm_nonneg _) hM0
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by linarith)]
        calc R⁻¹ * ‖m‖ ≤ 1 * 1 :=
              mul_le_mul (inv_le_one_of_one_le₀ hR) hm (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      _ = M := mul_one M

/-- Y1: the form inequality on `C_c^∞` extends to Schwartz functions. -/
theorem form_schwartz (V W : EuclideanSpace ℝ ι → ℝ) (hV : Measurable V) (hW : Measurable W)
    (C : ℝ) (hWC : ∀ x, |W x| ≤ C) (a b : ℝ)
    (h : ∀ f : EuclideanSpace ℝ ι → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (a * ∫ x, ‖f x‖ ^ 2)
          - b * (∑ p : ι, ∫ x, ‖fderiv ℝ f x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2)
          - (∫ x, W x * ‖f x‖ ^ 2) ≤
        (∑ p : ι, ∫ x, ‖fderiv ℝ f x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2)
          + ∫ x, V x * ‖f x‖ ^ 2)
    (g : 𝓢(EuclideanSpace ℝ ι, ℂ)) (hVint : Integrable (fun x => V x * ‖g x‖ ^ 2)) :
    (a * ∫ x, ‖g x‖ ^ 2)
        - b * (∑ p : ι, ∫ x, ‖fderiv ℝ g x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2)
        - (∫ x, W x * ‖g x‖ ^ 2) ≤
      (∑ p : ι, ∫ x, ‖fderiv ℝ g x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2)
        + ∫ x, V x * ‖g x‖ ^ 2 := by
  obtain ⟨M, hM⟩ := bump_deriv_bound (ι := ι)
  have hR1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hRpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by linarith [hR1 n]
  have hev : ∀ x, ∀ᶠ n : ℕ in atTop, cut ((n : ℝ) + 1) g =ᶠ[𝓝 x] g := fun x => by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop ‖x‖] with n hn
    exact cut_eq _ (hRpos n) g x (by linarith)
  have hg2 := sq_int g
  have T1 : Tendsto (fun n : ℕ => ∫ x, ‖cut ((n : ℝ) + 1) g x‖ ^ 2) atTop
      (𝓝 (∫ x, ‖g x‖ ^ 2)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖g x‖ ^ 2) (fun n => ?_) hg2
      (fun n => ?_) ?_
    · exact (((cut_smooth 0 _ g).continuous).norm.pow 2).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (cut_norm_le _ g x) 2
    · exact Eventually.of_forall fun x => tendsto_const_nhds.congr'
        ((hev x).mono fun n hn => by simp only [hn.eq_of_nhds])
  have T2 : ∀ p : ι, Tendsto
      (fun n : ℕ => ∫ x, ‖fderiv ℝ (cut ((n : ℝ) + 1) g) x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2)
      atTop (𝓝 (∫ x, ‖fderiv ℝ g x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2)) := fun p => by
    refine tendsto_integral_of_dominated_convergence
      (fun x => 2 * ‖fderiv ℝ g x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2 + 2 * M ^ 2 * ‖g x‖ ^ 2)
      (fun n => ?_) (((dsq_int g _).const_mul 2).add (hg2.const_mul _)) (fun n => ?_) ?_
    · exact ((((cut_smooth 1 _ g).continuous_fderiv (by norm_num)).clm_apply
        continuous_const).norm.pow 2).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hb := cut_fderiv_bound M hM _ (hR1 n) g x (EuclideanSpace.single p (1 : ℝ))
        (by rw [PiLp.norm_single, norm_one])
      have h0 := norm_nonneg (fderiv ℝ (cut ((n : ℝ) + 1) g) x (EuclideanSpace.single p (1 : ℝ)))
      nlinarith [sq_nonneg (‖fderiv ℝ g x (EuclideanSpace.single p (1 : ℝ))‖ - M * ‖g x‖)]
    · exact Eventually.of_forall fun x => tendsto_const_nhds.congr'
        ((hev x).mono fun n hn => by simp only [hn.fderiv_eq])
  have T3 : Tendsto (fun n : ℕ => ∫ x, W x * ‖cut ((n : ℝ) + 1) g x‖ ^ 2) atTop
      (𝓝 (∫ x, W x * ‖g x‖ ^ 2)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => C * ‖g x‖ ^ 2) (fun n => ?_)
      (hg2.const_mul C) (fun n => ?_) ?_
    · exact (hW.mul (((cut_smooth 0 _ g).continuous).norm.pow 2).measurable).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖cut ((n : ℝ) + 1) g x‖ ^ 2)]
      exact mul_le_mul (hWC x) (pow_le_pow_left₀ (norm_nonneg _) (cut_norm_le _ g x) 2)
        (by positivity) ((abs_nonneg _).trans (hWC x))
    · exact Eventually.of_forall fun x => tendsto_const_nhds.congr'
        ((hev x).mono fun n hn => by simp only [hn.eq_of_nhds])
  have T4 : Tendsto (fun n : ℕ => ∫ x, V x * ‖cut ((n : ℝ) + 1) g x‖ ^ 2) atTop
      (𝓝 (∫ x, V x * ‖g x‖ ^ 2)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖V x * ‖g x‖ ^ 2‖) (fun n => ?_)
      hVint.norm (fun n => ?_) ?_
    · exact (hV.mul (((cut_smooth 0 _ g).continuous).norm.pow 2).measurable).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖cut ((n : ℝ) + 1) g x‖ ^ 2),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖g x‖ ^ 2)]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (cut_norm_le _ g x) 2) (abs_nonneg _)
    · exact Eventually.of_forall fun x => tendsto_const_nhds.congr'
        ((hev x).mono fun n hn => by simp only [hn.eq_of_nhds])
  have hK := tendsto_finsetSum (Finset.univ : Finset ι) fun p _ => T2 p
  have hlhs := ((T1.const_mul a).sub (hK.const_mul b)).sub T3
  have hrhs := hK.add T4
  exact le_of_tendsto_of_tendsto' hlhs hrhs fun n =>
    h _ (cut_smooth ⊤ _ g) (cut_supp _ (hRpos n).ne' g)

end HVZY1

end SecY1

end SecY1all

open TeschlQM.Atomic MeasureTheory Filter in
theorem solution (γne γee : ℝ) (hne : 0 < γne) (hee : 0 < γee)
    (N : ℕ) (hN : 1 ≤ N) (lam : ℝ)
    (hlam : TeschlQM.Shared.IsBoundedBelowBy (atomicHamiltonian γne γee (N - 1)) lam) (δ : ℝ) (hδ : 0 < δ) :
    ∃ W : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ, Measurable W ∧ (∃ C : ℝ, ∀ x, |W x| ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x, R ≤ ‖x‖ → |W x| ≤ ε) ∧
      ∀ g : SchwartzMap (EuclideanSpace ℝ (Fin N × Fin 3)) ℂ,
        (lam * ∫ x, ‖g x‖ ^ 2)
          - δ * (∑ p : Fin N × Fin 3, ∫ x, ‖fderiv ℝ g x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2)
          - (∫ x, W x * ‖g x‖ ^ 2) ≤
        (∑ p : Fin N × Fin 3, ∫ x, ‖fderiv ℝ g x (EuclideanSpace.single p (1 : ℝ))‖ ^ 2)
          + ∫ x, atomicPotential γne γee N x * ‖g x‖ ^ 2 := by
  obtain ⟨W, hWm, ⟨C, hWC⟩, hdec, hX⟩ := HVZXF.smooth_bound γne γee hne hee N hN lam hlam δ hδ
  refine ⟨W, hWm, ⟨C, hWC⟩, hdec, fun g => ?_⟩
  exact HVZY1.form_schwartz (atomicPotential γne γee N) W (HVZFib.pot_meas γne γee N) hWm C hWC lam δ hX g
    (HVZFib.int_pot_self γne γee N (fun g j => HVZHS.hardyS_of N g j)
      (fun g j k h => HVZHS.hardyP_of N g j k h) g)
