-- Prove2me | solution 1 for PolicyGradTheory.LogBarrier.log_barrier_smoothness
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T12:56:44.100092+00:00
-- url     : https://prove2.me/submissions/93d5bd7d-1114-4edf-bdb7-9a7147f1d316

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy
import Definitions.Def_PolicyGradTheory_LogBarrier_Algorithm

set_option autoImplicit false

open FoundationsML.ReinforcementLearning in
theorem rl_M_nonneg {S A : Type*} [Fintype S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (s s' : S) : 0 ≤ InducedTransition π P s s' := by
  unfold InducedTransition
  exact Finset.sum_nonneg (fun a _ => mul_nonneg ((hπ s).1 a) ((hP s a).1 s'))

open FoundationsML.ReinforcementLearning in
theorem rl_M_sum {S A : Type*} [Fintype S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (s : S) : ∑ s', InducedTransition π P s s' = 1 := by
  unfold InducedTransition
  rw [Finset.sum_comm]
  have h1 : ∀ a, ∑ s', P s a s' = 1 := fun a => (hP s a).2
  simp_rw [← Finset.mul_sum, h1, mul_one]
  exact (hπ s).2

open FoundationsML.ReinforcementLearning in
theorem rl_D_zero {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (s0 s : S) :
    OccupationDist π P s0 0 s = if s = s0 then 1 else 0 := rfl

open FoundationsML.ReinforcementLearning in
theorem rl_D_succ {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (s0 : S) (t : ℕ) (s' : S) :
    OccupationDist π P s0 (t + 1) s' =
      ∑ s, OccupationDist π P s0 t s * InducedTransition π P s s' := rfl

open FoundationsML.ReinforcementLearning in
theorem rl_D_prob {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (s0 : S) (t : ℕ) :
    (∀ s, 0 ≤ OccupationDist π P s0 t s) ∧ ∑ s, OccupationDist π P s0 t s = 1 := by
  induction t with
  | zero =>
    refine ⟨fun s => ?_, ?_⟩
    · rw [rl_D_zero]
      split_ifs <;> norm_num
    · simp [rl_D_zero]
  | succ t ih =>
    refine ⟨fun s' => ?_, ?_⟩
    · rw [rl_D_succ]
      exact Finset.sum_nonneg (fun s _ => mul_nonneg (ih.1 s) (rl_M_nonneg π hπ P hP s s'))
    · simp only [rl_D_succ]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, rl_M_sum π hπ P hP, mul_one]
      exact ih.2

open FoundationsML.ReinforcementLearning in
theorem rl_D_front {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (t : ℕ) :
    ∀ (s0 u : S), OccupationDist π P s0 (t + 1) u =
      ∑ s', InducedTransition π P s0 s' * OccupationDist π P s' t u := by
  induction t with
  | zero =>
    intro s0 u
    simp [rl_D_succ, rl_D_zero]
  | succ t ih =>
    intro s0 u
    calc OccupationDist π P s0 (t + 1 + 1) u
        = ∑ v, (∑ s', InducedTransition π P s0 s' * OccupationDist π P s' t v) *
            InducedTransition π P v u := by
          rw [rl_D_succ]
          exact Finset.sum_congr rfl (fun v _ => by rw [ih s0 v])
      _ = ∑ s', InducedTransition π P s0 s' *
            ∑ v, OccupationDist π P s' t v * InducedTransition π P v u := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
      _ = ∑ s', InducedTransition π P s0 s' * OccupationDist π P s' (t + 1) u := by
          simp only [rl_D_succ]

open FoundationsML.ReinforcementLearning in
theorem rl_summable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (g : S → ℝ) (s0 : S) :
    Summable (fun t : ℕ => γ ^ t * ∑ s', OccupationDist π P s0 t s' * g s') := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hγ0 hγ1).mul_right (∑ s', |g s'|)) (fun t => ?_)
  obtain ⟨hnn, hsum⟩ := rl_D_prob π hπ P hP s0 t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hγ0 t)
  calc |∑ s', OccupationDist π P s0 t s' * g s'|
      ≤ ∑ s', |OccupationDist π P s0 t s' * g s'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', |g s'| := by
      apply Finset.sum_le_sum
      intro s' _
      rw [abs_mul, abs_of_nonneg (hnn s')]
      have h1 : OccupationDist π P s0 t s' ≤ 1 := by
        rw [← hsum]
        exact Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ s')
      calc OccupationDist π P s0 t s' * |g s'| ≤ 1 * |g s'| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = |g s'| := one_mul _

open FoundationsML.ReinforcementLearning in
theorem rl_bellman {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π)
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    PolicyValue π P Er γ s =
      InducedReward π Er s + γ * ∑ s' : S, InducedTransition π P s s' * PolicyValue π P Er γ s' := by
  have hsum := fun s0 => rl_summable π hπ P hP γ hγ0 hγ1 (InducedReward π Er) s0
  have key : ∀ t : ℕ, γ ^ (t + 1) * ∑ u, OccupationDist π P s (t + 1) u * InducedReward π Er u =
      γ * ∑ s', InducedTransition π P s s' *
        (γ ^ t * ∑ u, OccupationDist π P s' t u * InducedReward π Er u) := by
    intro t
    simp_rw [rl_D_front π P t s]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  unfold PolicyValue
  rw [(hsum s).tsum_eq_zero_add, tsum_congr key, tsum_mul_left,
    Summable.tsum_finsetSum (fun s' _ => (hsum s').mul_left (InducedTransition π P s s'))]
  simp_rw [tsum_mul_left]
  have h0 : γ ^ 0 * ∑ u, OccupationDist π P s 0 u * InducedReward π Er u = InducedReward π Er s := by
    simp [rl_D_zero]
  rw [h0]

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA in
theorem pd_g {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (s : S) :
    ∑ a, π s a * advantage π' P r γ s a =
      InducedReward π r s + γ * ∑ s', InducedTransition π P s s' * PolicyValue π' P r γ s'
        - PolicyValue π' P r γ s := by
  unfold advantage QFunction InducedReward InducedTransition
  have h1 : ∑ a, π s a * PolicyValue π' P r γ s = PolicyValue π' P r γ s := by
    rw [← Finset.sum_mul, (hπ s).2, one_mul]
  have h2 : ∑ a, π s a * (γ * ∑ s', P s a s' * PolicyValue π' P r γ s') =
      γ * ∑ s', (∑ a, π s a * P s a s') * PolicyValue π' P r γ s' := by
    calc ∑ a, π s a * (γ * ∑ s', P s a s' * PolicyValue π' P r γ s')
        = ∑ a, ∑ s', γ * (π s a * P s a s' * PolicyValue π' P r γ s') := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ = ∑ s', ∑ a, γ * (π s a * P s a s' * PolicyValue π' P r γ s') := Finset.sum_comm
      _ = γ * ∑ s', (∑ a, π s a * P s a s') * PolicyValue π' P r γ s' := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun s' _ => ?_)
          rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [mul_sub, mul_add]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, h1, h2]

open FoundationsML.ReinforcementLearning in
theorem pd_shift {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (s0 : S) (t : ℕ) (V : S → ℝ) :
    ∑ s, OccupationDist π P s0 t s * ∑ s', InducedTransition π P s s' * V s' =
      ∑ u, OccupationDist π P s0 (t + 1) u * V u := by
  simp only [rl_D_succ, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA in
theorem pd_visit {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (γ : ℝ) (s₀ s : S) :
    visitation π P γ (fun x => if x = s₀ then 1 else 0) s =
      (1 - γ) * ∑' t : ℕ, γ ^ t * OccupationDist π P s₀ t s := by
  unfold visitation
  simp [ite_mul, Finset.sum_ite_eq']

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA in
theorem pd_main {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (s₀ : S) :
    PolicyValue π P r γ s₀ - PolicyValue π' P r γ s₀ =
      1 / (1 - γ) * ∑ s, visitation π P γ (fun x => if x = s₀ then 1 else 0) s *
        ∑ a, π s a * advantage π' P r γ s a := by
  obtain ⟨hP, -, hγ0, hγ1⟩ := hM
  have hne : (1 - γ) ≠ 0 := by linarith
  set V' : S → ℝ := PolicyValue π' P r γ with hV'
  set R : S → ℝ := InducedReward π r with hR
  set D : ℕ → S → ℝ := OccupationDist π P s₀ with hD
  have hT : ∀ s, Summable (fun t : ℕ => γ ^ t * D t s) := by
    intro s
    refine Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hγ0 t)
      ((rl_D_prob π hπ P hP s₀ t).1 s)) (fun t => ?_) (summable_geometric_of_lt_one hγ0 hγ1)
    obtain ⟨hnn, hsum⟩ := rl_D_prob π hπ P hP s₀ t
    have h1 : D t s ≤ 1 := by
      rw [hD, ← hsum]
      exact Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ s)
    exact mul_le_of_le_one_right (pow_nonneg hγ0 t) h1
  have hb : Summable (fun t : ℕ => γ ^ t * ∑ u, D t u * V' u) :=
    rl_summable π hπ P hP γ hγ0 hγ1 V' s₀
  have hR' : Summable (fun t : ℕ => γ ^ t * ∑ u, D t u * R u) :=
    rl_summable π hπ P hP γ hγ0 hγ1 R s₀
  have hb1 : Summable (fun t : ℕ => γ ^ (t + 1) * ∑ u, D (t + 1) u * V' u) :=
    (summable_nat_add_iff 1).mpr hb
  simp_rw [pd_visit, pd_g P r γ π π' hπ]
  have step1 : 1 / (1 - γ) * ∑ s, (1 - γ) * (∑' t : ℕ, γ ^ t * D t s) *
        (R s + γ * ∑ s', InducedTransition π P s s' * V' s' - V' s) =
      ∑ s, ∑' t : ℕ, γ ^ t * D t s *
        (R s + γ * ∑ s', InducedTransition π P s s' * V' s' - V' s) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [tsum_mul_right]
    field_simp
  rw [step1, ← Summable.tsum_finsetSum (fun s _ => (hT s).mul_right _)]
  have step2 : ∀ t : ℕ, ∑ s, γ ^ t * D t s *
        (R s + γ * ∑ s', InducedTransition π P s s' * V' s' - V' s) =
      γ ^ t * ∑ u, D t u * R u + γ ^ (t + 1) * ∑ u, D (t + 1) u * V' u
        - γ ^ t * ∑ u, D t u * V' u := by
    intro t
    have e : ∀ s, γ ^ t * D t s *
        (R s + γ * ∑ s', InducedTransition π P s s' * V' s' - V' s) =
        γ ^ t * (D t s * R s) + γ ^ (t + 1) * (D t s * ∑ s', InducedTransition π P s s' * V' s')
          - γ ^ t * (D t s * V' s) := by intro s; ring
    simp_rw [e]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, hD, pd_shift]
  rw [tsum_congr step2, (hR'.add hb1).tsum_sub hb, hR'.tsum_add hb1, hb.tsum_eq_zero_add]
  have h0 : γ ^ 0 * ∑ u, D 0 u * V' u = V' s₀ := by
    simp [hD, rl_D_zero]
  rw [h0]
  have hV : PolicyValue π P r γ s₀ = ∑' t : ℕ, γ ^ t * ∑ u, D t u * R u := rfl
  rw [hV]
  ring

open Filter Topology in
theorem sg_hasFDerivAt {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    (f : E → ℝ) (g h : ι → E → ℝ) (h' : ι → E →L[ℝ] ℝ) (x0 : E)
    (hfx : ∀ x, f x - f x0 = ∑ i, g i x * (h i x - h i x0))
    (hg : ∀ i, ContinuousAt (g i) x0) (hh : ∀ i, HasFDerivAt (h i) (h' i) x0) :
    HasFDerivAt f (∑ i, g i x0 • h' i) x0 := by
  have key : ∀ i, HasFDerivAt (fun x => g i x * (h i x - h i x0)) (g i x0 • h' i) x0 := by
    intro i
    apply HasFDerivAt.of_isLittleO
    have t1 : (fun x => g i x - g i x0) =o[𝓝 x0] (fun _ => (1 : ℝ)) :=
      (Asymptotics.isLittleO_one_iff ℝ).mpr (tendsto_sub_nhds_zero_iff.mpr (hg i))
    have t2 : (fun x => h i x - h i x0) =O[𝓝 x0] (fun x => ‖x - x0‖) :=
      (hh i).isBigO_sub.norm_right
    have t3 : (fun x => (g i x - g i x0) * (h i x - h i x0)) =o[𝓝 x0] (fun x => x - x0) := by
      have := t1.mul_isBigO t2
      simp only [one_mul] at this
      exact Asymptotics.isLittleO_norm_right.mp this
    have t4 : (fun x => g i x0 * (h i x - h i x0 - h' i (x - x0))) =o[𝓝 x0] (fun x => x - x0) :=
      (hh i).isLittleO.const_mul_left (g i x0)
    refine (t3.add t4).congr_left (fun x => ?_)
    simp only [sub_self, mul_zero, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hsum : HasFDerivAt (fun x => f x0 + ∑ i, g i x * (h i x - h i x0)) (∑ i, g i x0 • h' i) x0 :=
    (HasFDerivAt.fun_sum (fun i _ => key i)).const_add _
  exact hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by
    simp only
    linarith [hfx x])

theorem sg_coord {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : StrongDual ℝ (EuclideanSpace ℝ ι)) (i : ι) :
    ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm L) i =
      L (EuclideanSpace.single i (1 : ℝ)) := by
  rw [← InnerProductSpace.toDual_symm_apply, real_inner_comm, EuclideanSpace.inner_single_left]
  simp

open PolicyGradTheory.Softmax in
theorem sg_Z_pos {S A : Type*} [Fintype A] [Nonempty A] (θ : EuclideanSpace ℝ (S × A)) (s : S) :
    0 < ∑ a', Real.exp (θ (s, a')) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

open FoundationsML.ReinforcementLearning PolicyGradTheory.Softmax in
theorem sg_policy {S A : Type*} [Fintype A] [Nonempty A] (θ : EuclideanSpace ℝ (S × A)) :
    IsPolicy (softmaxPolicy θ) := by
  intro s
  refine ⟨fun a => div_nonneg (Real.exp_pos _).le (sg_Z_pos θ s).le, ?_⟩
  unfold softmaxPolicy
  rw [← Finset.sum_div, div_self (sg_Z_pos θ s).ne']

open PolicyGradTheory.Softmax in
theorem sg_cont {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (s : S) (a : A) :
    Continuous (fun θ : EuclideanSpace ℝ (S × A) => softmaxPolicy θ s a) := by
  have hp : ∀ i : S × A, Continuous (fun θ : EuclideanSpace ℝ (S × A) => θ i) :=
    fun i => (EuclideanSpace.proj i).continuous
  unfold softmaxPolicy
  exact Continuous.div (Real.continuous_exp.comp (hp _))
    (continuous_finsetSum _ (fun a' _ => Real.continuous_exp.comp (hp _)))
    (fun θ => (sg_Z_pos θ s).ne')

noncomputable def sgD {S A : Type*} [Fintype S] [Fintype A] (θ : EuclideanSpace ℝ (S × A)) (s : S) (a : A) :
    EuclideanSpace ℝ (S × A) →L[ℝ] ℝ :=
  Real.exp (θ (s, a)) • ((ContinuousLinearMap.toSpanSingleton ℝ
      (-((∑ a', Real.exp (θ (s, a'))) ^ 2)⁻¹)).comp
      (∑ a', Real.exp (θ (s, a')) • (EuclideanSpace.proj (s, a') : EuclideanSpace ℝ (S × A) →L[ℝ] ℝ)))
    + (∑ a', Real.exp (θ (s, a')))⁻¹ •
      (Real.exp (θ (s, a)) • (EuclideanSpace.proj (s, a) : EuclideanSpace ℝ (S × A) →L[ℝ] ℝ))

open PolicyGradTheory.Softmax in
theorem sg_hasFDeriv {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (θ : EuclideanSpace ℝ (S × A))
    (s : S) (a : A) :
    HasFDerivAt (fun θ' : EuclideanSpace ℝ (S × A) => softmaxPolicy θ' s a) (sgD θ s a) θ := by
  have hp : ∀ i : S × A, HasFDerivAt (fun θ' : EuclideanSpace ℝ (S × A) => θ' i)
      (EuclideanSpace.proj i : EuclideanSpace ℝ (S × A) →L[ℝ] ℝ) θ :=
    fun i => (EuclideanSpace.proj (𝕜 := ℝ) i :
      EuclideanSpace ℝ (S × A) →L[ℝ] ℝ).hasFDerivAt (x := θ)
  have he : ∀ i : S × A, HasFDerivAt (fun θ' : EuclideanSpace ℝ (S × A) => Real.exp (θ' i))
      (Real.exp (θ i) • (EuclideanSpace.proj i : EuclideanSpace ℝ (S × A) →L[ℝ] ℝ)) θ :=
    fun i => (hp i).exp
  have hZ : HasFDerivAt (fun θ' : EuclideanSpace ℝ (S × A) => ∑ a', Real.exp (θ' (s, a')))
      (∑ a', Real.exp (θ (s, a')) • (EuclideanSpace.proj (s, a') : EuclideanSpace ℝ (S × A) →L[ℝ] ℝ)) θ :=
    HasFDerivAt.fun_sum (fun a' _ => he (s, a'))
  have hinv := (hasFDerivAt_inv (𝕜 := ℝ) (sg_Z_pos θ s).ne').comp θ hZ
  have hm := (he (s, a)).mul hinv
  have hfun : (fun θ' : EuclideanSpace ℝ (S × A) => softmaxPolicy θ' s a) =
      (fun y => Real.exp (y (s, a)) * ((fun x : ℝ => x⁻¹) ∘
        (fun θ' : EuclideanSpace ℝ (S × A) => ∑ a', Real.exp (θ' (s, a')))) y) := by
    funext y
    simp [softmaxPolicy, div_eq_mul_inv]
  rw [hfun]
  exact hm

open PolicyGradTheory.Softmax in
theorem sg_D_single {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
    (θ : EuclideanSpace ℝ (S × A)) (s : S) (a : A) (s0 : S) (a0 : A) :
    sgD θ s a (EuclideanSpace.single (s0, a0) (1 : ℝ)) =
      if s = s0 then softmaxPolicy θ s a * ((if a = a0 then 1 else 0) - softmaxPolicy θ s0 a0)
      else 0 := by
  have hZ := (sg_Z_pos θ s).ne'
  by_cases hs : s = s0
  · subst hs
    simp [sgD, softmaxPolicy]
    split_ifs <;> field_simp <;> ring
  · simp [sgD, hs]

open FoundationsML.ReinforcementLearning in
theorem sg_occ_le {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (s0 : S) (t : ℕ) (u : S) :
    0 ≤ OccupationDist π P s0 t u ∧ OccupationDist π P s0 t u ≤ 1 := by
  obtain ⟨hnn, hsum⟩ := rl_D_prob π hπ P hP s0 t
  refine ⟨hnn u, ?_⟩
  rw [← hsum]
  exact Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ u)

open FoundationsML.ReinforcementLearning in
theorem sg_occ_summable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s0 u : S) :
    Summable (fun t : ℕ => γ ^ t * OccupationDist π P s0 t u) := by
  refine Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hγ0 t)
    (sg_occ_le π hπ P hP s0 t u).1) (fun t => ?_) (summable_geometric_of_lt_one hγ0 hγ1)
  exact mul_le_of_le_one_right (pow_nonneg hγ0 t) (sg_occ_le π hπ P hP s0 t u).2

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA in
theorem sg_vis_lin {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (μ : S → ℝ) (s : S) :
    visitation π P γ μ s =
      ∑ s0, μ s0 * visitation π P γ (fun x => if x = s0 then 1 else 0) s := by
  simp_rw [pd_visit]
  unfold visitation
  have e : ∀ t : ℕ, γ ^ t * ∑ s0, μ s0 * OccupationDist π P s0 t s =
      ∑ s0, μ s0 * (γ ^ t * OccupationDist π P s0 t s) := by
    intro t
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [tsum_congr e, Summable.tsum_finsetSum
    (fun s0 _ => (sg_occ_summable π hπ P hP γ hγ0 hγ1 s0 s).mul_left (μ s0))]
  simp_rw [tsum_mul_left]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA in
theorem sg_adv_zero {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (r : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    ∑ a, π s a * advantage π P r γ s a = 0 := by
  rw [pd_g P r γ π π hπ s, ← rl_bellman π hπ P hP r γ hγ0 hγ1 s]
  ring

open FoundationsML.ReinforcementLearning PolicyGradTheory.Softmax in
theorem sg_occ_cont {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]
    (P : S → A → S → ℝ) (s0 : S) (t : ℕ) (u : S) :
    Continuous (fun θ : EuclideanSpace ℝ (S × A) => OccupationDist (softmaxPolicy θ) P s0 t u) := by
  induction t generalizing u with
  | zero =>
    simp only [rl_D_zero]
    exact continuous_const
  | succ t ih =>
    simp only [rl_D_succ]
    refine continuous_finsetSum _ (fun s _ => (ih s).mul ?_)
    unfold InducedTransition
    exact continuous_finsetSum _ (fun a _ => (sg_cont s a).mul continuous_const)

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA PolicyGradTheory.Softmax in
theorem sg_vis_cont {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (μ : S → ℝ) (s : S) :
    Continuous (fun θ : EuclideanSpace ℝ (S × A) => visitation (softmaxPolicy θ) P γ μ s) := by
  unfold visitation
  refine continuous_const.mul (continuous_tsum (u := fun t : ℕ => γ ^ t * ∑ s0, |μ s0|)
    (fun t => ?_) ((summable_geometric_of_lt_one hγ0 hγ1).mul_right _) (fun t θ => ?_))
  · exact continuous_const.mul (continuous_finsetSum _
      (fun s0 _ => continuous_const.mul (sg_occ_cont P s0 t s)))
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hγ0 t)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s0 _ => ?_)
    obtain ⟨h0, h1⟩ := sg_occ_le (softmaxPolicy θ) (sg_policy θ) P hP s0 t s
    rw [abs_mul, abs_of_nonneg h0]
    exact mul_le_of_le_one_right (abs_nonneg _) h1

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA PolicyGradTheory.Softmax in
theorem sg_pdl {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ)
    (μ : S → ℝ) (θ θ' : EuclideanSpace ℝ (S × A)) :
    softmaxValue P r γ μ θ' - softmaxValue P r γ μ θ =
      ∑ i : S × A, (1 / (1 - γ) * visitation (softmaxPolicy θ') P γ μ i.1 *
        advantage (softmaxPolicy θ) P r γ i.1 i.2) *
        (softmaxPolicy θ' i.1 i.2 - softmaxPolicy θ i.1 i.2) := by
  have hP := hM.1
  have hγ0 := hM.2.2.1
  have hγ1 := hM.2.2.2
  set π' := softmaxPolicy θ' with hπ'
  set π := softmaxPolicy θ with hπ
  have hpol' : IsPolicy π' := sg_policy θ'
  have hpol : IsPolicy π := sg_policy θ
  have hv : ∀ s, visitation π' P γ μ s =
      ∑ s0, μ s0 * visitation π' P γ (fun x => if x = s0 then 1 else 0) s :=
    fun s => sg_vis_lin π' hpol' P hP γ hγ0 hγ1 μ s
  have hX : ∀ s, ∑ a, π' s a * advantage π P r γ s a =
      ∑ a, advantage π P r γ s a * (π' s a - π s a) := by
    intro s
    have h0 := sg_adv_zero π hpol P hP r γ hγ0 hγ1 s
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    have e1 : ∑ a, advantage π P r γ s a * π' s a = ∑ a, π' s a * advantage π P r γ s a :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    have e2 : ∑ a, advantage π P r γ s a * π s a = ∑ a, π s a * advantage π P r γ s a :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    rw [e1, e2, h0, sub_zero]
  unfold softmaxValue valueAt
  rw [← hπ', ← hπ, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  simp_rw [pd_main P r γ hM π' π hpol' hpol]
  rw [Fintype.sum_prod_type]
  simp_rw [hv]
  calc ∑ s0, μ s0 * (1 / (1 - γ) * ∑ s, visitation π' P γ (fun x => if x = s0 then 1 else 0) s *
          ∑ a, π' s a * advantage π P r γ s a)
      = ∑ s0, ∑ s, 1 / (1 - γ) * (μ s0 * visitation π' P γ (fun x => if x = s0 then 1 else 0) s) *
          ∑ a, advantage π P r γ s a * (π' s a - π s a) := by
        refine Finset.sum_congr rfl (fun s0 _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [hX s]
        ring
    _ = ∑ s, ∑ s0, 1 / (1 - γ) * (μ s0 * visitation π' P γ (fun x => if x = s0 then 1 else 0) s) *
          ∑ a, advantage π P r γ s a * (π' s a - π s a) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [← Finset.sum_mul, ← Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        ring

open FoundationsML.ReinforcementLearning in
theorem rl_expand {S A : Type*} [Fintype S] [Fintype A]
    (σ : S → A → ℝ) (P : S → A → S → ℝ) (Er : S → A → ℝ) (γ : ℝ) (W : S → ℝ) (u : S) :
    InducedReward σ Er u + γ * ∑ u', InducedTransition σ P u u' * W u' =
      ∑ c, σ u c * (Er u c + γ * ∑ u', P u c u' * W u') := by
  unfold InducedReward InducedTransition
  simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

open FoundationsML.ReinforcementLearning in
theorem rl_VQ {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π)
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (u : S) :
    PolicyValue π P Er γ u = ∑ c, π u c * QFunction π P Er γ u c := by
  rw [rl_bellman π hπ P hP Er γ hγ0 hγ1 u, rl_expand π P Er γ (PolicyValue π P Er γ) u]
  rfl

open FoundationsML.ReinforcementLearning in
theorem rl_compare {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (σ : S → A → ℝ) (hσ : IsPolicy σ) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (W : S → ℝ) (s0 : S) :
    W s0 - PolicyValue σ P Er γ s0 =
      ∑' t : ℕ, γ ^ t * ∑ u, OccupationDist σ P s0 t u *
        (W u - (InducedReward σ Er u + γ * ∑ u', InducedTransition σ P u u' * W u')) := by
  have hb := rl_summable σ hσ P hP γ hγ0 hγ1 W s0
  have hc := rl_summable σ hσ P hP γ hγ0 hγ1 (InducedReward σ Er) s0
  have hb1 : Summable (fun t : ℕ => γ ^ (t + 1) * ∑ u, OccupationDist σ P s0 (t + 1) u * W u) :=
    (summable_nat_add_iff 1).mpr hb
  have h1 : ∀ t : ℕ, ∑ u, OccupationDist σ P s0 (t + 1) u * W u =
      ∑ u, OccupationDist σ P s0 t u * ∑ u', InducedTransition σ P u u' * W u' := by
    intro t
    simp only [rl_D_succ]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  have hsplit : ∀ t : ℕ, ∑ u, OccupationDist σ P s0 t u *
        (W u - (InducedReward σ Er u + γ * ∑ u', InducedTransition σ P u u' * W u')) =
      ∑ u, OccupationDist σ P s0 t u * W u - ∑ u, OccupationDist σ P s0 t u * InducedReward σ Er u
        - γ * ∑ u, OccupationDist σ P s0 t u * ∑ u', InducedTransition σ P u u' * W u' := by
    intro t
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun u _ => by ring)
  have hterm : ∀ t : ℕ, γ ^ t * ∑ u, OccupationDist σ P s0 t u *
        (W u - (InducedReward σ Er u + γ * ∑ u', InducedTransition σ P u u' * W u')) =
      (γ ^ t * ∑ u, OccupationDist σ P s0 t u * W u
        - γ ^ (t + 1) * ∑ u, OccupationDist σ P s0 (t + 1) u * W u)
        - γ ^ t * ∑ u, OccupationDist σ P s0 t u * InducedReward σ Er u := by
    intro t
    rw [hsplit t, h1 t, pow_succ]
    ring
  rw [tsum_congr hterm, (hb.sub hb1).tsum_sub hc, hb.tsum_sub hb1, hb.tsum_eq_zero_add]
  have h0 : γ ^ 0 * ∑ u, OccupationDist σ P s0 0 u * W u = W s0 := by
    simp [rl_D_zero]
  rw [h0]
  unfold PolicyValue
  ring

open FoundationsML.ReinforcementLearning in
theorem rl_compare_fn {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (σ : S → A → ℝ) (hσ : IsPolicy σ) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (W δ : S → ℝ)
    (hδ : ∀ u, δ u = W u - (InducedReward σ Er u + γ * ∑ u', InducedTransition σ P u u' * W u'))
    (s0 : S) :
    W s0 - PolicyValue σ P Er γ s0 = ∑' t : ℕ, γ ^ t * ∑ u, OccupationDist σ P s0 t u * δ u := by
  have h : δ = fun u => W u - (InducedReward σ Er u + γ * ∑ u', InducedTransition σ P u u' * W u') :=
    funext hδ
  subst h
  exact rl_compare σ hσ P hP Er γ hγ0 hγ1 W s0

open FoundationsML.ReinforcementLearning in
theorem rl_improve_le {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (σ : S → A → ℝ) (hσ : IsPolicy σ) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (W δ : S → ℝ)
    (hδ : ∀ u, δ u = W u - (InducedReward σ Er u + γ * ∑ u', InducedTransition σ P u u' * W u'))
    (hnn : ∀ u, 0 ≤ δ u) (s0 : S) :
    PolicyValue σ P Er γ s0 ≤ W s0 := by
  have h := rl_compare_fn σ hσ P hP Er γ hγ0 hγ1 W δ hδ s0
  have h2 : 0 ≤ ∑' t : ℕ, γ ^ t * ∑ u, OccupationDist σ P s0 t u * δ u :=
    tsum_nonneg (fun t => mul_nonneg (pow_nonneg hγ0 t)
      (Finset.sum_nonneg (fun u _ => mul_nonneg ((rl_D_prob σ hσ P hP s0 t).1 u) (hnn u))))
  linarith


open FoundationsML.ReinforcementLearning Filter Topology PolicyGradTheory.Softmax in
theorem sg_grad {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (μ : S → ℝ) (θ : EuclideanSpace ℝ (S × A)) (s : S) (a : A) :
    gradient (softmaxValue P r γ μ) θ (s, a) =
      1 / (1 - γ) * PolicyGradTheory.ProjGA.visitation (softmaxPolicy θ) P γ μ s * softmaxPolicy θ s a *
        PolicyGradTheory.ProjGA.advantage (softmaxPolicy θ) P r γ s a := by
  have hP := hM.1
  have hγ0 := hM.2.2.1
  have hγ1 := hM.2.2.2
  set g : S × A → EuclideanSpace ℝ (S × A) → ℝ := fun i θ' =>
    1 / (1 - γ) * PolicyGradTheory.ProjGA.visitation (softmaxPolicy θ') P γ μ i.1 *
      PolicyGradTheory.ProjGA.advantage (softmaxPolicy θ) P r γ i.1 i.2 with hg
  have hf : HasFDerivAt (softmaxValue P r γ μ) (∑ i : S × A, g i θ • sgD θ i.1 i.2) θ :=
    sg_hasFDerivAt _ g (fun i θ' => softmaxPolicy θ' i.1 i.2) (fun i => sgD θ i.1 i.2) θ
      (fun θ' => sg_pdl P r γ hM μ θ θ')
      (fun i => ((continuous_const.mul (sg_vis_cont P hP γ hγ0 hγ1 μ i.1)).mul
        continuous_const).continuousAt)
      (fun i => sg_hasFDeriv θ i.1 i.2)
  rw [hf.hasGradientAt.gradient, sg_coord, ContinuousLinearMap.sum_apply]
  simp_rw [smul_apply, sg_D_single, smul_eq_mul]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single s (fun s' _ hs' => by simp [hs'])
    (fun h => absurd (Finset.mem_univ s) h)]
  simp only [if_true, hg]
  have h0 := sg_adv_zero (softmaxPolicy θ) (sg_policy θ) P hP r γ hγ0 hγ1 s
  set K := 1 / (1 - γ) * PolicyGradTheory.ProjGA.visitation (softmaxPolicy θ) P γ μ s
  set Ad := PolicyGradTheory.ProjGA.advantage (softmaxPolicy θ) P r γ s
  set π := softmaxPolicy θ s
  have e : ∀ a', K * Ad a' * (π a' * ((if a' = a then 1 else 0) - π a)) =
      (if a' = a then K * π a' * Ad a' else 0) - K * π a * (π a' * Ad a') := by
    intro a'
    split_ifs <;> ring
  simp_rw [e]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, h0, Finset.sum_ite_eq' Finset.univ a]
  simp

theorem pg_u_exp (u c : ℝ) (hc : 0 ≤ c) : 0 ≤ u * (Real.exp (c * u) - 1) := by
  rcases le_or_gt 0 u with hu | hu
  · have : 1 ≤ Real.exp (c * u) := Real.one_le_exp (mul_nonneg hc hu)
    exact mul_nonneg hu (by linarith)
  · have : Real.exp (c * u) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hc hu.le)
    exact mul_nonneg_of_nonpos_of_nonpos hu.le (by linarith)

theorem pg_u_exp_pos (u c : ℝ) (hu : 0 ≤ u) : c * u ^ 2 ≤ u * (Real.exp (c * u) - 1) := by
  have h := Real.add_one_le_exp (c * u)
  have := mul_le_mul_of_nonneg_left (show c * u ≤ Real.exp (c * u) - 1 by linarith) hu
  nlinarith

theorem pg_gain_abs {A : Type*} [Fintype A] [Nonempty A] (x x' π Ad : A → ℝ) (c K : ℝ)
    (hπ : ∀ a, π a = Real.exp (x a) / ∑ a', Real.exp (x a'))
    (hx' : ∀ a, x' a = x a + c * (π a * Ad a)) (hc : 0 ≤ c)
    (h0 : ∑ a, π a * Ad a = 0) (hK : ∀ a, π a * Ad a ≤ K) (b : A) :
    0 ≤ ∑ a, Real.exp (x' a) / (∑ a', Real.exp (x' a')) * Ad a ∧
    (0 ≤ π b * Ad b → c * (π b * Ad b) ^ 2 / Real.exp (c * K) ≤
      ∑ a, Real.exp (x' a) / (∑ a', Real.exp (x' a')) * Ad a) := by
  set Z := ∑ a', Real.exp (x a') with hZdef
  have hZ : 0 < Z := Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  set u : A → ℝ := fun a => π a * Ad a with hu
  set E : A → ℝ := fun a => Real.exp (c * u a) with hE
  have hπnn : ∀ a, 0 ≤ π a := fun a => by rw [hπ]; exact div_nonneg (Real.exp_pos _).le hZ.le
  have hπsum : ∑ a, π a = 1 := by simp_rw [hπ]; rw [← Finset.sum_div]; exact div_self hZ.ne'
  have hex : ∀ a, Real.exp (x' a) = Z * (π a * E a) := by
    intro a
    have h1 : Z * π a = Real.exp (x a) := by rw [hπ a]; field_simp
    rw [hx', Real.exp_add, ← h1]
    show Z * π a * Real.exp (c * (π a * Ad a)) = Z * (π a * Real.exp (c * (π a * Ad a)))
    ring
  set W := ∑ a, π a * E a with hW
  have hWpos : 0 < W := by
    obtain ⟨a0⟩ := (inferInstance : Nonempty A)
    have hpos : ∀ a, 0 < Real.exp (x a) / Z := fun a => div_pos (Real.exp_pos _) hZ
    refine Finset.sum_pos (fun a _ => mul_pos ?_ (Real.exp_pos _)) Finset.univ_nonempty
    rw [hπ]; exact hpos a
  have hWle : W ≤ Real.exp (c * K) := by
    calc W ≤ ∑ a, π a * Real.exp (c * K) := Finset.sum_le_sum (fun a _ =>
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hK a) hc))
            (hπnn a))
      _ = Real.exp (c * K) := by rw [← Finset.sum_mul, hπsum, one_mul]
  have hsumx : ∑ a', Real.exp (x' a') = Z * W := by
    simp_rw [hex]; rw [← Finset.mul_sum]
  have hform : ∑ a, Real.exp (x' a) / (∑ a', Real.exp (x' a')) * Ad a =
      (∑ a, u a * (E a - 1)) / W := by
    have h1 : ∑ a, u a * (E a - 1) = ∑ a, u a * E a := by
      simp_rw [mul_sub, mul_one]
      rw [Finset.sum_sub_distrib]
      have : ∑ a, u a = 0 := h0
      rw [this, sub_zero]
    rw [h1, hsumx, Finset.sum_div]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hex]
    simp only [hu]
    field_simp
  have hnum : 0 ≤ ∑ a, u a * (E a - 1) :=
    Finset.sum_nonneg (fun a _ => pg_u_exp (u a) c hc)
  rw [hform]
  refine ⟨div_nonneg hnum hWpos.le, fun hb => ?_⟩
  have h1 : c * u b ^ 2 ≤ ∑ a, u a * (E a - 1) :=
    (pg_u_exp_pos (u b) c hb).trans
      (Finset.single_le_sum (f := fun a => u a * (E a - 1))
        (fun a _ => pg_u_exp (u a) c hc) (Finset.mem_univ b))
  have h2 : 0 ≤ c * u b ^ 2 := mul_nonneg hc (sq_nonneg _)
  calc c * (π b * Ad b) ^ 2 / Real.exp (c * K) = c * u b ^ 2 / Real.exp (c * K) := rfl
    _ ≤ c * u b ^ 2 / W := div_le_div_of_nonneg_left h2 hWpos hWle
    _ ≤ (∑ a, u a * (E a - 1)) / W := div_le_div_of_nonneg_right h1 hWpos.le

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA in
theorem pg_V_bounds {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ)
    (π : S → A → ℝ) (hπ : IsPolicy π) (s : S) :
    0 ≤ PolicyValue π P r γ s ∧ PolicyValue π P r γ s ≤ 1 / (1 - γ) := by
  obtain ⟨hP, hr, hγ0, hγ1⟩ := hM
  have hR : ∀ u, 0 ≤ InducedReward π r u ∧ InducedReward π r u ≤ 1 := by
    intro u
    unfold InducedReward
    refine ⟨Finset.sum_nonneg (fun a _ => mul_nonneg ((hπ u).1 a) (hr u a).1), ?_⟩
    calc ∑ a, π u a * r u a ≤ ∑ a, π u a * 1 := Finset.sum_le_sum (fun a _ =>
          mul_le_mul_of_nonneg_left (hr u a).2 ((hπ u).1 a))
      _ = 1 := by simp [(hπ u).2]
  have hterm : ∀ t : ℕ, 0 ≤ γ ^ t * ∑ s', OccupationDist π P s t s' * InducedReward π r s' ∧
      γ ^ t * ∑ s', OccupationDist π P s t s' * InducedReward π r s' ≤ γ ^ t := by
    intro t
    obtain ⟨hnn, hsum⟩ := rl_D_prob π hπ P hP s t
    have h1 : 0 ≤ ∑ s', OccupationDist π P s t s' * InducedReward π r s' :=
      Finset.sum_nonneg (fun s' _ => mul_nonneg (hnn s') (hR s').1)
    have h2 : ∑ s', OccupationDist π P s t s' * InducedReward π r s' ≤ 1 := by
      calc ∑ s', OccupationDist π P s t s' * InducedReward π r s'
          ≤ ∑ s', OccupationDist π P s t s' * 1 := Finset.sum_le_sum (fun s' _ =>
            mul_le_mul_of_nonneg_left (hR s').2 (hnn s'))
        _ = 1 := by simp [hsum]
    exact ⟨mul_nonneg (pow_nonneg hγ0 t) h1, mul_le_of_le_one_right (pow_nonneg hγ0 t) h2⟩
  have hs := rl_summable π hπ P hP γ hγ0 hγ1 (InducedReward π r) s
  unfold PolicyValue
  refine ⟨tsum_nonneg (fun t => (hterm t).1), ?_⟩
  calc ∑' t : ℕ, γ ^ t * ∑ s', OccupationDist π P s t s' * InducedReward π r s'
      ≤ ∑' t : ℕ, γ ^ t := hs.tsum_le_tsum (fun t => (hterm t).2)
        (summable_geometric_of_lt_one hγ0 hγ1)
    _ = 1 / (1 - γ) := by rw [tsum_geometric_of_lt_one hγ0 hγ1, one_div]

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA in
theorem pg_Q_bounds {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ)
    (π : S → A → ℝ) (hπ : IsPolicy π) (s : S) (a : A) :
    0 ≤ QFunction π P r γ s a ∧ QFunction π P r γ s a ≤ 1 / (1 - γ) := by
  have hV := fun s' => pg_V_bounds P r γ hM π hπ s'
  obtain ⟨hP, hr, hγ0, hγ1⟩ := hM
  have hne : 0 < 1 - γ := by linarith
  unfold QFunction
  have h1 : 0 ≤ ∑ s', P s a s' * PolicyValue π P r γ s' :=
    Finset.sum_nonneg (fun s' _ => mul_nonneg ((hP s a).1 s') (hV s').1)
  have h2 : ∑ s', P s a s' * PolicyValue π P r γ s' ≤ 1 / (1 - γ) := by
    calc ∑ s', P s a s' * PolicyValue π P r γ s' ≤ ∑ s', P s a s' * (1 / (1 - γ)) :=
          Finset.sum_le_sum (fun s' _ => mul_le_mul_of_nonneg_left (hV s').2 ((hP s a).1 s'))
      _ = 1 / (1 - γ) := by rw [← Finset.sum_mul, (hP s a).2, one_mul]
  refine ⟨add_nonneg (hr s a).1 (mul_nonneg hγ0 h1), ?_⟩
  have h3 : γ * ∑ s', P s a s' * PolicyValue π P r γ s' ≤ γ * (1 / (1 - γ)) :=
    mul_le_mul_of_nonneg_left h2 hγ0
  have h4 : 1 + γ * (1 / (1 - γ)) = 1 / (1 - γ) := by field_simp; ring
  linarith [(hr s a).2]

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA in
theorem pg_adv_bound {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ)
    (π : S → A → ℝ) (hπ : IsPolicy π) (s : S) (a : A) :
    |advantage π P r γ s a| ≤ 1 / (1 - γ) := by
  have h1 := pg_V_bounds P r γ hM π hπ s
  have h2 := pg_Q_bounds P r γ hM π hπ s a
  unfold advantage
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA in
theorem pg_vis_point {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s₀ s : S) :
    0 ≤ visitation π P γ (fun x => if x = s₀ then 1 else 0) s ∧
    visitation π P γ (fun x => if x = s₀ then 1 else 0) s ≤ 1 ∧
    (s = s₀ → 1 - γ ≤ visitation π P γ (fun x => if x = s₀ then 1 else 0) s) := by
  rw [pd_visit]
  have hne : 0 ≤ 1 - γ := by linarith
  have hsum := sg_occ_summable π hπ P hP γ hγ0 hγ1 s₀ s
  have hnn : ∀ t : ℕ, 0 ≤ γ ^ t * OccupationDist π P s₀ t s := fun t =>
    mul_nonneg (pow_nonneg hγ0 t) (sg_occ_le π hπ P hP s₀ t s).1
  refine ⟨mul_nonneg hne (tsum_nonneg hnn), ?_, fun hs => ?_⟩
  · have h1 : ∑' t : ℕ, γ ^ t * OccupationDist π P s₀ t s ≤ ∑' t : ℕ, γ ^ t :=
      hsum.tsum_le_tsum (fun t => mul_le_of_le_one_right (pow_nonneg hγ0 t)
        (sg_occ_le π hπ P hP s₀ t s).2) (summable_geometric_of_lt_one hγ0 hγ1)
    rw [tsum_geometric_of_lt_one hγ0 hγ1] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hne
    rw [mul_inv_cancel₀ (by linarith)] at h2
    exact h2
  · have h1 : γ ^ 0 * OccupationDist π P s₀ 0 s ≤ ∑' t : ℕ, γ ^ t * OccupationDist π P s₀ t s :=
      hsum.le_tsum 0 (fun j _ => hnn j)
    have h0 : γ ^ 0 * OccupationDist π P s₀ 0 s = 1 := by simp [rl_D_zero, hs]
    rw [h0] at h1
    have := mul_le_mul_of_nonneg_left h1 hne
    linarith

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA in
theorem pg_vis_mu {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (μ : S → ℝ) (hμ : IsDist μ) (s : S) :
    (1 - γ) * μ s ≤ visitation π P γ μ s ∧ visitation π P γ μ s ≤ 1 := by
  rw [sg_vis_lin π hπ P hP γ hγ0 hγ1 μ s]
  have hv := fun s₀ => pg_vis_point π hπ P hP γ hγ0 hγ1 s₀ s
  constructor
  · have h1 : μ s * visitation π P γ (fun x => if x = s then 1 else 0) s ≤
        ∑ s0, μ s0 * visitation π P γ (fun x => if x = s0 then 1 else 0) s :=
      Finset.single_le_sum (f := fun s0 => μ s0 * visitation π P γ (fun x => if x = s0 then 1 else 0) s)
        (fun s0 _ => mul_nonneg (hμ.1 s0) (hv s0).1) (Finset.mem_univ s)
    have h2 := mul_le_mul_of_nonneg_left ((hv s).2.2 rfl) (hμ.1 s)
    linarith
  · calc ∑ s0, μ s0 * visitation π P γ (fun x => if x = s0 then 1 else 0) s
        ≤ ∑ s0, μ s0 * 1 := Finset.sum_le_sum (fun s0 _ =>
          mul_le_mul_of_nonneg_left (hv s0).2.1 (hμ.1 s0))
      _ = 1 := by simp [hμ.2]


/-! ## Glue for Corollary 5.1 -/

open FoundationsML.ReinforcementLearning PolicyGradTheory.Softmax PolicyGradTheory.ProjGA in
theorem lb_sv_diff {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ)
    (μ : S → ℝ) (θ : EuclideanSpace ℝ (S × A)) :
    DifferentiableAt ℝ (softmaxValue P r γ μ) θ := by
  have hP := hM.1
  have hγ0 := hM.2.2.1
  have hγ1 := hM.2.2.2
  set g : S × A → EuclideanSpace ℝ (S × A) → ℝ := fun i θ' =>
    1 / (1 - γ) * PolicyGradTheory.ProjGA.visitation (softmaxPolicy θ') P γ μ i.1 *
      PolicyGradTheory.ProjGA.advantage (softmaxPolicy θ) P r γ i.1 i.2 with hg
  have hf : HasFDerivAt (softmaxValue P r γ μ) (∑ i : S × A, g i θ • sgD θ i.1 i.2) θ :=
    sg_hasFDerivAt _ g (fun i θ' => softmaxPolicy θ' i.1 i.2) (fun i => sgD θ i.1 i.2) θ
      (fun θ' => sg_pdl P r γ hM μ θ θ')
      (fun i => ((continuous_const.mul (sg_vis_cont P hP γ hγ0 hγ1 μ i.1)).mul
        continuous_const).continuousAt)
      (fun i => sg_hasFDeriv θ i.1 i.2)
  exact hf.differentiableAt

open FoundationsML.ReinforcementLearning PolicyGradTheory.Softmax PolicyGradTheory.ProjGA in
theorem lb_obj_diff {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ)
    (μ : S → ℝ) (lam : ℝ) :
    Differentiable ℝ (PolicyGradTheory.LogBarrier.logBarrierObj P r γ μ lam) := by
  intro θ
  have hlog : ∀ s a, DifferentiableAt ℝ
      (fun θ' : EuclideanSpace ℝ (S × A) => Real.log (softmaxPolicy θ' s a)) θ := by
    intro s a
    have hpos : 0 < softmaxPolicy θ s a := div_pos (Real.exp_pos _) (sg_Z_pos θ s)
    exact ((sg_hasFDeriv θ s a).differentiableAt).log hpos.ne'
  have hsum : DifferentiableAt ℝ (fun θ' : EuclideanSpace ℝ (S × A) =>
      ∑ s, ∑ a, Real.log (softmaxPolicy θ' s a)) θ :=
    DifferentiableAt.fun_sum (fun s _ => DifferentiableAt.fun_sum (fun a _ => hlog s a))
  have h := ((lb_sv_diff P r γ hM μ θ).add (hsum.const_mul
    (lam / ((Fintype.card S : ℝ) * (Fintype.card A : ℝ))))).add
    (differentiableAt_const (lam * Real.log (Fintype.card A : ℝ)))
  exact h

/-! ## New lemmas for Lemma D.4 (log barrier smoothness) -/

theorem lbs_sm_l1 {A : Type*} [Fintype A] [Nonempty A] (x y : A → ℝ) (δ : ℝ)
    (h : ∀ a, |x a - y a| ≤ δ) :
    ∑ a, |Real.exp (x a) / ∑ b, Real.exp (x b) - Real.exp (y a) / ∑ b, Real.exp (y b)|
      ≤ 2 * δ := by
  set u : A → ℝ := fun a => x a - y a with hu
  have hu' : ∀ a, |u a| ≤ δ := fun a => h a
  set σ : A → ℝ := fun a => if 0 ≤ Real.exp (x a) / ∑ b, Real.exp (x b)
      - Real.exp (y a) / ∑ b, Real.exp (y b) then 1 else -1 with hσ
  set N : A → ℝ → ℝ := fun a t => Real.exp (y a + t * u a) with hN
  set Z : ℝ → ℝ := fun t => ∑ b, N b t with hZ
  have hZpos : ∀ t, 0 < Z t := fun t =>
    Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  have hNd : ∀ a t, HasDerivAt (N a) (N a t * u a) t := by
    intro a t
    have h1 : HasDerivAt (fun t : ℝ => y a + t * u a) (u a) t := by
      simpa using ((hasDerivAt_id t).mul_const (u a)).const_add (y a)
    exact h1.exp
  have hZd : ∀ t, HasDerivAt Z (∑ b, N b t * u b) t := fun t =>
    HasDerivAt.fun_sum (fun b _ => hNd b t)
  set f : ℝ → ℝ := fun t => ∑ a, σ a * (N a t / Z t) with hf
  set f' : ℝ → ℝ := fun t => ∑ a, σ a *
      ((N a t * u a * Z t - N a t * ∑ b, N b t * u b) / Z t ^ 2) with hf'
  have hfd : ∀ t, HasDerivAt f (f' t) t := fun t =>
    HasDerivAt.fun_sum (fun a _ => ((hNd a t).div (hZd t) (hZpos t).ne').const_mul (σ a))
  have hbound : ∀ t, |f' t| ≤ 2 * δ := by
    intro t
    have hZt := hZpos t
    set p : A → ℝ := fun a => N a t / Z t with hp
    have hp0 : ∀ a, 0 ≤ p a := fun a => div_nonneg (Real.exp_pos _).le hZt.le
    have hp1 : ∑ a, p a = 1 := by
      simp only [hp]; rw [← Finset.sum_div]; exact div_self hZt.ne'
    set ub := ∑ b, p b * u b with hub
    have hub_le : |ub| ≤ δ := by
      calc |ub| ≤ ∑ b, |p b * u b| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ b, p b * |u b| := by
            refine Finset.sum_congr rfl (fun b _ => ?_); rw [abs_mul, abs_of_nonneg (hp0 b)]
        _ ≤ ∑ b, p b * δ :=
            Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hu' b) (hp0 b))
        _ = δ := by rw [← Finset.sum_mul, hp1, one_mul]
    have hub' : ub = (∑ b, N b t * u b) / Z t := by
      rw [hub, Finset.sum_div]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      simp only [hp]; ring
    have he : ∀ a, (N a t * u a * Z t - N a t * ∑ b, N b t * u b) / Z t ^ 2
        = p a * (u a - ub) := by
      intro a
      rw [hub']
      simp only [hp]
      field_simp
    have hf'e : f' t = ∑ a, σ a * (p a * (u a - ub)) := by
      simp only [hf']
      exact Finset.sum_congr rfl (fun a _ => by rw [he a])
    rw [hf'e]
    calc |∑ a, σ a * (p a * (u a - ub))| ≤ ∑ a, |σ a * (p a * (u a - ub))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, p a * (2 * δ) := by
          apply Finset.sum_le_sum; intro a _
          have hs : |σ a| = 1 := by simp only [hσ]; split_ifs <;> simp
          rw [abs_mul, hs, one_mul, abs_mul, abs_of_nonneg (hp0 a)]
          apply mul_le_mul_of_nonneg_left _ (hp0 a)
          have h1 := abs_le.mp (hu' a)
          have h2 := abs_le.mp hub_le
          exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
      _ = 2 * δ := by rw [← Finset.sum_mul, hp1, one_mul]
  obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope f f' (zero_lt_one' ℝ)
    (fun t _ => (hfd t).continuousAt.continuousWithinAt) (fun t _ => hfd t)
  have e1 : ∀ a, y a + 1 * u a = x a := fun a => by simp only [hu]; ring
  have e0 : ∀ a, y a + 0 * u a = y a := fun a => by ring
  have h1 : f 1 - f 0 = ∑ a, |Real.exp (x a) / ∑ b, Real.exp (x b)
      - Real.exp (y a) / ∑ b, Real.exp (y b)| := by
    simp only [hf, hZ, hN, e1, e0]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [hσ]
    split_ifs with hh
    · rw [abs_of_nonneg hh]; ring
    · rw [abs_of_neg (not_le.mp hh)]; ring
  rw [← h1]
  have h2 : f 1 - f 0 = f' c := by rw [hc]; simp
  rw [h2]
  exact (le_abs_self _).trans (hbound c)

open PolicyGradTheory.Softmax in
theorem lbs_pol_l1 {S A : Type*} [Fintype A] [Nonempty A] (θ θ' : EuclideanSpace ℝ (S × A))
    (s : S) (δ : ℝ) (h : ∀ a, |θ (s, a) - θ' (s, a)| ≤ δ) :
    ∑ a, |softmaxPolicy θ s a - softmaxPolicy θ' s a| ≤ 2 * δ :=
  lbs_sm_l1 (fun a => θ (s, a)) (fun a => θ' (s, a)) δ h

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA in
theorem lbs_vis_val {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s0 : S) (x : S → ℝ) :
    ∑ s, visitation π P γ (fun z => if z = s0 then 1 else 0) s * x s =
      (1 - γ) * PolicyValue π P (fun s _ => x s) γ s0 := by
  simp_rw [pd_visit]
  unfold PolicyValue
  have hIR : ∀ s', InducedReward π (fun s _ => x s) s' = x s' := by
    intro s'; unfold InducedReward; rw [← Finset.sum_mul, (hπ s').2, one_mul]
  simp_rw [hIR]
  have hsum := fun s => sg_occ_summable π hπ P hP γ hγ0 hγ1 s0 s
  calc ∑ s, (1 - γ) * (∑' t : ℕ, γ ^ t * OccupationDist π P s0 t s) * x s
      = (1 - γ) * ∑ s, ∑' t : ℕ, γ ^ t * OccupationDist π P s0 t s * x s := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [tsum_mul_right]; ring
    _ = (1 - γ) * ∑' t : ℕ, ∑ s, γ ^ t * OccupationDist π P s0 t s * x s := by
        rw [← Summable.tsum_finsetSum (fun s _ => (hsum s).mul_right _)]
    _ = _ := by
        congr 1
        refine tsum_congr (fun t => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        ring

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA in
theorem lbs_vis_one {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s0 : S) :
    ∑ s, visitation π P γ (fun z => if z = s0 then 1 else 0) s = 1 := by
  have h := lbs_vis_val π hπ P hP γ hγ0 hγ1 s0 (fun _ => 1)
  simp only [mul_one] at h
  rw [h]
  unfold PolicyValue
  have hIR : ∀ s', InducedReward π (fun _ _ => (1:ℝ)) s' = 1 := by
    intro s'; unfold InducedReward; simp [(hπ s').2]
  have hD : ∀ t, ∑ s, OccupationDist π P s0 t s = 1 := fun t => (rl_D_prob π hπ P hP s0 t).2
  simp_rw [hIR, mul_one, hD, mul_one]
  rw [tsum_geometric_of_lt_one hγ0 hγ1, mul_inv_cancel₀ (by linarith : (1:ℝ) - γ ≠ 0)]

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA in
theorem lbs_vis_mu_val {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (μ : S → ℝ) (x : S → ℝ) :
    ∑ s, visitation π P γ μ s * x s =
      ∑ s0, μ s0 * ((1 - γ) * PolicyValue π P (fun s _ => x s) γ s0) := by
  simp_rw [sg_vis_lin π hπ P hP γ hγ0 hγ1 μ, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s0 _ => ?_)
  rw [← lbs_vis_val π hπ P hP γ hγ0 hγ1 s0 x, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  ring

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA in
theorem lbs_vis_mu_one {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (μ : S → ℝ) (hμ : IsDist μ) :
    ∑ s, visitation π P γ μ s = 1 := by
  simp_rw [sg_vis_lin π hπ P hP γ hγ0 hγ1 μ]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, lbs_vis_one π hπ P hP γ hγ0 hγ1, mul_one]
  exact hμ.2

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA in
theorem lbs_dV {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (ε : ℝ)
    (hε : ∀ s, ∑ a, |π s a - π' s a| ≤ ε) (s0 : S) :
    |PolicyValue π P r γ s0 - PolicyValue π' P r γ s0| ≤ ε / 2 * (1 / (1 - γ)) ^ 2 := by
  obtain ⟨hP, hr, hγ0, hγ1⟩ := hM
  have hne : 0 < 1 - γ := by linarith
  have hR0 : (0:ℝ) ≤ 1 / (1 - γ) := by positivity
  rw [pd_main P r γ ⟨hP, hr, hγ0, hγ1⟩ π π' hπ hπ' s0]
  have hX : ∀ s, |∑ a, π s a * advantage π' P r γ s a| ≤ ε * (1 / (1 - γ) / 2) := by
    intro s
    have hv := rl_VQ π' hπ' P hP r γ hγ0 hγ1 s
    have e : ∑ a, π s a * advantage π' P r γ s a =
        ∑ a, (π s a - π' s a) * (QFunction π' P r γ s a - 1 / (1 - γ) / 2) := by
      unfold advantage
      have h3 : ∀ a, π s a * (QFunction π' P r γ s a - PolicyValue π' P r γ s) =
          (π s a - π' s a) * (QFunction π' P r γ s a - 1 / (1 - γ) / 2) +
          (π' s a * QFunction π' P r γ s a + (1 / (1 - γ) / 2) * π s a
            - (1 / (1 - γ) / 2) * π' s a - π s a * PolicyValue π' P r γ s) := by
        intro a; ring
      rw [Finset.sum_congr rfl (fun a _ => h3 a), Finset.sum_add_distrib]
      have hz : ∑ a, (π' s a * QFunction π' P r γ s a + (1 / (1 - γ) / 2) * π s a
            - (1 / (1 - γ) / 2) * π' s a - π s a * PolicyValue π' P r γ s) = 0 := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul, (hπ s).2, (hπ' s).2, ← hv]
        ring
      rw [hz, add_zero]
    rw [e]
    calc |∑ a, (π s a - π' s a) * (QFunction π' P r γ s a - 1 / (1 - γ) / 2)|
        ≤ ∑ a, |π s a - π' s a| * (1 / (1 - γ) / 2) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun a _ => ?_))
          rw [abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          have hq := pg_Q_bounds P r γ ⟨hP, hr, hγ0, hγ1⟩ π' hπ' s a
          rw [abs_le]; constructor <;> linarith [hq.1, hq.2]
      _ ≤ ε * (1 / (1 - γ) / 2) := by
          rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hε s) (by positivity)
  have hd := fun s => pg_vis_point π hπ P hP γ hγ0 hγ1 s0 s
  have hd1 := lbs_vis_one π hπ P hP γ hγ0 hγ1 s0
  have hs : |∑ s, visitation π P γ (fun x => if x = s0 then 1 else 0) s *
      ∑ a, π s a * advantage π' P r γ s a| ≤ ε * (1 / (1 - γ) / 2) := by
    calc _ ≤ ∑ s, |visitation π P γ (fun x => if x = s0 then 1 else 0) s *
          ∑ a, π s a * advantage π' P r γ s a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s, visitation π P γ (fun x => if x = s0 then 1 else 0) s *
          (ε * (1 / (1 - γ) / 2)) := by
          refine Finset.sum_le_sum (fun s _ => ?_)
          rw [abs_mul, abs_of_nonneg (hd s).1]
          exact mul_le_mul_of_nonneg_left (hX s) (hd s).1
      _ = ε * (1 / (1 - γ) / 2) := by rw [← Finset.sum_mul, hd1, one_mul]
  rw [abs_mul, abs_of_nonneg hR0]
  calc 1 / (1 - γ) * |∑ s, visitation π P γ (fun x => if x = s0 then 1 else 0) s *
      ∑ a, π s a * advantage π' P r γ s a| ≤ 1 / (1 - γ) * (ε * (1 / (1 - γ) / 2)) :=
        mul_le_mul_of_nonneg_left hs hR0
    _ = ε / 2 * (1 / (1 - γ)) ^ 2 := by ring

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA in
theorem lbs_dQ {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (ε : ℝ)
    (hε : ∀ s, ∑ a, |π s a - π' s a| ≤ ε) (s : S) (a : A) :
    |QFunction π P r γ s a - QFunction π' P r γ s a| ≤ γ * (ε / 2 * (1 / (1 - γ)) ^ 2) := by
  have hP := hM.1
  have hγ0 := hM.2.2.1
  unfold QFunction
  have e : r s a + γ * ∑ s', P s a s' * PolicyValue π P r γ s'
      - (r s a + γ * ∑ s', P s a s' * PolicyValue π' P r γ s') =
      γ * ∑ s', P s a s' * (PolicyValue π P r γ s' - PolicyValue π' P r γ s') := by
    rw [show ∀ x y z : ℝ, z + γ * x - (z + γ * y) = γ * (x - y) from fun x y z => by ring,
      ← Finset.sum_sub_distrib]
    simp only [mul_sub]
  rw [e, abs_mul, abs_of_nonneg hγ0]
  apply mul_le_mul_of_nonneg_left _ hγ0
  calc |∑ s', P s a s' * (PolicyValue π P r γ s' - PolicyValue π' P r γ s')|
      ≤ ∑ s', |P s a s' * (PolicyValue π P r γ s' - PolicyValue π' P r γ s')| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', P s a s' * (ε / 2 * (1 / (1 - γ)) ^ 2) := by
        refine Finset.sum_le_sum (fun s' _ => ?_)
        rw [abs_mul, abs_of_nonneg ((hP s a).1 s')]
        exact mul_le_mul_of_nonneg_left (lbs_dV P r γ hM π π' hπ hπ' ε hε s') ((hP s a).1 s')
    _ = ε / 2 * (1 / (1 - γ)) ^ 2 := by rw [← Finset.sum_mul, (hP s a).2, one_mul]

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA in
theorem lbs_dvis {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (ε : ℝ)
    (hε : ∀ s, ∑ a, |π s a - π' s a| ≤ ε) (μ : S → ℝ) (hμ : IsDist μ) :
    ∑ s, |visitation π P γ μ s - visitation π' P γ μ s| ≤
      2 * (1 - γ) * (ε / 2 * (1 / (1 - γ)) ^ 2) := by
  obtain ⟨hP, hr, hγ0, hγ1⟩ := hM
  set T : S → ℝ := fun s => if visitation π' P γ μ s ≤ visitation π P γ μ s then 1 else 0 with hT
  have habs : ∀ s, |visitation π P γ μ s - visitation π' P γ μ s| =
      2 * (T s * visitation π P γ μ s - T s * visitation π' P γ μ s)
        - (visitation π P γ μ s - visitation π' P γ μ s) := by
    intro s
    simp only [hT]
    split_ifs with hh
    · rw [abs_of_nonneg (by linarith)]; ring
    · rw [abs_of_neg (by linarith)]; ring
  have hMT : IsFiniteMDP P (fun s _ => T s) γ := by
    refine ⟨hP, fun s _ => ?_, hγ0, hγ1⟩
    simp only [hT]; split_ifs <;> norm_num
  have h1 := lbs_vis_mu_val π hπ P hP γ hγ0 hγ1 μ T
  have h2 := lbs_vis_mu_val π' hπ' P hP γ hγ0 hγ1 μ T
  have hsum0 : ∑ s, visitation π P γ μ s - ∑ s, visitation π' P γ μ s = 0 := by
    rw [lbs_vis_mu_one π hπ P hP γ hγ0 hγ1 μ hμ, lbs_vis_mu_one π' hπ' P hP γ hγ0 hγ1 μ hμ]
    ring
  have hTsum : ∑ s, (T s * visitation π P γ μ s - T s * visitation π' P γ μ s) ≤
      (1 - γ) * (ε / 2 * (1 / (1 - γ)) ^ 2) := by
    have e : ∑ s, (T s * visitation π P γ μ s - T s * visitation π' P γ μ s) =
        ∑ s, visitation π P γ μ s * T s - ∑ s, visitation π' P γ μ s * T s := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun s _ => ?_); ring
    rw [e, h1, h2, ← Finset.sum_sub_distrib]
    calc ∑ s0, (μ s0 * ((1 - γ) * PolicyValue π P (fun s _ => T s) γ s0)
          - μ s0 * ((1 - γ) * PolicyValue π' P (fun s _ => T s) γ s0))
        = ∑ s0, μ s0 * ((1 - γ) * (PolicyValue π P (fun s _ => T s) γ s0
            - PolicyValue π' P (fun s _ => T s) γ s0)) := by
          refine Finset.sum_congr rfl (fun s0 _ => ?_); ring
      _ ≤ ∑ s0, μ s0 * ((1 - γ) * (ε / 2 * (1 / (1 - γ)) ^ 2)) := by
          refine Finset.sum_le_sum (fun s0 _ => mul_le_mul_of_nonneg_left ?_ (hμ.1 s0))
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact (le_abs_self _).trans (lbs_dV P (fun s _ => T s) γ hMT π π' hπ hπ' ε hε s0)
      _ = (1 - γ) * (ε / 2 * (1 / (1 - γ)) ^ 2) := by rw [← Finset.sum_mul, hμ.2, one_mul]
  rw [Finset.sum_congr rfl (fun s _ => habs s), Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hz : ∑ s, (visitation π P γ μ s - visitation π' P γ μ s) = 0 := by
    rw [Finset.sum_sub_distrib]; exact hsum0
  rw [hz]
  linarith

set_option maxHeartbeats 1000000 in
open FoundationsML.ReinforcementLearning PolicyGradTheory.Softmax PolicyGradTheory.ProjGA in
theorem lbs_gV {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ)
    (μ : S → ℝ) (hμ : IsDist μ) (θ θ' : EuclideanSpace ℝ (S × A)) (δ m : ℝ)
    (hδ0 : 0 ≤ δ) (hm0 : 0 ≤ m)
    (hδ : ∀ i, |θ i - θ' i| ≤ δ) (w : S × A → ℝ) (hw : ∀ i, |w i| ≤ m) :
    ∑ i : S × A, (gradient (softmaxValue P r γ μ) θ i - gradient (softmaxValue P r γ μ) θ' i) * w i
      ≤ 8 / (1 - γ) ^ 3 * δ * m := by
  have hM' := hM
  obtain ⟨hP, hr, hγ0, hγ1⟩ := hM'
  have hne : 0 < 1 - γ := by linarith
  set R : ℝ := 1 / (1 - γ) with hR
  have hR0 : 0 ≤ R := by positivity
  have hK : (1 - γ) * R = 1 := by rw [hR]; field_simp
  have hR1 : 1 ≤ R := by rw [hR, le_div_iff₀ hne]; linarith
  set π := softmaxPolicy θ with hπdef
  set π' := softmaxPolicy θ' with hπ'def
  have hπ : IsPolicy π := sg_policy θ
  have hπ' : IsPolicy π' := sg_policy θ'
  set d := visitation π P γ μ with hd
  set d' := visitation π' P γ μ with hd'
  set Ad := advantage π P r γ with hAd
  set Ad' := advantage π' P r γ with hAd'
  have hε : ∀ s, ∑ a, |π s a - π' s a| ≤ 2 * δ := fun s =>
    lbs_pol_l1 θ θ' s δ (fun a => hδ (s, a))
  set B : ℝ := 2 * δ / 2 * R ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  set φ : S → ℝ := fun s => ∑ a, π s a * Ad s a * w (s, a) with hφ
  set φ' : S → ℝ := fun s => ∑ a, π' s a * Ad' s a * w (s, a) with hφ'
  have hrow : ∀ s, ∑ a, (gradient (softmaxValue P r γ μ) θ (s, a)
      - gradient (softmaxValue P r γ μ) θ' (s, a)) * w (s, a) =
      R * ((d s - d' s) * φ s + d' s * (φ s - φ' s)) := by
    intro s
    simp_rw [sg_grad P r γ hM μ θ s, sg_grad P r γ hM μ θ' s]
    simp only [hφ, hφ']
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hR]; ring
  -- per-state bounds
  have hAb : ∀ s a, |Ad s a| ≤ R := fun s a => pg_adv_bound P r γ hM π hπ s a
  have hφb : ∀ s, |φ s| ≤ R * m := by
    intro s
    calc |φ s| ≤ ∑ a, |π s a * Ad s a * w (s, a)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, π s a * (R * m) := by
          refine Finset.sum_le_sum (fun a _ => ?_)
          rw [abs_mul, abs_mul, abs_of_nonneg ((hπ s).1 a), mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul (hAb s a) (hw _) (abs_nonneg _) hR0) ((hπ s).1 a)
      _ = R * m := by rw [← Finset.sum_mul, (hπ s).2, one_mul]
  have hdA : ∀ s a, |Ad s a - Ad' s a| ≤ (1 + γ) * B := by
    intro s a
    have hq := lbs_dQ P r γ hM π π' hπ hπ' (2 * δ) hε s a
    have hv := lbs_dV P r γ hM π π' hπ hπ' (2 * δ) hε s
    simp only [hAd, hAd', advantage]
    have e : QFunction π P r γ s a - PolicyValue π P r γ s - (QFunction π' P r γ s a
        - PolicyValue π' P r γ s) = (QFunction π P r γ s a - QFunction π' P r γ s a)
        - (PolicyValue π P r γ s - PolicyValue π' P r γ s) := by ring
    rw [e]
    calc _ ≤ |QFunction π P r γ s a - QFunction π' P r γ s a|
          + |PolicyValue π P r γ s - PolicyValue π' P r γ s| := abs_sub _ _
      _ ≤ γ * B + B := add_le_add hq hv
      _ = (1 + γ) * B := by ring
  have hdφ : ∀ s, |φ s - φ' s| ≤ m * (2 * δ * R + (1 + γ) * B) := by
    intro s
    have e : φ s - φ' s = ∑ a, ((π s a - π' s a) * Ad s a + π' s a * (Ad s a - Ad' s a))
        * w (s, a) := by
      simp only [hφ, hφ']
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_); ring
    rw [e]
    calc _ ≤ ∑ a, |((π s a - π' s a) * Ad s a + π' s a * (Ad s a - Ad' s a)) * w (s, a)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, (|π s a - π' s a| * R + π' s a * ((1 + γ) * B)) * m := by
          refine Finset.sum_le_sum (fun a _ => ?_)
          rw [abs_mul]
          apply mul_le_mul _ (hw _) (abs_nonneg _) (by
            have := (hπ' s).1 a; positivity)
          calc _ ≤ |(π s a - π' s a) * Ad s a| + |π' s a * (Ad s a - Ad' s a)| := abs_add_le _ _
            _ ≤ _ := by
              rw [abs_mul, abs_mul, abs_of_nonneg ((hπ' s).1 a)]
              exact add_le_add (mul_le_mul_of_nonneg_left (hAb s a) (abs_nonneg _))
                (mul_le_mul_of_nonneg_left (hdA s a) ((hπ' s).1 a))
      _ = m * ((∑ a, |π s a - π' s a|) * R + (1 + γ) * B) := by
          rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
            (hπ' s).2]; ring
      _ ≤ m * (2 * δ * R + (1 + γ) * B) := by
          apply mul_le_mul_of_nonneg_left _ hm0
          have := mul_le_mul_of_nonneg_right (hε s) hR0
          linarith
  have hdd := lbs_dvis P r γ hM π π' hπ hπ' (2 * δ) hε μ hμ
  have hd'0 : ∀ s, 0 ≤ d' s := fun s => (pg_vis_mu π' hπ' P hP γ hγ0 hγ1 μ hμ s).1.trans' (by
    have := hμ.1 s; positivity)
  have hd'1 := lbs_vis_mu_one π' hπ' P hP γ hγ0 hγ1 μ hμ
  rw [Fintype.sum_prod_type]
  simp_rw [hrow]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have t1 : ∑ s, (d s - d' s) * φ s ≤ 2 * (1 - γ) * B * (R * m) := by
    calc _ ≤ ∑ s, |(d s - d' s) * φ s| := (Finset.abs_sum_le_sum_abs _ _).trans' (le_abs_self _)
      _ ≤ ∑ s, |d s - d' s| * (R * m) := by
          refine Finset.sum_le_sum (fun s _ => ?_)
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hφb s) (abs_nonneg _)
      _ = (∑ s, |d s - d' s|) * (R * m) := by rw [Finset.sum_mul]
      _ ≤ 2 * (1 - γ) * B * (R * m) := mul_le_mul_of_nonneg_right hdd (by positivity)
  have t2 : ∑ s, d' s * (φ s - φ' s) ≤ m * (2 * δ * R + (1 + γ) * B) := by
    calc _ ≤ ∑ s, d' s * (m * (2 * δ * R + (1 + γ) * B)) := by
          refine Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left ?_ (hd'0 s))
          exact (le_abs_self _).trans (hdφ s)
      _ = m * (2 * δ * R + (1 + γ) * B) := by rw [← Finset.sum_mul, hd'1, one_mul]
  have hR3 : 8 / (1 - γ) ^ 3 = 8 * R ^ 3 := by rw [hR]; field_simp
  rw [hR3]
  calc R * (∑ s, (d s - d' s) * φ s + ∑ s, d' s * (φ s - φ' s))
      ≤ R * (2 * (1 - γ) * B * (R * m) + m * (2 * δ * R + (1 + γ) * B)) :=
        mul_le_mul_of_nonneg_left (add_le_add t1 t2) hR0
    _ = δ * m * (2 * ((1 - γ) * R) * R ^ 3 + 2 * R ^ 2 + (1 + γ) * R ^ 3) := by
        rw [hB]; ring
    _ = δ * m * (2 * R ^ 3 + 2 * R ^ 2 + (1 + γ) * R ^ 3) := by rw [hK]; ring
    _ ≤ δ * m * (8 * R ^ 3) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h3 : R ^ 2 ≤ R ^ 3 := by
          have := mul_le_mul_of_nonneg_left hR1 (sq_nonneg R)
          nlinarith
        have h4 : (1 + γ) * R ^ 3 ≤ 2 * R ^ 3 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        nlinarith [pow_nonneg hR0 3]
    _ = 8 * R ^ 3 * δ * m := by ring

open FoundationsML.ReinforcementLearning PolicyGradTheory.Softmax PolicyGradTheory.ProjGA PolicyGradTheory.LogBarrier in
theorem lbs_grad {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ)
    (μ : S → ℝ) (lam : ℝ) (θ : EuclideanSpace ℝ (S × A)) (s0 : S) (a0 : A) :
    gradient (logBarrierObj P r γ μ lam) θ (s0, a0) =
      gradient (softmaxValue P r γ μ) θ (s0, a0) +
        lam / ((Fintype.card S : ℝ) * (Fintype.card A : ℝ)) *
          (1 - (Fintype.card A : ℝ) * softmaxPolicy θ s0 a0) := by
  have hpos : ∀ s a, 0 < softmaxPolicy θ s a := fun s a => div_pos (Real.exp_pos _) (sg_Z_pos θ s)
  have hlog : ∀ s a, HasFDerivAt (fun θ' : EuclideanSpace ℝ (S × A) =>
      Real.log (softmaxPolicy θ' s a)) ((softmaxPolicy θ s a)⁻¹ • sgD θ s a) θ :=
    fun s a => (sg_hasFDeriv θ s a).log (hpos s a).ne'
  have hsum : HasFDerivAt (fun θ' : EuclideanSpace ℝ (S × A) =>
      ∑ s, ∑ a, Real.log (softmaxPolicy θ' s a))
      (∑ s, ∑ a, (softmaxPolicy θ s a)⁻¹ • sgD θ s a) θ :=
    HasFDerivAt.fun_sum (fun s _ => HasFDerivAt.fun_sum (fun a _ => hlog s a))
  have hV := (lb_sv_diff P r γ hM μ θ).hasFDerivAt
  have hL : HasFDerivAt (logBarrierObj P r γ μ lam)
      (fderiv ℝ (softmaxValue P r γ μ) θ +
        (lam / ((Fintype.card S : ℝ) * (Fintype.card A : ℝ))) •
          ∑ s, ∑ a, (softmaxPolicy θ s a)⁻¹ • sgD θ s a) θ :=
    (hV.add (hsum.const_mul (lam / ((Fintype.card S : ℝ) * (Fintype.card A : ℝ))))).add_const
      (lam * Real.log (Fintype.card A : ℝ))
  have key : ∑ s, ∑ a, (softmaxPolicy θ s a)⁻¹ * sgD θ s a (EuclideanSpace.single (s0, a0) 1)
      = 1 - (Fintype.card A : ℝ) * softmaxPolicy θ s0 a0 := by
    simp_rw [sg_D_single]
    rw [Finset.sum_eq_single s0 (fun s _ hs => by simp [hs])
      (fun h => absurd (Finset.mem_univ s0) h)]
    simp only [if_true]
    have e : ∀ a, (softmaxPolicy θ s0 a)⁻¹ * (softmaxPolicy θ s0 a *
        ((if a = a0 then 1 else 0) - softmaxPolicy θ s0 a0)) =
        (if a = a0 then 1 else 0) - softmaxPolicy θ s0 a0 := fun a => by
      rw [← mul_assoc, inv_mul_cancel₀ (hpos s0 a).ne', one_mul]
    simp_rw [e]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ a0]
    simp
  unfold gradient
  rw [hL.fderiv, sg_coord, sg_coord, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.sum_apply]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [key]

theorem lbs_sq_le {ι : Type*} [Fintype ι] (y : ι → ℝ) :
    ∑ i, y i ^ 2 ≤ (∑ i, |y i|) ^ 2 := by
  calc ∑ i, y i ^ 2 = ∑ i, |y i| * |y i| := by
        refine Finset.sum_congr rfl (fun i _ => ?_); rw [← sq, sq_abs]
    _ ≤ ∑ i, |y i| * ∑ j, |y j| := by
        refine Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
        exact Finset.single_le_sum (f := fun j => |y j|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ i)
    _ = (∑ i, |y i|) ^ 2 := by rw [← Finset.sum_mul, sq]

open PolicyGradTheory.Softmax in
theorem lbs_dpi_sq {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (θ θ' : EuclideanSpace ℝ (S × A)) :
    ∑ i : S × A, (softmaxPolicy θ i.1 i.2 - softmaxPolicy θ' i.1 i.2) ^ 2 ≤ 4 * ‖θ - θ'‖ ^ 2 := by
  have hn : ‖θ - θ'‖ ^ 2 = ∑ i : S × A, (θ i - θ' i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Real.norm_eq_abs, sq_abs, PiLp.sub_apply]
  rw [hn, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_le_sum (fun s _ => ?_)
  set δs := Real.sqrt (∑ a, (θ (s, a) - θ' (s, a)) ^ 2) with hδs
  have hδ : ∀ a, |θ (s, a) - θ' (s, a)| ≤ δs := fun a => Real.abs_le_sqrt
    (Finset.single_le_sum (f := fun b => (θ (s, b) - θ' (s, b)) ^ 2)
      (fun b _ => sq_nonneg _) (Finset.mem_univ a))
  have hδ0 : 0 ≤ δs := Real.sqrt_nonneg _
  have h1 := lbs_pol_l1 θ θ' s δs hδ
  calc ∑ a, (softmaxPolicy θ s a - softmaxPolicy θ' s a) ^ 2
      ≤ (∑ a, |softmaxPolicy θ s a - softmaxPolicy θ' s a|) ^ 2 := lbs_sq_le _
    _ ≤ (2 * δs) ^ 2 := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) h1 2
    _ = 4 * ∑ a, (θ (s, a) - θ' (s, a)) ^ 2 := by
        rw [mul_pow, hδs, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]; norm_num

open FoundationsML.ReinforcementLearning PolicyGradTheory.Softmax PolicyGradTheory.ProjGA PolicyGradTheory.LogBarrier in
theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ) (μ : S → ℝ) (hμ : PolicyGradTheory.ProjGA.IsDist μ) (lam : ℝ) (hlam : 0 ≤ lam)
    (θ θ' : EuclideanSpace ℝ (S × A)) :
    ‖gradient (logBarrierObj P r γ μ lam) θ - gradient (logBarrierObj P r γ μ lam) θ'‖ ≤
      betaLam S γ lam * ‖θ - θ'‖ := by
  set v := gradient (logBarrierObj P r γ μ lam) θ - gradient (logBarrierObj P r γ μ lam) θ'
    with hv
  set δ := ‖θ - θ'‖ with hδ
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hθi : ∀ i, |θ i - θ' i| ≤ δ := fun i => by
    have := PiLp.norm_apply_le (θ - θ') i
    simpa [Real.norm_eq_abs] using this
  have hvi : ∀ i, |v i| ≤ ‖v‖ := fun i => by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v i
  have hA : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcA : lam / ((Fintype.card S : ℝ) * (Fintype.card A : ℝ)) * (Fintype.card A : ℝ) =
      lam / (Fintype.card S : ℝ) := by
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hA]
  set c := lam / (Fintype.card S : ℝ) with hc
  have hc0 : 0 ≤ c := by positivity
  have hcoord : ∀ i : S × A, v i = (gradient (softmaxValue P r γ μ) θ i
      - gradient (softmaxValue P r γ μ) θ' i)
      + c * (-(softmaxPolicy θ i.1 i.2 - softmaxPolicy θ' i.1 i.2)) := by
    rintro ⟨s, a⟩
    rw [hv, PiLp.sub_apply, lbs_grad P r γ hM μ lam θ s a, lbs_grad P r γ hM μ lam θ' s a, ← hcA]
    ring
  have hnv : ‖v‖ ^ 2 = ∑ i, v i * v i := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Real.norm_eq_abs, sq_abs, sq]
  have hnv' : Real.sqrt (∑ i, v i ^ 2) = ‖v‖ := by
    rw [← Real.sqrt_sq (norm_nonneg v), EuclideanSpace.norm_sq_eq]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Real.norm_eq_abs, sq_abs]
  have b1 := lbs_gV P r γ hM μ hμ θ θ' δ ‖v‖ hδ0 (norm_nonneg v) hθi v hvi
  have b2 : ∑ i : S × A, (-(softmaxPolicy θ i.1 i.2 - softmaxPolicy θ' i.1 i.2)) * v i
      ≤ 2 * δ * ‖v‖ := by
    calc _ ≤ Real.sqrt (∑ i : S × A, (-(softmaxPolicy θ i.1 i.2 - softmaxPolicy θ' i.1 i.2)) ^ 2)
          * Real.sqrt (∑ i, v i ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ (2 * δ) * ‖v‖ := by
          rw [hnv']
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
          rw [show (2 * δ) = Real.sqrt ((2 * δ) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
          apply Real.sqrt_le_sqrt
          simp_rw [neg_sq]
          have := lbs_dpi_sq θ θ'
          rw [mul_pow]; norm_num; linarith
  have hmain : ‖v‖ ^ 2 ≤ betaLam S γ lam * δ * ‖v‖ := by
    rw [hnv]
    have e : ∑ i : S × A, v i * v i =
        ∑ i : S × A, (gradient (softmaxValue P r γ μ) θ i
          - gradient (softmaxValue P r γ μ) θ' i) * v i
        + c * ∑ i : S × A, (-(softmaxPolicy θ i.1 i.2 - softmaxPolicy θ' i.1 i.2)) * v i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      nth_rewrite 1 [hcoord i]
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left b2 hc0
    unfold betaLam
    rw [hc] at this
    have e2 : (8 / (1 - γ) ^ 3 + 2 * lam / (Fintype.card S : ℝ)) * δ * ‖v‖ =
        8 / (1 - γ) ^ 3 * δ * ‖v‖ + lam / (Fintype.card S : ℝ) * (2 * δ * ‖v‖) := by ring
    rw [e2]
    linarith
  rcases (norm_nonneg v).eq_or_lt with h0 | hpos
  · rw [← h0]
    have : 0 ≤ betaLam S γ lam := by
      unfold betaLam
      have hne : 0 < 1 - γ := by linarith [hM.2.2.2]
      positivity
    positivity
  · have : ‖v‖ * ‖v‖ ≤ (betaLam S γ lam * δ) * ‖v‖ := by nlinarith
    exact le_of_mul_le_mul_right this hpos
