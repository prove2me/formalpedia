-- Prove2me | solution 1 for PolicyGradTheory.Softmax.softmax_pg_global_convergence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-18T05:12:13.151795+00:00
-- url     : https://prove2.me/submissions/def2590c-5911-4d6a-b5cb-efd134361a34

import Mathlib
import Definitions.Def_PolicyGradTheory_Softmax_Algorithm
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy

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


open Filter Topology in
theorem pg_abs_contra {A : Type*} [Fintype A] [DecidableEq A]
    (x : ℕ → A → ℝ) (p u : ℕ → A → ℝ) (c : ℕ → ℝ) (K δ : ℝ) (b : A) (T : ℕ)
    (hp : ∀ t a, p t a = Real.exp (x t a) / ∑ a', Real.exp (x t a'))
    (hstep : ∀ t a, x (t + 1) a = x t a + c t * (p t a * u t a))
    (hc : ∀ t, 0 ≤ c t)
    (hsum : ∀ t, ∑ a, p t a * u t a = 0)
    (hK : ∀ t a, |u t a| ≤ K)
    (hδ : 0 < δ) (hb : ∀ t, T ≤ t → δ ≤ u t b)
    (hlim : Tendsto (fun t => p t b) atTop (𝓝 0)) : False := by
  classical
  have hAne : (Finset.univ : Finset A).Nonempty := ⟨b, Finset.mem_univ b⟩
  set N : ℕ := Fintype.card A with hN
  have hN1 : (1:ℝ) ≤ N := by
    have : 0 < Fintype.card A := Finset.card_pos.mpr hAne
    exact_mod_cast this
  have hKpos : δ ≤ K := (hb T le_rfl).trans ((le_abs_self _).trans (hK T b))
  have hK0 : 0 < K := hδ.trans_le hKpos
  set ε : ℝ := δ / (2 * N * K) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε < 1 := by
    rw [hε, div_lt_one (by positivity)]; nlinarith
  set L : ℝ := Real.log ε with hL
  have hexpL : Real.exp L = ε := Real.exp_log hε0
  have hL0 : L < 0 := Real.log_neg hε0 hε1
  set D : ℕ → A → ℝ := fun t a => x t a - x t b with hD
  have hZ : ∀ t, 0 < ∑ a', Real.exp (x t a') := fun t =>
    Finset.sum_pos (fun _ _ => Real.exp_pos _) hAne
  have hpb : ∀ t, 0 < p t b := fun t => by rw [hp]; exact div_pos (Real.exp_pos _) (hZ t)
  have hpa : ∀ t a, p t a = p t b * Real.exp (D t a) := by
    intro t a
    rw [hp, hp, div_mul_eq_mul_div, ← Real.exp_add]
    congr 2
    simp only [hD]
    ring
  have hpnn : ∀ t a, 0 ≤ p t a := fun t a => by
    rw [hpa]; exact mul_nonneg (hpb t).le (Real.exp_pos _).le
  have hpsum : ∀ t, ∑ a, p t a = 1 := by
    intro t; simp_rw [hp]; rw [← Finset.sum_div]; exact div_self (hZ t).ne'
  have hsmall : ∀ t a, D t a ≤ L → p t a * K ≤ p t b * (δ / (2 * N)) := by
    intro t a h
    rw [hpa]
    have h1 : Real.exp (D t a) ≤ ε := hexpL ▸ Real.exp_le_exp.mpr h
    calc p t b * Real.exp (D t a) * K ≤ p t b * ε * K := by
          have := (hpb t).le
          gcongr
      _ = p t b * (δ / (2 * N)) := by
          rw [hε]; field_simp
  have hinv : ∀ t a, T ≤ t → D t a ≤ L → D (t + 1) a ≤ D t a := by
    intro t a ht h
    have h1 : p t a * u t a ≤ p t b * u t b := by
      have h2 := hsmall t a h
      have hu : u t a ≤ K := (le_abs_self _).trans (hK t a)
      have hδ2 : δ / (2 * N) ≤ u t b := by
        have : δ / (2 * N) ≤ δ := div_le_self hδ.le (by linarith)
        linarith [hb t ht]
      calc p t a * u t a ≤ p t a * K := mul_le_mul_of_nonneg_left hu (hpnn t a)
        _ ≤ p t b * (δ / (2 * N)) := h2
        _ ≤ p t b * u t b := mul_le_mul_of_nonneg_left hδ2 (hpb t).le
    have h3 := mul_le_mul_of_nonneg_left h1 (hc t)
    simp only [hD, hstep]
    linarith
  have hpers : ∀ a t0, T ≤ t0 → D t0 a ≤ L → ∀ t, t0 ≤ t → D t a ≤ L := by
    intro a t0 ht0 h t ht
    induction t, ht using Nat.le_induction with
    | base => exact h
    | succ n hn ih => exact (hinv n a (ht0.trans hn) ih).trans ih
  set B : Finset A := Finset.univ.filter (fun a => ∃ t0, T ≤ t0 ∧ D t0 a ≤ L) with hB
  set G : Finset A := Finset.univ \ B with hG
  have hmemG : ∀ a, a ∈ G ↔ a ∉ B := fun a => by simp [hG]
  have hev : ∀ᶠ t in atTop, ∀ a, a ∈ B → D t a ≤ L := by
    rw [Filter.eventually_all]
    intro a
    by_cases ha : a ∈ B
    · obtain ⟨t0, ht0, h0⟩ := (Finset.mem_filter.mp ha).2
      exact (eventually_ge_atTop t0).mono (fun t ht _ => hpers a t0 ht0 h0 t ht)
    · exact Eventually.of_forall (fun t h => absurd h ha)
  obtain ⟨T1, hT1⟩ := eventually_atTop.mp hev
  have hGbig : ∀ t a, T ≤ t → a ∉ B → L < D t a := by
    intro t a ht ha
    by_contra h
    have h := not_lt.mp h
    exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ht, h⟩)
  have hbG : b ∉ B := by
    intro h
    obtain ⟨t0, _, h0⟩ := (Finset.mem_filter.mp h).2
    simp only [hD, sub_self] at h0
    linarith
  set T2 := max T T1 with hT2
  have hS : ∀ t, T2 ≤ t → ∑ a ∈ G, D (t + 1) a ≤ ∑ a ∈ G, D t a := by
    intro t ht
    have htT : T ≤ t := le_trans (le_max_left _ _) ht
    have htT1 : T1 ≤ t := le_trans (le_max_right _ _) ht
    have hdiff : ∀ a, D (t + 1) a = D t a + c t * (p t a * u t a - p t b * u t b) := by
      intro a; simp only [hD, hstep]; ring
    simp_rw [hdiff]
    rw [Finset.sum_add_distrib]
    have htot : ∑ a ∈ G, p t a * u t a + ∑ a ∈ B, p t a * u t a = 0 := by
      rw [hG, Finset.sum_sdiff (Finset.subset_univ B)]; exact hsum t
    have hBb : -∑ a ∈ B, p t a * u t a ≤ p t b * (δ / 2) := by
      have hterm : ∀ a ∈ B, -(p t a * u t a) ≤ p t b * (δ / (2 * N)) := by
        intro a ha
        have h1 := hsmall t a (hT1 t htT1 a ha)
        have hu : -u t a ≤ K := (neg_le_abs _).trans (hK t a)
        have h2 := mul_le_mul_of_nonneg_left hu (hpnn t a)
        linarith
      have hcard : (B.card : ℝ) ≤ N := by exact_mod_cast Finset.card_le_univ B
      have hnn : 0 ≤ p t b * (δ / (2 * N)) := by have := hpb t; positivity
      calc -∑ a ∈ B, p t a * u t a = ∑ a ∈ B, -(p t a * u t a) := by
            rw [Finset.sum_neg_distrib]
        _ ≤ ∑ a ∈ B, p t b * (δ / (2 * N)) := Finset.sum_le_sum hterm
        _ = B.card * (p t b * (δ / (2 * N))) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ N * (p t b * (δ / (2 * N))) := mul_le_mul_of_nonneg_right hcard hnn
        _ = p t b * (δ / 2) := by field_simp
    have hGb : p t b * δ ≤ ∑ a ∈ G, p t b * u t b := by
      have hbmem : b ∈ G := (hmemG b).mpr hbG
      have hub := hb t htT
      calc p t b * δ ≤ p t b * u t b := mul_le_mul_of_nonneg_left hub (hpb t).le
        _ ≤ ∑ a ∈ G, p t b * u t b :=
          Finset.single_le_sum (f := fun _ => p t b * u t b)
            (fun _ _ => mul_nonneg (hpb t).le (by linarith)) hbmem
    have hneg : ∑ a ∈ G, c t * (p t a * u t a - p t b * u t b) ≤ 0 := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      apply mul_nonpos_of_nonneg_of_nonpos (hc t)
      have hpbd := hpb t
      nlinarith
    linarith
  have hSle : ∀ t, T2 ≤ t → ∑ a ∈ G, D t a ≤ ∑ a ∈ G, D T2 a := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih => exact (hS n hn).trans ih
  set M : ℝ := ∑ a ∈ G, D T2 a - G.card * L + L with hM
  have hDG : ∀ t, T2 ≤ t → ∀ a ∈ G, D t a ≤ M := by
    intro t ht a ha
    have htT : T ≤ t := le_trans (le_max_left _ _) ht
    have hnn : ∀ a' ∈ G, 0 ≤ D t a' - L := fun a' ha' => by
      have := hGbig t a' htT ((hmemG a').mp ha'); linarith
    have h1 : D t a - L ≤ ∑ a' ∈ G, (D t a' - L) := Finset.single_le_sum hnn ha
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h1
    have := hSle t ht
    linarith
  set M' : ℝ := max M L with hM'
  have hall : ∀ t, T2 ≤ t → ∀ a, D t a ≤ M' := by
    intro t ht a
    by_cases ha : a ∈ B
    · exact (hT1 t (le_trans (le_max_right _ _) ht) a ha).trans (le_max_right _ _)
    · exact (hDG t ht a ((hmemG a).mpr ha)).trans (le_max_left _ _)
  have hlow : ∀ t, T2 ≤ t → 1 / (N * Real.exp M') ≤ p t b := by
    intro t ht
    have h1 : (1:ℝ) ≤ N * (p t b * Real.exp M') := by
      calc (1:ℝ) = ∑ a, p t a := (hpsum t).symm
        _ ≤ ∑ _a : A, p t b * Real.exp M' := Finset.sum_le_sum (fun a _ => by
            rw [hpa]
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hall t ht a)) (hpb t).le)
        _ = N * (p t b * Real.exp M') := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [div_le_iff₀ (by positivity)]
    have e : p t b * (↑N * Real.exp M') = ↑N * (p t b * Real.exp M') := by ring
    linarith
  have hpos : 0 < 1 / (N * Real.exp M') := by positivity
  obtain ⟨T3, hT3⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hpos))
  have h1 := hT3 (max T2 T3) (le_max_right _ _)
  have h2 := hlow (max T2 T3) (le_max_left _ _)
  linarith


open FoundationsML.ReinforcementLearning Filter Topology PolicyGradTheory.Softmax PolicyGradTheory.ProjGA in
theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (μ : S → ℝ) (hμ : PolicyGradTheory.ProjGA.IsDist μ) (η : ℝ) (hη : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (hrun : IsSoftmaxPGRun P r γ μ η θ)
    (hμpos : ∀ s, 0 < μ s) (hηle : η ≤ (1 - γ) ^ 3 / 8)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar) (hopt : IsOptimalPolicy πstar P r γ) :
    ∀ s, Tendsto (fun t => PolicyValue (softmaxPolicy (θ t)) P r γ s) atTop
      (𝓝 (PolicyValue πstar P r γ s)) := by
  classical
  have hP := hM.1
  have hγ0 := hM.2.2.1
  have hγ1 := hM.2.2.2
  have hg : 0 < 1 - γ := by linarith
  set K : ℝ := 1 / (1 - γ) with hK
  have hK0 : 0 ≤ K := by positivity
  have hpol : ∀ t, IsPolicy (softmaxPolicy (θ t)) := fun t => sg_policy (θ t)
  have hπle : ∀ t s a, softmaxPolicy (θ t) s a ≤ 1 := by
    intro t s a
    rw [← ((hpol t) s).2]
    exact Finset.single_le_sum (f := fun a => softmaxPolicy (θ t) s a)
      (fun a _ => ((hpol t) s).1 a) (Finset.mem_univ a)
  set c : ℕ → S → ℝ := fun t s =>
    η * (1 / (1 - γ) * visitation (softmaxPolicy (θ t)) P γ μ s) with hc
  have hstep : ∀ t s a, θ (t + 1) (s, a) = θ t (s, a) + c t s *
      (softmaxPolicy (θ t) s a * advantage (softmaxPolicy (θ t)) P r γ s a) := by
    intro t s a
    rw [hrun t, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, sg_grad P r γ hM μ (θ t) s a]
    simp only [hc]
    ring
  have hvis := fun t s => pg_vis_mu (softmaxPolicy (θ t)) (hpol t) P hP γ hγ0 hγ1 μ hμ s
  have hcmin : ∀ t s, η * μ s ≤ c t s := by
    intro t s
    simp only [hc]
    have h1 := (hvis t s).1
    have h2 : μ s ≤ 1 / (1 - γ) * visitation (softmaxPolicy (θ t)) P γ μ s := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hg]; linarith
    exact mul_le_mul_of_nonneg_left h2 hη.le
  have hc0 : ∀ t s, 0 ≤ c t s := fun t s =>
    le_trans (mul_nonneg hη.le (hμpos s).le) (hcmin t s)
  have hcmax : ∀ t s, c t s ≤ η * K := by
    intro t s
    simp only [hc, hK]
    have h1 := (hvis t s).2
    have h2 : 1 / (1 - γ) * visitation (softmaxPolicy (θ t)) P γ μ s ≤ 1 / (1 - γ) :=
      mul_le_of_le_one_right (by positivity) h1
    exact mul_le_mul_of_nonneg_left h2 hη.le
  have hgain := fun t s b => pg_gain_abs (fun a => θ t (s, a)) (fun a => θ (t + 1) (s, a))
    (fun a => softmaxPolicy (θ t) s a) (fun a => advantage (softmaxPolicy (θ t)) P r γ s a)
    (c t s) K (fun a => rfl) (fun a => hstep t s a) (hc0 t s)
    (sg_adv_zero _ (hpol t) P hP r γ hγ0 hγ1 s)
    (fun a => by
      have h1 := pg_adv_bound P r γ hM _ (hpol t) s a
      have h2 := ((hpol t) s).1 a
      have h3 := hπle t s a
      have h4 : advantage (softmaxPolicy (θ t)) P r γ s a ≤ K := (le_abs_self _).trans h1
      have h5 := abs_nonneg (advantage (softmaxPolicy (θ t)) P r γ s a)
      nlinarith) b
  have hX0 : ∀ t s, 0 ≤ ∑ a, softmaxPolicy (θ (t + 1)) s a *
      advantage (softmaxPolicy (θ t)) P r γ s a := fun t s =>
    (hgain t s (Classical.arbitrary A)).1
  have hX1 : ∀ t s b, 0 ≤ softmaxPolicy (θ t) s b * advantage (softmaxPolicy (θ t)) P r γ s b →
      c t s * (softmaxPolicy (θ t) s b * advantage (softmaxPolicy (θ t)) P r γ s b) ^ 2 /
        Real.exp (c t s * K) ≤
      ∑ a, softmaxPolicy (θ (t + 1)) s a * advantage (softmaxPolicy (θ t)) P r γ s a :=
    fun t s b => (hgain t s b).2
  have hpd := fun t s₀ => pd_main P r γ hM (softmaxPolicy (θ (t + 1))) (softmaxPolicy (θ t))
    (hpol _) (hpol _) s₀
  have hvp := fun t s₀ s => pg_vis_point (softmaxPolicy (θ (t + 1))) (hpol _) P hP γ hγ0 hγ1 s₀ s
  have hmono : ∀ t s, PolicyValue (softmaxPolicy (θ t)) P r γ s ≤
      PolicyValue (softmaxPolicy (θ (t + 1))) P r γ s := by
    intro t s
    have h := hpd t s
    have h1 : 0 ≤ 1 / (1 - γ) * ∑ s', visitation (softmaxPolicy (θ (t + 1))) P γ
        (fun x => if x = s then 1 else 0) s' *
        ∑ a, softmaxPolicy (θ (t + 1)) s' a * advantage (softmaxPolicy (θ t)) P r γ s' a :=
      mul_nonneg (by positivity) (Finset.sum_nonneg (fun s' _ =>
        mul_nonneg (hvp t s s').1 (hX0 t s')))
    linarith
  have hgainpt : ∀ t s, ∑ a, softmaxPolicy (θ (t + 1)) s a *
      advantage (softmaxPolicy (θ t)) P r γ s a ≤
      PolicyValue (softmaxPolicy (θ (t + 1))) P r γ s - PolicyValue (softmaxPolicy (θ t)) P r γ s := by
    intro t s
    rw [hpd t s]
    set X := fun s' => ∑ a, softmaxPolicy (θ (t + 1)) s' a * advantage (softmaxPolicy (θ t)) P r γ s' a
      with hXdef
    have h1 : visitation (softmaxPolicy (θ (t + 1))) P γ (fun x => if x = s then 1 else 0) s * X s ≤
        ∑ s', visitation (softmaxPolicy (θ (t + 1))) P γ (fun x => if x = s then 1 else 0) s' * X s' :=
      Finset.single_le_sum (f := fun s' => visitation (softmaxPolicy (θ (t + 1))) P γ
        (fun x => if x = s then 1 else 0) s' * X s')
        (fun s' _ => mul_nonneg (hvp t s s').1 (hX0 t s')) (Finset.mem_univ s)
    have h2 : (1 - γ) * X s ≤
        visitation (softmaxPolicy (θ (t + 1))) P γ (fun x => if x = s then 1 else 0) s * X s :=
      mul_le_mul_of_nonneg_right ((hvp t s s).2.2 rfl) (hX0 t s)
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (h2.trans h1) (by positivity))
    rw [one_div, ← mul_assoc, inv_mul_cancel₀ hg.ne', one_mul]
    all_goals rfl
  set Vinf : S → ℝ := fun s => ⨆ t, PolicyValue (softmaxPolicy (θ t)) P r γ s with hVinf
  have hV : ∀ s, Tendsto (fun t => PolicyValue (softmaxPolicy (θ t)) P r γ s) atTop (𝓝 (Vinf s)) := by
    intro s
    refine tendsto_atTop_ciSup (monotone_nat_of_le_succ (fun t => hmono t s)) ⟨K, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact (pg_V_bounds P r γ hM _ (hpol t) s).2
  set Qinf : S → A → ℝ := fun s a => r s a + γ * ∑ s', P s a s' * Vinf s' with hQinf
  have hQ : ∀ s a, Tendsto (fun t => QFunction (softmaxPolicy (θ t)) P r γ s a) atTop
      (𝓝 (Qinf s a)) := by
    intro s a
    unfold QFunction
    exact tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_finset_sum _
      (fun s' _ => tendsto_const_nhds.mul (hV s'))))
  have hAd : ∀ s a, Tendsto (fun t => advantage (softmaxPolicy (θ t)) P r γ s a) atTop
      (𝓝 (Qinf s a - Vinf s)) := fun s a => (hQ s a).sub (hV s)
  have hdiff : ∀ s, Tendsto (fun t => PolicyValue (softmaxPolicy (θ (t + 1))) P r γ s -
      PolicyValue (softmaxPolicy (θ t)) P r γ s) atTop (𝓝 0) := by
    intro s
    have h := ((hV s).comp (tendsto_add_atTop_nat 1)).sub (hV s)
    rw [sub_self] at h
    exact h
  have hkey : ∀ s b, Qinf s b ≤ Vinf s := by
    intro s b
    by_contra hlt
    have hlt := lt_of_not_ge hlt
    set δ : ℝ := (Qinf s b - Vinf s) / 2 with hδ
    have hδ0 : 0 < δ := by linarith
    have hev : ∀ᶠ t in atTop, δ ≤ advantage (softmaxPolicy (θ t)) P r γ s b :=
      (hAd s b).eventually (le_mem_nhds (by linarith))
    obtain ⟨T, hT⟩ := eventually_atTop.mp hev
    have hπ0 : Tendsto (fun t => softmaxPolicy (θ t) s b) atTop (𝓝 0) := by
      set C : ℝ := Real.exp (η * K * K) / (η * μ s * δ ^ 2) with hC
      have hμs := hμpos s
      have hbound : ∀ t, T ≤ t → (softmaxPolicy (θ t) s b) ^ 2 ≤
          C * (PolicyValue (softmaxPolicy (θ (t + 1))) P r γ s -
            PolicyValue (softmaxPolicy (θ t)) P r γ s) := by
        intro t ht
        have hp0 : 0 ≤ softmaxPolicy (θ t) s b := ((hpol t) s).1 b
        have had : δ ≤ advantage (softmaxPolicy (θ t)) P r γ s b := hT t ht
        have hu0 : 0 ≤ softmaxPolicy (θ t) s b * advantage (softmaxPolicy (θ t)) P r γ s b :=
          mul_nonneg hp0 (by linarith)
        have h1 := hX1 t s b hu0
        have h2 := hgainpt t s
        have h3 : η * μ s * (softmaxPolicy (θ t) s b * δ) ^ 2 / Real.exp (η * K * K) ≤
            c t s * (softmaxPolicy (θ t) s b * advantage (softmaxPolicy (θ t)) P r γ s b) ^ 2 /
              Real.exp (c t s * K) := by
          apply div_le_div₀ (mul_nonneg (hc0 t s) (sq_nonneg _)) ?_ (Real.exp_pos _) ?_
          · refine mul_le_mul (hcmin t s) ?_ (sq_nonneg _) (hc0 t s)
            exact pow_le_pow_left₀ (mul_nonneg hp0 hδ0.le)
              (mul_le_mul_of_nonneg_left had hp0) 2
          · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hcmax t s) hK0)
        have h4 := h3.trans (h1.trans h2)
        rw [div_le_iff₀ (Real.exp_pos _)] at h4
        rw [hC, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        have e : (softmaxPolicy (θ t) s b) ^ 2 * (η * μ s * δ ^ 2) =
            η * μ s * (softmaxPolicy (θ t) s b * δ) ^ 2 := by ring
        rw [e]
        linarith
      have hsq : Tendsto (fun t => (softmaxPolicy (θ t) s b) ^ 2) atTop (𝓝 0) := by
        have hup := (hdiff s).const_mul C
        rw [mul_zero] at hup
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
        · exact Eventually.of_forall (fun t => sq_nonneg _)
        · exact (eventually_ge_atTop T).mono hbound
      have h := hsq.sqrt
      rw [Real.sqrt_zero] at h
      refine h.congr (fun t => ?_)
      exact Real.sqrt_sq (((hpol t) s).1 b)
    exact pg_abs_contra (fun t a => θ t (s, a)) (fun t a => softmaxPolicy (θ t) s a)
      (fun t a => advantage (softmaxPolicy (θ t)) P r γ s a) (fun t => c t s) K δ b T
      (fun t a => rfl) (fun t a => hstep t s a) (fun t => hc0 t s)
      (fun t => sg_adv_zero _ (hpol t) P hP r γ hγ0 hγ1 s)
      (fun t a => pg_adv_bound P r γ hM _ (hpol t) s a) hδ0 hT hπ0
  have hle : ∀ s, Vinf s ≤ PolicyValue πstar P r γ s := fun s =>
    le_of_tendsto' (hV s) (fun t => hopt _ (hpol t) s)
  have hge : ∀ s, PolicyValue πstar P r γ s ≤ Vinf s := by
    intro s
    refine rl_improve_le πstar hπstar P hP r γ hγ0 hγ1 Vinf
      (fun u => Vinf u - (InducedReward πstar r u + γ * ∑ u', InducedTransition πstar P u u' * Vinf u'))
      (fun u => rfl) (fun u => ?_) s
    rw [rl_expand πstar P r γ Vinf u]
    have h1 : ∑ c, πstar u c * (r u c + γ * ∑ u', P u c u' * Vinf u') ≤ ∑ c, πstar u c * Vinf u :=
      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (hkey u c) ((hπstar u).1 c))
    rw [← Finset.sum_mul, (hπstar u).2, one_mul] at h1
    linarith
  intro s
  have h := hV s
  rw [le_antisymm (hle s) (hge s)] at h
  exact h
