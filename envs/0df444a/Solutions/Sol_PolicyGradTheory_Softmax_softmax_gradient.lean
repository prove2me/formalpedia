-- Prove2me | solution 1 for PolicyGradTheory.Softmax.softmax_gradient
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:01:00.973788+00:00
-- url     : https://prove2.me/submissions/3471965c-7a3e-463a-a175-ec6962ebb4b3

import Mathlib
import Definitions.Def_PolicyGradTheory_Softmax_Algorithm

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

open FoundationsML.ReinforcementLearning Filter Topology PolicyGradTheory.Softmax in
theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
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
