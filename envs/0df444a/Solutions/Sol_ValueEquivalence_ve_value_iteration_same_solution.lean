-- Prove2me | solution 1 for ValueEquivalence.ve_value_iteration_same_solution
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T07:20:28.637007+00:00
-- url     : https://prove2.me/submissions/fba71592-13e1-4124-b552-6313f3abdad3

import Mathlib
import Definitions.Def_ValueEquivalence_Basic

universe u v

namespace ValueEquivalence

theorem ve1_span_zero {X : Type*} [Fintype X] (d : X → ℝ) (H : Set (X → ℝ))
    (h : ∀ w ∈ H, ∑ x, w x * d x = 0) (w : X → ℝ) (hw : w ∈ Submodule.span ℝ H) :
    ∑ x, w x * d x = 0 := by
  let L : (X → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun w => ∑ x, w x * d x
      map_add' := by intro u v; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c u; simp [Finset.mul_sum, mul_assoc] }
  have hle : Submodule.span ℝ H ≤ LinearMap.ker L :=
    Submodule.span_le.mpr (fun u hu => by simpa [L] using h u hu)
  simpa [L] using hle hw

theorem ve1_diff {S A : Type*} [Fintype S] [Fintype A] (m m' : Model S A) (hr : m.r = m'.r)
    (γ : ℝ) (π : S → A → ℝ) (v : S → ℝ) (s : S) :
    bellman m γ π v s - bellman m' γ π v s =
      ∑ a, π s a * (γ * ∑ s', (m.p s a s' - m'.p s a s') * v s') := by
  simp only [bellman, hr, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

theorem ve1_swap {S A : Type*} [Fintype S] [Fintype A] (w : A → ℝ) (γ : ℝ)
    (c : A → S → ℝ) (v : S → ℝ) :
    ∑ a, w a * (γ * ∑ s', c a s' * v s') = ∑ s', v s' * ∑ a, w a * (γ * c a s') := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem ve1_extend {S A : Type*} [Fintype S] [Fintype A] {γ : ℝ} {Pol : Set (S → A → ℝ)}
    {V : Set (S → ℝ)} {m m' : Model S A} (hr : m.r = m'.r)
    (h : IsValueEquivalent γ Pol V m m') :
    IsValueEquivalent γ (pspan Pol) (Submodule.span ℝ V : Set (S → ℝ)) m m' := by
  -- reformulate via differences
  have key : ∀ π ∈ Pol, ∀ v ∈ V, ∀ s,
      ∑ a, π s a * (γ * ∑ s', (m.p s a s' - m'.p s a s') * v s') = 0 := by
    intro π hπ v hv s
    rw [← ve1_diff m m' hr, h π hπ v hv, sub_self]
  -- step 1: extend in the policy
  have step1 : ∀ π' ∈ pspan Pol, ∀ v ∈ V, ∀ s,
      ∑ a, π' s a * (γ * ∑ s', (m.p s a s' - m'.p s a s') * v s') = 0 := by
    intro π' hπ' v hv s
    have hm : π' s ∈ Submodule.span ℝ ((fun h => h s) '' Pol) := hπ' s
    have hH : ∀ w ∈ ((fun h => h s) '' Pol),
        ∑ a, w a * (fun a => γ * ∑ s', (m.p s a s' - m'.p s a s') * v s') a = 0 := by
      rintro w ⟨π, hπ, rfl⟩
      exact key π hπ v hv s
    exact ve1_span_zero _ _ hH (π' s) hm
  -- step 2: extend in the function
  intro π' hπ' v hv
  funext s
  rw [← sub_eq_zero, ve1_diff m m' hr, ve1_swap]
  refine ve1_span_zero (fun s' => ∑ a, π' s a * (γ * (m.p s a s' - m'.p s a s'))) V ?_ v hv
  intro u hu
  rw [← ve1_swap]
  exact step1 π' hπ' u hu s

theorem ve1_mono {S A : Type*} [Fintype S] [Fintype A] {γ : ℝ} {Pol Pol' : Set (S → A → ℝ)}
    {V V' : Set (S → ℝ)} {m m' : Model S A} (hP : Pol' ⊆ Pol) (hV : V' ⊆ V)
    (h : IsValueEquivalent γ Pol V m m') : IsValueEquivalent γ Pol' V' m m' :=
  fun π hπ v hv => h π (hP hπ) v (hV hv)

theorem ve1_det_policy {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A] (g : S → A) :
    (fun s a => if a = g s then (1 : ℝ) else 0) ∈ (policies : Set (S → A → ℝ)) := by
  refine ⟨fun s a => ?_, fun s => ?_⟩
  · dsimp only
    split_ifs <;> norm_num
  · simp

theorem ve1_bellman_det {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A] (m : Model S A)
    (γ : ℝ) (g : S → A) (v : S → ℝ) (s : S) :
    bellman m γ (fun s a => if a = g s then (1 : ℝ) else 0) v s =
      m.r s (g s) + γ * ∑ s', m.p s (g s) s' * v s' := by
  simp [bellman, ite_mul]

theorem ve1_sup_close {A : Type*} [Fintype A] [Nonempty A] (f g : A → ℝ) (C : ℝ)
    (h : ∀ a, |f a - g a| ≤ C) : |(⨆ a, f a) - ⨆ a, g a| ≤ C := by
  have h1 : ∀ (f g : A → ℝ), (∀ a, |f a - g a| ≤ C) → (⨆ a, f a) ≤ (⨆ a, g a) + C := by
    intro f g h
    refine ciSup_le fun a => ?_
    have := (abs_le.mp (h a)).2
    have := le_ciSup (Finite.bddAbove_range g) a
    linarith
  rw [abs_sub_le_iff]
  constructor
  · linarith [h1 f g h]
  · linarith [h1 g f (fun a => by rw [abs_sub_comm]; exact h a)]

theorem ve1_lip {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (m : Model S A) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (v w : S → ℝ) :
    dist (bellmanOpt m γ v) (bellmanOpt m γ w) ≤ γ * dist v w := by
  refine (dist_pi_le_iff (mul_nonneg hγ0 dist_nonneg)).mpr fun s => ?_
  rw [Real.dist_eq]
  refine ve1_sup_close _ _ _ fun a => ?_
  have hk := m.isKernel
  have e : (m.r s a + γ * ∑ s', m.p s a s' * v s') - (m.r s a + γ * ∑ s', m.p s a s' * w s')
      = γ * ∑ s', m.p s a s' * (v s' - w s') := by
    simp only [mul_sub, Finset.sum_sub_distrib]; ring
  rw [e, abs_mul, abs_of_nonneg hγ0]
  refine mul_le_mul_of_nonneg_left ?_ hγ0
  calc |∑ s', m.p s a s' * (v s' - w s')| ≤ ∑ s', |m.p s a s' * (v s' - w s')| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', m.p s a s' * dist v w := by
        refine Finset.sum_le_sum fun s' _ => ?_
        rw [abs_mul, abs_of_nonneg (hk.1 s a s')]
        refine mul_le_mul_of_nonneg_left ?_ (hk.1 s a s')
        rw [← Real.dist_eq]
        exact dist_le_pi_dist v w s'
    _ = dist v w := by rw [← Finset.sum_mul, hk.2 s a, one_mul]

theorem ve1_fixed_transfer {E : Type*} [MetricSpace E] (T1 T2 : E → E) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hL1 : ∀ v w, dist (T1 v) (T1 w) ≤ γ * dist v w)
    (hL2 : ∀ v w, dist (T2 v) (T2 w) ≤ γ * dist v w)
    (x : E) (hit : ∀ n : ℕ, T1^[n] x = T2^[n] x) (u : E) (hu : T1 u = u) : T2 u = u := by
  have hb : ∀ n : ℕ, dist (T1^[n] x) u ≤ γ ^ n * dist x u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc dist (T1 (T1^[n] x)) u = dist (T1 (T1^[n] x)) (T1 u) := by rw [hu]
        _ ≤ γ * dist (T1^[n] x) u := hL1 _ _
        _ ≤ γ * (γ ^ n * dist x u) := mul_le_mul_of_nonneg_left ih hγ0
        _ = γ ^ (n + 1) * dist x u := by ring
  have ht : Filter.Tendsto (fun n : ℕ => T1^[n] x) Filter.atTop (nhds u) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have h0 : Filter.Tendsto (fun n : ℕ => γ ^ n * dist x u) Filter.atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const (dist x u)
    exact squeeze_zero (fun n => dist_nonneg) hb h0
  have hc : Continuous T2 := by
    have : LipschitzWith (Real.toNNReal γ) T2 :=
      LipschitzWith.of_dist_le_mul fun v w => by
        rw [Real.coe_toNNReal _ hγ0]; exact hL2 v w
    exact this.continuous
  have h1 : Filter.Tendsto (fun n : ℕ => T2 (T1^[n] x)) Filter.atTop (nhds (T2 u)) :=
    (hc.tendsto u).comp ht
  have h2 : Filter.Tendsto (fun n : ℕ => T1^[n + 1] x) Filter.atTop (nhds u) :=
    ht.comp (Filter.tendsto_add_atTop_nat 1)
  have heq : (fun n : ℕ => T2 (T1^[n] x)) = fun n : ℕ => T1^[n + 1] x := by
    funext n
    rw [hit n, hit (n + 1), Function.iterate_succ_apply']
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

end ValueEquivalence

open ValueEquivalence in
theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (M : Set (Model S A)) (mstar : Model S A)
    (hM : ∀ m ∈ M, m.r = mstar.r)
    (Pol : Set (S → A → ℝ)) (V : Set (S → ℝ)) (V' : Submodule ℝ (S → ℝ))
    (hPol : Pol ⊆ policies)
    (hclosed : ∀ π ∈ (policies : Set (S → A → ℝ)), ∀ v ∈ V', bellman mstar γ π v ∈ V')
    (hcover : policies ⊆ pspan Pol) (hspan : Submodule.span ℝ V = V')
    (mt : Model S A) (hmt : mt ∈ veSpace γ M mstar Pol V) (v' : S → ℝ) (hv' : v' ∈ V') :
    (∀ n : ℕ, (bellmanOpt mt γ)^[n] v' = (bellmanOpt mstar γ)^[n] v') ∧
    (∀ u : S → ℝ, Function.IsFixedPt (bellmanOpt mt γ) u ↔
      Function.IsFixedPt (bellmanOpt mstar γ) u) := by
  classical
  obtain ⟨hmtM, hve⟩ := hmt
  have hr := hM mt hmtM
  have hve2 : IsValueEquivalent γ policies (V' : Set (S → ℝ)) mstar mt := by
    have h := ve1_extend hr.symm hve
    rw [hspan] at h
    exact ve1_mono hcover subset_rfl h
  have stepA : ∀ w ∈ V', bellmanOpt mt γ w = bellmanOpt mstar γ w := by
    intro w hw
    funext s
    simp only [bellmanOpt]
    congr 1
    funext a
    have h := congrFun (hve2 _ (ve1_det_policy (fun _ => a)) w hw) s
    rw [ve1_bellman_det, ve1_bellman_det] at h
    exact h.symm
  have stepB : ∀ w ∈ V', bellmanOpt mstar γ w ∈ V' := by
    intro w hw
    have hex : ∀ s, ∃ a, (mstar.r s a + γ * ∑ s', mstar.p s a s' * w s') =
        ⨆ a, (mstar.r s a + γ * ∑ s', mstar.p s a s' * w s') :=
      fun s => exists_eq_ciSup_of_finite
    choose g hg using hex
    have he : bellmanOpt mstar γ w =
        bellman mstar γ (fun s a => if a = g s then (1 : ℝ) else 0) w := by
      funext s
      rw [ve1_bellman_det]
      exact (hg s).symm
    rw [he]
    exact hclosed _ (ve1_det_policy g) w hw
  have part1 : ∀ n : ℕ, (bellmanOpt mt γ)^[n] v' = (bellmanOpt mstar γ)^[n] v' ∧
      (bellmanOpt mstar γ)^[n] v' ∈ V' := by
    intro n
    induction n with
    | zero => exact ⟨rfl, hv'⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih.1]
      exact ⟨stepA _ ih.2, stepB _ ih.2⟩
  refine ⟨fun n => (part1 n).1, fun u => ⟨fun hu => ?_, fun hu => ?_⟩⟩
  · exact ve1_fixed_transfer _ _ γ hγ0 hγ1 (ve1_lip mt γ hγ0) (ve1_lip mstar γ hγ0) v'
      (fun n => (part1 n).1) u hu
  · exact ve1_fixed_transfer _ _ γ hγ0 hγ1 (ve1_lip mstar γ hγ0) (ve1_lip mt γ hγ0) v'
      (fun n => (part1 n).1.symm) u hu
