-- Prove2me | solution 1 for YoungConventions.Perturbed.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:57:00.107241+00:00
-- url     : https://prove2.me/submissions/2485fe3d-9a50-484a-a833-1dce7d51645c

import Mathlib
import Definitions.Def_YoungConventions_Perturbed_FiniteChain
import Definitions.Def_YoungConventions_Perturbed_InTree
import Definitions.Def_YoungConventions_Perturbed_RegularPerturbation
import Definitions.Def_YoungConventions_Perturbed_StochasticPotential

open Filter Topology Finset


namespace YoungConventions.Perturbed

theorem hasRes_unique_core {X : Type*} [Fintype X] [DecidableEq X]
    (P : ℝ → Matrix X X ℝ) (x y : X) (r r' : ℝ)
    (h : HasResistance P x y r) (h' : HasResistance P x y r') (hlt : r < r') : False := by
  obtain ⟨-, c, hc, hT⟩ := h
  obtain ⟨-, c', -, hT'⟩ := h'
  have hpow : Tendsto (fun ε : ℝ => ε ^ (r' - r)) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 (r' - r) (Or.inr (by linarith))).tendsto
    rw [Real.zero_rpow (by linarith)] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hprod := hpow.mul hT'
  rw [zero_mul] at hprod
  have heq : (fun ε : ℝ => ε ^ (r' - r) * (ε ^ (-r') * P ε x y)) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => ε ^ (-r) * P ε x y) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [← mul_assoc, ← Real.rpow_add hε]
    ring_nf
  have h2 := hprod.congr' heq
  have := tendsto_nhds_unique h2 hT
  linarith

theorem resistance_spec_core {X : Type*} [Fintype X] [DecidableEq X]
    (P0 : Matrix X X ℝ) (hP0 : P0 ∈ Matrix.rowStochastic ℝ X)
    (P : ℝ → Matrix X X ℝ) (a : ℝ) (hP : IsRegularPerturbation P0 P a) (x y : X) :
    (∀ r r' : ℝ, HasResistance P x y r → HasResistance P x y r' → r = r') ∧
    ((∃ ε ∈ Set.Ioc 0 a, 0 < P ε x y) → IsEdge P x y) ∧
    (IsEdge P x y → HasResistance P x y (resistance P x y)) ∧
    ((IsEdge P x y ∧ resistance P x y = 0) ↔ 0 < P0 x y) := by
  have huniq : ∀ r r' : ℝ, HasResistance P x y r → HasResistance P x y r' → r = r' := by
    intro r r' h h'
    rcases lt_trichotomy r r' with hl | he | hg
    · exact (hasRes_unique_core P x y r r' h h' hl).elim
    · exact he
    · exact (hasRes_unique_core P x y r' r h' h hg).elim
  have hedge : (∃ ε ∈ Set.Ioc 0 a, 0 < P ε x y) → IsEdge P x y := by
    intro hex
    obtain ⟨r, -, c, hc, hT⟩ := hP.order x y hex
    have hev := hT.eventually_const_lt hc
    filter_upwards [hev, self_mem_nhdsWithin] with ε h1 h2
    have hp : 0 < ε ^ (-r) := Real.rpow_pos_of_pos h2 _
    exact (mul_pos_iff_of_pos_left hp).mp h1
  have hres : IsEdge P x y → HasResistance P x y (resistance P x y) := by
    intro he
    have hex : ∃ ε ∈ Set.Ioc 0 a, 0 < P ε x y := by
      obtain ⟨ε, h1, h2⟩ := (he.and (Ioc_mem_nhdsGT hP.pos)).exists
      exact ⟨ε, h2, h1⟩
    have hr := hP.order x y hex
    unfold resistance
    rw [dif_pos hr]
    exact Classical.choose_spec hr
  refine ⟨huniq, hedge, hres, ?_, ?_⟩
  · rintro ⟨he, h0⟩
    have h := hres he
    rw [h0] at h
    obtain ⟨-, c, hc, hT⟩ := h
    have hT2 : Tendsto (fun ε : ℝ => P ε x y) (𝓝[>] 0) (𝓝 c) := by
      refine hT.congr ?_
      intro ε
      simp
    have := tendsto_nhds_unique (hP.tendsto x y) hT2
    linarith
  · intro hpos
    have he : IsEdge P x y := (hP.tendsto x y).eventually_const_lt hpos
    refine ⟨he, ?_⟩
    have h0 : HasResistance P x y 0 := by
      refine ⟨le_rfl, P0 x y, hpos, ?_⟩
      refine (hP.tendsto x y).congr ?_
      intro ε
      simp
    exact huniq _ _ (hres he) h0

theorem iter_update_reach_core {X : Type*} [DecidableEq X] (F : X → X) (r t : X) :
    ∀ n : ℕ, ∀ v, F^[n] v = r → ∃ m, (Function.update F r t)^[m] v = r := by
  intro n
  induction n with
  | zero => intro v hv; exact ⟨0, by simpa using hv⟩
  | succ n ih =>
    intro v hv
    by_cases h : v = r
    · exact ⟨0, by simpa using h⟩
    rw [Function.iterate_succ_apply] at hv
    obtain ⟨m, hm⟩ := ih (F v) hv
    refine ⟨m + 1, ?_⟩
    rw [Function.iterate_succ_apply, Function.update_of_ne h]
    exact hm

/-- `F` is a unicyclic map through `y`. -/
def IsUni {X : Type*} (y : X) (F : X → X) : Prop :=
  (∃ n, F^[n + 1] y = y) ∧ ∀ v, ∃ n, F^[n] v = y

theorem pred_unique_core {X : Type*} (F : X → X) (x y : X) (k : ℕ)
    (hFx : F x = y) (hk : F^[k] y = x) :
    x = F^[Function.minimalPeriod F y - 1] y := by
  have hper : Function.IsPeriodicPt F (k + 1) y := by
    show F^[k + 1] y = y
    rw [Function.iterate_succ_apply', hk, hFx]
  have hp := hper.minimalPeriod_pos (Nat.succ_pos k)
  obtain ⟨c, hc⟩ := hper.minimalPeriod_dvd
  set p := Function.minimalPeriod F y with hpdef
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h] at hc; omega
    · exact h
  have hkeq : k = (p - 1) + p * (c - 1) := by
    have : p * c = p * (c - 1) + p := by
      conv_lhs => rw [show c = (c - 1) + 1 by omega]
      ring
    omega
  have hmc : F^[p * (c - 1)] y = y := ((Function.isPeriodicPt_minimalPeriod F y).mul_const (c - 1)).eq
  rw [← hk, hkeq, Function.iterate_add_apply, hmc]

theorem tree_pos_core {X : Type*} [Fintype X] [DecidableEq X]
    (A : Matrix X X ℝ) (hA : A ∈ Matrix.rowStochastic ℝ X)
    (hirr : A.IsIrreducible) (z : X) :
    ∃ T : X → X, IsInTree z T ∧ ∀ v, v ≠ z → 0 < A v (T v) := by
  classical
  have hnn : ∀ i j, 0 ≤ A i j := (Matrix.mem_rowStochastic_iff_sum.mp hA).1
  have hpnn : ∀ n : ℕ, ∀ i j, 0 ≤ (A ^ n) i j := fun n =>
    (Matrix.mem_rowStochastic_iff_sum.mp (pow_mem hA n)).1
  have hreach := (Matrix.isIrreducible_iff_exists_pow_pos hnn).mp hirr
  have hex : ∀ v, ∃ n, 0 < (A ^ n) v z := fun v => by
    obtain ⟨k, -, hk⟩ := hreach v z; exact ⟨k, hk⟩
  let d : X → ℕ := fun v => Nat.find (hex v)
  have hd : ∀ v, 0 < (A ^ d v) v z := fun v => Nat.find_spec (hex v)
  have hdmin : ∀ v n, 0 < (A ^ n) v z → d v ≤ n := fun v n h => Nat.find_min' (hex v) h
  have hstep : ∀ v, v ≠ z → ∃ u, 0 < A v u ∧ d u < d v := by
    intro v hv
    have h0 := hd v
    rcases Nat.eq_zero_or_pos (d v) with h | h
    · rw [h, pow_zero, Matrix.one_apply_ne hv] at h0; exact absurd h0 (lt_irrefl 0)
    obtain ⟨m, hm⟩ : ∃ m, d v = m + 1 := ⟨d v - 1, by omega⟩
    rw [hm, pow_succ', Matrix.mul_apply] at h0
    by_contra hcon
    push Not at hcon
    have : ∑ k, A v k * (A ^ m) k z ≤ 0 := by
      apply Finset.sum_nonpos
      intro k _
      by_contra hk
      push Not at hk
      have h1 : 0 < A v k := by
        rcases lt_or_eq_of_le (hnn v k) with h' | h'
        · exact h'
        · rw [← h'] at hk; simp at hk
      have h2 : 0 < (A ^ m) k z := by
        rcases lt_or_eq_of_le (hpnn m k z) with h' | h'
        · exact h'
        · rw [← h'] at hk; simp at hk
      have := hcon k h1
      have := hdmin k m h2
      omega
    linarith
  let T : X → X := fun v => if h : v = z then z else Classical.choose (hstep v h)
  have hTz : T z = z := by simp [T]
  have hTv : ∀ v, v ≠ z → 0 < A v (T v) ∧ d (T v) < d v := by
    intro v hv
    simp only [T, dif_neg hv]
    exact Classical.choose_spec (hstep v hv)
  refine ⟨T, ⟨hTz, ?_⟩, fun v hv => (hTv v hv).1⟩
  have key : ∀ n, ∀ v, d v ≤ n → ∃ m, T^[m] v = z := by
    intro n
    induction n with
    | zero =>
      intro v hv
      refine ⟨0, ?_⟩
      by_contra hne
      have := (hTv v hne).2
      omega
    | succ n ih =>
      intro v hv
      by_cases hvz : v = z
      · exact ⟨0, hvz⟩
      obtain ⟨m, hm⟩ := ih (T v) (by have := (hTv v hvz).2; omega)
      exact ⟨m + 1, by rw [Function.iterate_succ_apply]; exact hm⟩
  intro v
  exact key (d v) v le_rfl

theorem treeWeight_pos_core {X : Type*} [Fintype X] [DecidableEq X]
    (A : Matrix X X ℝ) (hA : A ∈ Matrix.rowStochastic ℝ X)
    (hirr : A.IsIrreducible) (z : X) : 0 < treeWeight A z := by
  classical
  have hnn : ∀ i j, 0 ≤ A i j := (Matrix.mem_rowStochastic_iff_sum.mp hA).1
  obtain ⟨T, hT, hpos⟩ := tree_pos_core A hA hirr z
  unfold treeWeight
  apply Finset.sum_pos'
  · intro T' _
    exact Finset.prod_nonneg (fun v _ => hnn _ _)
  · refine ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩, ?_⟩
    exact Finset.prod_pos (fun v hv => hpos v (Finset.ne_of_mem_erase hv))

open Classical in
theorem lhs_eq_core {X : Type*} [Fintype X] [DecidableEq X]
    (A : Matrix X X ℝ) (y : X) :
    ∑ x, treeWeight A x * A x y =
      ∑ F ∈ (univ : Finset (X → X)).filter (fun F => IsUni y F), ∏ v, A v (F v) := by
  classical
  have h1 : ∑ x, treeWeight A x * A x y =
      ∑ p ∈ (univ : Finset (X × (X → X))).filter (fun p => IsInTree p.1 p.2),
        (∏ v ∈ univ.erase p.1, A v (p.2 v)) * A p.1 y := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    unfold treeWeight
    rw [Finset.sum_mul, Finset.sum_filter]
  rw [h1]
  apply Finset.sum_bij'
    (fun p _ => Function.update p.2 p.1 y)
    (fun F _ => (F^[Function.minimalPeriod F y - 1] y,
      Function.update F (F^[Function.minimalPeriod F y - 1] y) (F^[Function.minimalPeriod F y - 1] y)))
  · -- hi
    rintro ⟨x, T⟩ hp
    have hT : IsInTree x T := (Finset.mem_filter.mp hp).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hreach : ∀ v, ∃ m, (Function.update T x y)^[m] v = x := fun v => by
      obtain ⟨n, hn⟩ := hT.2 v
      exact iter_update_reach_core T x y n v hn
    refine ⟨?_, fun v => ?_⟩
    · obtain ⟨m, hm⟩ := hreach y
      exact ⟨m, by rw [Function.iterate_succ_apply', hm, Function.update_self]⟩
    · obtain ⟨m, hm⟩ := hreach v
      exact ⟨m + 1, by rw [Function.iterate_succ_apply', hm, Function.update_self]⟩
  · -- hj
    intro F hF
    have hU : IsUni y F := (Finset.mem_filter.mp hF).2
    set x := F^[Function.minimalPeriod F y - 1] y with hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    refine ⟨Function.update_self _ _ _, fun v => ?_⟩
    obtain ⟨n, hn⟩ := hU.2 v
    have : F^[(Function.minimalPeriod F y - 1) + n] v = x := by
      rw [Function.iterate_add_apply, hn]
    exact iter_update_reach_core F x x _ v this
  · -- left_inv
    rintro ⟨x, T⟩ hp
    have hT : IsInTree x T := (Finset.mem_filter.mp hp).2
    obtain ⟨n, hn⟩ := hT.2 y
    obtain ⟨m, hm⟩ := iter_update_reach_core T x y n y hn
    have hxe := pred_unique_core (Function.update T x y) x y m (Function.update_self _ _ _) hm
    simp only
    rw [← hxe]
    simp only [Function.update_idem, Prod.mk.injEq, true_and]
    exact Function.update_eq_self_iff.mpr hT.1.symm
  · -- right_inv
    intro F hF
    have hU : IsUni y F := (Finset.mem_filter.mp hF).2
    simp only [Function.update_idem]
    have hFx : F (F^[Function.minimalPeriod F y - 1] y) = y := by
      obtain ⟨n, hn⟩ := hU.1
      have hper : Function.IsPeriodicPt F (n + 1) y := hn
      have hp := hper.minimalPeriod_pos (Nat.succ_pos n)
      rw [← Function.iterate_succ_apply' F, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]
      exact (Function.isPeriodicPt_minimalPeriod F y).eq
    exact Function.update_eq_self_iff.mpr hFx.symm
  · -- weights
    rintro ⟨x, T⟩ _
    simp only
    rw [← Finset.prod_erase_mul univ _ (Finset.mem_univ x), Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro v hv
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]

open Classical in
theorem rhs_eq_core {X : Type*} [Fintype X] [DecidableEq X]
    (A : Matrix X X ℝ) (y : X) :
    ∑ x, treeWeight A y * A y x =
      ∑ F ∈ (univ : Finset (X → X)).filter (fun F => IsUni y F), ∏ v, A v (F v) := by
  classical
  have h1 : ∑ x, treeWeight A y * A y x =
      ∑ p ∈ (univ : Finset (X × (X → X))).filter (fun p => IsInTree y p.2),
        (∏ v ∈ univ.erase y, A v (p.2 v)) * A y p.1 := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    unfold treeWeight
    rw [Finset.sum_mul, Finset.sum_filter]
  rw [h1]
  apply Finset.sum_bij'
    (fun (p : X × (X → X)) _ => Function.update p.2 y p.1)
    (fun (F : X → X) _ => (F y, Function.update F y y))
  · rintro ⟨x, T⟩ hp
    have hT : IsInTree y T := (Finset.mem_filter.mp hp).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hreach : ∀ v, ∃ m, (Function.update T y x)^[m] v = y := fun v => by
      obtain ⟨n, hn⟩ := hT.2 v
      exact iter_update_reach_core T y x n v hn
    refine ⟨?_, hreach⟩
    obtain ⟨m, hm⟩ := hreach x
    exact ⟨m, by rw [Function.iterate_succ_apply, Function.update_self, hm]⟩
  · intro F hF
    have hU : IsUni y F := (Finset.mem_filter.mp hF).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    refine ⟨Function.update_self _ _ _, fun v => ?_⟩
    obtain ⟨n, hn⟩ := hU.2 v
    exact iter_update_reach_core F y y n v hn
  · rintro ⟨x, T⟩ hp
    have hT : IsInTree y T := (Finset.mem_filter.mp hp).2
    simp only [Function.update_self, Function.update_idem, Prod.mk.injEq, true_and]
    exact Function.update_eq_self_iff.mpr hT.1.symm
  · intro F _
    simp only [Function.update_idem, Function.update_eq_self]
  · rintro ⟨x, T⟩ _
    simp only
    rw [← Finset.prod_erase_mul univ _ (Finset.mem_univ y), Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro v hv
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]

theorem mctf_core {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (A : Matrix X X ℝ) (hA : A ∈ Matrix.rowStochastic ℝ X)
    (hirr : A.IsIrreducible) :
    (∀ z, 0 < treeWeight A z) ∧
    IsStationaryDist A (fun z => treeWeight A z / ∑ x, treeWeight A x) ∧
    ∀ ν : X → ℝ, IsStationaryDist A ν → ν = fun z => treeWeight A z / ∑ x, treeWeight A x := by
  have hnn : ∀ i j, 0 ≤ A i j := (Matrix.mem_rowStochastic_iff_sum.mp hA).1
  have hrow : ∀ i, ∑ j, A i j = 1 := (Matrix.mem_rowStochastic_iff_sum.mp hA).2
  have hpos := treeWeight_pos_core A hA hirr
  set S := ∑ x, treeWeight A x with hS
  have hSpos : 0 < S := Finset.sum_pos (fun z _ => hpos z) Finset.univ_nonempty
  have hbal : ∀ y, ∑ x, treeWeight A x * A x y = treeWeight A y := by
    intro y
    rw [lhs_eq_core, ← rhs_eq_core, ← Finset.mul_sum, hrow, mul_one]
  have hstat : IsStationaryDist A (fun z => treeWeight A z / S) := by
    refine ⟨fun z => (div_pos (hpos z) hSpos).le, ?_, fun y => ?_⟩
    · rw [← Finset.sum_div, div_self hSpos.ne']
    · simp only [div_mul_eq_mul_div]
      rw [← Finset.sum_div, hbal]
  refine ⟨hpos, hstat, ?_⟩
  intro ν hν
  obtain ⟨hν0, hν1, hνA⟩ := hν
  set μ : X → ℝ := fun z => treeWeight A z / S with hμ
  have hμpos : ∀ z, 0 < μ z := fun z => div_pos (hpos z) hSpos
  obtain ⟨z0, -, hz0⟩ := Finset.exists_min_image univ (fun z => ν z / μ z) Finset.univ_nonempty
  set t := ν z0 / μ z0 with ht
  let w : X → ℝ := fun z => ν z - t * μ z
  have hw0 : ∀ z, 0 ≤ w z := by
    intro z
    have := hz0 z (Finset.mem_univ _)
    rw [le_div_iff₀ (hμpos z)] at this
    simp only [w]; linarith
  have hwz0 : w z0 = 0 := by
    simp only [w, ht]; field_simp [(hμpos z0).ne']; ring
  have hwA : Matrix.vecMul w A = w := by
    funext y
    simp only [Matrix.vecMul, dotProduct, w, sub_mul, Finset.sum_sub_distrib, mul_assoc]
    rw [← Finset.mul_sum, hνA y]
    have := hstat.2.2 y
    rw [this]
  have hwn : ∀ n : ℕ, Matrix.vecMul w (A ^ n) = w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hwA]
  have hpnn : ∀ n : ℕ, ∀ i j, 0 ≤ (A ^ n) i j := fun n =>
    (Matrix.mem_rowStochastic_iff_sum.mp (pow_mem hA n)).1
  have hreach := (Matrix.isIrreducible_iff_exists_pow_pos hnn).mp hirr
  have hwall : ∀ x, w x = 0 := by
    intro x
    obtain ⟨k, -, hk⟩ := hreach x z0
    have h := congrFun (hwn k) z0
    simp only [Matrix.vecMul, dotProduct] at h
    rw [hwz0] at h
    have hle : w x * (A ^ k) x z0 ≤ ∑ x', w x' * (A ^ k) x' z0 :=
      Finset.single_le_sum (f := fun x' => w x' * (A ^ k) x' z0)
        (fun x' _ => mul_nonneg (hw0 x') (hpnn k x' z0)) (Finset.mem_univ x)
    rw [h] at hle
    have := mul_nonneg (hw0 x) (hpnn k x z0)
    have h0 : w x * (A ^ k) x z0 = 0 := le_antisymm hle this
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact h'
    · linarith
  have hνeq : ∀ z, ν z = t * μ z := fun z => by
    have := hwall z; simp only [w] at this; linarith
  have ht1 : t = 1 := by
    have h1 : ∑ z, ν z = t * ∑ z, μ z := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun z _ => hνeq z)
    rw [hν1, hstat.2.1, mul_one] at h1
    exact h1.symm
  funext z
  rw [hνeq z, ht1, one_mul]


theorem edge_lim_core {X : Type*} [Fintype X] [DecidableEq X]
    (P0 : Matrix X X ℝ) (hP0 : P0 ∈ Matrix.rowStochastic ℝ X)
    (P : ℝ → Matrix X X ℝ) (a : ℝ) (hP : IsRegularPerturbation P0 P a) (v w : X)
    (he : IsEdge P v w) :
    ∃ c, 0 < c ∧ Tendsto (fun ε : ℝ => ε ^ (-resistance P v w) * P ε v w) (𝓝[>] 0) (𝓝 c) :=
  ((resistance_spec_core P0 hP0 P a hP v w).2.2.1 he).2

theorem nonedge_zero_core {X : Type*} [Fintype X] [DecidableEq X]
    (P0 : Matrix X X ℝ) (hP0 : P0 ∈ Matrix.rowStochastic ℝ X)
    (P : ℝ → Matrix X X ℝ) (a : ℝ) (hP : IsRegularPerturbation P0 P a) (v w : X)
    (hne : ¬ IsEdge P v w) : ∀ ε ∈ Set.Ioc 0 a, P ε v w = 0 := by
  intro ε hε
  have h2 := (resistance_spec_core P0 hP0 P a hP v w).2.1
  have hnn := (Matrix.mem_rowStochastic_iff_sum.mp (hP.stochastic ε hε)).1 v w
  by_contra hc
  exact hne (h2 ⟨ε, hε, lt_of_le_of_ne hnn (Ne.symm hc)⟩)

theorem gtree_lim_core {X : Type*} [Fintype X] [DecidableEq X]
    (P0 : Matrix X X ℝ) (hP0 : P0 ∈ Matrix.rowStochastic ℝ X)
    (P : ℝ → Matrix X X ℝ) (a : ℝ) (hP : IsRegularPerturbation P0 P a) (x : X) (T : X → X)
    (hT : IsGTree P x T) :
    ∃ C, 0 < C ∧ Tendsto (fun ε : ℝ => ε ^ (-(∑ v ∈ univ.erase x, resistance P v (T v))) *
      ∏ v ∈ univ.erase x, P ε v (T v)) (𝓝[>] 0) (𝓝 C) := by
  have h : ∀ v ∈ univ.erase x, ∃ c, 0 < c ∧
      Tendsto (fun ε : ℝ => ε ^ (-resistance P v (T v)) * P ε v (T v)) (𝓝[>] 0) (𝓝 c) :=
    fun v hv => edge_lim_core P0 hP0 P a hP v (T v) (hT.2 v (Finset.ne_of_mem_erase hv))
  choose! c hc0 hcT using h
  refine ⟨∏ v ∈ univ.erase x, c v, Finset.prod_pos hc0, ?_⟩
  have := tendsto_finsetProd _ hcT
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [Finset.prod_mul_distrib, ← Finset.sum_neg_distrib, Real.rpow_sum_of_pos hε]

theorem tree_term_lim_core {X : Type*} [Fintype X] [DecidableEq X]
    (P0 : Matrix X X ℝ) (hP0 : P0 ∈ Matrix.rowStochastic ℝ X)
    (P : ℝ → Matrix X X ℝ) (a : ℝ) (hP : IsRegularPerturbation P0 P a) (m : ℝ) (x : X)
    (hm : ∀ T, IsGTree P x T → m ≤ ∑ v ∈ univ.erase x, resistance P v (T v))
    (T : X → X) (hT : IsInTree x T) :
    ∃ ℓ, 0 ≤ ℓ ∧ Tendsto (fun ε : ℝ => ε ^ (-m) * ∏ v ∈ univ.erase x, P ε v (T v))
      (𝓝[>] 0) (𝓝 ℓ) ∧
      (0 < ℓ ↔ IsGTree P x T ∧ ∑ v ∈ univ.erase x, resistance P v (T v) = m) := by
  by_cases hG : IsGTree P x T
  · set R := ∑ v ∈ univ.erase x, resistance P v (T v) with hR
    obtain ⟨C, hC, hCT⟩ := gtree_lim_core P0 hP0 P a hP x T hG
    have hRm := hm T hG
    refine ⟨(0 : ℝ) ^ (R - m) * C, mul_nonneg (Real.rpow_nonneg le_rfl _) hC.le, ?_, ?_⟩
    · have hpow : Tendsto (fun ε : ℝ => ε ^ (R - m)) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ (R - m))) :=
        ((Real.continuousAt_rpow_const 0 (R - m) (Or.inr (by linarith))).tendsto).mono_left
          nhdsWithin_le_nhds
      refine (hpow.mul hCT).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [← mul_assoc, ← Real.rpow_add hε, hR]
      congr 2
      ring
    · constructor
      · intro hpos
        refine ⟨hG, ?_⟩
        by_contra hne
        rw [Real.zero_rpow (sub_ne_zero.mpr hne), zero_mul] at hpos
        exact lt_irrefl 0 hpos
      · rintro ⟨-, he⟩
        rw [he, sub_self, Real.rpow_zero, one_mul]
        exact hC
  · refine ⟨0, le_rfl, ?_, ?_⟩
    · have hex : ∃ v, v ≠ x ∧ ¬ IsEdge P v (T v) := by
        by_contra hno
        push Not at hno
        exact hG ⟨hT, hno⟩
      obtain ⟨v, hvx, hv⟩ := hex
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioc_mem_nhdsGT hP.pos] with ε hε
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hvx, Finset.mem_univ v⟩)
        (nonedge_zero_core P0 hP0 P a hP v (T v) hv ε hε), mul_zero]
    · constructor
      · intro h; exact absurd h (lt_irrefl 0)
      · rintro ⟨h, -⟩; exact absurd h hG

theorem tw_lim_core {X : Type*} [Fintype X] [DecidableEq X]
    (P0 : Matrix X X ℝ) (hP0 : P0 ∈ Matrix.rowStochastic ℝ X)
    (P : ℝ → Matrix X X ℝ) (a : ℝ) (hP : IsRegularPerturbation P0 P a) (m : ℝ) (x : X)
    (hm : ∀ T, IsGTree P x T → m ≤ ∑ v ∈ univ.erase x, resistance P v (T v)) :
    ∃ L, 0 ≤ L ∧ Tendsto (fun ε : ℝ => ε ^ (-m) * treeWeight (P ε) x) (𝓝[>] 0) (𝓝 L) ∧
      (0 < L ↔ ∃ T, IsGTree P x T ∧ ∑ v ∈ univ.erase x, resistance P v (T v) = m) := by
  classical
  have h : ∀ T ∈ (univ : Finset (X → X)).filter (fun T => IsInTree x T), ∃ ℓ, 0 ≤ ℓ ∧
      Tendsto (fun ε : ℝ => ε ^ (-m) * ∏ v ∈ univ.erase x, P ε v (T v)) (𝓝[>] 0) (𝓝 ℓ) ∧
      (0 < ℓ ↔ IsGTree P x T ∧ ∑ v ∈ univ.erase x, resistance P v (T v) = m) :=
    fun T hT => tree_term_lim_core P0 hP0 P a hP m x hm T (Finset.mem_filter.mp hT).2
  choose! ℓ hℓ0 hℓT hℓpos using h
  refine ⟨∑ T ∈ (univ : Finset (X → X)).filter (fun T => IsInTree x T), ℓ T,
    Finset.sum_nonneg hℓ0, ?_, ?_⟩
  · have := tendsto_finsetSum _ hℓT
    refine this.congr' (Eventually.of_forall fun ε => ?_)
    simp only
    unfold treeWeight
    rw [Finset.mul_sum]
  · rw [Finset.sum_pos_iff_of_nonneg hℓ0]
    constructor
    · rintro ⟨T, hT, hpos⟩
      exact ⟨T, (hℓpos T hT).mp hpos⟩
    · rintro ⟨T, hG, hR⟩
      have hT : T ∈ (univ : Finset (X → X)).filter (fun T => IsInTree x T) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG.1⟩
      exact ⟨T, hT, (hℓpos T hT).mpr ⟨hG, hR⟩⟩

theorem lemma_1_core {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (P0 : Matrix X X ℝ) (hP0 : P0 ∈ Matrix.rowStochastic ℝ X)
    (P : ℝ → Matrix X X ℝ) (a : ℝ) (hP : IsRegularPerturbation P0 P a)
    (μ : ℝ → X → ℝ) (hμ : ∀ ε ∈ Set.Ioc 0 a, IsStationaryDist (P ε) (μ ε)) :
    ∃ μ0 : X → ℝ,
      (∀ x, Tendsto (fun ε : ℝ => μ ε x) (𝓝[>] 0) (𝓝 (μ0 x))) ∧
      IsStationaryDist P0 μ0 ∧
      ∀ x, (0 < μ0 x ↔ ∀ y, statePotential P x ≤ statePotential P y) := by
  classical
  have haI : a ∈ Set.Ioc 0 a := ⟨hP.pos, le_rfl⟩
  -- existence of a G-tree
  obtain ⟨T0, hT0, hT0pos⟩ := tree_pos_core (P a) (hP.stochastic a haI) (hP.irreducible a haI)
    (Classical.arbitrary X)
  have hG0 : IsGTree P (Classical.arbitrary X) T0 :=
    ⟨hT0, fun v hv => (resistance_spec_core P0 hP0 P a hP v (T0 v)).2.1 ⟨a, haI, hT0pos v hv⟩⟩
  let Rf : X × (X → X) → ℝ := fun p => ∑ v ∈ univ.erase p.1, resistance P v (p.2 v)
  let 𝒯 := (univ : Finset (X × (X → X))).filter (fun p => IsGTree P p.1 p.2)
  have hne : 𝒯.Nonempty := ⟨(Classical.arbitrary X, T0), Finset.mem_filter.mpr ⟨mem_univ _, hG0⟩⟩
  obtain ⟨ps, hps, hpsmin⟩ := Finset.exists_min_image 𝒯 Rf hne
  have hpsG : IsGTree P ps.1 ps.2 := (Finset.mem_filter.mp hps).2
  set m := Rf ps with hmdef
  have hm : ∀ x T, IsGTree P x T → m ≤ ∑ v ∈ univ.erase x, resistance P v (T v) :=
    fun x T hT => hpsmin (x, T) (Finset.mem_filter.mpr ⟨mem_univ _, hT⟩)
  -- potentials
  have hγlow : ∀ y, ((m : ℝ) : EReal) ≤ statePotential P y := by
    intro y
    unfold statePotential
    exact le_iInf₂ fun T hT => EReal.coe_le_coe_iff.mpr (hm y T hT)
  have hγup : ∀ x T, IsGTree P x T → ∑ v ∈ univ.erase x, resistance P v (T v) = m →
      statePotential P x ≤ ((m : ℝ) : EReal) := by
    intro x T hT hR
    unfold statePotential
    refine le_trans (iInf₂_le T hT) ?_
    rw [hR]
  have hγconv : ∀ x, statePotential P x ≤ ((m : ℝ) : EReal) →
      ∃ T, IsGTree P x T ∧ ∑ v ∈ univ.erase x, resistance P v (T v) = m := by
    intro x hx
    by_contra hno
    push Not at hno
    have hlt : ∀ T, IsGTree P x T → m < ∑ v ∈ univ.erase x, resistance P v (T v) :=
      fun T hT => lt_of_le_of_ne (hm x T hT) (Ne.symm (hno T hT))
    let s := (univ : Finset (X → X)).filter (fun T => IsGTree P x T)
    by_cases hs : s.Nonempty
    · obtain ⟨T1, hT1, hmin⟩ := Finset.exists_min_image s
        (fun T => ∑ v ∈ univ.erase x, resistance P v (T v)) hs
      have hle : ((∑ v ∈ univ.erase x, resistance P v (T1 v) : ℝ) : EReal) ≤ statePotential P x := by
        unfold statePotential
        exact le_iInf₂ fun T hT => EReal.coe_le_coe_iff.mpr
          (hmin T (Finset.mem_filter.mpr ⟨mem_univ _, hT⟩))
      have := le_trans hle hx
      rw [EReal.coe_le_coe_iff] at this
      have := hlt T1 (Finset.mem_filter.mp hT1).2
      linarith
    · have htop : (⊤ : EReal) ≤ statePotential P x := by
        unfold statePotential
        exact le_iInf₂ fun T hT => (hs ⟨T, Finset.mem_filter.mpr ⟨mem_univ _, hT⟩⟩).elim
      have := lt_of_le_of_lt (le_trans htop hx) (EReal.coe_lt_top m)
      exact lt_irrefl _ this
  -- limits of the scaled tree weights
  have hL := fun x => tw_lim_core P0 hP0 P a hP m x (hm x)
  choose L hL0 hLT hLpos using hL
  have hLps : 0 < L ps.1 := (hLpos ps.1).mpr ⟨ps.2, hpsG, rfl⟩
  have hSpos : 0 < ∑ x, L x :=
    Finset.sum_pos' (fun x _ => hL0 x) ⟨ps.1, mem_univ _, hLps⟩
  let μ0 : X → ℝ := fun x => L x / ∑ y, L y
  have hconv : ∀ x, Tendsto (fun ε : ℝ => μ ε x) (𝓝[>] 0) (𝓝 (μ0 x)) := by
    intro x
    have hlim := (hLT x).div (tendsto_finsetSum _ (fun y _ => hLT y)) hSpos.ne'
    refine hlim.congr' ?_
    filter_upwards [Ioc_mem_nhdsGT hP.pos] with ε hε
    have hμe := (mctf_core (P ε) (hP.stochastic ε hε) (hP.irreducible ε hε)).2.2 (μ ε) (hμ ε hε)
    rw [hμe]
    simp only [Pi.div_apply]
    rw [← Finset.mul_sum, mul_div_mul_left _ _ (Real.rpow_pos_of_pos hε.1 _).ne']
  refine ⟨μ0, hconv, ⟨fun x => div_nonneg (hL0 x) hSpos.le, ?_, fun y => ?_⟩, fun x => ?_⟩
  · simp only [μ0]
    rw [← Finset.sum_div, div_self hSpos.ne']
  · have h1 : Tendsto (fun ε : ℝ => ∑ x, μ ε x * P ε x y) (𝓝[>] 0) (𝓝 (∑ x, μ0 x * P0 x y)) :=
      tendsto_finsetSum _ (fun x _ => (hconv x).mul (hP.tendsto x y))
    have h2 : Tendsto (fun ε : ℝ => ∑ x, μ ε x * P ε x y) (𝓝[>] 0) (𝓝 (μ0 y)) := by
      refine (hconv y).congr' ?_
      filter_upwards [Ioc_mem_nhdsGT hP.pos] with ε hε
      exact ((hμ ε hε).2.2 y).symm
    exact tendsto_nhds_unique h1 h2
  · rw [div_pos_iff_of_pos_right hSpos, hLpos x]
    constructor
    · rintro ⟨T, hT, hR⟩ y
      exact le_trans (hγup x T hT hR) (hγlow y)
    · intro h
      exact hγconv x (le_trans (h ps.1) (hγup ps.1 ps.2 hpsG rfl))

end YoungConventions.Perturbed

open YoungConventions.Perturbed


theorem solution {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (P0 : Matrix X X ℝ) (hP0 : P0 ∈ Matrix.rowStochastic ℝ X)
    (P : ℝ → Matrix X X ℝ) (a : ℝ) (hP : IsRegularPerturbation P0 P a)
    (μ : ℝ → X → ℝ) (hμ : ∀ ε ∈ Set.Ioc 0 a, IsStationaryDist (P ε) (μ ε)) :
    ∃ μ0 : X → ℝ,
      (∀ x, Tendsto (fun ε : ℝ => μ ε x) (𝓝[>] 0) (𝓝 (μ0 x))) ∧
      IsStationaryDist P0 μ0 ∧
      ∀ x, (0 < μ0 x ↔ ∀ y, statePotential P x ≤ statePotential P y) := by
  exact lemma_1_core P0 hP0 P a hP μ hμ
