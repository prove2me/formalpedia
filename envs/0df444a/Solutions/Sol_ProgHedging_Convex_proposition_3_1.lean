-- Prove2me | solution 1 for ProgHedging.Convex.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T14:17:45.124198+00:00
-- url     : https://prove2.me/submissions/536eb6c8-2109-41a6-a58b-db84c8943d59

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_ProgHedging_Convex_Duality
import Definitions.Def_ProgHedging_Convex_Algorithm
open scoped RealInnerProductSpace Pointwise Topology
open Filter

namespace PH51Aux
open ProgHedging.Convex

section avg
variable {S : Type*} [Fintype S]

open Classical in
noncomputable def avg (R : Setoid S) (p : S → ℝ) (x : S → ℝ) (s : S) : ℝ :=
  (∑ s' ∈ Finset.univ.filter (fun s' => R.r s' s), p s' * x s') /
    (∑ s' ∈ Finset.univ.filter (fun s' => R.r s' s), p s')

open Classical in
theorem filter_eq_of_rel (R : Setoid S) {s s₁ : S} (h : R.r s s₁) :
    Finset.univ.filter (fun s' => R.r s' s) = Finset.univ.filter (fun s' => R.r s' s₁) := by
  ext s'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h' => R.iseqv.trans h' h, fun h' => R.iseqv.trans h' (R.iseqv.symm h)⟩

theorem avg_eq_of_rel (R : Setoid S) (p x : S → ℝ) {s s₁ : S} (h : R.r s s₁) :
    avg R p x s = avg R p x s₁ := by
  classical
  unfold avg
  rw [filter_eq_of_rel R h]

open Classical in
theorem denom_pos (R : Setoid S) (p : S → ℝ) (hp : ∀ s, 0 < p s) (s : S) :
    0 < ∑ s' ∈ Finset.univ.filter (fun s' => R.r s' s), p s' := by
  apply Finset.sum_pos (fun i _ => hp i)
  exact ⟨s, by simp⟩

theorem avg_const (R : Setoid S) (p x : S → ℝ) (hp : ∀ s, 0 < p s)
    (hx : ∀ s s', R.r s s' → x s = x s') (s : S) : avg R p x s = x s := by
  classical
  unfold avg
  have hd := denom_pos R p hp s
  rw [div_eq_iff hd.ne', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s' hs'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs'
  rw [hx s' s hs']; ring

theorem avg_add (R : Setoid S) (p x y : S → ℝ) (s : S) :
    avg R p (x + y) s = avg R p x s + avg R p y s := by
  classical
  unfold avg
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl; intro i _; simp [mul_add]

theorem avg_smul (R : Setoid S) (p x : S → ℝ) (c : ℝ) (s : S) :
    avg R p (c • x) s = c * avg R p x s := by
  classical
  unfold avg
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro i _; simp; ring

theorem avg_selfAdj (R : Setoid S) (p x y : S → ℝ) :
    ∑ s, p s * (avg R p x s * y s) = ∑ s, p s * (x s * avg R p y s) := by
  classical
  unfold avg
  set D : S → ℝ := fun s => ∑ s' ∈ Finset.univ.filter (fun s' => R.r s' s), p s' with hD
  have hDr : ∀ s s', R.r s' s → D s = D s' := by
    intro s s' h
    simp only [hD]
    rw [filter_eq_of_rel R h]
  have lhs : ∀ s, p s * ((∑ s' ∈ Finset.univ.filter (fun s' => R.r s' s), p s' * x s') / D s * y s)
      = ∑ s', if R.r s' s then p s * p s' * x s' * y s / D s' else 0 := by
    intro s
    rw [Finset.sum_filter] at *
    rw [Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s' _
    split_ifs with h
    · rw [hDr s s' h]; ring
    · simp
  have rhs : ∀ s', p s' * (x s' * ((∑ s ∈ Finset.univ.filter (fun s => R.r s s'), p s * y s) / D s'))
      = ∑ s, if R.r s' s then p s * p s' * x s' * y s / D s' else 0 := by
    intro s'
    rw [Finset.sum_filter]
    rw [Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s _
    have : R.r s s' ↔ R.r s' s := ⟨fun h => R.iseqv.symm h, fun h => R.iseqv.symm h⟩
    by_cases h : R.r s' s
    · rw [if_pos (this.2 h), if_pos h]; ring
    · rw [if_neg (fun h' => h (this.1 h')), if_neg h]; ring
  simp only [hD] at lhs rhs ⊢
  rw [Finset.sum_congr rfl (fun s _ => lhs s), Finset.sum_congr rfl (fun s _ => rhs s)]
  exact Finset.sum_comm

end avg

end PH51Aux

namespace ProgHedging.Convex.Problem
open PH51Aux

variable {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)

theorem J_apply (X : Policy S n) (s : S) (j : Fin n) :
    pr.J X s j = avg (pr.bundle (pr.period j)) pr.p (fun s => X s j) s := by
  classical
  simp only [Problem.J, avg]
  rfl

theorem J_mem_N (X : Policy S n) : pr.J X ∈ pr.N := by
  intro j s s' h
  rw [J_apply, J_apply]
  exact avg_eq_of_rel _ _ _ h

theorem J_of_mem_N {X : Policy S n} (hX : X ∈ pr.N) : pr.J X = X := by
  funext s
  ext j
  rw [J_apply]
  exact avg_const _ _ _ pr.p_pos (fun s s' h => hX j s s' h) s

theorem J_add (X Y : Policy S n) : pr.J (X + Y) = pr.J X + pr.J Y := by
  funext s
  ext j
  simp only [J_apply, Pi.add_apply, PiLp.add_apply]
  exact avg_add _ _ (fun s => X s j) (fun s => Y s j) s

theorem J_smul (c : ℝ) (X : Policy S n) : pr.J (c • X) = c • pr.J X := by
  funext s
  ext j
  simp only [J_apply, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
  exact avg_smul _ _ (fun s => X s j) c s

noncomputable def Jl : Policy S n →ₗ[ℝ] Policy S n where
  toFun := pr.J
  map_add' := pr.J_add
  map_smul' := pr.J_smul

theorem Jl_apply (X : Policy S n) : pr.Jl X = pr.J X := rfl

theorem J_sub (X Y : Policy S n) : pr.J (X - Y) = pr.J X - pr.J Y := (pr.Jl).map_sub X Y

theorem J_zero : pr.J 0 = 0 := (pr.Jl).map_zero

theorem J_J (X : Policy S n) : pr.J (pr.J X) = pr.J X := pr.J_of_mem_N (pr.J_mem_N X)

theorem ip_expand (X Y : Policy S n) :
    pr.ip X Y = ∑ j, ∑ s, pr.p s * (X s j * Y s j) := by
  unfold Problem.ip
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro s _
  simp [PiLp.inner_apply, Finset.mul_sum, mul_comm]

theorem ip_J_left (X Y : Policy S n) : pr.ip (pr.J X) Y = pr.ip X (pr.J Y) := by
  rw [ip_expand, ip_expand]
  apply Finset.sum_congr rfl; intro j _
  simp only [J_apply]
  exact avg_selfAdj _ _ (fun s => X s j) (fun s => Y s j)

theorem ip_add_left (X Y Z : Policy S n) : pr.ip (X + Y) Z = pr.ip X Z + pr.ip Y Z := by
  unfold Problem.ip
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s _
  simp [inner_add_left, mul_add]

theorem ip_smul_left (c : ℝ) (X Y : Policy S n) : pr.ip (c • X) Y = c * pr.ip X Y := by
  unfold Problem.ip
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _
  simp [real_inner_smul_left]; ring

theorem ip_comm (X Y : Policy S n) : pr.ip X Y = pr.ip Y X := by
  unfold Problem.ip
  apply Finset.sum_congr rfl; intro s _
  rw [real_inner_comm]

theorem ip_add_right (X Y Z : Policy S n) : pr.ip Z (X + Y) = pr.ip Z X + pr.ip Z Y := by
  rw [ip_comm, ip_add_left, ip_comm, pr.ip_comm Y]

theorem ip_smul_right (c : ℝ) (X Y : Policy S n) : pr.ip Y (c • X) = c * pr.ip Y X := by
  rw [ip_comm, ip_smul_left, ip_comm]

noncomputable def ipL : Policy S n →ₗ[ℝ] Policy S n →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ pr.ip pr.ip_add_left (fun c X Y => pr.ip_smul_left c X Y)
    (fun X Y Z => pr.ip_add_right Y Z X) (fun c X Y => pr.ip_smul_right c Y X)

theorem ipL_apply (X Y : Policy S n) : pr.ipL X Y = pr.ip X Y := rfl

theorem ip_continuous : Continuous fun q : Policy S n × Policy S n => pr.ip q.1 q.2 := by
  unfold Problem.ip
  fun_prop

theorem ip_cont {α : Type*} [TopologicalSpace α] {f g : α → Policy S n} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => pr.ip (f x) (g x) := by
  unfold Problem.ip
  fun_prop

theorem ip_self_nonneg (X : Policy S n) : 0 ≤ pr.ip X X := by
  unfold Problem.ip
  exact Finset.sum_nonneg (fun s _ => mul_nonneg (pr.p_pos s).le real_inner_self_nonneg)

theorem ip_single_le (X : Policy S n) (s : S) : pr.p s * ‖X s‖ ^ 2 ≤ pr.ip X X := by
  unfold Problem.ip
  have := Finset.single_le_sum (f := fun s => pr.p s * ⟪X s, X s⟫)
    (fun s _ => mul_nonneg (pr.p_pos s).le real_inner_self_nonneg) (Finset.mem_univ s)
  simpa [real_inner_self_eq_norm_sq] using this

theorem ip_self_eq_zero {X : Policy S n} (h : pr.ip X X = 0) : X = 0 := by
  funext s
  have h1 := pr.ip_single_le X s
  have h2 : ‖X s‖ ^ 2 ≤ 0 := by
    rw [h] at h1
    by_contra hc; push Not at hc
    have := mul_pos (pr.p_pos s) hc; linarith
  have : ‖X s‖ = 0 := by nlinarith [norm_nonneg (X s)]
  simpa using this

noncomputable def cst : ℝ := ∑ s, (pr.p s)⁻¹

theorem cst_nonneg : 0 ≤ pr.cst := Finset.sum_nonneg (fun s _ => (inv_pos.2 (pr.p_pos s)).le)

theorem norm_sq_le (X : Policy S n) : ‖X‖ ^ 2 ≤ pr.cst * pr.ip X X := by
  have hc := pr.cst_nonneg
  have hi := pr.ip_self_nonneg X
  have key : ∀ s, ‖X s‖ ≤ Real.sqrt (pr.cst * pr.ip X X) := by
    intro s
    apply Real.le_sqrt_of_sq_le
    have h1 := pr.ip_single_le X s
    have hp := pr.p_pos s
    have h2 : ‖X s‖ ^ 2 ≤ (pr.p s)⁻¹ * pr.ip X X := by
      rw [← div_eq_inv_mul, le_div_iff₀ hp]; linarith
    have h3 : (pr.p s)⁻¹ ≤ pr.cst :=
      Finset.single_le_sum (f := fun s => (pr.p s)⁻¹)
        (fun s _ => (inv_pos.2 (pr.p_pos s)).le) (Finset.mem_univ s)
    nlinarith
  have := (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 key
  calc ‖X‖ ^ 2 ≤ Real.sqrt (pr.cst * pr.ip X X) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) this 2
    _ = _ := Real.sq_sqrt (mul_nonneg hc hi)

theorem K_eq (X : Policy S n) : pr.K X = X - pr.J X := rfl

theorem mem_M_iff (W : Policy S n) : W ∈ pr.M ↔ pr.J W = 0 := Iff.rfl

theorem mem_N_iff (X : Policy S n) : X ∈ pr.N ↔ pr.J X = X :=
  ⟨fun h => pr.J_of_mem_N h, fun h => h ▸ pr.J_mem_N X⟩

theorem K_mem_M (X : Policy S n) : pr.K X ∈ pr.M := by
  rw [mem_M_iff, K_eq, J_sub, J_J, sub_self]

theorem orth {Y Wv : Policy S n} (hY : Y ∈ pr.N) (hW : Wv ∈ pr.M) : pr.ip Y Wv = 0 := by
  rw [← pr.J_of_mem_N hY, ip_J_left, (mem_M_iff pr Wv).1 hW]
  unfold Problem.ip; simp

theorem orth' {Y Wv : Policy S n} (hY : Y ∈ pr.N) (hW : Wv ∈ pr.M) : pr.ip Wv Y = 0 := by
  rw [ip_comm]; exact pr.orth hY hW

theorem J_continuous : Continuous pr.J := (pr.Jl).continuous_of_finiteDimensional

theorem N_closed : IsClosed pr.N := by
  have : pr.N = {X | pr.J X = X} := by ext X; exact pr.mem_N_iff X
  rw [this]; exact isClosed_eq pr.J_continuous continuous_id

theorem M_closed : IsClosed pr.M := isClosed_eq pr.J_continuous continuous_const

theorem N_sum {ι : Type*} (t : Finset ι) (a : ι → ℝ) (V : ι → Policy S n)
    (h : ∀ i ∈ t, V i ∈ pr.N) : ∑ i ∈ t, a i • V i ∈ pr.N := by
  rw [mem_N_iff, ← Jl_apply, map_sum]
  apply Finset.sum_congr rfl; intro i hi
  rw [map_smul, Jl_apply, pr.J_of_mem_N (h i hi)]

theorem M_sum {ι : Type*} (t : Finset ι) (a : ι → ℝ) (V : ι → Policy S n)
    (h : ∀ i ∈ t, V i ∈ pr.M) : ∑ i ∈ t, a i • V i ∈ pr.M := by
  rw [mem_M_iff, ← Jl_apply, map_sum]
  apply Finset.sum_eq_zero; intro i hi
  rw [map_smul, Jl_apply, (mem_M_iff pr _).1 (h i hi), smul_zero]

theorem N_add {X Y : Policy S n} (hX : X ∈ pr.N) (hY : Y ∈ pr.N) : X + Y ∈ pr.N := by
  rw [mem_N_iff, J_add, pr.J_of_mem_N hX, pr.J_of_mem_N hY]
theorem N_sub {X Y : Policy S n} (hX : X ∈ pr.N) (hY : Y ∈ pr.N) : X - Y ∈ pr.N := by
  rw [mem_N_iff, J_sub, pr.J_of_mem_N hX, pr.J_of_mem_N hY]
theorem M_add {X Y : Policy S n} (hX : X ∈ pr.M) (hY : Y ∈ pr.M) : X + Y ∈ pr.M := by
  rw [mem_M_iff, J_add, (mem_M_iff pr _).1 hX, (mem_M_iff pr _).1 hY, add_zero]
theorem M_sub {X Y : Policy S n} (hX : X ∈ pr.M) (hY : Y ∈ pr.M) : X - Y ∈ pr.M := by
  rw [mem_M_iff, J_sub, (mem_M_iff pr _).1 hX, (mem_M_iff pr _).1 hY, sub_zero]
theorem M_smul (c : ℝ) {X : Policy S n} (hX : X ∈ pr.M) : c • X ∈ pr.M := by
  rw [mem_M_iff, J_smul, (mem_M_iff pr _).1 hX, smul_zero]
theorem M_neg {X : Policy S n} (hX : X ∈ pr.M) : -X ∈ pr.M := by
  have := pr.M_smul (-1) hX; simpa using this

theorem adm_closed : IsClosed pr.adm := by
  have : pr.adm = ⋂ s, (fun X : Policy S n => X s) ⁻¹' pr.C s := by
    ext X; simp [Problem.adm]
  rw [this]
  exact isClosed_iInter (fun s => (pr.C_closed s).preimage (continuous_apply s))

theorem F_continuous : Continuous pr.F := by
  unfold Problem.F
  have hf : ∀ s, Continuous (pr.f s) := fun s => (pr.f_locallyLipschitz s).continuous
  fun_prop

theorem adm_convex (hconv : pr.ConvexCase) : Convex ℝ pr.adm := by
  intro X hX Y hY a b ha hb hab s
  exact (hconv s).1 (hX s) (hY s) ha hb hab

theorem F_convexOn (hconv : pr.ConvexCase) : ConvexOn ℝ pr.adm pr.F := by
  refine ⟨pr.adm_convex hconv, ?_⟩
  intro X _ Y _ a b ha hb hab
  unfold Problem.F
  simp only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro s _
  have := (hconv s).2.2 (Set.mem_univ (X s)) (Set.mem_univ (Y s)) ha hb hab
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
  have hp := (pr.p_pos s).le
  nlinarith [mul_le_mul_of_nonneg_left this hp]
end ProgHedging.Convex.Problem

namespace PH51Aux

theorem vi_core {E : Type*} [AddCommGroup E] [Module ℝ E] (φ q : E → ℝ) (A : Set E) (x z : E)
    (ℓ m : ℝ)
    (hseg : ∀ t : ℝ, 0 < t → t ≤ 1 → x + t • (z - x) ∈ A)
    (hφ : ∀ t : ℝ, 0 < t → t ≤ 1 → φ (x + t • (z - x)) ≤ (1 - t) * φ x + t * φ z)
    (hq : ∀ t : ℝ, q (x + t • (z - x)) = q x + t * ℓ + t ^ 2 * m)
    (hmin : ∀ y ∈ A, φ x + q x ≤ φ y + q y) : 0 ≤ φ z - φ x + ℓ := by
  by_contra hD
  push Not at hD
  set D := φ z - φ x + ℓ with hDdef
  set t := min 1 (-D / (|m| + 1)) with ht
  have hm1 : 0 < |m| + 1 := by positivity
  have ht0 : 0 < t := lt_min one_pos (div_pos (by linarith) hm1)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ -D / (|m| + 1) := min_le_right _ _
  have ht3 : t * (|m| + 1) ≤ -D := by rwa [le_div_iff₀ hm1] at ht2
  have h1 := hmin _ (hseg t ht0 ht1)
  rw [hq t] at h1
  have h2 := hφ t ht0 ht1
  have h3 : 0 ≤ t * (D + t * m) := by rw [hDdef]; nlinarith
  have h4 : 0 ≤ D + t * m := by
    by_contra hc; push Not at hc; nlinarith
  have h5 : t * m ≤ t * |m| := mul_le_mul_of_nonneg_left (le_abs_self m) ht0.le
  nlinarith

end PH51Aux

namespace ProgHedging.Convex.Problem
open PH51Aux

variable {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)

theorem seg_eq {E : Type*} [AddCommGroup E] [Module ℝ E] (x z : E) (t : ℝ) :
    x + t • (z - x) = (1 - t) • x + t • z := by
  rw [smul_sub, sub_smul, one_smul]; abel

theorem scen_vi (hconv : pr.ConvexCase) {r : ℝ} (hr : 0 < r) (s : S)
    (v w x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ pr.C s)
    (hmin : ∀ z ∈ pr.C s, pr.subObj s v w r x ≤ pr.subObj s v w r z)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ pr.C s) :
    pr.f s x + ⟪z - x, -w - r • (x - v)⟫ ≤ pr.f s z := by
  have key := vi_core (fun y => pr.f s y + ⟪y, w⟫) (fun y => r / 2 * ‖y - v‖ ^ 2) (pr.C s) x z
    (r * ⟪x - v, z - x⟫) (r / 2 * ‖z - x‖ ^ 2)
    (fun t ht0 ht1 => by
      rw [seg_eq]; exact (hconv s).1 hx hz (by linarith) ht0.le (by ring))
    (fun t ht0 ht1 => by
      beta_reduce
      rw [seg_eq]
      have := (hconv s).2.2 (Set.mem_univ x) (Set.mem_univ z) (by linarith : (0:ℝ) ≤ 1 - t)
        ht0.le (by ring)
      simp only [smul_eq_mul] at this
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      nlinarith)
    (fun t => by
      beta_reduce
      have : x + t • (z - x) - v = (x - v) + t • (z - x) := by abel
      rw [this, norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs]
      ring)
    (fun y hy => by
      have := hmin y hy
      simp only [Problem.subObj] at this
      linarith)
  beta_reduce at key
  simp only [inner_sub_left, inner_sub_right, inner_neg_right, real_inner_smul_right] at key ⊢
  rw [real_inner_comm x v, real_inner_comm z v, real_inner_comm x z, real_inner_comm w x,
    real_inner_comm w z] at *
  nlinarith

def Sub (Xp g : Policy S n) : Prop :=
  Xp ∈ pr.adm ∧ ∀ Z ∈ pr.adm, pr.F Xp + pr.ip (Z - Xp) g ≤ pr.F Z

def KKT (Xs Ws : Policy S n) : Prop :=
  Xs ∈ pr.N ∧ Ws ∈ pr.M ∧ pr.Sub Xs (-Ws)

theorem step_sub (hconv : pr.ConvexCase) {r : ℝ} (hr : 0 < r) (V W Xp : Policy S n)
    (h : ∀ s, Xp s ∈ pr.C s ∧ ∀ z ∈ pr.C s,
      pr.subObj s (V s) (W s) r (Xp s) ≤ pr.subObj s (V s) (W s) r z) :
    pr.Sub Xp (-W - r • (Xp - V)) := by
  refine ⟨fun s => (h s).1, fun Z hZ => ?_⟩
  unfold Problem.F Problem.ip
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro s _
  have := pr.scen_vi hconv hr s (V s) (W s) (Xp s) (h s).1 (h s).2 (Z s) (hZ s)
  have hp := (pr.p_pos s).le
  simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply]
  nlinarith [mul_le_mul_of_nonneg_left this hp]

theorem ip_sub_left (X Y Z : Policy S n) : pr.ip (X - Y) Z = pr.ip X Z - pr.ip Y Z := by
  simp only [← ipL_apply, map_sub, LinearMap.sub_apply]
theorem ip_sub_right (X Y Z : Policy S n) : pr.ip Z (X - Y) = pr.ip Z X - pr.ip Z Y := by
  simp only [← ipL_apply, map_sub]
theorem ip_neg_left (X Z : Policy S n) : pr.ip (-X) Z = - pr.ip X Z := by
  simp only [← ipL_apply, map_neg, LinearMap.neg_apply]
theorem ip_neg_right (X Z : Policy S n) : pr.ip Z (-X) = - pr.ip Z X := by
  simp only [← ipL_apply, map_neg]
theorem ip_zero_right (Z : Policy S n) : pr.ip Z 0 = 0 := by
  simp only [← ipL_apply, map_zero]
theorem ip_zero_left (Z : Policy S n) : pr.ip 0 Z = 0 := by
  simp only [← ipL_apply, map_zero, LinearMap.zero_apply]

theorem mono {X1 g1 X2 g2 : Policy S n} (h1 : pr.Sub X1 g1) (h2 : pr.Sub X2 g2) :
    0 ≤ pr.ip (X1 - X2) (g1 - g2) := by
  have a := h1.2 X2 h2.1
  have b := h2.2 X1 h1.1
  have : pr.ip (X2 - X1) g1 = - pr.ip (X1 - X2) g1 := by
    rw [← ip_neg_left, neg_sub]
  rw [ip_sub_right]
  linarith

noncomputable def rsq (r : ℝ) (a b : Policy S n) : ℝ := pr.ip a a + (r⁻¹) ^ 2 * pr.ip b b

theorem rnorm_eq (r : ℝ) (a b : Policy S n) : pr.rnorm r a b = Real.sqrt (pr.rsq r a b) := rfl

theorem rsq_nonneg (r : ℝ) (a b : Policy S n) : 0 ≤ pr.rsq r a b := by
  unfold rsq
  have := pr.ip_self_nonneg a; have := pr.ip_self_nonneg b; positivity

theorem fne {r : ℝ} (hr : 0 < r) {V W V' W' U Y U' Y' : Policy S n}
    (hV : V ∈ pr.N) (hV' : V' ∈ pr.N) (hU : U ∈ pr.N) (hU' : U' ∈ pr.N)
    (hW : W ∈ pr.M) (hW' : W' ∈ pr.M) (hY : Y ∈ pr.M) (hY' : Y' ∈ pr.M)
    (h1 : pr.Sub (V' + r⁻¹ • (W' - W)) (-W' - r • (V' - V)))
    (h2 : pr.Sub (U' + r⁻¹ • (Y' - Y)) (-Y' - r • (U' - U))) :
    pr.rsq r (V' - U') (W' - Y') + pr.rsq r ((V - V') - (U - U')) ((W - W') - (Y - Y')) ≤
      pr.rsq r (V - U) (W - Y) := by
  have hm := pr.mono h1 h2
  have e1 : (V' + r⁻¹ • (W' - W)) - (U' + r⁻¹ • (Y' - Y)) =
      (V' - U') + r⁻¹ • ((W' - Y') - (W - Y)) := by module
  have e2 : (-W' - r • (V' - V)) - (-Y' - r • (U' - U)) =
      -(W' - Y') - r • ((V' - U') - (V - U)) := by module
  have e3 : (V - V') - (U - U') = (V - U) - (V' - U') := by abel
  have e4 : (W - W') - (Y - Y') = (W - Y) - (W' - Y') := by abel
  rw [e1, e2] at hm
  rw [e3, e4]
  have ha := pr.N_sub hV' hU'
  have ha0 := pr.N_sub hV hU
  have hb := pr.M_sub hW' hY'
  have hb0 := pr.M_sub hW hY
  generalize V' - U' = a at *
  generalize V - U = a0 at *
  generalize W' - Y' = b at *
  generalize W - Y = b0 at *
  unfold rsq
  simp only [← ipL_apply, map_add, map_sub, map_neg, map_smul, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at hm ⊢
  simp only [ipL_apply] at hm ⊢
  have o1 : pr.ip b a = 0 := pr.orth' ha hb
  have o2 : pr.ip b0 a = 0 := pr.orth' ha hb0
  have o3 : pr.ip b a0 = 0 := pr.orth' ha0 hb
  have o4 : pr.ip b0 a0 = 0 := pr.orth' ha0 hb0
  have c1 : pr.ip a0 a = pr.ip a a0 := pr.ip_comm a0 a
  have c2 : pr.ip b0 b = pr.ip b b0 := pr.ip_comm b0 b
  have o5 : pr.ip a b = 0 := pr.orth ha hb
  have o6 : pr.ip a b0 = 0 := pr.orth ha hb0
  have o7 : pr.ip a0 b = 0 := pr.orth ha0 hb
  have o8 : pr.ip a0 b0 = 0 := pr.orth ha0 hb0
  simp only [o1, o2, o3, o4, o5, o6, o7, o8, c1, c2] at hm ⊢
  have hri : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  set A := pr.ip a a
  set B := pr.ip a a0
  set C := pr.ip b b
  set D := pr.ip b b0
  have key : r⁻¹ * (r * (B - A) + r⁻¹ * (D - C)) = (B - A) + r⁻¹ ^ 2 * (D - C) := by
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]; ring
  have hm' : 0 ≤ r * (B - A) + r⁻¹ * (D - C) := by linear_combination hm
  have hk : 0 ≤ r⁻¹ * (r * (B - A) + r⁻¹ * (D - C)) :=
    mul_nonneg (inv_nonneg.2 hr.le) hm'
  rw [key] at hk
  linear_combination 2 * hk

end ProgHedging.Convex.Problem
namespace PH51Aux

theorem exists_min_of {E : Type*} [MetricSpace E] [ProperSpace E] (A : Set E) (hA : IsClosed A)
    (hne : A.Nonempty) (g : E → ℝ) (hg : Continuous g)
    (hb : ∀ β, Bornology.IsBounded {x | x ∈ A ∧ g x ≤ β}) : ∃ x ∈ A, ∀ y ∈ A, g x ≤ g y := by
  obtain ⟨x0, hx0⟩ := hne
  have hK : IsCompact {x | x ∈ A ∧ g x ≤ g x0} :=
    Metric.isCompact_of_isClosed_isBounded (hA.inter (isClosed_le hg continuous_const)) (hb _)
  obtain ⟨x1, hx1, hmin⟩ := hK.exists_isMinOn ⟨x0, hx0, le_rfl⟩ hg.continuousOn
  refine ⟨x1, hx1.1, fun y hy => ?_⟩
  by_cases h : g y ≤ g x0
  · exact hmin ⟨hy, h⟩
  · push Not at h; exact le_trans hx1.2 h.le

end PH51Aux

namespace ProgHedging.Convex.Problem
open PH51Aux

variable {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)

theorem solvesP_of_KKT {Xs Ws : Policy S n} (h : pr.KKT Xs Ws) : pr.SolvesP Xs := by
  obtain ⟨hN, hM, hadm, hsub⟩ := h
  refine ⟨⟨hadm, hN⟩, fun X hX => ?_⟩
  have := hsub X hX.1
  rw [ip_neg_right, pr.orth (pr.N_sub hX.2 hN) hM] at this
  linarith

theorem solvesD_of_KKT {Xs Ws : Policy S n} (h : pr.KKT Xs Ws) : pr.SolvesD Ws := by
  obtain ⟨hN, hM, hadm, hsub⟩ := h
  have hlow : ((pr.F Xs : ℝ) : EReal) ≤ pr.G Ws := by
    apply le_iInf₂; intro X hX
    apply EReal.coe_le_coe_iff.2
    have := hsub X hX
    rw [ip_neg_right, ip_sub_left, pr.orth hN hM] at this
    unfold Problem.L; linarith
  refine ⟨hM, lt_of_lt_of_le (EReal.bot_lt_coe _) hlow, fun W hW => le_trans ?_ hlow⟩
  refine le_trans (iInf₂_le Xs hadm) ?_
  apply EReal.coe_le_coe_iff.2
  unfold Problem.L; rw [pr.orth hN hW]; linarith

theorem f_bdd_below (s : S) : ∃ m, ∀ x ∈ pr.C s, m ≤ pr.f s x := by
  obtain ⟨x, _, hx⟩ := exists_min_of (pr.C s) (pr.C_closed s) (pr.C_nonempty s) (pr.f s)
    (pr.f_locallyLipschitz s).continuous (fun β => pr.levelSet_bounded s β)
  exact ⟨pr.f s x, hx⟩

theorem F_levelset_bdd (β : ℝ) : Bornology.IsBounded {X | X ∈ pr.adm ∧ pr.F X ≤ β} := by
  choose m hm using pr.f_bdd_below
  set Sm := ∑ s, pr.p s * m s
  apply (Bornology.IsBounded.pi (fun s => pr.levelSet_bounded s (m s + (β - Sm) / pr.p s))).subset
  intro X hX s _
  refine ⟨hX.1 s, ?_⟩
  have hp := pr.p_pos s
  have h1 : pr.p s * (pr.f s (X s) - m s) ≤ ∑ s', pr.p s' * (pr.f s' (X s') - m s') :=
    Finset.single_le_sum (f := fun s' => pr.p s' * (pr.f s' (X s') - m s'))
      (fun s' _ => mul_nonneg (pr.p_pos s').le (sub_nonneg.2 (hm s' _ (hX.1 s'))))
      (Finset.mem_univ s)
  have h2 : ∑ s', pr.p s' * (pr.f s' (X s') - m s') = pr.F X - Sm := by
    unfold Problem.F; rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro s' _; ring
  have h3 : pr.f s (X s) - m s ≤ (β - Sm) / pr.p s := by
    rw [le_div_iff₀ hp]; nlinarith [hX.2]
  linarith

theorem K_add (X Y : Policy S n) : pr.K (X + Y) = pr.K X + pr.K Y := by
  simp only [K_eq, J_add]; abel
theorem K_sub (X Y : Policy S n) : pr.K (X - Y) = pr.K X - pr.K Y := by
  simp only [K_eq, J_sub]; abel
theorem K_smul (c : ℝ) (X : Policy S n) : pr.K (c • X) = c • pr.K X := by
  simp only [K_eq, J_smul, smul_sub]

theorem K_continuous : Continuous pr.K := by
  have : pr.K = fun X => X - pr.J X := rfl
  rw [this]; exact continuous_id.sub pr.J_continuous

theorem ip_K_K (A B : Policy S n) : pr.ip (pr.K A) (pr.K B) = pr.ip (pr.K A) B := by
  rw [pr.K_eq B, ip_sub_right, pr.orth' (pr.J_mem_N B) (pr.K_mem_M A), sub_zero]

theorem decomp (X : Policy S n) : X = pr.J X + pr.K X := by
  rw [K_eq]; abel

theorem kkt_of_solvesD (hconv : pr.ConvexCase) {Ws : Policy S n} (hD : pr.SolvesD Ws) :
    ∃ Xs, pr.KKT Xs Ws := by
  have hWs := hD.1
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Policy S n → ℝ,
      Ψ = fun X => pr.F X + pr.ip X Ws + 1 / 2 * pr.ip (pr.K X) (pr.K X) := ⟨_, rfl⟩
  have hΨc : Continuous Ψ := by
    have h1 := pr.F_continuous
    have h2 : Continuous fun X => pr.ip X Ws := pr.ip_cont continuous_id continuous_const
    have h3 : Continuous fun X => pr.ip (pr.K X) (pr.K X) :=
      pr.ip_cont pr.K_continuous pr.K_continuous
    rw [hΨ]
    exact (h1.add h2).add (continuous_const.mul h3)
  have hlow : ∀ X, pr.F X - 1 / 2 * pr.ip Ws Ws ≤ Ψ X := by
    intro X
    have e : pr.ip X Ws = pr.ip (pr.K X) Ws := by
      conv_lhs => rw [pr.decomp X]
      rw [ip_add_left, pr.orth (pr.J_mem_N X) hWs, zero_add]
    have hn := pr.ip_self_nonneg (pr.K X + Ws)
    rw [ip_add_left, ip_add_right, ip_add_right, pr.ip_comm Ws (pr.K X)] at hn
    simp only [hΨ, e]; nlinarith
  have hne : pr.adm.Nonempty := by
    choose c hc using pr.C_nonempty
    exact ⟨c, hc⟩
  obtain ⟨Xb, hXb, hmin⟩ := exists_min_of pr.adm pr.adm_closed hne Ψ hΨc (fun β => by
    apply (pr.F_levelset_bdd (β + 1 / 2 * pr.ip Ws Ws)).subset
    intro X hX; refine ⟨hX.1, ?_⟩; have := hlow X; linarith [hX.2])
  -- variational inequality
  have hvi : ∀ Z ∈ pr.adm, 0 ≤ (pr.F Z + pr.ip Z Ws) - (pr.F Xb + pr.ip Xb Ws) +
      pr.ip (pr.K Xb) (pr.K (Z - Xb)) := by
    intro Z hZ
    have := vi_core (fun X => pr.F X + pr.ip X Ws)
      (fun X => 1 / 2 * pr.ip (pr.K X) (pr.K X)) pr.adm Xb Z
      (pr.ip (pr.K Xb) (pr.K (Z - Xb))) (1 / 2 * pr.ip (pr.K (Z - Xb)) (pr.K (Z - Xb)))
      (fun t ht0 ht1 => by
        rw [seg_eq]; exact pr.adm_convex hconv hXb hZ (by linarith) ht0.le (by ring))
      (fun t ht0 ht1 => by
        beta_reduce
        rw [seg_eq]
        have := (pr.F_convexOn hconv).2 hXb hZ (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
        simp only [smul_eq_mul] at this
        rw [ip_add_left, ip_smul_left, ip_smul_left]
        nlinarith)
      (fun t => by
        beta_reduce
        rw [K_add, K_smul, ip_add_left, ip_add_right, ip_add_right, ip_smul_left, ip_smul_left,
          ip_smul_right, ip_smul_right, pr.ip_comm (pr.K (Z - Xb)) (pr.K Xb)]
        ring)
      (fun y hy => by have := hmin y hy; simp only [hΨ] at this; linarith)
    exact this
  have hW1 : Ws + pr.K Xb ∈ pr.M := pr.M_add hWs (pr.K_mem_M Xb)
  have hG1 : ((pr.L Xb (Ws + pr.K Xb) : ℝ) : EReal) ≤ pr.G (Ws + pr.K Xb) := by
    apply le_iInf₂; intro Z hZ
    apply EReal.coe_le_coe_iff.2
    have := hvi Z hZ
    rw [ip_K_K, ip_sub_right, pr.ip_comm (pr.K Xb) Z, pr.ip_comm (pr.K Xb) Xb] at this
    unfold Problem.L; rw [ip_add_right, ip_add_right]; linarith
  have hG2 := hD.2.2 _ hW1
  have hG3 : pr.G Ws ≤ ((pr.L Xb Ws : ℝ) : EReal) := iInf₂_le Xb hXb
  have hreal : pr.L Xb (Ws + pr.K Xb) ≤ pr.L Xb Ws :=
    EReal.coe_le_coe_iff.1 (hG1.trans (hG2.trans hG3))
  unfold Problem.L at hreal
  rw [ip_add_right, pr.ip_comm Xb (pr.K Xb), ← ip_K_K] at hreal
  have hK0 : pr.K Xb = 0 := pr.ip_self_eq_zero (le_antisymm (by linarith) (pr.ip_self_nonneg _))
  have hXN : Xb ∈ pr.N := by
    rw [mem_N_iff]; have := pr.decomp Xb; rw [hK0, add_zero] at this; exact this.symm
  refine ⟨Xb, hXN, hWs, hXb, fun Z hZ => ?_⟩
  have := hvi Z hZ
  rw [hK0, ip_zero_left] at this
  rw [ip_neg_right, ip_sub_left]
  linarith

end ProgHedging.Convex.Problem
namespace ProgHedging.Convex.Problem
open PH51Aux

variable {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)

theorem norm_sq_le_rsq_left {r : ℝ} (a b : Policy S n) : ‖a‖ ^ 2 ≤ pr.cst * pr.rsq r a b := by
  have h1 := pr.norm_sq_le a
  have h2 : pr.ip a a ≤ pr.rsq r a b := by
    unfold rsq; have := pr.ip_self_nonneg b; nlinarith [sq_nonneg r⁻¹]
  nlinarith [pr.cst_nonneg]

theorem norm_sq_le_rsq_right {r : ℝ} (hr : 0 < r) (a b : Policy S n) :
    ‖b‖ ^ 2 ≤ pr.cst * r ^ 2 * pr.rsq r a b := by
  have h1 := pr.norm_sq_le b
  have h2 : pr.ip b b ≤ r ^ 2 * pr.rsq r a b := by
    unfold rsq
    have := pr.ip_self_nonneg a
    have e : r ^ 2 * (r⁻¹ ^ 2 * pr.ip b b) = pr.ip b b := by
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hr.ne', one_pow, one_mul]
    nlinarith [sq_nonneg r]
  nlinarith [pr.cst_nonneg]

theorem rsq_eq_zero {r : ℝ} (hr : 0 < r) {a b : Policy S n} (h : pr.rsq r a b ≤ 0) :
    a = 0 ∧ b = 0 := by
  have ha := pr.ip_self_nonneg a
  have hb := pr.ip_self_nonneg b
  have hr2 : 0 < r⁻¹ ^ 2 := by positivity
  unfold rsq at h
  have h1 : pr.ip a a = 0 := by nlinarith
  have h2 : pr.ip b b = 0 := by nlinarith
  exact ⟨pr.ip_self_eq_zero h1, pr.ip_self_eq_zero h2⟩

section seq
variable {pr} (hconv : pr.ConvexCase) {r : ℝ} (hr : 0 < r) {X W : ℕ → Policy S n}
  (hseq : pr.IsExactPHSeq r X W)
include hseq

theorem seq_W_mem (ν : ℕ) : W ν ∈ pr.M := by
  induction ν with
  | zero => exact hseq.1
  | succ k ih =>
    rw [(hseq.2 k).2]
    exact pr.M_add ih (pr.M_smul r (pr.K_mem_M _))

include hr in
theorem seq_X_eq (ν : ℕ) : X (ν + 1) = pr.J (X (ν + 1)) + r⁻¹ • (W (ν + 1) - W ν) := by
  rw [(hseq.2 ν).2, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  exact pr.decomp _

include hconv hr in
theorem seq_sub (ν : ℕ) :
    pr.Sub (pr.J (X (ν + 1)) + r⁻¹ • (W (ν + 1) - W ν))
      (-W (ν + 1) - r • (pr.J (X (ν + 1)) - pr.J (X ν))) := by
  have h := pr.step_sub hconv hr (pr.J (X ν)) (W ν) (X (ν + 1)) (hseq.2 ν).1
  have e1 := seq_X_eq hr hseq ν
  have e2 : -W ν - r • (X (ν + 1) - pr.J (X ν)) =
      -W (ν + 1) - r • (pr.J (X (ν + 1)) - pr.J (X ν)) := by
    rw [(hseq.2 ν).2]
    conv_lhs => rw [pr.decomp (X (ν + 1))]
    module
  rw [e2] at h
  rwa [← e1]

include hconv hr in
theorem seq_fejer {Xs Ws : Policy S n} (hk : pr.KKT Xs Ws) (ν : ℕ) :
    pr.rsq r (pr.J (X (ν + 1)) - Xs) (W (ν + 1) - Ws) +
      pr.rsq r (pr.J (X ν) - pr.J (X (ν + 1))) (W ν - W (ν + 1)) ≤
      pr.rsq r (pr.J (X ν) - Xs) (W ν - Ws) := by
  have h2 : pr.Sub (Xs + r⁻¹ • (Ws - Ws)) (-Ws - r • (Xs - Xs)) := by
    simpa using hk.2.2
  have := pr.fne hr (pr.J_mem_N (X ν)) (pr.J_mem_N (X (ν + 1))) hk.1 hk.1
    (seq_W_mem hseq ν) (seq_W_mem hseq (ν + 1)) hk.2.1 hk.2.1
    (seq_sub hconv hr hseq ν) h2
  simpa using this

include hconv hr in
theorem seq_step_mono (m : ℕ) :
    pr.rsq r (pr.J (X (m + 2)) - pr.J (X (m + 1))) (W (m + 2) - W (m + 1)) ≤
      pr.rsq r (pr.J (X (m + 1)) - pr.J (X m)) (W (m + 1) - W m) := by
  have := pr.fne hr (pr.J_mem_N (X (m + 1))) (pr.J_mem_N (X (m + 2))) (pr.J_mem_N (X m))
    (pr.J_mem_N (X (m + 1)))
    (seq_W_mem hseq (m + 1)) (seq_W_mem hseq (m + 2)) (seq_W_mem hseq m) (seq_W_mem hseq (m + 1))
    (seq_sub hconv hr hseq (m + 1)) (seq_sub hconv hr hseq m)
  have := pr.rsq_nonneg r ((pr.J (X (m + 1)) - pr.J (X (m + 2))) - (pr.J (X m) - pr.J (X (m + 1))))
    ((W (m + 1) - W (m + 2)) - (W m - W (m + 1)))
  linarith

end seq

end ProgHedging.Convex.Problem
namespace ProgHedging.Convex.Problem
open PH51Aux

variable {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)

theorem limit_sub {Xi Wi : ℕ → Policy S n} {εi : ℕ → ℝ} {Xh Wh : Policy S n}
    (hXi : ∀ i, Xi i ∈ pr.adm) (hX : Tendsto Xi atTop (𝓝 Xh)) (hW : Tendsto Wi atTop (𝓝 Wh))
    (hε : Tendsto εi atTop (𝓝 0))
    (h : ∀ i, ∀ Z ∈ pr.adm, pr.F (Xi i) ≤ pr.F Z + pr.ip Z (Wi i) + εi i) :
    Xh ∈ pr.adm ∧ ∀ Z ∈ pr.adm, pr.F Xh ≤ pr.F Z + pr.ip Z Wh := by
  refine ⟨pr.adm_closed.mem_of_tendsto hX (Eventually.of_forall hXi), fun Z hZ => ?_⟩
  have h1 : Tendsto (fun i => pr.F (Xi i)) atTop (𝓝 (pr.F Xh)) :=
    (pr.F_continuous.tendsto Xh).comp hX
  have h2 : Tendsto (fun i => pr.F Z + pr.ip Z (Wi i) + εi i) atTop
      (𝓝 (pr.F Z + pr.ip Z Wh + 0)) := by
    refine (tendsto_const_nhds.add ?_).add hε
    exact ((pr.ip_cont continuous_const continuous_id).tendsto Wh).comp hW
  have := le_of_tendsto_of_tendsto' h1 h2 (fun i => h i Z hZ)
  simpa using this

theorem kkt_of_limit {Xh Wh : Policy S n} (hN : Xh ∈ pr.N) (hM : Wh ∈ pr.M)
    (h : Xh ∈ pr.adm ∧ ∀ Z ∈ pr.adm, pr.F Xh ≤ pr.F Z + pr.ip Z Wh) : pr.KKT Xh Wh := by
  refine ⟨hN, hM, h.1, fun Z hZ => ?_⟩
  have := h.2 Z hZ
  rw [ip_neg_right, ip_sub_left, pr.orth hN hM]
  linarith

theorem tendsto_smul_bdd {t : ℕ → ℝ} {v : ℕ → Policy S n} {C : ℝ}
    (ht : Tendsto t atTop (𝓝 0)) (hv : ∀ i, ‖v i‖ ≤ C) :
    Tendsto (fun i => t i • v i) atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := fun i => |t i| * C)
  · intro i; rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _)
  · have := (ht.abs).mul_const C
    simpa using this

theorem step_energy {r : ℝ} (hr : 0 < r) {V V' Wv W' : Policy S n}
    (hV : V ∈ pr.N) (hV' : V' ∈ pr.N) (hW : Wv ∈ pr.M) (hW' : W' ∈ pr.M) :
    (r * pr.ip V' V' + r⁻¹ * pr.ip W' W') - (r * pr.ip V V + r⁻¹ * pr.ip Wv Wv) ≤
      -2 * pr.ip (V' + r⁻¹ • (W' - Wv)) (-W' - r • (V' - V)) := by
  have hd := pr.ip_self_nonneg (V' - V)
  have he := pr.ip_self_nonneg (W' - Wv)
  simp only [← ipL_apply, map_add, map_sub, map_neg, map_smul, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.neg_apply, smul_eq_mul] at hd he ⊢
  simp only [ipL_apply] at hd he ⊢
  have o1 : pr.ip V' W' = 0 := pr.orth hV' hW'
  have o2 : pr.ip Wv V' = 0 := pr.orth' hV' hW
  have o3 : pr.ip Wv V = 0 := pr.orth' hV hW
  have o4 : pr.ip W' V' = 0 := pr.orth' hV' hW'
  have o5 : pr.ip W' V = 0 := pr.orth' hV hW'
  have c1 : pr.ip V V' = pr.ip V' V := pr.ip_comm _ _
  have c2 : pr.ip Wv W' = pr.ip W' Wv := pr.ip_comm _ _
  simp only [o1, o2, o3, o4, o5, c1, c2] at hd he ⊢
  have hri : 0 < r⁻¹ := inv_pos.2 hr
  nlinarith [mul_nonneg hr.le hd, mul_nonneg hri.le he]

end ProgHedging.Convex.Problem
namespace ProgHedging.Convex.Problem
open PH51Aux

variable {S : Type*} [Fintype S] {n T : ℕ} {pr : Problem S n T}

theorem ip_sum_right (Z : Policy S n) (t : Finset ℕ) (c : ℕ → ℝ) (g : ℕ → Policy S n) :
    pr.ip Z (∑ i ∈ t, c i • g i) = ∑ i ∈ t, c i * pr.ip Z (g i) := by
  simp only [← ipL_apply, map_sum, map_smul, smul_eq_mul]

section seq2
variable (hconv : pr.ConvexCase) {r : ℝ} (hr : 0 < r) {X W : ℕ → Policy S n}
  (hseq : pr.IsExactPHSeq r X W)
include hconv hr hseq

theorem seq_ergodic (K : ℕ) (Z : Policy S n) (hZ : Z ∈ pr.adm) :
    pr.F (∑ ν ∈ Finset.range (K + 1), ((K : ℝ) + 1)⁻¹ • X (ν + 1)) ≤
      pr.F Z + pr.ip Z (∑ ν ∈ Finset.range (K + 1), ((K : ℝ) + 1)⁻¹ • W (ν + 1) +
        (((K : ℝ) + 1)⁻¹ * r) • (pr.J (X (K + 1)) - pr.J (X 0))) +
      ((K : ℝ) + 1)⁻¹ * ((r * pr.ip (pr.J (X 0)) (pr.J (X 0)) + r⁻¹ * pr.ip (W 0) (W 0)) / 2) := by
  set a : ℝ := ((K : ℝ) + 1)⁻¹ with ha
  have ha0 : 0 ≤ a := by positivity
  have hsum1 : ∑ ν ∈ Finset.range (K + 1), a = 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ha]; push_cast
    field_simp
  set Φ : ℕ → ℝ := fun ν => r * pr.ip (pr.J (X ν)) (pr.J (X ν)) + r⁻¹ * pr.ip (W ν) (W ν)
    with hΦ
  have hΦnn : ∀ ν, 0 ≤ Φ ν := fun ν => by
    simp only [hΦ]
    have := pr.ip_self_nonneg (pr.J (X ν)); have := pr.ip_self_nonneg (W ν)
    have := inv_pos.2 hr; positivity
  set g : ℕ → Policy S n := fun ν => -W (ν + 1) - r • (pr.J (X (ν + 1)) - pr.J (X ν)) with hg
  have hstep : ∀ ν, pr.F (X (ν + 1)) ≤ pr.F Z - pr.ip Z (g ν) - (Φ (ν + 1) - Φ ν) / 2 := by
    intro ν
    have h1 := (seq_sub hconv hr hseq ν).2 Z hZ
    have h2 := pr.step_energy hr (pr.J_mem_N (X ν)) (pr.J_mem_N (X (ν + 1)))
      (seq_W_mem hseq ν) (seq_W_mem hseq (ν + 1))
    rw [← seq_X_eq hr hseq ν] at h1 h2
    rw [ip_sub_left] at h1
    simp only [hΦ, hg]
    linarith
  have hconvF := pr.F_convexOn hconv
  have hjensen := hconvF.map_sum_le (t := Finset.range (K + 1)) (w := fun _ => a)
    (p := fun ν => X (ν + 1)) (fun _ _ => ha0) hsum1 (fun ν _ => fun s => ((hseq.2 ν).1 s).1)
  simp only [smul_eq_mul] at hjensen
  have hsum2 : ∑ ν ∈ Finset.range (K + 1), a * pr.F (X (ν + 1)) ≤
      ∑ ν ∈ Finset.range (K + 1), a * (pr.F Z - pr.ip Z (g ν) - (Φ (ν + 1) - Φ ν) / 2) :=
    Finset.sum_le_sum (fun ν _ => mul_le_mul_of_nonneg_left (hstep ν) ha0)
  have hsum3 : ∑ ν ∈ Finset.range (K + 1), a * (pr.F Z - pr.ip Z (g ν) - (Φ (ν + 1) - Φ ν) / 2)
      = pr.F Z - pr.ip Z (∑ ν ∈ Finset.range (K + 1), a • g ν) - a * (Φ (K + 1) - Φ 0) / 2 := by
    rw [ip_sum_right]
    have e1 : ∑ ν ∈ Finset.range (K + 1), a * (Φ (ν + 1) - Φ ν) = a * (Φ (K + 1) - Φ 0) := by
      rw [← Finset.mul_sum, Finset.sum_range_sub]
    have e2 : ∑ ν ∈ Finset.range (K + 1), a * pr.F Z = pr.F Z := by
      rw [← Finset.sum_mul, hsum1, one_mul]
    have e3 : ∀ ν, a * (pr.F Z - pr.ip Z (g ν) - (Φ (ν + 1) - Φ ν) / 2) =
        a * pr.F Z - a * pr.ip Z (g ν) - (a * (Φ (ν + 1) - Φ ν)) / 2 := fun ν => by ring
    rw [Finset.sum_congr rfl (fun ν _ => e3 ν), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_div, e1, e2]
  have hg2 : ∑ ν ∈ Finset.range (K + 1), g ν =
      -(∑ ν ∈ Finset.range (K + 1), W (ν + 1)) - r • (pr.J (X (K + 1)) - pr.J (X 0)) := by
    simp only [hg]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.smul_sum,
      Finset.sum_range_sub (fun ν => pr.J (X ν))]
  have hgsum : ∑ ν ∈ Finset.range (K + 1), a • g ν =
      -(∑ ν ∈ Finset.range (K + 1), a • W (ν + 1) + (a * r) • (pr.J (X (K + 1)) - pr.J (X 0))) := by
    rw [← Finset.smul_sum, hg2, ← Finset.smul_sum]
    module
  rw [hgsum, ip_neg_right] at hsum3
  have := hΦnn (K + 1)
  have : 0 ≤ a * Φ (K + 1) := mul_nonneg ha0 this
  simp only [hΦ] at *
  linarith

end seq2

end ProgHedging.Convex.Problem
namespace PH51Aux

theorem wsum (K : ℕ) : ∑ _ν ∈ Finset.range (K + 1), ((K : ℝ) + 1)⁻¹ = 1 := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast
  field_simp

theorem avg_norm_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] (v : ℕ → E) (C : ℝ)
    (hv : ∀ ν, ‖v ν‖ ≤ C) (K : ℕ) :
    ‖∑ ν ∈ Finset.range (K + 1), ((K : ℝ) + 1)⁻¹ • v ν‖ ≤ C := by
  refine (norm_sum_le _ _).trans ?_
  have : ∀ ν ∈ Finset.range (K + 1), ‖((K : ℝ) + 1)⁻¹ • v ν‖ ≤ ((K : ℝ) + 1)⁻¹ * C := by
    intro ν _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left (hv ν) (by positivity)
  refine (Finset.sum_le_sum this).trans ?_
  rw [← Finset.sum_mul, wsum, one_mul]

theorem tendsto_wt {φ : ℕ → ℕ} (hφ : StrictMono φ) (c : ℝ) :
    Tendsto (fun i => ((φ i : ℝ) + 1)⁻¹ * c) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
  have := h.mul_const c
  simp only [zero_mul] at this
  refine this.congr (fun i => ?_)
  simp [one_div]

end PH51Aux

namespace ProgHedging.Convex.Problem
open PH51Aux

variable {S : Type*} [Fintype S] {n T : ℕ} {pr : Problem S n T}

section seq3
variable (hconv : pr.ConvexCase) {r : ℝ} (hr : 0 < r) {X W : ℕ → Policy S n}
  (hseq : pr.IsExactPHSeq r X W)
include hconv hr hseq

theorem seq_kkt_of_bounded (CV CW : ℝ) (hCV : ∀ ν, ‖pr.J (X ν)‖ ≤ CV)
    (hCW : ∀ ν, ‖W ν‖ ≤ CW) : ∃ Xs Ws, pr.KKT Xs Ws := by
  set Ab : ℕ → Policy S n := fun K =>
    ∑ ν ∈ Finset.range (K + 1), ((K : ℝ) + 1)⁻¹ • pr.J (X (ν + 1)) with hAb
  set Bb : ℕ → Policy S n := fun K =>
    ∑ ν ∈ Finset.range (K + 1), ((K : ℝ) + 1)⁻¹ • W (ν + 1) with hBb
  set Xb : ℕ → Policy S n := fun K =>
    ∑ ν ∈ Finset.range (K + 1), ((K : ℝ) + 1)⁻¹ • X (ν + 1) with hXb
  have hXbeq : ∀ K, Xb K = Ab K + (((K : ℝ) + 1)⁻¹ * r⁻¹) • (W (K + 1) - W 0) := by
    intro K
    simp only [hXb, hAb]
    rw [Finset.sum_congr rfl (fun ν _ => by rw [seq_X_eq hr hseq ν])]
    simp only [smul_add, Finset.sum_add_distrib]
    congr 1
    rw [← Finset.smul_sum, ← Finset.smul_sum, Finset.sum_range_sub (fun ν => W ν), smul_smul]
  have hAbnd : ∀ K, ‖Ab K‖ ≤ CV := fun K => avg_norm_le _ CV (fun ν => hCV (ν + 1)) K
  have hBbnd : ∀ K, ‖Bb K‖ ≤ CW := fun K => avg_norm_le _ CW (fun ν => hCW (ν + 1)) K
  have hmem : ∀ K, (Ab K, Bb K) ∈ Metric.closedBall (0 : Policy S n × Policy S n) (max CV CW) := by
    intro K
    rw [mem_closedBall_zero_iff, Prod.norm_def]
    exact max_le_max (hAbnd K) (hBbnd K)
  obtain ⟨Ph, _, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hmem
  have hA : Tendsto (fun i => Ab (φ i)) atTop (𝓝 Ph.1) := (continuous_fst.tendsto _).comp hlim
  have hB : Tendsto (fun i => Bb (φ i)) atTop (𝓝 Ph.2) := (continuous_snd.tendsto _).comp hlim
  have hX : Tendsto (fun i => Xb (φ i)) atTop (𝓝 Ph.1) := by
    have h0 : Tendsto (fun i => (((φ i : ℝ) + 1)⁻¹ * r⁻¹) • (W (φ i + 1) - W 0)) atTop (𝓝 0) :=
      tendsto_smul_bdd (C := CW + CW) (tendsto_wt hφ r⁻¹)
        (fun i => (norm_sub_le _ _).trans (add_le_add (hCW _) (hCW _)))
    have := hA.add h0
    rw [add_zero] at this
    exact this.congr (fun i => (hXbeq (φ i)).symm)
  have hW' : Tendsto (fun i => Bb (φ i) +
      (((φ i : ℝ) + 1)⁻¹ * r) • (pr.J (X (φ i + 1)) - pr.J (X 0))) atTop (𝓝 Ph.2) := by
    have h0 : Tendsto (fun i => (((φ i : ℝ) + 1)⁻¹ * r) • (pr.J (X (φ i + 1)) - pr.J (X 0)))
        atTop (𝓝 0) :=
      tendsto_smul_bdd (C := CV + CV) (tendsto_wt hφ r)
        (fun i => (norm_sub_le _ _).trans (add_le_add (hCV _) (hCV _)))
    have := hB.add h0
    rwa [add_zero] at this
  have hlimit := pr.limit_sub (Xi := fun i => Xb (φ i))
    (fun i => (pr.adm_convex hconv).sum_mem (fun _ _ => by positivity) (wsum _)
      (fun ν _ => fun s => ((hseq.2 ν).1 s).1)) hX hW'
    (tendsto_wt hφ ((r * pr.ip (pr.J (X 0)) (pr.J (X 0)) + r⁻¹ * pr.ip (W 0) (W 0)) / 2))
    (fun i Z hZ => seq_ergodic hconv hr hseq (φ i) Z hZ)
  have hN : Ph.1 ∈ pr.N := pr.N_closed.mem_of_tendsto hA
    (Eventually.of_forall (fun i => pr.N_sum _ _ _ (fun ν _ => pr.J_mem_N _)))
  have hM : Ph.2 ∈ pr.M := pr.M_closed.mem_of_tendsto hB
    (Eventually.of_forall (fun i => pr.M_sum _ _ _ (fun ν _ => seq_W_mem hseq _)))
  exact ⟨Ph.1, Ph.2, pr.kkt_of_limit hN hM hlimit⟩

end seq3

end ProgHedging.Convex.Problem
namespace PH51Aux

theorem tendsto_zero_of_sq_le {E : Type*} [SeminormedAddCommGroup E] {u : ℕ → E} {t : ℕ → ℝ}
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ ν, ‖u ν‖ ^ 2 ≤ c * t ν) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := fun ν => Real.sqrt (c * t ν))
  · intro ν; exact Real.le_sqrt_of_sq_le (h ν)
  · have h1 : Tendsto (fun ν => c * t ν) atTop (𝓝 0) := by
      simpa using ht.const_mul c
    have := ((Real.continuous_sqrt.tendsto 0).comp h1)
    rw [Real.sqrt_zero] at this
    exact this

end PH51Aux

namespace ProgHedging.Convex.Problem
open PH51Aux

variable {S : Type*} [Fintype S] {n T : ℕ} {pr : Problem S n T}

theorem rsq_cont {r : ℝ} (Xh Wh : Policy S n) :
    Continuous fun q : Policy S n × Policy S n => pr.rsq r (q.1 - Xh) (q.2 - Wh) := by
  unfold rsq
  have h1 : Continuous fun q : Policy S n × Policy S n => q.1 - Xh :=
    continuous_fst.sub continuous_const
  have h2 : Continuous fun q : Policy S n × Policy S n => q.2 - Wh :=
    continuous_snd.sub continuous_const
  exact (pr.ip_cont h1 h1).add (continuous_const.mul (pr.ip_cont h2 h2))

section seq4
variable (hconv : pr.ConvexCase) {r : ℝ} (hr : 0 < r) {X W : ℕ → Policy S n}
  (hseq : pr.IsExactPHSeq r X W)
include hconv hr hseq

theorem seq_antitone {Xs Ws : Policy S n} (hk : pr.KKT Xs Ws) :
    Antitone fun ν => pr.rsq r (pr.J (X ν) - Xs) (W ν - Ws) := by
  apply antitone_nat_of_succ_le
  intro ν
  have := seq_fejer hconv hr hseq hk ν
  have := pr.rsq_nonneg r (pr.J (X ν) - pr.J (X (ν + 1))) (W ν - W (ν + 1))
  linarith

theorem seq_bounds {Xs Ws : Policy S n} (hk : pr.KKT Xs Ws) :
    (∀ ν, ‖pr.J (X ν)‖ ≤ ‖Xs‖ + Real.sqrt (pr.cst * pr.rsq r (pr.J (X 0) - Xs) (W 0 - Ws))) ∧
    (∀ ν, ‖W ν‖ ≤ ‖Ws‖ + Real.sqrt (pr.cst * r ^ 2 * pr.rsq r (pr.J (X 0) - Xs) (W 0 - Ws))) := by
  have hanti := seq_antitone hconv hr hseq hk
  have hc := pr.cst_nonneg
  constructor
  · intro ν
    have h1 := pr.norm_sq_le_rsq_left (r := r) (pr.J (X ν) - Xs) (W ν - Ws)
    have h2 := hanti (Nat.zero_le ν)
    have h3 : ‖pr.J (X ν) - Xs‖ ≤ Real.sqrt (pr.cst * pr.rsq r (pr.J (X 0) - Xs) (W 0 - Ws)) :=
      Real.le_sqrt_of_sq_le (h1.trans (mul_le_mul_of_nonneg_left h2 hc))
    have := norm_le_insert' (pr.J (X ν)) Xs
    linarith [norm_sub_norm_le (pr.J (X ν)) Xs]
  · intro ν
    have h1 := pr.norm_sq_le_rsq_right hr (pr.J (X ν) - Xs) (W ν - Ws)
    have h2 := hanti (Nat.zero_le ν)
    have h3 : ‖W ν - Ws‖ ≤ Real.sqrt (pr.cst * r ^ 2 * pr.rsq r (pr.J (X 0) - Xs) (W 0 - Ws)) :=
      Real.le_sqrt_of_sq_le (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity)))
    linarith [norm_sub_norm_le (W ν) Ws]

theorem seq_converge {Xs Ws : Policy S n} (hk : pr.KKT Xs Ws) :
    ∃ Xh Wh, pr.KKT Xh Wh ∧ Tendsto (fun ν => pr.J (X ν)) atTop (𝓝 Xh) ∧
      Tendsto W atTop (𝓝 Wh) := by
  have hc := pr.cst_nonneg
  obtain ⟨hbV, hbW⟩ := seq_bounds hconv hr hseq hk
  set CV := ‖Xs‖ + Real.sqrt (pr.cst * pr.rsq r (pr.J (X 0) - Xs) (W 0 - Ws))
  set CW := ‖Ws‖ + Real.sqrt (pr.cst * r ^ 2 * pr.rsq r (pr.J (X 0) - Xs) (W 0 - Ws))
  -- the steps tend to zero
  set d : ℕ → ℝ := fun ν => pr.rsq r (pr.J (X ν) - pr.J (X (ν + 1))) (W ν - W (ν + 1)) with hd
  have hdnn : ∀ ν, 0 ≤ d ν := fun ν => pr.rsq_nonneg _ _ _
  have hdsum : ∀ K, ∑ ν ∈ Finset.range K, d ν ≤ pr.rsq r (pr.J (X 0) - Xs) (W 0 - Ws) := by
    have : ∀ K, ∑ ν ∈ Finset.range K, d ν + pr.rsq r (pr.J (X K) - Xs) (W K - Ws) ≤
        pr.rsq r (pr.J (X 0) - Xs) (W 0 - Ws) := by
      intro K
      induction K with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ]
        have := seq_fejer hconv hr hseq hk k
        simp only [hd]; linarith
    intro K
    have := this K
    have := pr.rsq_nonneg r (pr.J (X K) - Xs) (W K - Ws)
    linarith
  have hd0 : Tendsto d atTop (𝓝 0) :=
    (summable_of_sum_range_le hdnn hdsum).tendsto_atTop_zero
  have hdV : Tendsto (fun ν => pr.J (X ν) - pr.J (X (ν + 1))) atTop (𝓝 0) :=
    tendsto_zero_of_sq_le hc (fun ν => pr.norm_sq_le_rsq_left _ _) hd0
  have hdW : Tendsto (fun ν => W ν - W (ν + 1)) atTop (𝓝 0) :=
    tendsto_zero_of_sq_le (by positivity) (fun ν => pr.norm_sq_le_rsq_right hr _ _) hd0
  -- a cluster point
  have hmem : ∀ ν, (pr.J (X ν), W ν) ∈
      Metric.closedBall (0 : Policy S n × Policy S n) (max CV CW) := by
    intro ν
    rw [mem_closedBall_zero_iff, Prod.norm_def]
    exact max_le_max (hbV ν) (hbW ν)
  obtain ⟨Ph, _, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hmem
  have hA : Tendsto (fun i => pr.J (X (φ i))) atTop (𝓝 Ph.1) :=
    (continuous_fst.tendsto _).comp hlim
  have hB : Tendsto (fun i => W (φ i)) atTop (𝓝 Ph.2) := (continuous_snd.tendsto _).comp hlim
  have hdVφ := hdV.comp hφ.tendsto_atTop
  have hdWφ := hdW.comp hφ.tendsto_atTop
  have hN : Ph.1 ∈ pr.N :=
    pr.N_closed.mem_of_tendsto hA (Eventually.of_forall (fun i => pr.J_mem_N _))
  have hM : Ph.2 ∈ pr.M :=
    pr.M_closed.mem_of_tendsto hB (Eventually.of_forall (fun i => seq_W_mem hseq _))
  have hA1 : Tendsto (fun i => pr.J (X (φ i + 1))) atTop (𝓝 Ph.1) := by
    have := hA.sub hdVφ
    rw [sub_zero] at this
    exact this.congr (fun i => by simp)
  have hB1 : Tendsto (fun i => W (φ i + 1)) atTop (𝓝 Ph.2) := by
    have := hB.sub hdWφ
    rw [sub_zero] at this
    exact this.congr (fun i => by simp)
  set Xi : ℕ → Policy S n := fun i => pr.J (X (φ i + 1)) + r⁻¹ • (W (φ i + 1) - W (φ i))
    with hXi
  set gi : ℕ → Policy S n := fun i => -W (φ i + 1) - r • (pr.J (X (φ i + 1)) - pr.J (X (φ i)))
    with hgi
  have hXlim : Tendsto Xi atTop (𝓝 Ph.1) := by
    have := hA1.add ((hB1.sub hB).const_smul r⁻¹)
    simpa using this
  have hglim : Tendsto gi atTop (𝓝 (-Ph.2)) := by
    have := hB1.neg.sub ((hA1.sub hA).const_smul r)
    simpa using this
  have hεlim : Tendsto (fun i => pr.ip (Xi i) (gi i)) atTop (𝓝 0) := by
    have := ((pr.ip_cont continuous_fst continuous_snd).tendsto (Ph.1, -Ph.2)).comp
      (hXlim.prodMk_nhds hglim)
    rw [ip_neg_right, pr.orth hN hM, neg_zero] at this
    exact this
  have hlimit := pr.limit_sub (Xi := Xi) (Wi := fun i => -gi i)
    (fun i => (seq_sub hconv hr hseq (φ i)).1) hXlim (by simpa using hglim.neg) hεlim
    (fun i Z hZ => by
      have := (seq_sub hconv hr hseq (φ i)).2 Z hZ
      rw [ip_sub_left] at this
      rw [ip_neg_right]
      simp only [hXi, hgi] at this ⊢
      linarith)
  have hkh := pr.kkt_of_limit hN hM hlimit
  refine ⟨Ph.1, Ph.2, hkh, ?_⟩
  -- Fejér monotonicity with respect to the cluster point
  set e : ℕ → ℝ := fun ν => pr.rsq r (pr.J (X ν) - Ph.1) (W ν - Ph.2) with he
  have hanti : Antitone e := seq_antitone hconv hr hseq hkh
  have heφ : Tendsto (fun i => e (φ i)) atTop (𝓝 0) := by
    have := ((rsq_cont (pr := pr) (r := r) Ph.1 Ph.2).tendsto Ph).comp hlim
    simp only [sub_self] at this
    have h0 : pr.rsq r (0 : Policy S n) 0 = 0 := by
      unfold rsq; rw [ip_zero_left]; ring
    rw [h0] at this
    exact this
  have hbdd : BddBelow (Set.range e) := ⟨0, by rintro _ ⟨ν, rfl⟩; exact pr.rsq_nonneg _ _ _⟩
  have hinf := tendsto_atTop_ciInf hanti hbdd
  have hinf0 : (⨅ ν, e ν) = 0 :=
    tendsto_nhds_unique (hinf.comp hφ.tendsto_atTop) heφ
  rw [hinf0] at hinf
  have h1 : Tendsto (fun ν => pr.J (X ν) - Ph.1) atTop (𝓝 0) :=
    tendsto_zero_of_sq_le hc (fun ν => pr.norm_sq_le_rsq_left _ _) hinf
  have h2 : Tendsto (fun ν => W ν - Ph.2) atTop (𝓝 0) :=
    tendsto_zero_of_sq_le (by positivity) (fun ν => pr.norm_sq_le_rsq_right hr _ _) hinf
  exact ⟨tendsto_sub_nhds_zero_iff.1 h1, tendsto_sub_nhds_zero_iff.1 h2⟩

end seq4

end ProgHedging.Convex.Problem


open ProgHedging.Convex in
theorem solution {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) :
    (∀ s, ∃ x ∈ pr.C s, ∀ z ∈ pr.C s, pr.f s x ≤ pr.f s z) ∧
    (∃ X ∈ pr.adm, ((pr.F X : ℝ) : EReal) = pr.alphaHat) ∧
    (∀ xs : S → EuclideanSpace ℝ (Fin n),
      (∀ s, xs s ∈ pr.C s ∧ ∀ z ∈ pr.C s, pr.f s (xs s) ≤ pr.f s z) →
        pr.alphaHat = ((∑ s, pr.p s * pr.f s (xs s) : ℝ) : EReal)) ∧
    pr.alphaHat ≤ pr.minP := by
  have h1 : ∀ s, ∃ x ∈ pr.C s, ∀ z ∈ pr.C s, pr.f s x ≤ pr.f s z := fun s =>
    PH51Aux.exists_min_of (pr.C s) (pr.C_closed s) (pr.C_nonempty s) (pr.f s)
      (pr.f_locallyLipschitz s).continuous (fun β => pr.levelSet_bounded s β)
  have h3 : ∀ xs : S → EuclideanSpace ℝ (Fin n),
      (∀ s, xs s ∈ pr.C s ∧ ∀ z ∈ pr.C s, pr.f s (xs s) ≤ pr.f s z) →
        pr.alphaHat = ((∑ s, pr.p s * pr.f s (xs s) : ℝ) : EReal) := by
    intro xs hxs
    apply le_antisymm
    · exact iInf₂_le (f := fun X (_ : X ∈ pr.adm) => ((pr.F X : ℝ) : EReal)) xs
        (fun s => (hxs s).1)
    · apply le_iInf₂; intro X hX
      apply EReal.coe_le_coe_iff.2
      unfold Problem.F
      exact Finset.sum_le_sum (fun s _ =>
        mul_le_mul_of_nonneg_left ((hxs s).2 _ (hX s)) (pr.p_pos s).le)
  refine ⟨h1, ?_, h3, ?_⟩
  · choose xs hxs using h1
    exact ⟨xs, fun s => (hxs s).1, (h3 xs (fun s => hxs s)).symm⟩
  · unfold Problem.alphaHat Problem.minP
    exact biInf_mono (fun X hX => hX.1)
