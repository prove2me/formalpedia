-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P35.cubic_optimal_decomposition_equations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:16:39.464436+00:00
-- url     : https://prove2.me/submissions/bd8a93af-28f1-4258-bce9-a44db7292a36

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P35

-- ===== P35R =====

noncomputable section

namespace X4PR
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P35

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- the hull fiber over `r` is exactly the set of roof values. -/
lemma fiber_eq (V : Set E) (f : E → ℝ) (r : E) :
    {a : ℝ | (r, a) ∈ convexHull ℝ (graphOn V f)} = roofValues V f r := by
  ext a
  constructor
  · intro h
    obtain ⟨ι, _, w, z, hw0, hw1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.1 h
    have hx : ∀ i, ∃ x ∈ V, (x, f x) = z i := fun i => hz i
    choose x hxV hxz using hx
    set e := Fintype.equivFin ι
    have hpos : 0 < Fintype.card ι := by
      rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | h0
      · exfalso
        have : IsEmpty ι := Fintype.card_eq_zero_iff.1 h0
        rw [Finset.univ_eq_empty, Finset.sum_empty] at hw1
        exact zero_ne_one hw1
      · exact h0
    have hs1 : ∑ j : Fin (Fintype.card ι), w (e.symm j) = 1 := by
      rw [← hw1]; exact Equiv.sum_comp e.symm w
    have hsum' : ∑ i, w i • z i = (r, a) := hsum
    have hfst : ∑ i, w i • x i = r := by
      have := congrArg Prod.fst hsum'
      rw [Prod.fst_sum] at this
      simpa [← hxz] using this
    have hsnd : ∑ i, w i * f (x i) = a := by
      have := congrArg Prod.snd hsum'
      rw [Prod.snd_sum] at this
      simpa [← hxz] using this
    refine ⟨⟨Fintype.card ι, hpos, fun j => x (e.symm j), fun j => hxV _, fun j => w (e.symm j),
      fun j => hw0 _, hs1, ?_⟩, ?_⟩
    · rw [← hfst]; exact Equiv.sum_comp e.symm (fun i => w i • x i)
    · rw [← hsnd]; exact (Equiv.sum_comp e.symm (fun i => w i * f (x i))).symm
  · rintro ⟨d, rfl⟩
    have : (r, ∑ j, d.weight j * f (d.point j)) = ∑ j, d.weight j • (d.point j, f (d.point j)) := by
      ext
      · simp [Prod.fst_sum, d.barycenter]
      · simp [Prod.snd_sum]
    show (r, ∑ j, d.weight j * f (d.point j)) ∈ convexHull ℝ (graphOn V f)
    rw [this]
    exact (convex_convexHull ℝ _).sum_mem (fun j _ => d.nonnegative j) d.total
      (fun j _ => subset_convexHull ℝ _ ⟨d.point j, d.member j, rfl⟩)

end X4PR

-- ===== P35K =====

noncomputable section

namespace X4PK
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P35

abbrev E := (Fin 2 → ℝ) × ℝ

/-- the lifted hull. -/
def S : Set E := convexHull ℝ (graphOn circle cubicCost)

/-- strict upper set of the lifted hull. -/
def T : Set E := {z | ∃ s, (z.1, s) ∈ S ∧ s < z.2}

lemma cost_ge {x : Fin 2 → ℝ} (hx : x ∈ circle) : -1 ≤ cubicCost x := by
  have h : x 0 ^ 2 + x 1 ^ 2 = 1 := hx
  unfold cubicCost
  nlinarith [sq_nonneg (x 1), sq_nonneg (x 0 + 1), sq_nonneg (x 0 - 1)]

lemma cost_le {x : Fin 2 → ℝ} (hx : x ∈ circle) : cubicCost x ≤ 1 := by
  have h : x 0 ^ 2 + x 1 ^ 2 = 1 := hx
  unfold cubicCost
  nlinarith [sq_nonneg (x 1), sq_nonneg (x 0 + 1), sq_nonneg (x 0 - 1)]

lemma bdd (r : Fin 2 → ℝ) : BddBelow (roofValues circle cubicCost r) := by
  refine ⟨-1, ?_⟩
  rintro a ⟨d, rfl⟩
  calc (-1 : ℝ) = ∑ j, d.weight j * (-1) := by simp [← Finset.sum_mul, d.total]
    _ ≤ ∑ j, d.weight j * cubicCost (d.point j) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (cost_ge (d.member j)) (d.nonnegative j)

lemma low_le {x : Fin 2 → ℝ} {s : ℝ} (h : (x, s) ∈ S) : lowerRoof circle cubicCost x ≤ s := by
  have : s ∈ roofValues circle cubicCost x := by
    rw [← X4PR.fiber_eq]; exact h
  exact csInf_le (bdd x) this

lemma graph_mem {x : Fin 2 → ℝ} (hx : x ∈ circle) : (x, cubicCost x) ∈ S :=
  subset_convexHull ℝ _ ⟨x, hx, rfl⟩

lemma T_convex : Convex ℝ T := by
  rintro ⟨x1, t1⟩ ⟨s1, h1, l1⟩ ⟨x2, t2⟩ ⟨s2, h2, l2⟩ a b ha hb hab
  refine ⟨a * s1 + b * s2, ?_, ?_⟩
  · have := (convex_convexHull ℝ (graphOn circle cubicCost)) h1 h2 ha hb hab
    show _ ∈ convexHull ℝ _
    simpa using this
  · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    rcases ha.eq_or_lt with h0 | h0
    · subst h0; simp at hab; subst hab; simp; linarith
    · nlinarith

lemma T_int : (interior T).Nonempty := by
  set B : Set E := {z | z.1 0 ^ 2 + z.1 1 ^ 2 < 1 / 4 ∧ 2 < z.2}
  have hB : IsOpen B := by
    apply IsOpen.inter
    · exact isOpen_lt (f := fun z : E => z.1 0 ^ 2 + z.1 1 ^ 2) (g := fun _ => (1 / 4 : ℝ))
        (by fun_prop) continuous_const
    · exact isOpen_lt (f := fun _ : E => (2 : ℝ)) (g := fun z : E => z.2) continuous_const (by fun_prop)
  have hBT : B ⊆ T := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    set ρ := Real.sqrt (x 0 ^ 2 + x 1 ^ 2)
    have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
    have hρ2 : ρ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := Real.sq_sqrt (by positivity)
    have hρ1 : ρ < 1 / 2 := by nlinarith
    obtain ⟨u, hu, hxu⟩ : ∃ u : Fin 2 → ℝ, u ∈ circle ∧ x = ρ • u := by
      by_cases h0 : ρ = 0
      · refine ⟨![1, 0], by simp [circle], ?_⟩
        have : x 0 = 0 ∧ x 1 = 0 := by constructor <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
        ext i; fin_cases i <;> simp [h0, this.1, this.2]
      · refine ⟨ρ⁻¹ • x, ?_, ?_⟩
        · show (ρ⁻¹ * x 0) ^ 2 + (ρ⁻¹ * x 1) ^ 2 = 1
          rw [mul_pow, mul_pow, ← mul_add, ← hρ2]; field_simp
        · rw [smul_smul, mul_inv_cancel₀ h0, one_smul]
    have hu' : -u ∈ circle := by
      have h : u 0 ^ 2 + u 1 ^ 2 = 1 := hu
      show (-u) 0 ^ 2 + (-u) 1 ^ 2 = 1
      simp [h]
    refine ⟨((1 + ρ) / 2) * cubicCost u + ((1 - ρ) / 2) * cubicCost (-u), ?_, ?_⟩
    · have := (convex_convexHull ℝ (graphOn circle cubicCost)) (graph_mem hu) (graph_mem hu')
        (a := (1 + ρ) / 2) (b := (1 - ρ) / 2) (by linarith) (by linarith) (by ring)
      show _ ∈ convexHull ℝ (graphOn circle cubicCost)
      convert this using 1
      simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
      congr 1
      rw [hxu]; ext i; simp; ring
    · have h1 := cost_le hu
      have h2 := cost_le hu'
      simp only
      nlinarith
  exact ⟨((0 : Fin 2 → ℝ), 3), interior_maximal hBT hB ⟨by simp, by norm_num⟩⟩

lemma lin (f : StrongDual ℝ E) (x : Fin 2 → ℝ) (t : ℝ) :
    f (x, t) = x 0 * f (Pi.single 0 1, 0) + x 1 * f (Pi.single 1 1, 0) + t * f (0, 1) := by
  have : ((x, t) : E) = x 0 • ((Pi.single 0 1 : Fin 2 → ℝ), (0 : ℝ)) + x 1 • ((Pi.single 1 1 : Fin 2 → ℝ), (0 : ℝ)) +
      t • ((0 : Fin 2 → ℝ), (1 : ℝ)) := by
    ext i
    · fin_cases i <;> simp
    · simp
  rw [this, map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]

/-- rotation curve on the circle. -/
def rot (q : Fin 2 → ℝ) (θ : ℝ) : Fin 2 → ℝ :=
  ![q 0 * Real.cos θ - q 1 * Real.sin θ, q 0 * Real.sin θ + q 1 * Real.cos θ]

lemma rot_mem {q : Fin 2 → ℝ} (hq : q ∈ circle) (θ : ℝ) : rot q θ ∈ circle := by
  have h : q 0 ^ 2 + q 1 ^ 2 = 1 := hq
  show (rot q θ) 0 ^ 2 + (rot q θ) 1 ^ 2 = 1
  simp only [rot, Matrix.cons_val_zero, Matrix.cons_val_one]
  have := Real.sin_sq_add_cos_sq θ
  nlinarith [this]

lemma rot_zero (q : Fin 2 → ℝ) : rot q 0 = q := by
  ext i; fin_cases i <;> simp [rot]

/-- tangency: a linear functional maximal on the lifted circle at `q` kills the lifted tangent. -/
lemma tangent (a0 a1 c : ℝ) {q : Fin 2 → ℝ} (hq : q ∈ circle)
    (hmax : ∀ x ∈ circle, x 0 * a0 + x 1 * a1 + cubicCost x * c ≤ q 0 * a0 + q 1 * a1 + cubicCost q * c) :
    q 1 * a0 + (-q 0) * a1 + (3 * q 0 ^ 2 * q 1) * c = 0 := by
  set g : ℝ → ℝ := fun θ => (q 0 * Real.cos θ - q 1 * Real.sin θ) * a0 +
    (q 0 * Real.sin θ + q 1 * Real.cos θ) * a1 + (q 0 * Real.cos θ - q 1 * Real.sin θ) ^ 3 * c
  have hg : ∀ θ, g θ = (rot q θ) 0 * a0 + (rot q θ) 1 * a1 + cubicCost (rot q θ) * c := by
    intro θ; simp [g, rot, cubicCost]
  have hd : HasDerivAt g ((q 0 * (-Real.sin 0) - q 1 * Real.cos 0) * a0 +
      (q 0 * Real.cos 0 + q 1 * (-Real.sin 0)) * a1 +
      (3 * (q 0 * Real.cos 0 - q 1 * Real.sin 0) ^ 2 * (q 0 * (-Real.sin 0) - q 1 * Real.cos 0)) * c) 0 := by
    have hc := Real.hasDerivAt_cos 0
    have hs := Real.hasDerivAt_sin 0
    have h1 := ((hc.const_mul (q 0)).sub (hs.const_mul (q 1)))
    have h2 := ((hs.const_mul (q 0)).add (hc.const_mul (q 1)))
    have h3 := (h1.pow 3)
    have := ((h1.mul_const a0).add (h2.mul_const a1)).add (h3.mul_const c)
    refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun θ => ?_)).congr_deriv ?_
    · simp [g]
    · norm_num
  have hloc : IsLocalMax g 0 := by
    refine Filter.Eventually.of_forall fun θ => ?_
    rw [hg, hg, rot_zero]
    exact hmax _ (rot_mem hq θ)
  have := hloc.hasDerivAt_eq_zero hd
  simp only [Real.sin_zero, Real.cos_zero, neg_zero, mul_zero, mul_one, sub_zero, zero_sub, add_zero,
    zero_add] at this
  linarith

theorem main (q : Fin 2 → (Fin 2 → ℝ))
    (p : ℝ) (hp : 0 < p ∧ p < 1) (hq : ∀ j, q j ∈ circle)
    (r : Fin 2 → ℝ)
    (hb : p • q 0 + (1 - p) • q 1 = r)
    (hopt : p * cubicCost (q 0) + (1 - p) * cubicCost (q 1) = lowerRoof circle cubicCost r) :
    Matrix.det (!![q 0 1, -q 0 0, 3 * q 0 0 ^ 2 * q 0 1;
      q 1 1, -q 1 0, 3 * q 1 0 ^ 2 * q 1 1;
      q 0 0 - q 1 0, q 0 1 - q 1 1, q 0 0 ^ 3 - q 1 0 ^ 3] : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
  set m := lowerRoof circle cubicCost r
  set z : E := (r, m)
  have hzS : z ∈ S := by
    have := (convex_convexHull ℝ (graphOn circle cubicCost)) (graph_mem (hq 0)) (graph_mem (hq 1))
      (a := p) (b := 1 - p) hp.1.le (by linarith) (by ring)
    show _ ∈ convexHull ℝ (graphOn circle cubicCost)
    convert this using 1
    refine Prod.ext ?_ ?_
    · simp [z, ← hb]
    · simp [z, m, ← hopt]
  have hzT : z ∉ T := by
    rintro ⟨s, hs, hlt⟩
    have := low_le hs
    exact absurd hlt (not_lt.2 this)
  obtain ⟨f, u, hf0, hfT, hfz⟩ := geometric_hahn_banach_of_nonempty_interior T_convex (convex_singleton z)
    (Set.disjoint_singleton_right.2 (fun h => hzT (interior_subset h))) T_int ⟨z, rfl⟩
  have hfz' : u ≤ f z := hfz z rfl
  -- f is bounded by f z on S
  have hS : ∀ x s, (x, s) ∈ S → f (x, s) ≤ f z := by
    intro x s hxs
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    set c := f (0, 1)
    have hε : 0 < δ / (|c| + 1) := by positivity
    have hT : ((x, s + δ / (|c| + 1)) : E) ∈ T := ⟨s, hxs, by linarith⟩
    have h1 := hfT _ hT
    rw [lin] at h1
    rw [lin]
    have h2 : -(δ / (|c| + 1) * c) ≤ δ := by
      have : |δ / (|c| + 1) * c| ≤ δ := by
        rw [abs_mul, abs_of_pos hε]
        calc δ / (|c| + 1) * |c| ≤ δ / (|c| + 1) * (|c| + 1) := by gcongr; linarith
          _ = δ := by field_simp
      linarith [neg_abs_le (δ / (|c| + 1) * c)]
    nlinarith
  set a0 := f (Pi.single 0 1, 0)
  set a1 := f (Pi.single 1 1, 0)
  set c := f (0, 1)
  have hlin : ∀ x t, f (x, t) = x 0 * a0 + x 1 * a1 + t * c := lin f
  -- equality at both contact points
  have hA := hS _ _ (graph_mem (hq 0))
  have hB := hS _ _ (graph_mem (hq 1))
  have hcomb : p * f (q 0, cubicCost (q 0)) + (1 - p) * f (q 1, cubicCost (q 1)) = f z := by
    rw [← smul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_smul, ← map_add]
    congr 1
    refine Prod.ext ?_ ?_
    · simp [z, ← hb]
    · simp [z, m, ← hopt]
  have hA' : f (q 0, cubicCost (q 0)) = f z := by nlinarith
  have hB' : f (q 1, cubicCost (q 1)) = f z := by nlinarith
  have hmax : ∀ j, ∀ x ∈ circle, x 0 * a0 + x 1 * a1 + cubicCost x * c ≤
      q j 0 * a0 + q j 1 * a1 + cubicCost (q j) * c := by
    intro j x hx
    rw [← hlin, ← hlin]
    have := hS _ _ (graph_mem hx)
    fin_cases j
    · simp only [Fin.zero_eta]; rw [hA']; exact this
    · simp only [Fin.mk_one]; rw [hB']; exact this
  have t0 := tangent a0 a1 c (hq 0) (hmax 0)
  have t1 := tangent a0 a1 c (hq 1) (hmax 1)
  have tc : (q 0 0 - q 1 0) * a0 + (q 0 1 - q 1 1) * a1 + (q 0 0 ^ 3 - q 1 0 ^ 3) * c = 0 := by
    have := hA'.trans hB'.symm
    rw [hlin, hlin] at this
    simp only [cubicCost] at this
    linarith
  have hn : (![a0, a1, c] : Fin 3 → ℝ) ≠ 0 := by
    intro h
    apply hf0
    refine ContinuousLinearMap.ext fun ⟨x, t⟩ => ?_
    rw [hlin]
    have e0 : a0 = 0 := by simpa using congrFun h 0
    have e1 : a1 = 0 := by simpa using congrFun h 1
    have e2 : c = 0 := by simpa using congrFun h 2
    simp [e0, e1, e2]
  refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, hn, ?_⟩
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; linarith
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; linarith
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; linarith

end X4PK

-- ===== P35KSol =====

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

theorem _root_.solution (q : Fin 2 → (Fin 2 → ℝ))
    (p : ℝ) (hp : 0 < p ∧ p < 1) (hq : ∀ j, q j ∈ circle)
    (r : Fin 2 → ℝ) (hr : r ∈ convexHull ℝ circle)
    (hb : p • q 0 + (1 - p) • q 1 = r)
    (hopt : p * cubicCost (q 0) + (1 - p) * cubicCost (q 1) = lowerRoof circle cubicCost r) :
    q 0 0 ^ 2 + q 0 1 ^ 2 - 1 = 0 ∧
    q 1 0 ^ 2 + q 1 1 ^ 2 - 1 = 0 ∧
    Matrix.det (!![q 0 1, -q 0 0, 3 * q 0 0 ^ 2 * q 0 1;
      q 1 1, -q 1 0, 3 * q 1 0 ^ 2 * q 1 1;
      q 0 0 - q 1 0, q 0 1 - q 1 1, q 0 0 ^ 3 - q 1 0 ^ 3] : Matrix (Fin 3) (Fin 3) ℝ) = 0 ∧
    p * q 0 0 + (1 - p) * q 1 0 - r 0 = 0 ∧
    p * q 0 1 + (1 - p) * q 1 1 - r 1 = 0 := by
  have h0 : q 0 0 ^ 2 + q 0 1 ^ 2 = 1 := hq 0
  have h1 : q 1 0 ^ 2 + q 1 1 ^ 2 = 1 := hq 1
  have e0 := congrFun hb 0
  have e1 := congrFun hb 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1
  exact ⟨by linarith, by linarith, X4PK.main q p hp hq r hb hopt, by linarith, by linarith⟩

end QAlgorithms.Papers.Independent.Support50.P35

end

#print axioms solution
