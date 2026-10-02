-- Prove2me | solution 1 for Transcendence.hermite_division_bound
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T10:12:12.804576+00:00
-- url     : https://prove2.me/submissions/196293d9-de5a-4eea-9970-9e4f2f3e146a

import Mathlib

/-!
# Hermite division with bounds (Waldschmidt, DALAG, proof of Prop. 4.7, Step 2.4)

For a list `Z` of nodes, `rem Z u` and `quot Z u` divide an entire `u` as `u = rem + P_Z · quot`,
with `P_Z(x) = ∏_{ζ ∈ Z} (x - ζ)` and `deg rem < |Z|`:
`rem (ζ :: Z) u = u ζ + (X - ζ) · rem Z (dslope u ζ)` and `quot (ζ :: Z) u = quot Z (dslope u ζ)`.
If `|u| ≤ M` on the disc of radius `R ≥ 5r` and the nodes lie in the disc of radius `r`, the
maximum modulus principle bounds `dslope u ζ` by `2M/(R - r)` there, and induction on `Z` gives
`2|rem| + M ≤ 3^|Z| M` and `|quot| ≤ (3/R)^|Z| M`. Since `P_Z` vanishes to order `count ζ Z` at
`ζ`, so does `u - rem`, which gives the jets of `rem`. A multiset of nodes is handled through any
list representing it.
-/

namespace HermiteDivisionBound

open Polynomial Metric

/-- Hermite remainder at the node list `Z`: `rem [] u = 0` and
`rem (ζ :: Z) u = u ζ + (X - ζ) · rem Z (dslope u ζ)`. -/
noncomputable def rem : List ℂ → (ℂ → ℂ) → ℂ[X]
  | [], _ => 0
  | ζ :: Z, u => C (u ζ) + (X - C ζ) * rem Z (dslope u ζ)

/-- Hermite quotient at the node list `Z`: `quot [] u = u` and
`quot (ζ :: Z) u = quot Z (dslope u ζ)`. -/
noncomputable def quot : List ℂ → (ℂ → ℂ) → ℂ → ℂ
  | [], u => u
  | ζ :: Z, u => quot Z (dslope u ζ)

lemma differentiable_dslope {u : ℂ → ℂ} (hu : Differentiable ℂ u) (ζ : ℂ) :
    Differentiable ℂ (dslope u ζ) :=
  differentiableOn_univ.mp
    ((Complex.differentiableOn_dslope Filter.univ_mem).2 hu.differentiableOn)

lemma differentiable_quot :
    ∀ (Z : List ℂ) {u : ℂ → ℂ}, Differentiable ℂ u → Differentiable ℂ (quot Z u)
  | [], _, hu => hu
  | ζ :: Z, _, hu => differentiable_quot Z (differentiable_dslope hu ζ)

/-- The division identity `u = rem + P_Z · quot`, with `P_Z = ∏ (X - ζ)`. -/
lemma rem_add_quot : ∀ (Z : List ℂ) (u : ℂ → ℂ) (x : ℂ),
    u x = (rem Z u).eval x + (Z.map (x - ·)).prod * quot Z u x
  | [], u, x => by simp [rem, quot]
  | ζ :: Z, u, x => by
    have h := sub_smul_dslope u ζ x
    rw [smul_eq_mul] at h
    have ih := rem_add_quot Z (dslope u ζ) x
    simp only [rem, quot, eval_add, eval_C, eval_mul, eval_sub, eval_X, List.map_cons,
      List.prod_cons]
    linear_combination (-1 : ℂ) * h + (x - ζ) * ih

/-- `rem Z u` has degree `< length Z`. -/
lemma rem_mem_degreeLT : ∀ (Z : List ℂ) (u : ℂ → ℂ), rem Z u ∈ degreeLT ℂ Z.length
  | [], _ => by simp [rem]
  | ζ :: Z, u => by
    have ih := rem_mem_degreeLT Z (dslope u ζ)
    rw [mem_degreeLT] at ih ⊢
    simp only [rem, List.length_cons]
    refine (degree_add_le _ _).trans_lt (max_lt (degree_C_le.trans_lt ?_) ?_)
    · exact_mod_cast Nat.succ_pos _
    · by_cases hq : rem Z (dslope u ζ) = 0
      · rw [hq, mul_zero, degree_zero]; exact WithBot.bot_lt_coe _
      · have h1 := (natDegree_lt_iff_degree_lt hq).mpr ih
        rw [degree_mul, degree_X_sub_C, degree_eq_natDegree hq]
        exact_mod_cast (by omega : 1 + (rem Z (dslope u ζ)).natDegree < Z.length + 1)

/-- Maximum modulus step: on the disc of radius `R`, `|dslope u ζ| ≤ 2M/(R - r)`. -/
lemma norm_dslope_le {u : ℂ → ℂ} (hu : Differentiable ℂ u) {ζ : ℂ} {r R M : ℝ}
    (hζ : ‖ζ‖ ≤ r) (hrR : r < R) (hM : ∀ w : ℂ, ‖w‖ ≤ R → ‖u w‖ ≤ M) (w : ℂ) (hw : ‖w‖ ≤ R) :
    ‖dslope u ζ w‖ ≤ 2 * M / (R - r) := by
  have hR : 0 < R := (norm_nonneg ζ).trans_lt (hζ.trans_lt hrR)
  have hRr : 0 < R - r := by linarith
  refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    (differentiable_dslope hu ζ).diffContOnCl (fun y hy => ?_)
    (by rwa [closure_ball _ hR.ne', mem_closedBall_zero_iff])
  rw [frontier_ball _ hR.ne', mem_sphere_zero_iff_norm] at hy
  have h1 : R - r ≤ ‖y - ζ‖ := by have := norm_sub_norm_le y ζ; linarith
  have hne : y ≠ ζ := by rintro rfl; linarith
  rw [dslope_of_ne _ hne, slope_def_field, norm_div]
  have h2 : ‖u y - u ζ‖ ≤ 2 * M := by
    have := norm_sub_le (u y) (u ζ)
    linarith [hM y hy.le, hM ζ (by linarith)]
  exact div_le_div₀ (by linarith [norm_nonneg (u y - u ζ)]) h2 hRr h1

/-- **Step 2.4.** If `|u| ≤ M` on the disc of radius `R ≥ 5r` and the nodes lie in the disc of
radius `r`, then on the disc of radius `R`: `2|rem| + M ≤ 3^p M` and `|quot| ≤ (3/R)^p M`. -/
lemma rem_quot_bound {r R : ℝ} (hr : 0 < r) (hR : 5 * r ≤ R) :
    ∀ (Z : List ℂ), (∀ ζ ∈ Z, ‖ζ‖ ≤ r) → ∀ (u : ℂ → ℂ) (M : ℝ), Differentiable ℂ u →
      (∀ w : ℂ, ‖w‖ ≤ R → ‖u w‖ ≤ M) → ∀ x : ℂ, ‖x‖ ≤ R →
      2 * ‖(rem Z u).eval x‖ + M ≤ 3 ^ Z.length * M ∧ ‖quot Z u x‖ ≤ (3 / R) ^ Z.length * M
  | [], _, u, M, _, hM, x, hx => by simp [rem, quot, hM x hx]
  | ζ :: Z, hZ, u, M, hu, hM, x, hx => by
    have hζ : ‖ζ‖ ≤ r := hZ ζ List.mem_cons_self
    have hRpos : 0 < R := by linarith
    have hRr : 0 < R - r := by linarith
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp; linarith))
    obtain ⟨h1, h2⟩ := rem_quot_bound hr hR Z (fun ζ' h => hZ ζ' (List.mem_cons_of_mem _ h))
      (dslope u ζ) (2 * M / (R - r)) (differentiable_dslope hu ζ)
      (norm_dslope_le hu hζ (by linarith) hM) x hx
    have hxζ : ‖x - ζ‖ ≤ R + r := (norm_sub_le x ζ).trans (by linarith)
    set A := ‖(rem Z (dslope u ζ)).eval x‖
    have hA : 0 ≤ A := norm_nonneg _
    have hq : 2 * M / (R - r) ≤ 3 / R * M := by
      rw [div_le_iff₀ hRr, show 3 / R * M * (R - r) = 3 * M * (R - r) / R by ring,
        le_div_iff₀ hRpos]
      nlinarith
    constructor
    · have e1 : ‖u ζ + (x - ζ) * (rem Z (dslope u ζ)).eval x‖ ≤ M + (R + r) * A := by
        calc _ ≤ ‖u ζ‖ + ‖x - ζ‖ * A := by rw [← norm_mul]; exact norm_add_le _ _
          _ ≤ M + (R + r) * A := by gcongr; exact hM ζ (by linarith)
      have e2 : A * (R - r) + M ≤ 3 ^ Z.length * M := by
        have := mul_le_mul_of_nonneg_right h1 hRr.le
        rw [add_mul, mul_assoc (3 ^ Z.length), div_mul_cancel₀ _ hRr.ne'] at this
        linarith
      simp only [rem, eval_add, eval_C, eval_mul, eval_sub, eval_X, List.length_cons, pow_succ]
      nlinarith [mul_nonneg hA (by linarith : (0 : ℝ) ≤ R - 5 * r)]
    · simp only [quot, List.length_cons, pow_succ]
      calc ‖quot Z (dslope u ζ) x‖ ≤ (3 / R) ^ Z.length * (2 * M / (R - r)) := h2
        _ ≤ (3 / R) ^ Z.length * (3 / R * M) := by gcongr
        _ = (3 / R) ^ Z.length * (3 / R) * M := by ring

lemma iteratedDeriv_eval (q : ℂ[X]) (k : ℕ) :
    iteratedDeriv k (fun x => q.eval x) = fun x => (derivative^[k] q).eval x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [Polynomial.deriv, Function.iterate_succ_apply']

/-- `P_Z` is `(x - ζ)^(count ζ Z)` times an entire function. -/
lemma prod_eq_pow_mul (ζ : ℂ) : ∀ Z : List ℂ, ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
    ∀ x, (Z.map (x - ·)).prod = (x - ζ) ^ Z.count ζ * G x
  | [] => ⟨fun _ => 1, differentiable_const _, fun x => by simp⟩
  | a :: Z => by
    obtain ⟨G, hG, h⟩ := prod_eq_pow_mul ζ Z
    by_cases ha : a = ζ
    · subst ha
      exact ⟨G, hG, fun x => by rw [List.map_cons, List.prod_cons, h, List.count_cons_self]; ring⟩
    · refine ⟨fun x => (x - a) * G x, (differentiable_id.sub_const a).mul hG, fun x => ?_⟩
      rw [List.map_cons, List.prod_cons, h, List.count_cons_of_ne ha]
      ring

/-- `rem Z u` has the jets of `u` at the nodes: `u - rem = P_Z · quot` vanishes to order
`count ζ Z` at `ζ`. -/
lemma jet_rem (Z : List ℂ) {u : ℂ → ℂ} (hu : Differentiable ℂ u) (ζ : ℂ) {k : ℕ}
    (hk : k < Z.count ζ) : (derivative^[k] (rem Z u)).eval ζ = iteratedDeriv k u ζ := by
  obtain ⟨G, hG, hP⟩ := prod_eq_pow_mul ζ Z
  have hGq : Differentiable ℂ fun x => G x * quot Z u x := hG.mul (differentiable_quot Z hu)
  set F : ℂ → ℂ := fun x => (x - ζ) ^ Z.count ζ * (G x * quot Z u x) with hFdef
  have hF : Differentiable ℂ F := ((differentiable_id.sub_const ζ).pow _).mul hGq
  have hsplit : u = fun x => (rem Z u).eval x + F x := by
    funext x
    rw [rem_add_quot Z u x, hP, hFdef, mul_assoc]
  have hF0 : iteratedDeriv k F ζ = 0 := by
    have hFa := hF.analyticAt ζ
    refine (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hFa).mp ?_ k hk
    exact (natCast_le_analyticOrderAt hFa).mpr
      ⟨_, hGq.analyticAt ζ, Filter.Eventually.of_forall fun x => by simp [hFdef, smul_eq_mul]⟩
  have hP : ContDiffAt ℂ k (fun x => (rem Z u).eval x) ζ :=
    (Polynomial.differentiable _).contDiff.contDiffAt
  conv_rhs => rw [hsplit]
  rw [iteratedDeriv_fun_add hP hF.contDiff.contDiffAt, hF0, add_zero, iteratedDeriv_eval]

end HermiteDivisionBound

open Polynomial HermiteDivisionBound in
/-- **Hermite division with bounds** (Waldschmidt, DALAG, proof of Prop. 4.7, Step 2.4). -/
theorem solution {r R : ℝ} (hr : 0 < r) (hR : 5 * r ≤ R) (Z : Multiset ℂ)
    (hZ : ∀ ζ ∈ Z, ‖ζ‖ ≤ r) {u : ℂ → ℂ} (hu : Differentiable ℂ u) {M : ℝ}
    (hM : ∀ w ∈ Metric.closedBall (0 : ℂ) R, ‖u w‖ ≤ M) :
    ∃ (ρ : ℂ[X]) (q : ℂ → ℂ), ρ ∈ degreeLT ℂ (Multiset.card Z) ∧ Differentiable ℂ q ∧
      (∀ x, u x = ρ.eval x + (Z.map fun ζ => x - ζ).prod * q x) ∧
      (∀ ζ, ∀ k < Z.count ζ, (derivative^[k] ρ).eval ζ = iteratedDeriv k u ζ) ∧
      ∀ x ∈ Metric.closedBall (0 : ℂ) R,
        2 * ‖ρ.eval x‖ + M ≤ 3 ^ Multiset.card Z * M ∧ ‖q x‖ ≤ (3 / R) ^ Multiset.card Z * M := by
  obtain ⟨l, rfl⟩ : ∃ l : List ℂ, (l : Multiset ℂ) = Z := ⟨Z.toList, Z.coe_toList⟩
  simp only [Multiset.coe_card, Multiset.map_coe, Multiset.prod_coe, Multiset.coe_count]
  refine ⟨rem l u, quot l u, rem_mem_degreeLT l u, differentiable_quot l hu, rem_add_quot l u,
    fun ζ k hk => jet_rem l hu ζ hk, fun x hx => ?_⟩
  exact rem_quot_bound hr hR l (fun ζ h => hZ ζ (Multiset.mem_coe.mpr h)) u M hu
    (fun w hw => hM w (mem_closedBall_zero_iff.mpr hw)) x (mem_closedBall_zero_iff.mp hx)
