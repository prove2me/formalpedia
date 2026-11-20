-- Prove2me | solution 1 for QuantumLTF.Membership.uniform_dyadic_window
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-20T02:32:21.615128+00:00
-- url     : https://prove2.me/submissions/84e7964b-d651-4ab6-9d9c-c075b0a162fc

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_addrOf

section UniformDyadicWindowProof

open QAlgorithms QuantumLTF.Membership MeasureTheory

private def radBit (b : Bool) : ℝ := if b then 1 else -1

private lemma sum_pow_two_rev (ℓ : ℕ) :
    ∑ j : Fin ℓ, (2 : ℝ) ^ (ℓ - 1 - (j : ℕ)) = (2 : ℝ) ^ ℓ - 1 := by
  induction ℓ with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.add_sub_cancel, tsub_zero, Fin.val_succ]
    have hsub : ∀ i : Fin m, m - ((i : ℕ) + 1) = m - 1 - (i : ℕ) := fun _ => by omega
    simp_rw [hsub]
    rw [ih]
    ring

private lemma fpVal_eq_radSum (f : ℕ) (x : Qubits (f + 2)) :
    fpVal (f + 2) f x = -(1 / (2 * (2 : ℝ) ^ f)) +
      ∑ j : Fin (f + 2), ((2 : ℝ)⁻¹) ^ (j : ℕ) * radBit (x j) := by
  unfold fpVal bitsToNat
  have hcast : ((∑ i : Fin (f + 2), if x i = true then 2 ^ (f + 2 - 1 - (i : ℕ)) else 0 : ℕ) : ℝ) =
      ∑ i : Fin (f + 2), ((1 + radBit (x i)) / 2) * (2 : ℝ) ^ (f + 1 - (i : ℕ)) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    cases x i <;> simp [radBit] <;> ring
  rw [hcast]
  have hsplit : ∑ i : Fin (f + 2), ((1 + radBit (x i)) / 2) * (2 : ℝ) ^ (f + 1 - (i : ℕ)) =
      (1 / 2) * (∑ i : Fin (f + 2), (2 : ℝ) ^ (f + 1 - (i : ℕ))) +
      ∑ i : Fin (f + 2), ((2 : ℝ) ^ (f + 1 - (i : ℕ)) / 2) * radBit (x i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun _ _ => by ring
  rw [hsplit]
  have hsum_pow := sum_pow_two_rev (f + 2)
  have hsub2 : f + 2 - 1 = f + 1 := by omega
  rw [hsub2] at hsum_pow
  rw [hsum_pow, add_sub_right_comm, add_div]
  have hmean : ((1 / 2) * ((2 : ℝ) ^ (f + 2) - 1) - (2 : ℝ) ^ (f + 2) / 2) / (2 : ℝ) ^ f =
      -(1 / (2 * (2 : ℝ) ^ f)) := by
    field_simp
    ring
  rw [hmean, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : (j : ℕ) ≤ f + 1 := by omega
  have hpow : ((2 : ℝ) ^ (f + 1 - (j : ℕ)) / 2) / (2 : ℝ) ^ f = ((2 : ℝ)⁻¹) ^ (j : ℕ) := by
    have h2 : (2 : ℝ) ^ (f + 1 - (j : ℕ)) * (2 : ℝ) ^ (j : ℕ) = (2 : ℝ) ^ (f + 1) := by
      rw [← pow_add, Nat.sub_add_cancel hj]
    rw [inv_pow]
    field_simp
    linear_combination h2
  rw [mul_div_right_comm, hpow]

private def splitRegEquiv (n ℓ : ℕ) : Qubits (n * ℓ) ≃ (Fin n → Qubits ℓ) where
  toFun := splitReg n ℓ
  invFun g k := g (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  left_inv y := by
    ext k
    change y (finProdFinEquiv ((finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2)) = y k
    rw [Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv g := by
    ext i j
    simp [splitReg]

private def qubitsSuccEquiv (m : ℕ) : Bool × Qubits m ≃ Qubits (m + 1) where
  toFun p := Fin.cons p.1 p.2
  invFun z := (z 0, Fin.tail z)
  left_inv := fun ⟨b, z'⟩ => by
    ext
    · simp
    · simp [Fin.tail_cons]
  right_inv z := Fin.cons_self_tail z

private lemma rademacher_moments (m : ℕ) (c : Fin m → ℝ) :
    (∑ z : Qubits m, (∑ k : Fin m, c k * radBit (z k)) ^ 2 =
      (2 : ℝ) ^ m * (∑ k : Fin m, c k ^ 2)) ∧
    (∑ z : Qubits m, (∑ k : Fin m, c k * radBit (z k)) ^ 4 ≤
      3 * (2 : ℝ) ^ m * (∑ k : Fin m, c k ^ 2) ^ 2) ∧
    (∑ z : Qubits m, (∑ k : Fin m, c k * radBit (z k)) ^ 6 ≤
      15 * (2 : ℝ) ^ m * (∑ k : Fin m, c k ^ 2) ^ 3) := by
  induction m with
  | zero =>
    have hcard : (Finset.univ : Finset (Qubits 0)).card = 1 := by simp
    simp [Finset.sum_const, hcard]
  | succ m ih =>
    let c' : Fin m → ℝ := fun k => c k.succ
    obtain ⟨ih2, ih4, ih6⟩ := ih c'
    let S' : Qubits m → ℝ := fun z' => ∑ k : Fin m, c' k * radBit (z' k)
    have h_step : ∀ r : ℕ, ∑ z : Qubits (m + 1), (∑ k : Fin (m + 1), c k * radBit (z k)) ^ r =
        ∑ z' : Qubits m, ((c 0 + S' z') ^ r + (-c 0 + S' z') ^ r) := by
      intro r
      rw [← Equiv.sum_comp (qubitsSuccEquiv m), Fintype.sum_prod_type, Fintype.sum_bool,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun z' _ => ?_
      simp [qubitsSuccEquiv, Fin.sum_univ_succ, radBit, S', c']
    have hcard_m : ∑ _ : Qubits m, (1 : ℝ) = (2 : ℝ) ^ m := by simp
    have hS_eq : ∑ k : Fin (m + 1), c k ^ 2 = c 0 ^ 2 + ∑ k : Fin m, c' k ^ 2 :=
      Fin.sum_univ_succ _
    have hS_nonneg : 0 ≤ ∑ k : Fin m, c' k ^ 2 :=
      Finset.sum_nonneg fun k _ => sq_nonneg (c' k)
    have h2 : ∑ z : Qubits (m + 1), (∑ k : Fin (m + 1), c k * radBit (z k)) ^ 2 =
        (2 : ℝ) ^ (m + 1) * ∑ k : Fin (m + 1), c k ^ 2 := by
      rw [h_step 2, hS_eq]
      have h_alg : ∀ z' : Qubits m,
          (c 0 + S' z') ^ 2 + (-c 0 + S' z') ^ 2 = 2 * S' z' ^ 2 + 2 * c 0 ^ 2 * 1 :=
        fun _ => by ring
      simp_rw [h_alg]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hcard_m]
      simp only [S']
      rw [ih2]
      ring
    have h4 : ∑ z : Qubits (m + 1), (∑ k : Fin (m + 1), c k * radBit (z k)) ^ 4 ≤
        3 * (2 : ℝ) ^ (m + 1) * (∑ k : Fin (m + 1), c k ^ 2) ^ 2 := by
      rw [h_step 4, hS_eq]
      have h_alg : ∀ z' : Qubits m,
          (c 0 + S' z') ^ 4 + (-c 0 + S' z') ^ 4 =
            2 * S' z' ^ 4 + 12 * c 0 ^ 2 * S' z' ^ 2 + 2 * c 0 ^ 4 * 1 :=
        fun _ => by ring
      simp_rw [h_alg]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum, hcard_m]
      dsimp only [S']
      have hp_pos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
      have hc0_4 : 0 ≤ c 0 ^ 4 := by positivity
      calc 2 * ∑ x : Qubits m, (∑ k : Fin m, c' k * radBit (x k)) ^ 4 +
              12 * c 0 ^ 2 * ∑ x : Qubits m, (∑ k : Fin m, c' k * radBit (x k)) ^ 2 +
              2 * c 0 ^ 4 * (2 : ℝ) ^ m
          ≤ 2 * (3 * (2 : ℝ) ^ m * (∑ k : Fin m, c' k ^ 2) ^ 2) +
              12 * c 0 ^ 2 * ((2 : ℝ) ^ m * ∑ k : Fin m, c' k ^ 2) +
              2 * c 0 ^ 4 * (2 : ℝ) ^ m := by
            refine add_le_add (add_le_add (mul_le_mul_of_nonneg_left ih4 (by norm_num)) ?_) le_rfl
            rw [ih2]
        _ ≤ 3 * (2 : ℝ) ^ (m + 1) * (c 0 ^ 2 + ∑ k : Fin m, c' k ^ 2) ^ 2 := by
            rw [pow_succ (2 : ℝ) m, ← sub_nonneg]
            have hdiff : 3 * ((2 : ℝ) ^ m * 2) * (c 0 ^ 2 + ∑ k : Fin m, c' k ^ 2) ^ 2 -
                (2 * (3 * (2 : ℝ) ^ m * (∑ k : Fin m, c' k ^ 2) ^ 2) +
                12 * c 0 ^ 2 * ((2 : ℝ) ^ m * ∑ k : Fin m, c' k ^ 2) +
                2 * c 0 ^ 4 * (2 : ℝ) ^ m) =
                (2 : ℝ) ^ m * (4 * c 0 ^ 4) := by ring
            rw [hdiff]
            positivity
    have h6 : ∑ z : Qubits (m + 1), (∑ k : Fin (m + 1), c k * radBit (z k)) ^ 6 ≤
        15 * (2 : ℝ) ^ (m + 1) * (∑ k : Fin (m + 1), c k ^ 2) ^ 3 := by
      rw [h_step 6, hS_eq]
      have h_alg : ∀ z' : Qubits m,
          (c 0 + S' z') ^ 6 + (-c 0 + S' z') ^ 6 =
            2 * S' z' ^ 6 + 30 * c 0 ^ 2 * S' z' ^ 4 + 30 * c 0 ^ 4 * S' z' ^ 2 +
              2 * c 0 ^ 6 * 1 :=
        fun _ => by ring
      simp_rw [h_alg]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hcard_m]
      dsimp only [S']
      have h_m4 : 30 * c 0 ^ 2 * ∑ z' : Qubits m, (∑ k : Fin m, c' k * radBit (z' k)) ^ 4 ≤
          30 * c 0 ^ 2 * (3 * (2 : ℝ) ^ m * (∑ k : Fin m, c' k ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left ih4 (by positivity)
      calc 2 * ∑ x : Qubits m, (∑ k : Fin m, c' k * radBit (x k)) ^ 6 +
              30 * c 0 ^ 2 * ∑ x : Qubits m, (∑ k : Fin m, c' k * radBit (x k)) ^ 4 +
              30 * c 0 ^ 4 * ∑ x : Qubits m, (∑ k : Fin m, c' k * radBit (x k)) ^ 2 +
              2 * c 0 ^ 6 * (2 : ℝ) ^ m
          ≤ 2 * (15 * (2 : ℝ) ^ m * (∑ k : Fin m, c' k ^ 2) ^ 3) +
              30 * c 0 ^ 2 * (3 * (2 : ℝ) ^ m * (∑ k : Fin m, c' k ^ 2) ^ 2) +
              30 * c 0 ^ 4 * ((2 : ℝ) ^ m * ∑ k : Fin m, c' k ^ 2) +
              2 * c 0 ^ 6 * (2 : ℝ) ^ m := by
            refine add_le_add (add_le_add
              (add_le_add (mul_le_mul_of_nonneg_left ih6 (by norm_num)) h_m4) ?_) le_rfl
            rw [ih2]
        _ ≤ 15 * (2 : ℝ) ^ (m + 1) * (c 0 ^ 2 + ∑ k : Fin m, c' k ^ 2) ^ 3 := by
            rw [pow_succ (2 : ℝ) m, ← sub_nonneg]
            have hdiff : 15 * ((2 : ℝ) ^ m * 2) * (c 0 ^ 2 + ∑ k : Fin m, c' k ^ 2) ^ 3 -
                (2 * (15 * (2 : ℝ) ^ m * (∑ k : Fin m, c' k ^ 2) ^ 3) +
                30 * c 0 ^ 2 * (3 * (2 : ℝ) ^ m * (∑ k : Fin m, c' k ^ 2) ^ 2) +
                30 * c 0 ^ 4 * ((2 : ℝ) ^ m * ∑ k : Fin m, c' k ^ 2) +
                2 * c 0 ^ 6 * (2 : ℝ) ^ m) =
                (2 : ℝ) ^ m * (60 * c 0 ^ 4 * (∑ k : Fin m, c' k ^ 2) + 28 * c 0 ^ 6) := by ring
            rw [hdiff]
            positivity
    exact ⟨h2, h4, h6⟩

private lemma sum_cos_rademacher (m : ℕ) (μ : ℝ) (a : Fin m → ℝ) :
    ∑ z : Qubits m, Real.cos (μ + ∑ k : Fin m, a k * radBit (z k)) =
      (2 : ℝ) ^ m * Real.cos μ * ∏ k : Fin m, Real.cos (a k) := by
  induction m generalizing μ with
  | zero =>
    have hcard : (Finset.univ : Finset (Qubits 0)).card = 1 := by simp
    simp [Finset.sum_const, hcard]
  | succ m ih =>
    let a' : Fin m → ℝ := fun k => a k.succ
    rw [← Equiv.sum_comp (qubitsSuccEquiv m), Fintype.sum_prod_type, Fintype.sum_bool,
      ← Finset.sum_add_distrib]
    have h_pair : ∀ z' : Qubits m,
        Real.cos (μ + ∑ k : Fin (m + 1), a k * radBit ((qubitsSuccEquiv m (true, z')) k)) +
        Real.cos (μ + ∑ k : Fin (m + 1), a k * radBit ((qubitsSuccEquiv m (false, z')) k)) =
        Real.cos ((μ + a 0) + ∑ k : Fin m, a' k * radBit (z' k)) +
        Real.cos ((μ - a 0) + ∑ k : Fin m, a' k * radBit (z' k)) := by
      intro z'
      simp only [qubitsSuccEquiv, Equiv.coe_fn_mk, Fin.sum_univ_succ, Fin.cons_zero,
        Fin.cons_succ, radBit, ↓reduceIte, Bool.false_eq_true, mul_one, mul_neg]
      congr 1 <;> congr 1 <;> ring
    simp_rw [h_pair]
    rw [Finset.sum_add_distrib, ih (μ + a 0) a', ih (μ - a 0) a', Fin.prod_univ_succ]
    have htrig : Real.cos (μ + a 0) + Real.cos (μ - a 0) = 2 * Real.cos μ * Real.cos (a 0) := by
      rw [Real.cos_add, Real.cos_sub]
      ring
    calc (2 : ℝ) ^ m * Real.cos (μ + a 0) * ∏ x : Fin m, Real.cos (a' x) +
            (2 : ℝ) ^ m * Real.cos (μ - a 0) * ∏ x : Fin m, Real.cos (a' x)
        = (2 : ℝ) ^ m * (Real.cos (μ + a 0) + Real.cos (μ - a 0)) *
            ∏ x : Fin m, Real.cos (a' x) := by ring
      _ = (2 : ℝ) ^ (m + 1) * Real.cos μ * (Real.cos (a 0) * ∏ i : Fin m, Real.cos (a' i)) := by
            rw [htrig, pow_succ]
            ring

private lemma viete_cos_prod (ℓ : ℕ) (θ : ℝ) :
    (2 : ℝ) ^ ℓ * Real.sin (θ / (2 : ℝ) ^ ℓ) *
      ∏ j : Fin ℓ, Real.cos (θ / (2 : ℝ) ^ ((j : ℕ) + 1)) = Real.sin θ := by
  induction ℓ with
  | zero => simp
  | succ m ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    have h_double : 2 * Real.sin (θ / (2 : ℝ) ^ (m + 1)) * Real.cos (θ / (2 : ℝ) ^ (m + 1)) =
        Real.sin (θ / (2 : ℝ) ^ m) := by
      have harg : 2 * (θ / (2 : ℝ) ^ (m + 1)) = θ / (2 : ℝ) ^ m := by
        rw [pow_succ]
        ring
      rw [← Real.sin_two_mul, harg]
    calc (2 : ℝ) ^ (m + 1) * Real.sin (θ / (2 : ℝ) ^ (m + 1)) *
            ((∏ i : Fin m, Real.cos (θ / (2 : ℝ) ^ ((i : ℕ) + 1))) *
              Real.cos (θ / (2 : ℝ) ^ (m + 1)))
        = (2 : ℝ) ^ m * (2 * Real.sin (θ / (2 : ℝ) ^ (m + 1)) *
            Real.cos (θ / (2 : ℝ) ^ (m + 1))) *
            ∏ i : Fin m, Real.cos (θ / (2 : ℝ) ^ ((i : ℕ) + 1)) := by
              rw [pow_succ]; ring
      _ = Real.sin θ := by rw [h_double, ih]

private lemma nonneg_of_deriv_nonneg {g g' : ℝ → ℝ} (hg0 : g 0 = 0)
    (hd : ∀ x, HasDerivAt g (g' x) x) (hpos : ∀ x ≥ 0, 0 ≤ g' x) :
    ∀ x ≥ 0, 0 ≤ g x := by
  have hmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact Continuous.continuousOn (continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt)
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hd x).deriv]
      exact hpos x (interior_subset hx)
  intro x hx
  rw [← hg0]
  exact hmono (le_refl (0 : ℝ)) hx hx

private lemma hasDerivAt_sin_fun (x : ℝ) : HasDerivAt (fun t : ℝ => Real.sin t) (Real.cos x) x :=
  Real.hasDerivAt_sin x

private lemma hasDerivAt_cos_fun (x : ℝ) : HasDerivAt (fun t : ℝ => Real.cos t) (-Real.sin x) x :=
  Real.hasDerivAt_cos x

private lemma cos_le_exp_neg_sq_div_two {u : ℝ} (hu : |u| ≤ Real.pi / 2) :
    0 ≤ Real.cos u ∧ Real.cos u ≤ Real.exp (-u ^ 2 / 2) := by
  have hbounds := abs_le.mp hu
  have hcos_nonneg : 0 ≤ Real.cos u := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hbounds.2⟩
  refine ⟨hcos_nonneg, ?_⟩
  suffices h_abs : ∀ v : ℝ, 0 ≤ v → v ≤ Real.pi / 2 → Real.cos v ≤ Real.exp (-v ^ 2 / 2) by
    have := h_abs |u| (abs_nonneg u) hu
    rwa [Real.cos_abs, sq_abs] at this
  intro v hv0 hvpi
  have hp_deriv : ∀ x : ℝ, HasDerivAt (fun t => Real.sin t - t * Real.cos t) (x * Real.sin x) x := by
    intro x
    have h1 := hasDerivAt_sin_fun x
    have h2 := (hasDerivAt_id' x).mul (hasDerivAt_cos_fun x)
    have h3 := h1.sub h2
    rw [show Real.cos x - (1 * Real.cos x + x * -Real.sin x) = x * Real.sin x by ring] at h3
    exact h3
  have hp_mono : MonotoneOn (fun t => Real.sin t - t * Real.cos t) (Set.Icc 0 (Real.pi / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (Real.pi / 2))
    · exact Continuous.continuousOn (by fun_prop)
    · exact fun x _ => (hp_deriv x).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' := interior_subset hx
      rw [(hp_deriv x).deriv]
      exact mul_nonneg hx'.1 (Real.sin_nonneg_of_nonneg_of_le_pi hx'.1 (by linarith [hx'.2]))
  have hh_deriv : ∀ x : ℝ, HasDerivAt (fun t => Real.cos t * Real.exp (t ^ 2 / 2))
      ((x * Real.cos x - Real.sin x) * Real.exp (x ^ 2 / 2)) x := by
    intro x
    have hsq : HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * t ^ 2)
        ((1 / 2 : ℝ) * (↑(2 : ℕ) * x ^ (2 - 1))) x :=
      (hasDerivAt_pow 2 x).const_mul (1 / 2)
    have hsq' : HasDerivAt (fun t : ℝ => t ^ 2 / 2) x x := by
      rw [show ((1 / 2 : ℝ) * (↑(2 : ℕ) * x ^ (2 - 1))) = x by norm_num; ring] at hsq
      exact hsq.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by ring)
    have h3 := (hasDerivAt_cos_fun x).mul hsq'.exp
    rw [show -Real.sin x * Real.exp (x ^ 2 / 2) + Real.cos x * (Real.exp (x ^ 2 / 2) * x) =
        (x * Real.cos x - Real.sin x) * Real.exp (x ^ 2 / 2) by ring] at h3
    exact h3
  have hh_anti : AntitoneOn (fun t => Real.cos t * Real.exp (t ^ 2 / 2))
      (Set.Icc 0 (Real.pi / 2)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 (Real.pi / 2))
    · exact Continuous.continuousOn (by fun_prop)
    · exact fun x _ => (hh_deriv x).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' := interior_subset hx
      rw [(hh_deriv x).deriv]
      have hp0 : 0 ≤ Real.sin x - x * Real.cos x := by
        have := hp_mono ⟨le_refl 0, by positivity⟩ hx' hx'.1
        simpa using this
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_nonneg _)
  have hh_le : Real.cos v * Real.exp (v ^ 2 / 2) ≤ 1 := by
    have := hh_anti ⟨le_refl 0, by positivity⟩ ⟨hv0, hvpi⟩ hv0
    simpa using this
  calc Real.cos v = (Real.cos v * Real.exp (v ^ 2 / 2)) * Real.exp (-v ^ 2 / 2) := by
        rw [mul_assoc, ← Real.exp_add, show v ^ 2 / 2 + -v ^ 2 / 2 = 0 by ring,
          Real.exp_zero, mul_one]
    _ ≤ 1 * Real.exp (-v ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right hh_le (Real.exp_nonneg _)
    _ = Real.exp (-v ^ 2 / 2) := one_mul _

private lemma hd_monomial (k : ℕ) (c x : ℝ) :
    HasDerivAt (fun t : ℝ => c * t ^ (k + 1)) (c * ((k + 1 : ℕ) : ℝ) * x ^ k) x := by
  have h := (hasDerivAt_pow (k + 1) x).const_mul c
  rw [Nat.add_sub_cancel, ← mul_assoc] at h
  exact h

private lemma sin_ge_taylor7 {u : ℝ} (hu : 0 ≤ u) :
    u - u ^ 3 / 6 + u ^ 5 / 120 - u ^ 7 / 5040 ≤ Real.sin u := by
  have h1 : ∀ x ≥ 0, 0 ≤ x - Real.sin x := by
    refine nonneg_of_deriv_nonneg (g' := fun x => 1 - Real.cos x) (by simp) (fun x => ?_)
      (fun x _ => sub_nonneg.2 (Real.cos_le_one x))
    refine HasDerivAt.congr_of_eventuallyEq ((hasDerivAt_id' x).sub (hasDerivAt_sin_fun x))
      (Filter.Eventually.of_forall fun t => ?_)
    simp
  have h2 : ∀ x ≥ 0, 0 ≤ (1 / 2 : ℝ) * x ^ 2 - 1 + Real.cos x := by
    refine nonneg_of_deriv_nonneg (g' := fun x => x - Real.sin x) (by norm_num) (fun x => ?_)
      (fun x hx => h1 x hx)
    have hp := hd_monomial 1 (1 / 2) x
    have htot := (hp.sub (hasDerivAt_const x (1 : ℝ))).add (hasDerivAt_cos_fun x)
    rw [show (1 / 2 : ℝ) * ((1 + 1 : ℕ) : ℝ) * x ^ 1 - 0 + -Real.sin x =
        x - Real.sin x by push_cast; ring] at htot
    refine HasDerivAt.congr_of_eventuallyEq htot (Filter.Eventually.of_forall fun t => ?_)
    simp
  have h3 : ∀ x ≥ 0, 0 ≤ (1 / 6 : ℝ) * x ^ 3 - x + Real.sin x := by
    refine nonneg_of_deriv_nonneg (g' := fun x => (1 / 2 : ℝ) * x ^ 2 - 1 + Real.cos x)
      (by norm_num) (fun x => ?_) (fun x hx => h2 x hx)
    have hp := hd_monomial 2 (1 / 6) x
    have htot := (hp.sub (hasDerivAt_id' x)).add (hasDerivAt_sin_fun x)
    rw [show (1 / 6 : ℝ) * ((2 + 1 : ℕ) : ℝ) * x ^ 2 - 1 + Real.cos x =
        (1 / 2 : ℝ) * x ^ 2 - 1 + Real.cos x by push_cast; ring] at htot
    refine HasDerivAt.congr_of_eventuallyEq htot (Filter.Eventually.of_forall fun t => ?_)
    simp
  have h4 : ∀ x ≥ 0, 0 ≤ (1 / 24 : ℝ) * x ^ 4 - (1 / 2 : ℝ) * x ^ 2 + 1 - Real.cos x := by
    refine nonneg_of_deriv_nonneg (g' := fun x => (1 / 6 : ℝ) * x ^ 3 - x + Real.sin x)
      (by norm_num) (fun x => ?_) (fun x hx => h3 x hx)
    have htot := (((hd_monomial 3 (1 / 24) x).sub (hd_monomial 1 (1 / 2) x)).add
      (hasDerivAt_const x (1 : ℝ))).sub (hasDerivAt_cos_fun x)
    rw [show (1 / 24 : ℝ) * ((3 + 1 : ℕ) : ℝ) * x ^ 3 -
        (1 / 2 : ℝ) * ((1 + 1 : ℕ) : ℝ) * x ^ 1 + 0 - -Real.sin x =
        (1 / 6 : ℝ) * x ^ 3 - x + Real.sin x by push_cast; ring] at htot
    refine HasDerivAt.congr_of_eventuallyEq htot (Filter.Eventually.of_forall fun t => ?_)
    simp
  have h5 : ∀ x ≥ 0, 0 ≤ (1 / 120 : ℝ) * x ^ 5 - (1 / 6 : ℝ) * x ^ 3 + x - Real.sin x := by
    refine nonneg_of_deriv_nonneg
      (g' := fun x => (1 / 24 : ℝ) * x ^ 4 - (1 / 2 : ℝ) * x ^ 2 + 1 - Real.cos x)
      (by norm_num) (fun x => ?_) (fun x hx => h4 x hx)
    have htot := (((hd_monomial 4 (1 / 120) x).sub (hd_monomial 2 (1 / 6) x)).add
      (hasDerivAt_id' x)).sub (hasDerivAt_sin_fun x)
    rw [show (1 / 120 : ℝ) * ((4 + 1 : ℕ) : ℝ) * x ^ 4 -
        (1 / 6 : ℝ) * ((2 + 1 : ℕ) : ℝ) * x ^ 2 + 1 - Real.cos x =
        (1 / 24 : ℝ) * x ^ 4 - (1 / 2 : ℝ) * x ^ 2 + 1 - Real.cos x by push_cast; ring] at htot
    refine HasDerivAt.congr_of_eventuallyEq htot (Filter.Eventually.of_forall fun t => ?_)
    simp
  have h6 : ∀ x ≥ 0, 0 ≤ (1 / 720 : ℝ) * x ^ 6 - (1 / 24 : ℝ) * x ^ 4 + (1 / 2 : ℝ) * x ^ 2 -
      1 + Real.cos x := by
    refine nonneg_of_deriv_nonneg
      (g' := fun x => (1 / 120 : ℝ) * x ^ 5 - (1 / 6 : ℝ) * x ^ 3 + x - Real.sin x)
      (by norm_num) (fun x => ?_) (fun x hx => h5 x hx)
    have htot := ((((hd_monomial 5 (1 / 720) x).sub (hd_monomial 3 (1 / 24) x)).add
      (hd_monomial 1 (1 / 2) x)).sub (hasDerivAt_const x (1 : ℝ))).add (hasDerivAt_cos_fun x)
    rw [show (1 / 720 : ℝ) * ((5 + 1 : ℕ) : ℝ) * x ^ 5 -
        (1 / 24 : ℝ) * ((3 + 1 : ℕ) : ℝ) * x ^ 3 +
        (1 / 2 : ℝ) * ((1 + 1 : ℕ) : ℝ) * x ^ 1 - 0 + -Real.sin x =
        (1 / 120 : ℝ) * x ^ 5 - (1 / 6 : ℝ) * x ^ 3 + x - Real.sin x by push_cast; ring] at htot
    refine HasDerivAt.congr_of_eventuallyEq htot (Filter.Eventually.of_forall fun t => ?_)
    simp
  have h7 : ∀ x ≥ 0, 0 ≤ (1 / 5040 : ℝ) * x ^ 7 - (1 / 120 : ℝ) * x ^ 5 + (1 / 6 : ℝ) * x ^ 3 -
      x + Real.sin x := by
    refine nonneg_of_deriv_nonneg
      (g' := fun x => (1 / 720 : ℝ) * x ^ 6 - (1 / 24 : ℝ) * x ^ 4 + (1 / 2 : ℝ) * x ^ 2 -
        1 + Real.cos x)
      (by norm_num) (fun x => ?_) (fun x hx => h6 x hx)
    have htot := ((((hd_monomial 6 (1 / 5040) x).sub (hd_monomial 4 (1 / 120) x)).add
      (hd_monomial 2 (1 / 6) x)).sub (hasDerivAt_id' x)).add (hasDerivAt_sin_fun x)
    rw [show (1 / 5040 : ℝ) * ((6 + 1 : ℕ) : ℝ) * x ^ 6 -
        (1 / 120 : ℝ) * ((4 + 1 : ℕ) : ℝ) * x ^ 4 +
        (1 / 6 : ℝ) * ((2 + 1 : ℕ) : ℝ) * x ^ 2 - 1 + Real.cos x =
        (1 / 720 : ℝ) * x ^ 6 - (1 / 24 : ℝ) * x ^ 4 + (1 / 2 : ℝ) * x ^ 2 -
          1 + Real.cos x by push_cast; ring] at htot
    refine HasDerivAt.congr_of_eventuallyEq htot (Filter.Eventually.of_forall fun t => ?_)
    simp
  linarith [h7 u hu]

private lemma inner_addrOf_eq {n f : ℕ} (w : EuclideanSpace ℝ (Fin n)) (z : Qubits (n * (f + 2))) :
    inner ℝ w (addrOf n (f + 2) f z) =
      -(1 / (2 * (2 : ℝ) ^ f)) * (∑ i : Fin n, w.ofLp i) +
      ∑ k : Fin (n * (f + 2)),
        (w.ofLp (finProdFinEquiv.symm k).1 * ((2 : ℝ)⁻¹) ^ ((finProdFinEquiv.symm k).2 : ℕ)) *
          radBit (z k) := by
  rw [addrOf, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  have h1 : ∑ i : Fin n, fpVal (f + 2) f (splitReg n (f + 2) z i) * w.ofLp i =
      -(1 / (2 * (2 : ℝ) ^ f)) * (∑ i : Fin n, w.ofLp i) +
      ∑ i : Fin n, ∑ j : Fin (f + 2),
        (w.ofLp i * ((2 : ℝ)⁻¹) ^ (j : ℕ)) * radBit (z (finProdFinEquiv (i, j))) := by
    simp_rw [fpVal_eq_radSum f, add_mul, Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl fun _ _ => by ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp only [splitReg]
      ring
  rw [h1]
  congr 1
  rw [← Fintype.sum_prod_type', ← Equiv.sum_comp finProdFinEquiv.symm]
  refine Finset.sum_congr rfl fun k _ => ?_
  change (w.ofLp (finProdFinEquiv.symm k).1 * ((2 : ℝ)⁻¹) ^ ((finProdFinEquiv.symm k).2 : ℕ)) *
      radBit (z (finProdFinEquiv ((finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2))) = _
  rw [Prod.mk.eta, Equiv.apply_symm_apply]

private lemma ceil_logb_props {n : ℕ} (hn : 2 ≤ n) :
    let k := ⌈Real.logb 2 n⌉₊
    1 ≤ k ∧ (n : ℝ) ≤ (2 : ℝ) ^ k ∧ (3 ≤ n → 2 ≤ k) ∧ (5 ≤ n → 3 ≤ k) := by
  intro k
  have hn_pos : (0 : ℝ) < n := by positivity
  have h2_gt : (1 : ℝ) < 2 := by norm_num
  have hk_ge : Real.logb 2 n ≤ (k : ℝ) := Nat.le_ceil _
  have hn_le : (n : ℝ) ≤ (2 : ℝ) ^ k := by
    have h := (Real.rpow_le_rpow_left_iff h2_gt).mpr hk_ge
    rwa [Real.rpow_logb (by norm_num) (by norm_num) hn_pos, Real.rpow_natCast] at h
  have hk1 : 1 ≤ k := by
    rw [Nat.one_le_iff_ne_zero]
    intro hk0
    have hle0 : Real.logb 2 n ≤ 0 := by simpa [hk0] using hk_ge
    have hlt : (1 : ℝ) < n := by exact_mod_cast hn
    have hpos : 0 < Real.logb 2 n := Real.logb_pos h2_gt hlt
    linarith
  have hk2 : 3 ≤ n → 2 ≤ k := by
    intro hn3
    have hlt : (2 : ℝ) ^ (1 : ℝ) < n := by norm_num; exact_mod_cast hn3
    have h1 : (1 : ℝ) < Real.logb 2 n := (Real.lt_logb_iff_rpow_lt h2_gt hn_pos).mpr hlt
    exact Nat.lt_ceil.mpr (by exact_mod_cast h1)
  have hk3 : 5 ≤ n → 3 ≤ k := by
    intro hn5
    have hlt : (2 : ℝ) ^ (2 : ℝ) < n := by norm_num; exact_mod_cast hn5
    have h2 : (2 : ℝ) < Real.logb 2 n := (Real.lt_logb_iff_rpow_lt h2_gt hn_pos).mpr hlt
    exact Nat.lt_ceil.mpr (by exact_mod_cast h2)
  exact ⟨hk1, hn_le, hk2, hk3⟩

private lemma norm_sq_eq_sum {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) :
    ∑ i : Fin n, w.ofLp i ^ 2 = 1 := by
  have h := EuclideanSpace.norm_eq w
  rw [hw] at h
  have hsq : (1 : ℝ) ^ 2 = (Real.sqrt (∑ i : Fin n, ‖w.ofLp i‖ ^ 2)) ^ 2 :=
    congrArg (· ^ 2) h
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)] at hsq
  simpa [Real.norm_eq_abs, sq_abs] using hsq.symm

private lemma geom_sum_quarter (m : ℕ) :
    ∑ j ∈ Finset.range m, ((4 : ℝ)⁻¹) ^ j = (4 / 3 : ℝ) * (1 - ((4 : ℝ)⁻¹) ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

private lemma upper_tail_card_le {n : ℕ} (hn : 2 ≤ n) (w : EuclideanSpace ℝ (Fin n))
    (hw : ‖w‖ = 1) :
    let k := ⌈Real.logb 2 n⌉₊
    let f := 2 + k
    let ℓ := 4 + k
    ((Finset.univ.filter (fun z : Qubits (n * ℓ) =>
        3 < |inner ℝ w (addrOf n ℓ f z)|)).card : ℝ) ≤
      (59 / 1000 : ℝ) * (2 : ℝ) ^ (n * ℓ) := by
  intro k f ℓ
  have hℓ_eq : ℓ = f + 2 := by omega
  obtain ⟨_, hn_le, _, _⟩ := ceil_logb_props hn
  have hsum_w_sq : ∑ i : Fin n, w.ofLp i ^ 2 = 1 := norm_sq_eq_sum w hw
  have hcs : (∑ i : Fin n, w.ofLp i) ^ 2 ≤ n := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) (fun _ => (1 : ℝ))
      (fun i => w.ofLp i)
    simpa [hsum_w_sq] using h
  let μ := -(1 / (2 * (2 : ℝ) ^ f)) * (∑ i : Fin n, w.ofLp i)
  have hμ_le : |μ| ≤ 9 / 100 := by
    have hμ_sq : μ ^ 2 ≤ (9 / 100 : ℝ) ^ 2 := by
      have hf_pow : (2 : ℝ) ^ f = 4 * (2 : ℝ) ^ k := by
        change (2 : ℝ) ^ (2 + k) = 4 * (2 : ℝ) ^ k
        rw [pow_add]; norm_num
      have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      have hn_ge2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have h2k_sq : 2 * (n : ℝ) ≤ ((2 : ℝ) ^ k) ^ 2 := by nlinarith
      have hμ_sq_eq : μ ^ 2 = (∑ i : Fin n, w.ofLp i) ^ 2 / (64 * ((2 : ℝ) ^ k) ^ 2) := by
        simp only [μ, hf_pow]; ring
      rw [hμ_sq_eq, div_le_iff₀ (by positivity)]
      nlinarith
    exact abs_le.mpr (abs_le_of_sq_le_sq' hμ_sq (by norm_num))
  let c : Fin (n * (f + 2)) → ℝ := fun r =>
    w.ofLp (finProdFinEquiv.symm r).1 * ((2 : ℝ)⁻¹) ^ ((finProdFinEquiv.symm r).2 : ℕ)
  have hc_sum_le : ∑ r : Fin (n * (f + 2)), c r ^ 2 ≤ 4 / 3 := by
    have hprod : ∑ r : Fin (n * (f + 2)), c r ^ 2 =
        (∑ i : Fin n, w.ofLp i ^ 2) * ∑ j : Fin (f + 2), (((2 : ℝ)⁻¹) ^ (j : ℕ)) ^ 2 := by
      rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [c, Equiv.symm_apply_apply]; ring
    rw [hprod, hsum_w_sq, one_mul]
    have hfin_eq : ∑ j : Fin (f + 2), (((2 : ℝ)⁻¹) ^ (j : ℕ)) ^ 2 =
        ∑ j ∈ Finset.range (f + 2), ((4 : ℝ)⁻¹) ^ j := by
      rw [Fin.sum_univ_eq_sum_range (fun j => (((2 : ℝ)⁻¹) ^ j) ^ 2)]
      refine Finset.sum_congr rfl fun j _ => by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
    rw [hfin_eq, geom_sum_quarter]
    have hpos4 : 0 ≤ ((4 : ℝ)⁻¹) ^ (f + 2) := by positivity
    linarith
  have hm6 := (rademacher_moments (n * (f + 2)) c).2.2
  rw [hℓ_eq]
  let F := Finset.univ.filter (fun z : Qubits (n * (f + 2)) =>
    3 < |inner ℝ w (addrOf n (f + 2) f z)|)
  have hmarkov : (F.card : ℝ) * (291 / 100 : ℝ) ^ 6 ≤
      ∑ z : Qubits (n * (f + 2)), (∑ r : Fin (n * (f + 2)), c r * radBit (z r)) ^ 6 := by
    calc (F.card : ℝ) * (291 / 100 : ℝ) ^ 6
        = ∑ _ ∈ F, (291 / 100 : ℝ) ^ 6 := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ z ∈ F, (∑ r : Fin (n * (f + 2)), c r * radBit (z r)) ^ 6 := by
            refine Finset.sum_le_sum fun z hz => ?_
            have hz' : 3 < |inner ℝ w (addrOf n (f + 2) f z)| := (Finset.mem_filter.mp hz).2
            rw [inner_addrOf_eq] at hz'
            change 3 < |μ + ∑ r : Fin (n * (f + 2)), c r * radBit (z r)| at hz'
            have htri := abs_add_le μ (∑ r : Fin (n * (f + 2)), c r * radBit (z r))
            have habs_gt : (291 / 100 : ℝ) ≤ |∑ r : Fin (n * (f + 2)), c r * radBit (z r)| := by
              linarith
            have hpow6 := pow_le_pow_left₀ (by norm_num) habs_gt 6
            simpa [Even.pow_abs (by decide : Even 6)] using hpow6
      _ ≤ ∑ z : Qubits (n * (f + 2)), (∑ r : Fin (n * (f + 2)), c r * radBit (z r)) ^ 6 :=
            Finset.sum_le_univ_sum_of_nonneg fun z => by positivity
  have hc_nonneg : 0 ≤ ∑ r : Fin (n * (f + 2)), c r ^ 2 :=
    Finset.sum_nonneg fun r _ => sq_nonneg (c r)
  have hcube : (∑ r : Fin (n * (f + 2)), c r ^ 2) ^ 3 ≤ (4 / 3 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hc_nonneg hc_sum_le 3
  have htotal : (F.card : ℝ) * (291 / 100 : ℝ) ^ 6 ≤
      15 * (2 : ℝ) ^ (n * (f + 2)) * (4 / 3 : ℝ) ^ 3 := by
    have h1 : 15 * (2 : ℝ) ^ (n * (f + 2)) * (∑ r : Fin (n * (f + 2)), c r ^ 2) ^ 3 ≤
        15 * (2 : ℝ) ^ (n * (f + 2)) * (4 / 3 : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    linarith
  have hnum : (15 : ℝ) * (4 / 3 : ℝ) ^ 3 ≤ (59 / 1000 : ℝ) * (291 / 100 : ℝ) ^ 6 := by norm_num
  have hpow_pos : (0 : ℝ) < (291 / 100 : ℝ) ^ 6 := by norm_num
  have h2pow_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (n * (f + 2)) := by positivity
  nlinarith

private lemma fin_interval_card_le {M : ℕ} (c r : ℝ) (hr : 0 ≤ r) :
    ((Finset.univ.filter (fun m : Fin M => |((m : ℕ) : ℝ) - c| < r)).card : ℝ) ≤ 2 * r + 1 := by
  let S := Finset.univ.filter (fun m : Fin M => |((m : ℕ) : ℝ) - c| < r)
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    let b := S.max' hS
    have ha_mem : a ∈ S := Finset.min'_mem S hS
    have hb_mem : b ∈ S := Finset.max'_mem S hS
    have ha_lt : |((a : ℕ) : ℝ) - c| < r := (Finset.mem_filter.mp ha_mem).2
    have hb_lt : |((b : ℕ) : ℝ) - c| < r := (Finset.mem_filter.mp hb_mem).2
    have hab : (a : ℕ) ≤ (b : ℕ) := Fin.le_iff_val_le_val.mp (Finset.min'_le S b hb_mem)
    have hdiff_lt : ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) < 2 * r := by
      linarith [(abs_lt.mp ha_lt).1, (abs_lt.mp hb_lt).2]
    have hinj : ∀ m ∈ S, (m : ℕ) ∈ Finset.Icc (a : ℕ) (b : ℕ) := by
      intro m hm
      exact Finset.mem_Icc.mpr ⟨Fin.le_iff_val_le_val.mp (Finset.min'_le S m hm),
        Fin.le_iff_val_le_val.mp (Finset.le_max' S m hm)⟩
    have hcard_nat : S.card ≤ (Finset.Icc (a : ℕ) (b : ℕ)).card := by
      calc S.card = (S.image Fin.val).card :=
            (Finset.card_image_of_injective S Fin.val_injective).symm
        _ ≤ (Finset.Icc (a : ℕ) (b : ℕ)).card :=
            Finset.card_le_card (Finset.image_subset_iff.mpr hinj)
    rw [Nat.card_Icc] at hcard_nat
    have hcast : (S.card : ℝ) ≤ ((b : ℕ) : ℝ) + 1 - ((a : ℕ) : ℝ) := by
      have h1 : (S.card : ℝ) ≤ (((b : ℕ) + 1 - (a : ℕ) : ℕ) : ℝ) := by exact_mod_cast hcard_nat
      have h2 : (((b : ℕ) + 1 - (a : ℕ) : ℕ) : ℝ) = ((b : ℕ) : ℝ) + 1 - ((a : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
      linarith
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    change (S.card : ℝ) ≤ 2 * r + 1
    rw [hS, Finset.card_empty, Nat.cast_zero]
    linarith

private lemma small_ball_case1 {n : ℕ} (hn : 2 ≤ n) (w : EuclideanSpace ℝ (Fin n))
    (hw : ‖w‖ = 1) (hcase1 : ∃ i : Fin n, (11 / 25 : ℝ) ≤ |w.ofLp i|) :
    let k := ⌈Real.logb 2 n⌉₊
    let f := 2 + k
    let ℓ := 4 + k
    ((Finset.univ.filter (fun z : Qubits (n * ℓ) =>
        |inner ℝ w (addrOf n ℓ f z)| < 1 / 10)).card : ℝ) ≤
      (141 / 1000 : ℝ) * (2 : ℝ) ^ (n * ℓ) := by
  intro k f ℓ
  have hℓ_eq : ℓ = f + 2 := by omega
  obtain ⟨hk1, _, hk2, hk3⟩ := ceil_logb_props hn
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩
  obtain ⟨i₀, _, hi₀_max⟩ := Finset.exists_max_image Finset.univ (fun i : Fin n => |w.ofLp i|) hne
  obtain ⟨i₁, hi₁⟩ := hcase1
  have hw_ge_tau : (11 / 25 : ℝ) ≤ |w.ofLp i₀| := hi₁.trans (hi₀_max i₁ (Finset.mem_univ i₁))
  have hw_pos : 0 < |w.ofLp i₀| := by linarith
  have hw_sq_max : (1 : ℝ) ≤ (n : ℝ) * |w.ofLp i₀| ^ 2 := by
    have hsum := norm_sq_eq_sum w hw
    calc (1 : ℝ) = ∑ i : Fin n, |w.ofLp i| ^ 2 := by simpa [sq_abs] using hsum.symm
      _ ≤ ∑ _ : Fin n, |w.ofLp i₀| ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact pow_le_pow_left₀ (abs_nonneg _) (hi₀_max i (Finset.mem_univ i)) 2
      _ = (n : ℝ) * |w.ofLp i₀| ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
  let splitCoord : (Fin n → Qubits ℓ) ≃ Qubits ℓ × ({i : Fin n // i ≠ i₀} → Qubits ℓ) :=
    { toFun := fun g => (g i₀, fun j => g j.1)
      invFun := fun p i => if h : i = i₀ then p.1 else p.2 ⟨i, h⟩
      left_inv := fun g => by
        ext i b
        by_cases h : i = i₀ <;> simp [h]
      right_inv := fun ⟨x, rest⟩ => by
        ext
        · simp
        · rename_i j _
          rcases j with ⟨i, hi⟩
          simp [hi] }
  let E : Qubits (n * ℓ) ≃ Fin (2 ^ ℓ) × ({i : Fin n // i ≠ i₀} → Qubits ℓ) :=
    (splitRegEquiv n ℓ).trans (splitCoord.trans (Equiv.prodCongr (bitsEquivFin ℓ) (Equiv.refl _)))
  let P : Qubits (n * ℓ) → Prop := fun z => |inner ℝ w (addrOf n ℓ f z)| < 1 / 10
  classical
  have hcard_sum : ((Finset.univ.filter P).card : ℝ) =
      ∑ rest : ({i : Fin n // i ≠ i₀} → Qubits ℓ),
        ((Finset.univ.filter (fun m : Fin (2 ^ ℓ) => P (E.symm (m, rest)))).card : ℝ) := by
    have hbij : (Finset.univ.filter P).card =
        (Finset.univ.filter (fun p : Fin (2 ^ ℓ) × ({i : Fin n // i ≠ i₀} → Qubits ℓ) =>
          P (E.symm p))).card :=
      Finset.card_bij (fun z _ => E z)
        (fun z hz => by simpa [Finset.mem_filter] using (Finset.mem_filter.mp hz).2)
        (fun z₁ _ z₂ _ h => E.injective h)
        (fun p hp => ⟨E.symm p, by simpa [Finset.mem_filter] using (Finset.mem_filter.mp hp).2,
          E.apply_symm_apply p⟩)
    rw [hbij]
    have hsum1 : ((Finset.univ.filter (fun p : Fin (2 ^ ℓ) × ({i : Fin n // i ≠ i₀} → Qubits ℓ) =>
        P (E.symm p))).card : ℝ) =
        ∑ p : Fin (2 ^ ℓ) × ({i : Fin n // i ≠ i₀} → Qubits ℓ),
          if P (E.symm p) then (1 : ℝ) else 0 := by
      simp [Finset.sum_boole]
    rw [hsum1, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun rest _ => ?_
    simp [Finset.sum_boole]
  let r := (2 : ℝ) ^ f / (10 * |w.ofLp i₀|)
  have hr_nonneg : 0 ≤ r := by positivity
  have hfiber_le : ∀ rest : ({i : Fin n // i ≠ i₀} → Qubits ℓ),
      ((Finset.univ.filter (fun m : Fin (2 ^ ℓ) => P (E.symm (m, rest)))).card : ℝ) ≤
        2 * r + 1 := by
    intro rest
    let S_rest : ℝ := ∑ i ∈ Finset.univ.erase i₀, w.ofLp i *
      fpVal ℓ f (if h : i = i₀ then (bitsEquivFin ℓ).symm ⟨0, Nat.two_pow_pos ℓ⟩ else rest ⟨i, h⟩)
    let center : ℝ := (2 : ℝ) ^ ℓ / 2 - (2 : ℝ) ^ f * S_rest / w.ofLp i₀
    have hsub : Finset.univ.filter (fun m : Fin (2 ^ ℓ) => P (E.symm (m, rest))) ⊆
        Finset.univ.filter (fun m : Fin (2 ^ ℓ) => |((m : ℕ) : ℝ) - center| < r) := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
      have hP : |inner ℝ w (addrOf n ℓ f (E.symm (m, rest)))| < 1 / 10 := hm
      have hsplit_reg : ∀ i : Fin n, splitReg n ℓ (E.symm (m, rest)) i =
          if h : i = i₀ then (bitsEquivFin ℓ).symm m else rest ⟨i, h⟩ := by
        intro i
        change (splitRegEquiv n ℓ (E.symm (m, rest))) i = _
        simp [E, splitCoord]
      have hinner : inner ℝ w (addrOf n ℓ f (E.symm (m, rest))) =
          w.ofLp i₀ * fpVal ℓ f ((bitsEquivFin ℓ).symm m) + S_rest := by
        rw [addrOf, PiLp.inner_apply]
        simp only [RCLike.inner_apply, conj_trivial]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
        congr 1
        · rw [hsplit_reg i₀, dif_pos rfl, mul_comm]
        · refine Finset.sum_congr rfl fun i hi => ?_
          have hne_i : i ≠ i₀ := Finset.ne_of_mem_erase hi
          rw [hsplit_reg i, dif_neg hne_i, dif_neg hne_i, mul_comm]
      have hbits : bitsToNat ((bitsEquivFin ℓ).symm m) = (m : ℕ) := by
        rw [← bitsEquivFin_apply, Equiv.apply_symm_apply]
      have hfp : fpVal ℓ f ((bitsEquivFin ℓ).symm m) =
          (((m : ℕ) : ℝ) - (2 : ℝ) ^ ℓ / 2) / (2 : ℝ) ^ f := by
        simp [fpVal, hbits]
      rw [hinner, hfp] at hP
      have hw_ne : w.ofLp i₀ ≠ 0 := abs_pos.mp hw_pos
      have h2f_pos : (0 : ℝ) < (2 : ℝ) ^ f := by positivity
      have hident : (((m : ℕ) : ℝ) - center) =
          ((2 : ℝ) ^ f / w.ofLp i₀) *
            (w.ofLp i₀ * ((((m : ℕ) : ℝ) - (2 : ℝ) ^ ℓ / 2) / (2 : ℝ) ^ f) + S_rest) := by
        simp only [center]
        field_simp [hw_ne]
        ring
      rw [hident, abs_mul, abs_div, abs_of_pos h2f_pos]
      calc (2 : ℝ) ^ f / |w.ofLp i₀| *
              |w.ofLp i₀ * ((((m : ℕ) : ℝ) - (2 : ℝ) ^ ℓ / 2) / (2 : ℝ) ^ f) + S_rest|
          < (2 : ℝ) ^ f / |w.ofLp i₀| * (1 / 10) :=
            mul_lt_mul_of_pos_left hP (div_pos h2f_pos hw_pos)
        _ = r := by simp only [r]; ring
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (fin_interval_card_le center r hr_nonneg)
  have h2r1_le : 2 * r + 1 ≤ (141 / 1000 : ℝ) * (2 : ℝ) ^ ℓ := by
    have h2ℓ : (2 : ℝ) ^ ℓ = 4 * (2 : ℝ) ^ f := by
      rw [hℓ_eq, pow_add]; ring
    have h2f_pos : (0 : ℝ) < (2 : ℝ) ^ f := by positivity
    by_cases hn5 : 5 ≤ n
    · have hk_ge3 : 3 ≤ k := hk3 hn5
      have hℓ_ge7 : 7 ≤ ℓ := by omega
      have h2ℓ_ge : (128 : ℝ) ≤ (2 : ℝ) ^ ℓ := by
        calc (128 : ℝ) = (2 : ℝ) ^ 7 := by norm_num
          _ ≤ (2 : ℝ) ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ_ge7
      have hr_le : 2 * r ≤ (5 / 44 : ℝ) * (2 : ℝ) ^ ℓ := by
        rw [h2ℓ]; simp only [r]
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    · by_cases hn3 : 3 ≤ n
      · have hk_ge2 : 2 ≤ k := hk2 hn3
        have hℓ_ge6 : 6 ≤ ℓ := by omega
        have h2ℓ_ge : (64 : ℝ) ≤ (2 : ℝ) ^ ℓ := by
          calc (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
            _ ≤ (2 : ℝ) ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ_ge6
        have hn_le4 : (n : ℝ) ≤ 4 := by exact_mod_cast (by omega : n ≤ 4)
        have hw_ge_half : (1 / 2 : ℝ) ≤ |w.ofLp i₀| := by
          have hsq : (1 / 4 : ℝ) ≤ |w.ofLp i₀| ^ 2 := by nlinarith
          nlinarith
        have hr_le : 2 * r ≤ (1 / 10 : ℝ) * (2 : ℝ) ^ ℓ := by
          rw [h2ℓ]; simp only [r]
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
        linarith
      · have hn_eq2 : n = 2 := by omega
        have hn2_real : (n : ℝ) = 2 := by exact_mod_cast hn_eq2
        have hℓ_ge5 : 5 ≤ ℓ := by omega
        have h2ℓ_ge : (32 : ℝ) ≤ (2 : ℝ) ^ ℓ := by
          calc (32 : ℝ) = (2 : ℝ) ^ 5 := by norm_num
            _ ≤ (2 : ℝ) ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ_ge5
        have hw_ge_7_10 : (7 / 10 : ℝ) ≤ |w.ofLp i₀| := by
          rw [hn2_real] at hw_sq_max
          nlinarith
        have hr_le : 2 * r ≤ (1 / 14 : ℝ) * (2 : ℝ) ^ ℓ := by
          rw [h2ℓ]; simp only [r]
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
        linarith
  have hcard_rest : (Fintype.card ({i : Fin n // i ≠ i₀} → Qubits ℓ) : ℝ) * (2 : ℝ) ^ ℓ =
      (2 : ℝ) ^ (n * ℓ) := by
    have hbij := Fintype.card_congr E
    rw [Fintype.card_prod, Fintype.card_fin] at hbij
    have htot : Fintype.card (Qubits (n * ℓ)) = 2 ^ (n * ℓ) := by simp
    rw [htot] at hbij
    have hcast : ((2 ^ ℓ * Fintype.card ({i : Fin n // i ≠ i₀} → Qubits ℓ) : ℕ) : ℝ) =
        ((2 ^ (n * ℓ) : ℕ) : ℝ) := by exact_mod_cast hbij.symm
    push_cast at hcast
    linarith
  rw [hcard_sum]
  calc ∑ rest : ({i : Fin n // i ≠ i₀} → Qubits ℓ),
          ((Finset.univ.filter (fun m : Fin (2 ^ ℓ) => P (E.symm (m, rest)))).card : ℝ)
      ≤ ∑ _ : ({i : Fin n // i ≠ i₀} → Qubits ℓ), (141 / 1000 : ℝ) * (2 : ℝ) ^ ℓ :=
        Finset.sum_le_sum fun rest _ => (hfiber_le rest).trans h2r1_le
    _ = (Fintype.card ({i : Fin n // i ≠ i₀} → Qubits ℓ) : ℝ) *
          ((141 / 1000 : ℝ) * (2 : ℝ) ^ ℓ) := by simp [Finset.sum_const, nsmul_eq_mul]
    _ = (141 / 1000 : ℝ) * (2 : ℝ) ^ (n * ℓ) := by linear_combination (141 / 1000 : ℝ) * hcard_rest

/-! ### Stage B: Case 2 Small-Ball Bound via Convolved Fejér Kernel -/

private noncomputable def fejerInt (y : ℝ) : ℝ :=
  (2 / 150 : ℝ) * ∫ t in (0 : ℝ)..150, (1 - t / 150) * Real.cos (t * y)

private lemma fejerInt_cont : Continuous fejerInt := by
  unfold fejerInt
  refine Continuous.const_mul ?_ _
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 150
  have : Function.uncurry (fun (y t : ℝ) => (1 - t / 150) * Real.cos (t * y)) =
      fun p : ℝ × ℝ => (1 - p.2 / 150) * Real.cos (p.2 * p.1) := by ext ⟨y, t⟩; rfl
  rw [this]
  fun_prop

private lemma fejerInt_even (y : ℝ) : fejerInt (-y) = fejerInt y := by
  simp [fejerInt, mul_neg, Real.cos_neg]

private lemma fejerInt_eq_sinc_sq (y : ℝ) :
    fejerInt y = if y = 0 then 1 else (Real.sin (75 * y) / (75 * y)) ^ 2 := by
  unfold fejerInt
  by_cases hy : y = 0
  · subst hy
    simp only [↓reduceIte, mul_zero, Real.cos_zero, mul_one]
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 150,
        HasDerivAt (fun x : ℝ => x - (1 / 300 : ℝ) * x ^ 2) (1 - t / 150) t := by
      intro t _
      have h1 := (hasDerivAt_id' t).sub (hd_monomial 1 (1 / 300) t)
      rw [show 1 - (1 / 300 : ℝ) * ((1 + 1 : ℕ) : ℝ) * t ^ 1 = 1 - t / 150 by push_cast; ring] at h1
      exact h1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((Continuous.continuousOn (by fun_prop)).intervalIntegrable)]
    norm_num
  · simp only [hy, ↓reduceIte]
    let G : ℝ → ℝ := fun t =>
      (1 / y) * ((1 - (1 / 150 : ℝ) * t) * Real.sin (y * t)) -
        (1 / (150 * y ^ 2)) * Real.cos (y * t)
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 150,
        HasDerivAt G ((1 - t / 150) * Real.cos (t * y)) t := by
      intro t _
      have hlin : HasDerivAt (fun x : ℝ => 1 - (1 / 150 : ℝ) * x) (-(1 / 150 : ℝ)) t := by
        have h := (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id' t).const_mul (1 / 150))
        rw [show (0 : ℝ) - (1 / 150 : ℝ) * 1 = -(1 / 150 : ℝ) by ring] at h
        exact h
      have harg : HasDerivAt (fun x : ℝ => y * x) y t := by
        simpa using (hasDerivAt_id' t).const_mul y
      have hsin : HasDerivAt (fun x : ℝ => Real.sin (y * x)) (Real.cos (y * t) * y) t :=
        (Real.hasDerivAt_sin (y * t)).comp t harg
      have hcos : HasDerivAt (fun x : ℝ => Real.cos (y * x)) (-Real.sin (y * t) * y) t :=
        (Real.hasDerivAt_cos (y * t)).comp t harg
      have htot := ((hlin.mul hsin).const_mul (1 / y)).sub (hcos.const_mul (1 / (150 * y ^ 2)))
      have hval : (1 / y) * (-(1 / 150 : ℝ) * Real.sin (y * t) +
            (1 - (1 / 150 : ℝ) * t) * (Real.cos (y * t) * y)) -
          (1 / (150 * y ^ 2)) * (-Real.sin (y * t) * y) =
          (1 - t / 150) * Real.cos (t * y) := by
        rw [show y * t = t * y by ring]
        field_simp [hy]
        ring
      rw [hval] at htot
      exact htot
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((Continuous.continuousOn (by fun_prop)).intervalIntegrable)]
    simp only [G]
    have hcos2 : 1 - Real.cos (y * 150) = 2 * Real.sin (75 * y) ^ 2 := by
      have harg : y * 150 = 2 * (75 * y) := by ring
      rw [harg, Real.cos_two_mul']
      have := Real.sin_sq_add_cos_sq (75 * y)
      linarith
    have halg : (2 / 150 : ℝ) *
        ((1 / y * ((1 - 1 / 150 * 150) * Real.sin (y * 150)) -
          1 / (150 * y ^ 2) * Real.cos (y * 150)) -
         (1 / y * ((1 - 1 / 150 * 0) * Real.sin (y * 0)) -
          1 / (150 * y ^ 2) * Real.cos (y * 0))) =
        (2 / 22500 : ℝ) * (1 - Real.cos (y * 150)) / y ^ 2 := by
      simp only [mul_zero, Real.sin_zero, Real.cos_zero]
      field_simp [hy]
      ring
    rw [halg, hcos2]
    field_simp [hy]
    ring

private lemma fejerInt_nonneg (y : ℝ) : 0 ≤ fejerInt y := by
  rw [fejerInt_eq_sinc_sq]
  split_ifs
  · norm_num
  · positivity

private noncomputable def Hkern (x : ℝ) : ℝ :=
  ∫ s in (-7 / 50 : ℝ)..(7 / 50), fejerInt (x - s)

private lemma Hkern_lower_bound {x : ℝ} (hx : |x| ≤ 1 / 10) :
    (4 / 150 : ℝ) * (63511641 / 44844800 : ℝ) ≤ Hkern x := by
  unfold Hkern
  have hsub := intervalIntegral.integral_comp_sub_left fejerInt x (a := -7 / 50) (b := 7 / 50)
  have heq_end1 : x - (-7 / 50 : ℝ) = x + 7 / 50 := by ring
  rw [heq_end1] at hsub
  have hx_bounds := abs_le.mp hx
  -- Split x - 7/50 ≤ -1/25 ≤ 1/25 ≤ x + 7/50
  have ha_le : x - 7 / 50 ≤ -1 / 25 := by linarith
  have hb_ge : (1 / 25 : ℝ) ≤ x + 7 / 50 := by linarith
  have h_split1 := intervalIntegral.integral_add_adjacent_intervals
    (fejerInt_cont.intervalIntegrable (μ := volume) (x - 7 / 50) (-1 / 25))
    (fejerInt_cont.intervalIntegrable (μ := volume) (-1 / 25) (x + 7 / 50))
  have h_split2 := intervalIntegral.integral_add_adjacent_intervals
    (fejerInt_cont.intervalIntegrable (μ := volume) (-1 / 25) (1 / 25))
    (fejerInt_cont.intervalIntegrable (μ := volume) (1 / 25) (x + 7 / 50))
  have h_left_nonneg : 0 ≤ ∫ y in (x - 7 / 50)..(-1 / 25), fejerInt y :=
    intervalIntegral.integral_nonneg ha_le (fun y _ => fejerInt_nonneg y)
  have h_right_nonneg : 0 ≤ ∫ y in (1 / 25 : ℝ)..(x + 7 / 50), fejerInt y :=
    intervalIntegral.integral_nonneg hb_ge (fun y _ => fejerInt_nonneg y)
  have h_ge_mid : ∫ y in (-1 / 25 : ℝ)..(1 / 25), fejerInt y ≤
      ∫ s in (-7 / 50 : ℝ)..(7 / 50), fejerInt (x - s) := by
    linarith
  have h_even_split : ∫ y in (-1 / 25 : ℝ)..(1 / 25), fejerInt y =
      2 * ∫ y in (0 : ℝ)..(1 / 25), fejerInt y := by
    have h_adj := intervalIntegral.integral_add_adjacent_intervals
      (fejerInt_cont.intervalIntegrable (μ := volume) (-1 / 25) 0)
      (fejerInt_cont.intervalIntegrable (μ := volume) 0 (1 / 25))
    have h_neg := intervalIntegral.integral_comp_neg (a := -1 / 25) (b := 0) fejerInt
    simp only [fejerInt_even, neg_zero] at h_neg
    linarith
  -- Polynomial lower bound on [0, 1/25]
  let P : ℝ → ℝ := fun u => 1 - u ^ 2 / 6 + u ^ 4 / 120 - u ^ 6 / 5040
  have hP_le : ∀ y ∈ Set.Icc (0 : ℝ) (1 / 25), P (75 * y) ^ 2 ≤ fejerInt y := by
    intro y ⟨hy0, hy1⟩
    rcases eq_or_lt_of_le hy0 with rfl | hy_pos
    · simp [P, fejerInt_eq_sinc_sq]
    · rw [fejerInt_eq_sinc_sq, if_neg (ne_of_gt hy_pos)]
      set u := 75 * y
      have hu_pos : 0 < u := by positivity
      have hu_le3 : u ≤ 3 := by linarith
      have hu_sq_le9 : u ^ 2 ≤ 9 := by nlinarith
      have hP_nonneg : 0 ≤ P u := by
        have hcert : P u = (153 + (9 - u ^ 2) * ((u ^ 2 - 33 / 2) ^ 2 + 1083 / 4)) / 5040 := by
          simp only [P]; ring
        rw [hcert]
        have h1 : 0 ≤ 9 - u ^ 2 := by linarith
        have h2 : 0 ≤ (u ^ 2 - 33 / 2) ^ 2 + 1083 / 4 := by positivity
        positivity
      have hsin_ge := sin_ge_taylor7 (le_of_lt hu_pos)
      have hdiv_ge : P u ≤ Real.sin u / u := by
        rw [le_div_iff₀ hu_pos]
        linarith [show P u * u = u - u ^ 3 / 6 + u ^ 5 / 120 - u ^ 7 / 5040 by simp only [P]; ring]
      exact pow_le_pow_left₀ hP_nonneg hdiv_ge 2
  have h_int_mono : ∫ y in (0 : ℝ)..(1 / 25), P (75 * y) ^ 2 ≤
      ∫ y in (0 : ℝ)..(1 / 25), fejerInt y :=
    intervalIntegral.integral_mono_on (by norm_num)
      ((Continuous.continuousOn (by fun_prop)).intervalIntegrable)
      (fejerInt_cont.intervalIntegrable 0 (1 / 25)) hP_le
  -- Evaluate ∫ y in 0..(1/25), P (75 * y) ^ 2 via change of variables u = 75 * y
  have h_cov : ∫ y in (0 : ℝ)..(1 / 25), P (75 * y) ^ 2 =
      (1 / 75 : ℝ) * ∫ u in (0 : ℝ)..3, P u ^ 2 := by
    have := intervalIntegral.integral_comp_mul_left (fun u => P u ^ 2) (c := (75 : ℝ))
      (by norm_num) (a := 0) (b := 1 / 25)
    norm_num at this
    simpa [smul_eq_mul] using this
  let Q : ℝ → ℝ := fun u =>
    u - (1 / 9 : ℝ) * u ^ 3 + (2 / 225 : ℝ) * u ^ 5 - (1 / 2205 : ℝ) * u ^ 7 +
      (41 / 2721600 : ℝ) * u ^ 9 - (1 / 3326400 : ℝ) * u ^ 11 +
      (1 / 330220800 : ℝ) * u ^ 13
  have hQ_deriv : ∀ u ∈ Set.uIcc (0 : ℝ) 3, HasDerivAt Q (P u ^ 2) u := by
    intro u _
    have hd := (((((((hasDerivAt_id' u).sub (hd_monomial 2 (1 / 9) u)).add
      (hd_monomial 4 (2 / 225) u)).sub (hd_monomial 6 (1 / 2205) u)).add
      (hd_monomial 8 (41 / 2721600) u)).sub (hd_monomial 10 (1 / 3326400) u)).add
      (hd_monomial 12 (1 / 330220800) u))
    have hval : 1 - (1 / 9 : ℝ) * ((2 + 1 : ℕ) : ℝ) * u ^ 2 +
        (2 / 225 : ℝ) * ((4 + 1 : ℕ) : ℝ) * u ^ 4 -
        (1 / 2205 : ℝ) * ((6 + 1 : ℕ) : ℝ) * u ^ 6 +
        (41 / 2721600 : ℝ) * ((8 + 1 : ℕ) : ℝ) * u ^ 8 -
        (1 / 3326400 : ℝ) * ((10 + 1 : ℕ) : ℝ) * u ^ 10 +
        (1 / 330220800 : ℝ) * ((12 + 1 : ℕ) : ℝ) * u ^ 12 = P u ^ 2 := by
      simp only [P]; push_cast; ring
    rw [hval] at hd
    exact hd
  have h_int_P2 : ∫ u in (0 : ℝ)..3, P u ^ 2 = 63511641 / 44844800 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hQ_deriv
      ((Continuous.continuousOn (by fun_prop)).intervalIntegrable)]
    simp only [Q]
    norm_num
  rw [h_cov, h_int_P2] at h_int_mono
  linarith

private lemma Hkern_eq_fourier (x : ℝ) :
    Hkern x = ∫ t in Set.Ioc (0 : ℝ) 150,
      (4 / 150 : ℝ) * (1 - t / 150) * (Real.sin ((7 / 50 : ℝ) * t) / t) * Real.cos (t * x) := by
  unfold Hkern fejerInt
  rw [intervalIntegral.integral_of_le (by norm_num)]
  have hinner : ∀ s : ℝ, (2 / 150 : ℝ) * ∫ t in (0 : ℝ)..150,
      (1 - t / 150) * Real.cos (t * (x - s)) =
      ∫ t in Set.Ioc (0 : ℝ) 150, (2 / 150 : ℝ) * (1 - t / 150) * Real.cos (t * (x - s)) := by
    intro s
    rw [intervalIntegral.integral_of_le (by norm_num), ← integral_const_mul]
    congr 1; ext t; ring
  simp_rw [hinner]
  let g : ℝ × ℝ → ℝ := fun p => (2 / 150 : ℝ) * (1 - p.2 / 150) * Real.cos (p.2 * (x - p.1))
  have hg_int : IntegrableOn g (Set.Ioc (-7 / 50 : ℝ) (7 / 50) ×ˢ Set.Ioc (0 : ℝ) 150)
      (volume.prod volume) := by
    have hvol_lt : (volume.prod volume)
        (Set.Ioc (-7 / 50 : ℝ) (7 / 50) ×ˢ Set.Ioc (0 : ℝ) 150) < ⊤ := by
      rw [Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc]
      exact ENNReal.mul_lt_top (by simp) (by simp)
    have hconst : IntegrableOn (fun _ : ℝ × ℝ => (1 : ℝ))
        (Set.Ioc (-7 / 50 : ℝ) (7 / 50) ×ˢ Set.Ioc (0 : ℝ) 150) (volume.prod volume) :=
      integrableOn_const hvol_lt.ne
    refine hconst.mono' ?_ ?_
    · exact (Continuous.measurable (by fun_prop)).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_Ioc) ?_
      rintro ⟨s, t⟩ ⟨_, ⟨ht0, ht150⟩⟩
      simp only [g, Real.norm_eq_abs, abs_mul]
      have h1 : |(2 / 150 : ℝ)| = 2 / 150 := by norm_num
      have h2 : |1 - t / 150| = 1 - t / 150 := abs_of_nonneg (by linarith)
      have h3 : |Real.cos (t * (x - s))| ≤ 1 := Real.abs_cos_le_one _
      rw [h1, h2]
      have hprod_le : (2 / 150 : ℝ) * (1 - t / 150) * |Real.cos (t * (x - s))| ≤
          (2 / 150 : ℝ) * (1 - t / 150) * 1 :=
        mul_le_mul_of_nonneg_left h3 (by linarith)
      linarith
  change ∫ s in Set.Ioc (-7 / 50 : ℝ) (7 / 50), (∫ t in Set.Ioc (0 : ℝ) 150, g (s, t)) = _
  rw [← setIntegral_prod g hg_int]
  have hswap : ∫ p in Set.Ioc (-7 / 50 : ℝ) (7 / 50) ×ˢ Set.Ioc (0 : ℝ) 150, g p ∂(volume.prod volume) =
      ∫ t in Set.Ioc (0 : ℝ) 150, ∫ s in Set.Ioc (-7 / 50 : ℝ) (7 / 50), g (s, t) := by
    have hg_int_res : Integrable g
        ((volume.restrict (Set.Ioc (-7 / 50 : ℝ) (7 / 50))).prod
          (volume.restrict (Set.Ioc (0 : ℝ) 150))) := by
      rwa [Measure.prod_restrict]
    change ∫ p, g p ∂((volume.prod volume).restrict
      (Set.Ioc (-7 / 50 : ℝ) (7 / 50) ×ˢ Set.Ioc (0 : ℝ) 150)) = _
    rw [← Measure.prod_restrict]
    exact MeasureTheory.integral_prod_symm g hg_int_res
  rw [hswap]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  have ht_pos : 0 < t := ht.1
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  simp only [g]
  have h_s_int : ∫ s in Set.Ioc (-7 / 50 : ℝ) (7 / 50),
      (2 / 150 : ℝ) * (1 - t / 150) * Real.cos (t * (x - s)) =
      (2 / 150 : ℝ) * (1 - t / 150) * ∫ s in (-7 / 50 : ℝ)..(7 / 50), Real.cos (t * (x - s)) := by
    rw [intervalIntegral.integral_of_le (by norm_num), ← integral_const_mul]
  rw [h_s_int]
  have hd_s : ∀ s ∈ Set.uIcc (-7 / 50 : ℝ) (7 / 50),
      HasDerivAt (fun u : ℝ => -(1 / t) * Real.sin (t * x - t * u))
        (Real.cos (t * (x - s))) s := by
    intro s _
    have hlin : HasDerivAt (fun u : ℝ => t * x - t * u) (-t) s := by
      have h := (hasDerivAt_const s (t * x)).sub ((hasDerivAt_id' s).const_mul t)
      rw [show (0 : ℝ) - t * 1 = -t by ring] at h
      exact h
    have hsin := ((Real.hasDerivAt_sin (t * x - t * s)).comp s hlin).const_mul (-(1 / t))
    have hval : -(1 / t) * (Real.cos (t * x - t * s) * -t) = Real.cos (t * (x - s)) := by
      rw [show t * x - t * s = t * (x - s) by ring]
      field_simp [ht_ne]
    rw [hval] at hsin
    exact hsin
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd_s
    ((Continuous.continuousOn (by fun_prop)).intervalIntegrable)]
  have htrig : -(1 / t) * Real.sin (t * x - t * (7 / 50)) -
      -(1 / t) * Real.sin (t * x - t * (-7 / 50)) =
      2 * (Real.sin ((7 / 50 : ℝ) * t) / t) * Real.cos (t * x) := by
    have h1 : t * x - t * (7 / 50) = t * x - (7 / 50) * t := by ring
    have h2 : t * x - t * (-7 / 50) = t * x + (7 / 50) * t := by ring
    rw [h1, h2, Real.sin_sub, Real.sin_add]
    field_simp [ht_ne]
    ring
  rw [htrig]
  ring

private lemma finset_prod_rpow_sum {ι : Type*} (s : Finset ι) {B : ℝ} (hB : 0 < B) (g : ι → ℝ) :
    ∏ i ∈ s, B ^ (g i) = B ^ (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Real.rpow_add hB, ih]

private lemma coord_cos_prod_bound {ℓ : ℕ} (hℓ : 7 ≤ ℓ) {t w_i : ℝ}
    (ht0 : 0 < t) (htT : t ≤ 150) (hw_lt : |w_i| < 11 / 25) :
    let sig0 : ℝ := 5461 / 4096
    let sig1 : ℝ := 1365 / 4096
    let T1 : ℝ := Real.pi / (22 / 25)
    let B : ℝ := Real.exp (-sig0 * t ^ 2 / 2) +
      (Set.Ioi T1).indicator (fun s => Real.exp (-sig1 * s ^ 2 / 2)) t + (1 / 1024 : ℝ)
    ∏ j : Fin ℓ, |Real.cos (t * w_i * ((2 : ℝ)⁻¹) ^ (j : ℕ))| ≤ B ^ (w_i ^ 2) := by
  intro sig0 sig1 T1 B
  have h_ind_nonneg : 0 ≤ (Set.Ioi T1).indicator (fun s => Real.exp (-sig1 * s ^ 2 / 2)) t :=
    Set.indicator_nonneg (fun s _ => Real.exp_nonneg _) t
  have hB_pos : 0 < B := by
    have h1 : 0 < Real.exp (-sig0 * t ^ 2 / 2) := Real.exp_pos _
    dsimp only [B]
    linarith
  set u := |w_i|
  rcases eq_or_lt_of_le (abs_nonneg w_i) with hu0 | hu_pos
  · have hw0 : w_i = 0 := abs_eq_zero.mp hu0.symm
    subst hw0
    simp
  · -- u > 0
    have hu_sq : w_i ^ 2 = u ^ 2 := (sq_abs w_i).symm
    by_cases htheta1 : 2 * u * t ≤ Real.pi
    · -- Piece 1: 2 * u * t ≤ π => all j have |t * w_i * 2^{-j}| ≤ π/2
      have hfactor : ∀ j : Fin ℓ,
          |Real.cos (t * w_i * ((2 : ℝ)⁻¹) ^ (j : ℕ))| ≤
            Real.exp (-(u ^ 2 * t ^ 2 / 2) * ((4 : ℝ)⁻¹) ^ (j : ℕ)) := by
        intro j
        have hpow_le1 : ((2 : ℝ)⁻¹) ^ (j : ℕ) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        have harg_le : |t * w_i * ((2 : ℝ)⁻¹) ^ (j : ℕ)| ≤ Real.pi / 2 := by
          have hp_pos : (0 : ℝ) < ((2 : ℝ)⁻¹) ^ (j : ℕ) := by positivity
          rw [abs_mul, abs_mul, abs_of_pos ht0, show |w_i| = u from rfl, abs_of_pos hp_pos]
          calc t * u * ((2 : ℝ)⁻¹) ^ (j : ℕ) ≤ t * u * 1 :=
                mul_le_mul_of_nonneg_left hpow_le1 (by positivity)
            _ ≤ Real.pi / 2 := by linarith
        obtain ⟨hc_nn, hc_le⟩ := cos_le_exp_neg_sq_div_two harg_le
        rw [abs_of_nonneg hc_nn]
        refine hc_le.trans (le_of_eq ?_)
        congr 1
        have h4 : (((2 : ℝ)⁻¹) ^ (j : ℕ)) ^ 2 = ((4 : ℝ)⁻¹) ^ (j : ℕ) := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        calc -(t * w_i * ((2 : ℝ)⁻¹) ^ (j : ℕ)) ^ 2 / 2
            = -(t ^ 2 * w_i ^ 2 / 2) * (((2 : ℝ)⁻¹) ^ (j : ℕ)) ^ 2 := by ring
          _ = -(u ^ 2 * t ^ 2 / 2) * ((4 : ℝ)⁻¹) ^ (j : ℕ) := by rw [hu_sq, h4]; ring
      have hprod_le : ∏ j : Fin ℓ, |Real.cos (t * w_i * ((2 : ℝ)⁻¹) ^ (j : ℕ))| ≤
          Real.exp (-(u ^ 2 * t ^ 2 / 2) * ∑ j ∈ Finset.range ℓ, ((4 : ℝ)⁻¹) ^ j) := by
        calc ∏ j : Fin ℓ, |Real.cos (t * w_i * ((2 : ℝ)⁻¹) ^ (j : ℕ))|
            ≤ ∏ j : Fin ℓ, Real.exp (-(u ^ 2 * t ^ 2 / 2) * ((4 : ℝ)⁻¹) ^ (j : ℕ)) :=
              Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun j _ => hfactor j)
          _ = Real.exp (∑ j : Fin ℓ, -(u ^ 2 * t ^ 2 / 2) * ((4 : ℝ)⁻¹) ^ (j : ℕ)) :=
              (Real.exp_sum _ _).symm
          _ = Real.exp (-(u ^ 2 * t ^ 2 / 2) * ∑ j ∈ Finset.range ℓ, ((4 : ℝ)⁻¹) ^ j) := by
              rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range]
      have hsum_ge : sig0 ≤ ∑ j ∈ Finset.range ℓ, ((4 : ℝ)⁻¹) ^ j := by
        calc sig0 = ∑ j ∈ Finset.range 7, ((4 : ℝ)⁻¹) ^ j := by
              rw [geom_sum_quarter]; dsimp only [sig0]; norm_num
          _ ≤ ∑ j ∈ Finset.range ℓ, ((4 : ℝ)⁻¹) ^ j :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hℓ) (fun _ _ _ => by positivity)
      have hexp_le : Real.exp (-(u ^ 2 * t ^ 2 / 2) * ∑ j ∈ Finset.range ℓ, ((4 : ℝ)⁻¹) ^ j) ≤
          (Real.exp (-sig0 * t ^ 2 / 2)) ^ (w_i ^ 2) := by
        rw [← Real.exp_mul, hu_sq, Real.exp_le_exp]
        have hut_nn : 0 ≤ u ^ 2 * t ^ 2 / 2 := by positivity
        nlinarith
      have hrpow_le : (Real.exp (-sig0 * t ^ 2 / 2)) ^ (w_i ^ 2) ≤ B ^ (w_i ^ 2) :=
        Real.rpow_le_rpow (Real.exp_nonneg _) (by dsimp only [B]; linarith) (sq_nonneg w_i)
      exact (hprod_le.trans hexp_le).trans hrpow_le
    · push Not at htheta1
      by_cases htheta2 : 2 * u * t ≤ 2 * Real.pi
      · -- Piece 2: π < 2 * u * t ≤ 2 * π => t > T1 and j ≥ 1 have |arg| ≤ π/2
        have ht_gt_T1 : T1 < t := by
          dsimp only [T1]
          rw [div_lt_iff₀ (by norm_num)]
          nlinarith
        obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
        have hm_ge6 : 6 ≤ m := by omega
        rw [Fin.prod_univ_succ]
        have h0_le1 : |Real.cos (t * w_i * ((2 : ℝ)⁻¹) ^ (0 : ℕ))| ≤ 1 := Real.abs_cos_le_one _
        have hfactor1 : ∀ j : Fin m,
            |Real.cos (t * w_i * ((2 : ℝ)⁻¹) ^ (j.succ : ℕ))| ≤
              Real.exp (-(u ^ 2 * t ^ 2 / 2) * ((4 : ℝ)⁻¹) ^ ((j : ℕ) + 1)) := by
          intro j
          have hpow_le_half : ((2 : ℝ)⁻¹) ^ ((j : ℕ) + 1) ≤ 1 / 2 := by
            calc ((2 : ℝ)⁻¹) ^ ((j : ℕ) + 1) ≤ ((2 : ℝ)⁻¹) ^ 1 :=
                  pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
              _ = 1 / 2 := by norm_num
          have harg_le : |t * w_i * ((2 : ℝ)⁻¹) ^ (j.succ : ℕ)| ≤ Real.pi / 2 := by
            have hp_pos : (0 : ℝ) < ((2 : ℝ)⁻¹) ^ ((j : ℕ) + 1) := by positivity
            rw [Fin.val_succ, abs_mul, abs_mul, abs_of_pos ht0, show |w_i| = u from rfl,
              abs_of_pos hp_pos]
            calc t * u * ((2 : ℝ)⁻¹) ^ ((j : ℕ) + 1) ≤ t * u * (1 / 2) :=
                  mul_le_mul_of_nonneg_left hpow_le_half (by positivity)
              _ ≤ Real.pi / 2 := by linarith
          obtain ⟨hc_nn, hc_le⟩ := cos_le_exp_neg_sq_div_two harg_le
          rw [abs_of_nonneg hc_nn]
          refine hc_le.trans (le_of_eq ?_)
          congr 1
          rw [Fin.val_succ]
          have h4 : (((2 : ℝ)⁻¹) ^ ((j : ℕ) + 1)) ^ 2 = ((4 : ℝ)⁻¹) ^ ((j : ℕ) + 1) := by
            rw [← pow_mul, mul_comm, pow_mul]; norm_num
          calc -(t * w_i * ((2 : ℝ)⁻¹) ^ ((j : ℕ) + 1)) ^ 2 / 2
              = -(t ^ 2 * w_i ^ 2 / 2) * (((2 : ℝ)⁻¹) ^ ((j : ℕ) + 1)) ^ 2 := by ring
            _ = -(u ^ 2 * t ^ 2 / 2) * ((4 : ℝ)⁻¹) ^ ((j : ℕ) + 1) := by rw [hu_sq, h4]; ring
        have hprod1_le : |Real.cos (t * w_i * ((2 : ℝ)⁻¹) ^ (0 : ℕ))| *
            ∏ j : Fin m, |Real.cos (t * w_i * ((2 : ℝ)⁻¹) ^ (j.succ : ℕ))| ≤
            Real.exp (-(u ^ 2 * t ^ 2 / 2) * ∑ j ∈ Finset.range m, ((4 : ℝ)⁻¹) ^ (j + 1)) := by
          calc |Real.cos (t * w_i * ((2 : ℝ)⁻¹) ^ (0 : ℕ))| *
                  ∏ j : Fin m, |Real.cos (t * w_i * ((2 : ℝ)⁻¹) ^ (j.succ : ℕ))|
              ≤ 1 * ∏ j : Fin m, Real.exp (-(u ^ 2 * t ^ 2 / 2) * ((4 : ℝ)⁻¹) ^ ((j : ℕ) + 1)) :=
                mul_le_mul h0_le1
                  (Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun j _ => hfactor1 j))
                  (Finset.prod_nonneg fun _ _ => abs_nonneg _) zero_le_one
            _ = Real.exp (∑ j : Fin m, -(u ^ 2 * t ^ 2 / 2) * ((4 : ℝ)⁻¹) ^ ((j : ℕ) + 1)) := by
                rw [one_mul, Real.exp_sum]
            _ = Real.exp (-(u ^ 2 * t ^ 2 / 2) * ∑ j ∈ Finset.range m, ((4 : ℝ)⁻¹) ^ (j + 1)) := by
                rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun j => ((4 : ℝ)⁻¹) ^ (j + 1))]
        have hsum1_ge : sig1 ≤ ∑ j ∈ Finset.range m, ((4 : ℝ)⁻¹) ^ (j + 1) := by
          have hshift : ∀ r, ∑ j ∈ Finset.range r, ((4 : ℝ)⁻¹) ^ (j + 1) =
              (1 / 4 : ℝ) * ∑ j ∈ Finset.range r, ((4 : ℝ)⁻¹) ^ j := by
            intro r
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => by rw [pow_succ]; ring
          calc sig1 = ∑ j ∈ Finset.range 6, ((4 : ℝ)⁻¹) ^ (j + 1) := by
                rw [hshift, geom_sum_quarter]; dsimp only [sig1]; norm_num
            _ ≤ ∑ j ∈ Finset.range m, ((4 : ℝ)⁻¹) ^ (j + 1) :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm_ge6)
                  (fun _ _ _ => by positivity)
        have hexp1_le : Real.exp (-(u ^ 2 * t ^ 2 / 2) *
            ∑ j ∈ Finset.range m, ((4 : ℝ)⁻¹) ^ (j + 1)) ≤
            (Real.exp (-sig1 * t ^ 2 / 2)) ^ (w_i ^ 2) := by
          rw [← Real.exp_mul, hu_sq, Real.exp_le_exp]
          have hut_nn : 0 ≤ u ^ 2 * t ^ 2 / 2 := by positivity
          nlinarith
        have hind_eq : (Set.Ioi T1).indicator (fun s => Real.exp (-sig1 * s ^ 2 / 2)) t =
            Real.exp (-sig1 * t ^ 2 / 2) := Set.indicator_of_mem ht_gt_T1 _
        have hrpow_le : (Real.exp (-sig1 * t ^ 2 / 2)) ^ (w_i ^ 2) ≤ B ^ (w_i ^ 2) := by
          refine Real.rpow_le_rpow (Real.exp_nonneg _) ?_ (sq_nonneg w_i)
          dsimp only [B]
          rw [hind_eq]
          linarith [Real.exp_pos (-sig0 * t ^ 2 / 2)]
        exact (hprod1_le.trans hexp1_le).trans hrpow_le
      · -- Piece 3: 2 * π < 2 * u * t ≤ 132 < 2^{ℓ-1} * π => Viète + Jordan gives ≤ 1/4 ≤ (1/1024)^(u^2)
        push Not at htheta2
        let θ := 2 * u * t
        have hθ_gt_2pi : 2 * Real.pi < θ := htheta2
        have hθ_lt : θ < (2 : ℝ) ^ (ℓ - 1) * Real.pi := by
          have hθ_bound : θ < 132 := by
            dsimp only [θ]; nlinarith
          have hpow_ge64 : (64 : ℝ) ≤ (2 : ℝ) ^ (ℓ - 1) := by
            calc (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
              _ ≤ (2 : ℝ) ^ (ℓ - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
          have hpi_gt : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
          nlinarith
        have hdiv_pos : 0 < θ / (2 : ℝ) ^ ℓ := by
          have : 0 < θ := by linarith [Real.pi_pos]
          positivity
        have hdiv_le_half_pi : θ / (2 : ℝ) ^ ℓ ≤ Real.pi / 2 := by
          rw [div_le_iff₀ (by positivity)]
          have h2ℓ_split : (2 : ℝ) ^ ℓ = 2 * (2 : ℝ) ^ (ℓ - 1) := by
            conv_lhs => rw [show ℓ = (ℓ - 1) + 1 by omega, pow_succ]
            ring
          rw [h2ℓ_split]
          linarith
        have hjordan := Real.mul_le_sin (le_of_lt hdiv_pos) hdiv_le_half_pi
        have hsin_pos : 0 < Real.sin (θ / (2 : ℝ) ^ ℓ) := by
          have hpos_lhs : 0 < 2 / Real.pi * (θ / (2 : ℝ) ^ ℓ) :=
            mul_pos (div_pos (by norm_num) Real.pi_pos) hdiv_pos
          linarith
        have hviete := congrArg abs (viete_cos_prod ℓ θ)
        rw [abs_mul, abs_mul, Finset.abs_prod, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ ℓ),
          abs_of_pos hsin_pos] at hviete
        have hcos_eq : ∏ j : Fin ℓ, |Real.cos (t * w_i * ((2 : ℝ)⁻¹) ^ (j : ℕ))| =
            ∏ j : Fin ℓ, |Real.cos (θ / (2 : ℝ) ^ ((j : ℕ) + 1))| := by
          refine Finset.prod_congr rfl fun j _ => ?_
          have hp_pos : (0 : ℝ) < ((2 : ℝ)⁻¹) ^ (j : ℕ) := by positivity
          have harg_abs : |t * w_i * ((2 : ℝ)⁻¹) ^ (j : ℕ)| = θ / (2 : ℝ) ^ ((j : ℕ) + 1) := by
            rw [abs_mul, abs_mul, abs_of_pos ht0, show |w_i| = u from rfl, abs_of_pos hp_pos]
            dsimp only [θ]
            rw [pow_succ, inv_pow]
            field_simp
          rw [← Real.cos_abs (t * w_i * ((2 : ℝ)⁻¹) ^ (j : ℕ)), harg_abs]
        have hprod_le_quarter : ∏ j : Fin ℓ, |Real.cos (t * w_i * ((2 : ℝ)⁻¹) ^ (j : ℕ))| ≤ 1 / 4 := by
          rw [hcos_eq]
          have hden_ge : 2 / Real.pi * θ ≤ (2 : ℝ) ^ ℓ * Real.sin (θ / (2 : ℝ) ^ ℓ) := by
            have hmul := mul_le_mul_of_nonneg_left hjordan (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ ℓ)
            have hlhs : (2 : ℝ) ^ ℓ * (2 / Real.pi * (θ / (2 : ℝ) ^ ℓ)) = 2 / Real.pi * θ := by
              field_simp
            linarith
          have hden_gt4 : 4 < 2 / Real.pi * θ := by
            have hpi_pos := Real.pi_pos
            rw [show (2 / Real.pi * θ) = (2 * θ) / Real.pi by ring, lt_div_iff₀ hpi_pos]
            linarith
          have hsin_le1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
          nlinarith [Finset.prod_nonneg (s := Finset.univ)
            (fun (j : Fin ℓ) _ => abs_nonneg (Real.cos (θ / (2 : ℝ) ^ ((j : ℕ) + 1))))]
        have hquarter_le : (1 / 4 : ℝ) ≤ ((1 / 1024 : ℝ)) ^ (w_i ^ 2) := by
          have h1024 : (1 / 1024 : ℝ) = (1 / 4 : ℝ) ^ (5 : ℝ) := by norm_num
          rw [h1024, ← Real.rpow_mul (by norm_num)]
          have hexp_le1 : 5 * w_i ^ 2 ≤ 1 := by
            rw [hu_sq]
            nlinarith
          have h14 : (1 / 4 : ℝ) = (1 / 4 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          conv_lhs => rw [h14]
          exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hexp_le1
        have hrpow_le : ((1 / 1024 : ℝ)) ^ (w_i ^ 2) ≤ B ^ (w_i ^ 2) :=
          Real.rpow_le_rpow (by norm_num)
            (by dsimp only [B]; linarith [Real.exp_nonneg (-sig0 * t ^ 2 / 2)]) (sq_nonneg w_i)
        exact (hprod_le_quarter.trans hquarter_le).trans hrpow_le

private lemma abs_sum_cos_addrOf_le {n f : ℕ} (w : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    |∑ z : Qubits (n * (f + 2)), Real.cos (t * inner ℝ w (addrOf n (f + 2) f z))| ≤
      (2 : ℝ) ^ (n * (f + 2)) * ∏ i : Fin n, ∏ j : Fin (f + 2),
        |Real.cos (t * w.ofLp i * ((2 : ℝ)⁻¹) ^ (j : ℕ))| := by
  let μ := t * (-(1 / (2 * (2 : ℝ) ^ f)) * ∑ i : Fin n, w.ofLp i)
  let a : Fin (n * (f + 2)) → ℝ := fun r =>
    t * w.ofLp (finProdFinEquiv.symm r).1 * ((2 : ℝ)⁻¹) ^ ((finProdFinEquiv.symm r).2 : ℕ)
  have hrew : ∀ z : Qubits (n * (f + 2)),
      t * inner ℝ w (addrOf n (f + 2) f z) =
        μ + ∑ r : Fin (n * (f + 2)), a r * radBit (z r) := by
    intro z
    rw [inner_addrOf_eq, mul_add]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => by simp only [a]; ring
  simp_rw [hrew]
  rw [sum_cos_rademacher, abs_mul, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (n * (f + 2))), Finset.abs_prod]
  have hprod_eq : ∏ r : Fin (n * (f + 2)), |Real.cos (a r)| =
      ∏ i : Fin n, ∏ j : Fin (f + 2),
        |Real.cos (t * w.ofLp i * ((2 : ℝ)⁻¹) ^ (j : ℕ))| := by
    rw [← Equiv.prod_comp finProdFinEquiv, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    simp only [a, Equiv.symm_apply_apply]
  rw [hprod_eq]
  have hcosμ : |Real.cos μ| ≤ 1 := Real.abs_cos_le_one μ
  have hp_nn : 0 ≤ ∏ i : Fin n, ∏ j : Fin (f + 2),
      |Real.cos (t * w.ofLp i * ((2 : ℝ)⁻¹) ^ (j : ℕ))| :=
    Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => abs_nonneg _
  calc (2 : ℝ) ^ (n * (f + 2)) * |Real.cos μ| *
          ∏ i : Fin n, ∏ j : Fin (f + 2), |Real.cos (t * w.ofLp i * ((2 : ℝ)⁻¹) ^ (j : ℕ))|
      ≤ (2 : ℝ) ^ (n * (f + 2)) * 1 *
          ∏ i : Fin n, ∏ j : Fin (f + 2), |Real.cos (t * w.ofLp i * ((2 : ℝ)⁻¹) ^ (j : ℕ))| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcosμ (by positivity)) hp_nn
    _ = (2 : ℝ) ^ (n * (f + 2)) *
          ∏ i : Fin n, ∏ j : Fin (f + 2), |Real.cos (t * w.ofLp i * ((2 : ℝ)⁻¹) ^ (j : ℕ))| := by
        ring

private lemma small_ball_case2 {n : ℕ} (hn : 2 ≤ n) (w : EuclideanSpace ℝ (Fin n))
    (hw : ‖w‖ = 1) (hcase2 : ∀ i : Fin n, |w.ofLp i| < 11 / 25) :
    let k := ⌈Real.logb 2 n⌉₊
    let f := 2 + k
    let ℓ := 4 + k
    ((Finset.univ.filter (fun z : Qubits (n * ℓ) =>
        |inner ℝ w (addrOf n ℓ f z)| < 1 / 10)).card : ℝ) ≤
      (141 / 1000 : ℝ) * (2 : ℝ) ^ (n * ℓ) := by
  intro k f ℓ
  have hℓ_eq : ℓ = f + 2 := by omega
  have hsum_w_sq : ∑ i : Fin n, w.ofLp i ^ 2 = 1 := norm_sq_eq_sum w hw
  have hn_ge6 : 6 ≤ n := by
    by_contra hlt6
    have hn_le5 : (n : ℝ) ≤ 5 := by exact_mod_cast (by omega : n ≤ 5)
    have hsum_lt : ∑ i : Fin n, w.ofLp i ^ 2 ≤ ∑ _ : Fin n, (11 / 25 : ℝ) ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (le_of_lt (hcase2 i)) 2
    rw [hsum_w_sq, Finset.sum_const, nsmul_eq_mul] at hsum_lt
    norm_num at hsum_lt
    linarith
  obtain ⟨_, _, _, hk3⟩ := ceil_logb_props hn
  have hk_ge3 : 3 ≤ k := hk3 (by omega)
  have hℓ_ge7 : 7 ≤ ℓ := by omega
  let F := Finset.univ.filter (fun z : Qubits (n * ℓ) => |inner ℝ w (addrOf n ℓ f z)| < 1 / 10)
  have hH_nonneg : ∀ x : ℝ, 0 ≤ Hkern x := fun x =>
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => fejerInt_nonneg _)
  have hmarkov_H : (F.card : ℝ) * ((4 / 150 : ℝ) * (63511641 / 44844800 : ℝ)) ≤
      ∑ z : Qubits (n * ℓ), Hkern (inner ℝ w (addrOf n ℓ f z)) := by
    calc (F.card : ℝ) * ((4 / 150 : ℝ) * (63511641 / 44844800 : ℝ))
        = ∑ _ ∈ F, (4 / 150 : ℝ) * (63511641 / 44844800 : ℝ) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ z ∈ F, Hkern (inner ℝ w (addrOf n ℓ f z)) := by
            refine Finset.sum_le_sum fun z hz => ?_
            exact Hkern_lower_bound (le_of_lt (Finset.mem_filter.mp hz).2)
      _ ≤ ∑ z : Qubits (n * ℓ), Hkern (inner ℝ w (addrOf n ℓ f z)) :=
            Finset.sum_le_univ_sum_of_nonneg fun z => hH_nonneg _
  simp_rw [Hkern_eq_fourier] at hmarkov_H
  have hint_each : ∀ z : Qubits (n * ℓ), IntegrableOn (fun t : ℝ =>
      (4 / 150 : ℝ) * (1 - t / 150) * (Real.sin ((7 / 50 : ℝ) * t) / t) *
        Real.cos (t * inner ℝ w (addrOf n ℓ f z))) (Set.Ioc 0 150) volume := by
    intro z
    have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 150) volume :=
      integrableOn_const (by simp [Real.volume_Ioc])
    refine hconst.mono' ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      exact (((Continuous.measurable (by fun_prop)).mul
        ((Continuous.measurable (by fun_prop)).div measurable_id)).mul
        (Continuous.measurable (by fun_prop)))
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ⟨ht0, ht150⟩ => ?_
      simp only [Real.norm_eq_abs, abs_mul]
      have h1 : |(4 / 150 : ℝ)| = 4 / 150 := by norm_num
      have h2 : |1 - t / 150| = 1 - t / 150 := abs_of_nonneg (by linarith)
      have h3 : |Real.sin ((7 / 50 : ℝ) * t) / t| ≤ 7 / 50 := by
        rw [abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
        have := @Real.abs_sin_le_abs ((7 / 50 : ℝ) * t)
        rwa [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 50), abs_of_pos ht0] at this
      have h4 : |Real.cos (t * inner ℝ w (addrOf n ℓ f z))| ≤ 1 := Real.abs_cos_le_one _
      rw [h1, h2]
      have hp1 : (4 / 150 : ℝ) * (1 - t / 150) * |Real.sin ((7 / 50 : ℝ) * t) / t| ≤
          (4 / 150 : ℝ) * (1 - t / 150) * (7 / 50) :=
        mul_le_mul_of_nonneg_left h3 (by linarith)
      have hp2 : (4 / 150 : ℝ) * (1 - t / 150) * |Real.sin ((7 / 50 : ℝ) * t) / t| *
          |Real.cos (t * inner ℝ w (addrOf n ℓ f z))| ≤
          (4 / 150 : ℝ) * (1 - t / 150) * (7 / 50) * 1 :=
        mul_le_mul hp1 h4 (abs_nonneg _) (by linarith)
      linarith
  rw [← MeasureTheory.integral_finsetSum Finset.univ (fun z _ => hint_each z)] at hmarkov_H
  let sig0 : ℝ := 5461 / 4096
  let sig1 : ℝ := 1365 / 4096
  let T1 : ℝ := Real.pi / (22 / 25)
  let B : ℝ → ℝ := fun t => Real.exp (-sig0 * t ^ 2 / 2) +
    (Set.Ioi T1).indicator (fun s => Real.exp (-sig1 * s ^ 2 / 2)) t + (1 / 1024 : ℝ)
  have hB_int : IntegrableOn B (Set.Ioc 0 150) volume := by
    have h1 : IntegrableOn (fun t : ℝ => Real.exp (-sig0 * t ^ 2 / 2)) (Set.Ioc 0 150) volume :=
      ((Continuous.continuousOn (by fun_prop)).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    have h2 : IntegrableOn (fun t : ℝ =>
        (Set.Ioi T1).indicator (fun s => Real.exp (-sig1 * s ^ 2 / 2)) t) (Set.Ioc 0 150) volume :=
      (((Continuous.continuousOn (by fun_prop)).integrableOn_Icc).mono_set
        Set.Ioc_subset_Icc_self).indicator measurableSet_Ioi
    have h3 : IntegrableOn (fun _ : ℝ => (1 / 1024 : ℝ)) (Set.Ioc 0 150) volume :=
      integrableOn_const (by simp [Real.volume_Ioc])
    exact (h1.add h2).add h3
  have hpointwise : ∀ t ∈ Set.Ioc (0 : ℝ) 150,
      ∑ z : Qubits (n * ℓ),
        (4 / 150 : ℝ) * (1 - t / 150) * (Real.sin ((7 / 50 : ℝ) * t) / t) *
          Real.cos (t * inner ℝ w (addrOf n ℓ f z)) ≤
      ((4 / 150 : ℝ) * (7 / 50 : ℝ) * (2 : ℝ) ^ (n * ℓ)) * B t := by
    intro t ⟨ht0, ht150⟩
    rw [← Finset.mul_sum]
    have hcos_sum_le : |∑ z : Qubits (n * ℓ), Real.cos (t * inner ℝ w (addrOf n ℓ f z))| ≤
        (2 : ℝ) ^ (n * ℓ) * B t := by
      have hsum_cos : |∑ z : Qubits (n * ℓ), Real.cos (t * inner ℝ w (addrOf n ℓ f z))| ≤
          (2 : ℝ) ^ (n * ℓ) * ∏ i : Fin n, ∏ j : Fin ℓ,
            |Real.cos (t * w.ofLp i * ((2 : ℝ)⁻¹) ^ (j : ℕ))| := by
        have h := abs_sum_cos_addrOf_le (f := f) w t
        rwa [← hℓ_eq] at h
      have hB_pos : 0 < B t := by
        have h1 : 0 < Real.exp (-sig0 * t ^ 2 / 2) := Real.exp_pos _
        have h2 : 0 ≤ (Set.Ioi T1).indicator (fun s => Real.exp (-sig1 * s ^ 2 / 2)) t :=
          Set.indicator_nonneg (fun _ _ => Real.exp_nonneg _) t
        dsimp only [B]; linarith
      have hprod_B : ∏ i : Fin n, ∏ j : Fin ℓ,
          |Real.cos (t * w.ofLp i * ((2 : ℝ)⁻¹) ^ (j : ℕ))| ≤ B t := by
        calc ∏ i : Fin n, ∏ j : Fin ℓ, |Real.cos (t * w.ofLp i * ((2 : ℝ)⁻¹) ^ (j : ℕ))|
            ≤ ∏ i : Fin n, (B t) ^ (w.ofLp i ^ 2) :=
              Finset.prod_le_prod (fun _ _ => Finset.prod_nonneg fun _ _ => abs_nonneg _)
                (fun i _ => coord_cos_prod_bound hℓ_ge7 ht0 ht150 (hcase2 i))
          _ = (B t) ^ (∑ i : Fin n, w.ofLp i ^ 2) := finset_prod_rpow_sum Finset.univ hB_pos _
          _ = B t := by rw [hsum_w_sq, Real.rpow_one]
      calc |∑ z : Qubits (n * ℓ), Real.cos (t * inner ℝ w (addrOf n ℓ f z))|
          ≤ (2 : ℝ) ^ (n * ℓ) * ∏ i : Fin n, ∏ j : Fin ℓ,
              |Real.cos (t * w.ofLp i * ((2 : ℝ)⁻¹) ^ (j : ℕ))| := hsum_cos
        _ ≤ (2 : ℝ) ^ (n * ℓ) * B t := mul_le_mul_of_nonneg_left hprod_B (by positivity)
    have hcoeff_le : |(4 / 150 : ℝ) * (1 - t / 150) * (Real.sin ((7 / 50 : ℝ) * t) / t)| ≤
        (4 / 150 : ℝ) * (7 / 50 : ℝ) := by
      rw [abs_mul, abs_mul, show |(4 / 150 : ℝ)| = 4 / 150 by norm_num,
        abs_of_nonneg (by linarith : 0 ≤ 1 - t / 150)]
      have hsin_le : |Real.sin ((7 / 50 : ℝ) * t) / t| ≤ 7 / 50 := by
        rw [abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
        have := @Real.abs_sin_le_abs ((7 / 50 : ℝ) * t)
        rwa [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 50), abs_of_pos ht0] at this
      have hp1 : (4 / 150 : ℝ) * (1 - t / 150) * |Real.sin ((7 / 50 : ℝ) * t) / t| ≤
          (4 / 150 : ℝ) * (1 - t / 150) * (7 / 50) :=
        mul_le_mul_of_nonneg_left hsin_le (by linarith)
      linarith
    calc ((4 / 150 : ℝ) * (1 - t / 150) * (Real.sin ((7 / 50 : ℝ) * t) / t)) *
            ∑ z : Qubits (n * ℓ), Real.cos (t * inner ℝ w (addrOf n ℓ f z))
        ≤ |((4 / 150 : ℝ) * (1 - t / 150) * (Real.sin ((7 / 50 : ℝ) * t) / t)) *
            ∑ z : Qubits (n * ℓ), Real.cos (t * inner ℝ w (addrOf n ℓ f z))| := le_abs_self _
      _ = |(4 / 150 : ℝ) * (1 - t / 150) * (Real.sin ((7 / 50 : ℝ) * t) / t)| *
            |∑ z : Qubits (n * ℓ), Real.cos (t * inner ℝ w (addrOf n ℓ f z))| := abs_mul _ _
      _ ≤ ((4 / 150 : ℝ) * (7 / 50 : ℝ)) * ((2 : ℝ) ^ (n * ℓ) * B t) :=
            mul_le_mul hcoeff_le hcos_sum_le (abs_nonneg _) (by norm_num)
      _ = ((4 / 150 : ℝ) * (7 / 50 : ℝ) * (2 : ℝ) ^ (n * ℓ)) * B t := by ring
  have hint_sum : IntegrableOn (fun t : ℝ => ∑ z : Qubits (n * ℓ),
      (4 / 150 : ℝ) * (1 - t / 150) * (Real.sin ((7 / 50 : ℝ) * t) / t) *
        Real.cos (t * inner ℝ w (addrOf n ℓ f z))) (Set.Ioc 0 150) volume :=
    integrable_finsetSum Finset.univ (fun z _ => hint_each z)
  have h_int_le := setIntegral_mono_on hint_sum (hB_int.const_mul _) measurableSet_Ioc hpointwise
  rw [integral_const_mul] at h_int_le
  -- Bound the three integrals in ∫ t in Ioc 0 150, B t
  have hB1_int : IntegrableOn (fun t : ℝ => Real.exp (-sig0 * t ^ 2 / 2)) (Set.Ioc 0 150) volume :=
    ((Continuous.continuousOn (by fun_prop)).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hB2_int : IntegrableOn (fun t : ℝ =>
      (Set.Ioi T1).indicator (fun s => Real.exp (-sig1 * s ^ 2 / 2)) t) (Set.Ioc 0 150) volume :=
    (((Continuous.continuousOn (by fun_prop)).integrableOn_Icc).mono_set
      Set.Ioc_subset_Icc_self).indicator measurableSet_Ioi
  have hB3_int : IntegrableOn (fun _ : ℝ => (1 / 1024 : ℝ)) (Set.Ioc 0 150) volume :=
    integrableOn_const (by simp [Real.volume_Ioc])
  have hB_split : ∫ t in Set.Ioc (0 : ℝ) 150, B t =
      (∫ t in Set.Ioc (0 : ℝ) 150, Real.exp (-sig0 * t ^ 2 / 2)) +
      (∫ t in Set.Ioc (0 : ℝ) 150,
        (Set.Ioi T1).indicator (fun s => Real.exp (-sig1 * s ^ 2 / 2)) t) +
      (∫ _ : ℝ in Set.Ioc (0 : ℝ) 150, (1 / 1024 : ℝ)) := by
    have h12 := MeasureTheory.integral_add hB1_int hB2_int
    have h123 := MeasureTheory.integral_add (hB1_int.add hB2_int) hB3_int
    exact h123.trans (congrArg (· + ∫ _ : ℝ in Set.Ioc (0 : ℝ) 150, (1 / 1024 : ℝ)) h12)
  -- Bound 1: ∫ t in Ioc 0 150, exp (-sig0 * t^2 / 2) ≤ 109 / 100
  have hI1_le : ∫ t in Set.Ioc (0 : ℝ) 150, Real.exp (-sig0 * t ^ 2 / 2) ≤ 109 / 100 := by
    let b0 : ℝ := sig0 / 2
    have hb0_pos : 0 < b0 := by dsimp only [b0, sig0]; norm_num
    have hgauss_int : Integrable (fun x : ℝ => Real.exp (-b0 * x ^ 2)) volume :=
      integrable_exp_neg_mul_sq hb0_pos
    have hrew : ∀ t : ℝ, Real.exp (-sig0 * t ^ 2 / 2) = Real.exp (-b0 * t ^ 2) := fun t => by
      congr 1; dsimp only [b0]; ring
    simp_rw [hrew]
    have hsub_ioi : ∫ t in Set.Ioc (0 : ℝ) 150, Real.exp (-b0 * t ^ 2) ≤
        ∫ t in Set.Ioi (0 : ℝ), Real.exp (-b0 * t ^ 2) :=
      setIntegral_mono_set hgauss_int.integrableOn
        (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)
        (Filter.Eventually.of_forall fun t ht => ht.1)
    have hhalf : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-b0 * t ^ 2) =
        (1 / 2 : ℝ) * ∫ t : ℝ, Real.exp (-b0 * t ^ 2) := by
      have hsplit := integral_add_compl (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi hgauss_int
      have hcompl : (Set.Ioi (0 : ℝ))ᶜ = Set.Iic 0 := Set.compl_Ioi
      rw [hcompl] at hsplit
      have heven : ∫ t in Set.Iic (0 : ℝ), Real.exp (-b0 * t ^ 2) =
          ∫ t in Set.Ioi (0 : ℝ), Real.exp (-b0 * t ^ 2) := by
        have hcomp := integral_comp_neg_Ioi (0 : ℝ) (fun t : ℝ => Real.exp (-b0 * t ^ 2))
        simp only [neg_zero, even_two.neg_pow] at hcomp
        exact hcomp.symm
      rw [heven] at hsplit
      rw [← hsplit]
      ring
    rw [integral_gaussian b0] at hhalf
    have hsqrt_le : (1 / 2 : ℝ) * Real.sqrt (Real.pi / b0) ≤ 109 / 100 := by
      have hpi_lt : Real.pi < 3.15 := Real.pi_lt_d2
      have hsq : Real.pi / b0 ≤ (218 / 100 : ℝ) ^ 2 := by
        dsimp only [b0, sig0]
        linarith
      have h1 := Real.sqrt_le_iff.mpr ⟨by norm_num, hsq⟩
      linarith
    exact hsub_ioi.trans (hhalf.trans_le hsqrt_le)
  -- Bound 2: ∫ t in Ioc 0 150, (Ioi T1).indicator (exp (-sig1 * t^2 / 2)) t ≤ 1 / 8
  have hI2_le : ∫ t in Set.Ioc (0 : ℝ) 150,
      (Set.Ioi T1).indicator (fun s => Real.exp (-sig1 * s ^ 2 / 2)) t ≤ 1 / 8 := by
    have hT1_gt : (157 / 44 : ℝ) < T1 := by
      dsimp only [T1]
      have hpi_gt : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
      linarith
    have hT1_lt150 : T1 < 150 := by
      dsimp only [T1]
      have hpi_lt : Real.pi < 3.15 := Real.pi_lt_d2
      linarith
    have hT1_pos : 0 < T1 := by linarith
    rw [setIntegral_indicator measurableSet_Ioi]
    have hinter : Set.Ioc (0 : ℝ) 150 ∩ Set.Ioi T1 = Set.Ioc T1 150 := by
      ext t; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]
      exact ⟨fun ⟨⟨_, h2⟩, h3⟩ => ⟨h3, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨by linarith, h2⟩, h1⟩⟩
    rw [hinter, ← intervalIntegral.integral_of_le (le_of_lt hT1_lt150)]
    have hdom : ∀ t ∈ Set.Icc T1 150,
        Real.exp (-sig1 * t ^ 2 / 2) ≤
          (1 / (sig1 * T1)) * (sig1 * t * Real.exp (-sig1 * t ^ 2 / 2)) := by
      intro t ⟨ht1, _⟩
      have hsig1_pos : 0 < sig1 := by dsimp only [sig1]; norm_num
      have hratio : 1 ≤ (1 / (sig1 * T1)) * (sig1 * t) := by
        rw [one_div, le_inv_mul_iff₀ (by positivity), mul_one]
        exact mul_le_mul_of_nonneg_left ht1 (le_of_lt hsig1_pos)
      calc Real.exp (-sig1 * t ^ 2 / 2) = 1 * Real.exp (-sig1 * t ^ 2 / 2) := (one_mul _).symm
        _ ≤ ((1 / (sig1 * T1)) * (sig1 * t)) * Real.exp (-sig1 * t ^ 2 / 2) :=
              mul_le_mul_of_nonneg_right hratio (Real.exp_nonneg _)
        _ = (1 / (sig1 * T1)) * (sig1 * t * Real.exp (-sig1 * t ^ 2 / 2)) := by ring
    have hint_mono := intervalIntegral.integral_mono_on (le_of_lt hT1_lt150)
      ((Continuous.continuousOn (by fun_prop)).intervalIntegrable (μ := volume))
      ((Continuous.continuousOn (by fun_prop)).intervalIntegrable (μ := volume)) hdom
    have hd_exp : ∀ t ∈ Set.uIcc T1 150,
        HasDerivAt (fun x : ℝ => -(1 / (sig1 * T1)) * Real.exp (-sig1 * x ^ 2 / 2))
          ((1 / (sig1 * T1)) * (sig1 * t * Real.exp (-sig1 * t ^ 2 / 2))) t := by
      intro t _
      have hsq : HasDerivAt (fun x : ℝ => (-sig1 / 2) * x ^ 2)
          ((-sig1 / 2) * (↑(2 : ℕ) * t ^ (2 - 1))) t :=
        (hasDerivAt_pow 2 t).const_mul (-sig1 / 2)
      have hsq' : HasDerivAt (fun x : ℝ => -sig1 * x ^ 2 / 2) (-sig1 * t) t := by
        rw [show (-sig1 / 2) * (↑(2 : ℕ) * t ^ (2 - 1)) = -sig1 * t by norm_num; ring] at hsq
        exact hsq.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by ring)
      have hexp := (hsq'.exp).const_mul (-(1 / (sig1 * T1)))
      rw [show -(1 / (sig1 * T1)) * (Real.exp (-sig1 * t ^ 2 / 2) * (-sig1 * t)) =
          (1 / (sig1 * T1)) * (sig1 * t * Real.exp (-sig1 * t ^ 2 / 2)) by ring] at hexp
      exact hexp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd_exp
      ((Continuous.continuousOn (by fun_prop)).intervalIntegrable)] at hint_mono
    have hsig1_pos : 0 < sig1 := by dsimp only [sig1]; norm_num
    have hdrop150 : -(1 / (sig1 * T1)) * Real.exp (-sig1 * 150 ^ 2 / 2) -
        -(1 / (sig1 * T1)) * Real.exp (-sig1 * T1 ^ 2 / 2) ≤
        Real.exp (-sig1 * T1 ^ 2 / 2) / (sig1 * T1) := by
      have hpos : 0 ≤ (1 / (sig1 * T1)) * Real.exp (-sig1 * 150 ^ 2 / 2) := by positivity
      linarith [show (1 / (sig1 * T1)) * Real.exp (-sig1 * T1 ^ 2 / 2) =
        Real.exp (-sig1 * T1 ^ 2 / 2) / (sig1 * T1) by ring]
    -- Now use sig1 * T1^2 / 2 ≥ 2 => exp(-sig1 * T1^2 / 2) ≤ exp(-2) ≤ 1/7
    have hx_ge2 : 2 ≤ sig1 * T1 ^ 2 / 2 := by
      dsimp only [sig1]
      nlinarith
    have hexp_le_inv7 : Real.exp (-sig1 * T1 ^ 2 / 2) ≤ 1 / 7 := by
      have hle_neg2 : Real.exp (-sig1 * T1 ^ 2 / 2) ≤ Real.exp (-2) :=
        Real.exp_le_exp.mpr (by linarith)
      have hexp2_ge7 : (7 : ℝ) ≤ Real.exp 2 := by
        have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 5
        norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
        linarith
      have hneg2_le : Real.exp (-2) ≤ 1 / 7 := by
        rw [Real.exp_neg, inv_eq_one_div]
        exact one_div_le_one_div_of_le (by norm_num) hexp2_ge7
      exact hle_neg2.trans hneg2_le
    have hden_gt : (8 / 7 : ℝ) ≤ sig1 * T1 := by
      dsimp only [sig1]
      nlinarith
    have hfrac_le : Real.exp (-sig1 * T1 ^ 2 / 2) / (sig1 * T1) ≤ 1 / 8 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  -- Bound 3: ∫ _ in Ioc 0 150, (1 / 1024 : ℝ) = 150 / 1024
  have hI3_eq : ∫ _ in Set.Ioc (0 : ℝ) 150, (1 / 1024 : ℝ) = 150 / 1024 := by
    rw [setIntegral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  -- Combine all three into F.card ≤ (141 / 1000) * 2^(n * ℓ)
  have hB_tot : ∫ t in Set.Ioc (0 : ℝ) 150, B t ≤ 109 / 100 + 1 / 8 + 150 / 1024 := by
    rw [hB_split, hI3_eq]
    linarith
  have hchain : (F.card : ℝ) * ((4 / 150 : ℝ) * (63511641 / 44844800 : ℝ)) ≤
      ((4 / 150 : ℝ) * (7 / 50 : ℝ) * (2 : ℝ) ^ (n * ℓ)) *
        (109 / 100 + 1 / 8 + 150 / 1024) := by
    have hnonneg_pref : 0 ≤ (4 / 150 : ℝ) * (7 / 50 : ℝ) * (2 : ℝ) ^ (n * ℓ) := by positivity
    exact (hmarkov_H.trans h_int_le).trans (mul_le_mul_of_nonneg_left hB_tot hnonneg_pref)
  have hnum_final : ((4 / 150 : ℝ) * (7 / 50 : ℝ)) * (109 / 100 + 1 / 8 + 150 / 1024) ≤
      (141 / 1000 : ℝ) * ((4 / 150 : ℝ) * (63511641 / 44844800 : ℝ)) := by norm_num
  have h2pow_nn : (0 : ℝ) ≤ (2 : ℝ) ^ (n * ℓ) := by positivity
  nlinarith

end UniformDyadicWindowProof

open QAlgorithms QuantumLTF.Membership in
theorem solution (n : ℕ) (hn : 2 ≤ n) :
    ∃ ℓ f : ℕ, f ≤ ℓ ∧ ℓ ≤ 4 + ⌈Real.logb 2 n⌉₊ ∧
      ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
        ((PMF.uniformOfFintype (Qubits (n * ℓ))).toOuterMeasure
          {z | 1 / 10 ≤ |inner ℝ w (addrOf n ℓ f z)| ∧
            |inner ℝ w (addrOf n ℓ f z)| ≤ 3}).toReal ≥ 4 / 5 := by
  let k := ⌈Real.logb 2 n⌉₊
  let f := 2 + k
  let ℓ := 4 + k
  refine ⟨ℓ, f, by omega, le_rfl, ?_⟩
  intro w hw
  classical
  let S : Set (Qubits (n * ℓ)) :=
    {z | 1 / 10 ≤ |inner ℝ w (addrOf n ℓ f z)| ∧ |inner ℝ w (addrOf n ℓ f z)| ≤ 3}
  rw [PMF.toOuterMeasure_apply_fintype]
  have hcard_univ : Fintype.card (Qubits (n * ℓ)) = 2 ^ (n * ℓ) := by simp
  have hpmf_eval : (∑ x : Qubits (n * ℓ), S.indicator (⇑(PMF.uniformOfFintype (Qubits (n * ℓ)))) x).toReal =
      ((Finset.univ.filter (fun z : Qubits (n * ℓ) => z ∈ S)).card : ℝ) / (2 : ℝ) ^ (n * ℓ) := by
    have heq : ∀ x : Qubits (n * ℓ),
        S.indicator (⇑(PMF.uniformOfFintype (Qubits (n * ℓ)))) x =
          if x ∈ S then ((2 ^ (n * ℓ) : ℕ) : ENNReal)⁻¹ else 0 := by
      intro x
      by_cases hx : x ∈ S <;> simp [hx, PMF.uniformOfFintype_apply, hcard_univ]
    simp_rw [heq]
    rw [← Finset.sum_filter, Finset.sum_const, ENNReal.toReal_nsmul, ENNReal.toReal_inv,
      show (((2 ^ (n * ℓ) : ℕ) : ENNReal)).toReal = (2 : ℝ) ^ (n * ℓ) by norm_cast,
      nsmul_eq_mul]
    have hcard_eq : (Finset.univ.filter (fun x : Qubits (n * ℓ) => x ∈ S)).card =
        (Finset.univ.filter (fun z : Qubits (n * ℓ) => z ∈ S)).card := by congr
    rw [hcard_eq]
    ring
  change (∑ x : Qubits (n * ℓ), S.indicator (⇑(PMF.uniformOfFintype (Qubits (n * ℓ)))) x).toReal ≥ 4 / 5
  rw [hpmf_eval]
  let Flow := Finset.univ.filter (fun z : Qubits (n * ℓ) => |inner ℝ w (addrOf n ℓ f z)| < 1 / 10)
  let Fhigh := Finset.univ.filter (fun z : Qubits (n * ℓ) => 3 < |inner ℝ w (addrOf n ℓ f z)|)
  let Fgood := Finset.univ.filter (fun z : Qubits (n * ℓ) => z ∈ S)
  have hcover : (Finset.univ : Finset (Qubits (n * ℓ))) ⊆ Fgood ∪ (Flow ∪ Fhigh) := by
    intro z _
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Fgood, Flow, Fhigh]
    change (1 / 10 ≤ |inner ℝ w (addrOf n ℓ f z)| ∧ |inner ℝ w (addrOf n ℓ f z)| ≤ 3) ∨
      (|inner ℝ w (addrOf n ℓ f z)| < 1 / 10 ∨ 3 < |inner ℝ w (addrOf n ℓ f z)|)
    by_cases h1 : 1 / 10 ≤ |inner ℝ w (addrOf n ℓ f z)|
    · by_cases h2 : |inner ℝ w (addrOf n ℓ f z)| ≤ 3
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (Or.inr (lt_of_not_ge h2))
    · exact Or.inr (Or.inl (lt_of_not_ge h1))
  have hcard_union : 2 ^ (n * ℓ) ≤ Fgood.card + Flow.card + Fhigh.card := by
    have h1 : (Finset.univ : Finset (Qubits (n * ℓ))).card ≤ (Fgood ∪ (Flow ∪ Fhigh)).card :=
      Finset.card_le_card hcover
    have h2 : (Fgood ∪ (Flow ∪ Fhigh)).card ≤ Fgood.card + (Flow ∪ Fhigh).card :=
      Finset.card_union_le _ _
    have h3 : (Flow ∪ Fhigh).card ≤ Flow.card + Fhigh.card := Finset.card_union_le _ _
    have huniv : (Finset.univ : Finset (Qubits (n * ℓ))).card = 2 ^ (n * ℓ) := by simp
    omega
  have hcast_union : (2 : ℝ) ^ (n * ℓ) ≤ (Fgood.card : ℝ) + (Flow.card : ℝ) + (Fhigh.card : ℝ) := by
    have : ((2 ^ (n * ℓ) : ℕ) : ℝ) ≤ ((Fgood.card + Flow.card + Fhigh.card : ℕ) : ℝ) := by
      exact_mod_cast hcard_union
    simpa using this
  have h_high : (Fhigh.card : ℝ) ≤ (59 / 1000 : ℝ) * (2 : ℝ) ^ (n * ℓ) :=
    upper_tail_card_le hn w hw
  have h_low : (Flow.card : ℝ) ≤ (141 / 1000 : ℝ) * (2 : ℝ) ^ (n * ℓ) := by
    by_cases hcase : ∃ i : Fin n, (11 / 25 : ℝ) ≤ |w.ofLp i|
    · exact small_ball_case1 hn w hw hcase
    · push Not at hcase
      exact small_ball_case2 hn w hw hcase
  have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ (n * ℓ) := by positivity
  rw [ge_iff_le, le_div_iff₀ h2pow_pos]
  linarith
