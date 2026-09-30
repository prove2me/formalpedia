-- Prove2me | solution 1 for RobustMDP.Discounted.robust_bellman_recursion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-29T23:46:47.641567+00:00
-- url     : https://prove2.me/submissions/7905be32-be21-47cd-9ac3-8fb34bf72675

import Mathlib
import Definitions.Def_RobustMDP_Discounted_Model
import Definitions.Def_RobustMDP_Shared_supportFunction
import Definitions.Def_RobustMDP_Discounted_discountedCost
import Definitions.Def_RobustMDP_Discounted_bellmanOps

set_option autoImplicit false

open RobustMDP RobustMDP.Discounted

/-- dot product with a probability vector is bounded by the sup norm -/
theorem rbr_dot {n : ℕ} (p v : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n)) :
    |∑ j, p j * v j| ≤ ‖v‖ := by
  have hle : ∀ j, |v j| ≤ ‖v‖ := fun j => by
    have := norm_le_pi_norm v j
    rwa [Real.norm_eq_abs] at this
  rw [abs_le]
  have h1 : ∑ j, p j * v j ≤ ∑ j, p j * ‖v‖ :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (abs_le.1 (hle j)).2 (hp.1 j)
  have h2 : ∑ j, p j * (-‖v‖) ≤ ∑ j, p j * v j :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (abs_le.1 (hle j)).1 (hp.1 j)
  have h3 : ∑ j, p j * ‖v‖ = ‖v‖ := by rw [← Finset.sum_mul, hp.2, one_mul]
  have h4 : ∑ j, p j * (-‖v‖) = -‖v‖ := by
    rw [← Finset.sum_mul, hp.2, one_mul]
  constructor <;> linarith

theorem rbr_dot_mono {n : ℕ} (p v w : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n))
    (h : ∀ j, v j ≤ w j) : ∑ j, p j * v j ≤ ∑ j, p j * w j :=
  Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (hp.1 j)

theorem rbr_dot_lip {n : ℕ} (p v w : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n)) :
    ∑ j, p j * v j ≤ ∑ j, p j * w j + ‖v - w‖ := by
  have h1 : ∑ j, p j * v j = ∑ j, p j * w j + ∑ j, p j * (v - w) j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp only [Pi.sub_apply]; ring
  have h2 := (abs_le.1 (rbr_dot p (v - w) hp)).2
  linarith

theorem rbr_dot_shift {n : ℕ} (p v : Fin n → ℝ) (δ : ℝ) (hp : p ∈ stdSimplex ℝ (Fin n)) :
    ∑ j, p j * (v j - δ) = ∑ j, p j * v j - δ := by
  have : ∑ j, p j * (v j - δ) = ∑ j, p j * v j - ∑ j, p j * δ := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, ← Finset.sum_mul, hp.2, one_mul]

theorem rbr_sf_bdd {n : ℕ} (S : Set (Fin n → ℝ)) (hS : S ⊆ stdSimplex ℝ (Fin n))
    (v : Fin n → ℝ) : BddAbove ((fun p : Fin n → ℝ => ∑ j, p j * v j) '' S) :=
  ⟨‖v‖, by
    rintro _ ⟨p, hp, rfl⟩
    exact (abs_le.1 (rbr_dot p v (hS hp))).2⟩

theorem rbr_le_sf {n : ℕ} (S : Set (Fin n → ℝ)) (hS : S ⊆ stdSimplex ℝ (Fin n))
    (v : Fin n → ℝ) (p : Fin n → ℝ) (hp : p ∈ S) :
    ∑ j, p j * v j ≤ Shared.supportFunction S v :=
  le_csSup (rbr_sf_bdd S hS v) ⟨p, hp, rfl⟩

theorem rbr_sf_le {n : ℕ} (S : Set (Fin n → ℝ)) (hne : S.Nonempty)
    (v : Fin n → ℝ) (b : ℝ) (h : ∀ p ∈ S, ∑ j, p j * v j ≤ b) :
    Shared.supportFunction S v ≤ b :=
  csSup_le (hne.image _) (by
    rintro _ ⟨p, hp, rfl⟩
    exact h p hp)

theorem rbr_sf_approx {n : ℕ} (S : Set (Fin n → ℝ)) (hne : S.Nonempty)
    (v : Fin n → ℝ) (η : ℝ) (hη : 0 < η) :
    ∃ p ∈ S, Shared.supportFunction S v - η < ∑ j, p j * v j := by
  obtain ⟨_, ⟨p, hp, rfl⟩, h⟩ := exists_lt_of_lt_csSup (hne.image _) (sub_lt_self
    (Shared.supportFunction S v) hη)
  exact ⟨p, hp, h⟩

theorem rbr_sf_mono {n : ℕ} (S : Set (Fin n → ℝ)) (hS : S ⊆ stdSimplex ℝ (Fin n))
    (hne : S.Nonempty) (v w : Fin n → ℝ) (h : ∀ j, v j ≤ w j) :
    Shared.supportFunction S v ≤ Shared.supportFunction S w :=
  rbr_sf_le S hne v _ fun p hp =>
    (rbr_dot_mono p v w (hS hp) h).trans (rbr_le_sf S hS w p hp)

theorem rbr_sf_lip {n : ℕ} (S : Set (Fin n → ℝ)) (hS : S ⊆ stdSimplex ℝ (Fin n))
    (hne : S.Nonempty) (v w : Fin n → ℝ) :
    Shared.supportFunction S v ≤ Shared.supportFunction S w + ‖v - w‖ :=
  rbr_sf_le S hne v _ fun p hp => by
    have := rbr_dot_lip p v w (hS hp)
    have := rbr_le_sf S hS w p hp
    linarith

theorem rbr_policy_lip {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A)
    (v w : Fin n → ℝ) (i : Fin n) :
    M.policyOp π v i ≤ M.policyOp π w i + M.discount * ‖v - w‖ := by
  have := rbr_sf_lip (M.rows (π i) i) (M.rows_subset_simplex _ _) (M.rows_nonempty _ _) v w
  have h2 := mul_le_mul_of_nonneg_left this M.discount_nonneg
  simp only [Model.policyOp]
  linarith

theorem rbr_policy_mono {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A)
    (v w : Fin n → ℝ) (h : ∀ j, v j ≤ w j) (i : Fin n) :
    M.policyOp π v i ≤ M.policyOp π w i := by
  have := rbr_sf_mono (M.rows (π i) i) (M.rows_subset_simplex _ _) (M.rows_nonempty _ _) v w h
  have h2 := mul_le_mul_of_nonneg_left this M.discount_nonneg
  simp only [Model.policyOp]
  linarith

theorem rbr_bellman_lip {n : ℕ} {A : Type} [Fintype A] [Nonempty A] (M : Model n A)
    (v w : Fin n → ℝ) (i : Fin n) :
    M.bellmanOp v i ≤ M.bellmanOp w i + M.discount * ‖v - w‖ := by
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := A))
    (fun a => M.cost i a + M.discount * Shared.supportFunction (M.rows a i) w)
  have h1 : M.bellmanOp v i ≤ M.cost i a + M.discount * Shared.supportFunction (M.rows a i) v :=
    Finset.inf'_le _ (Finset.mem_univ a)
  have h2 : M.bellmanOp w i = M.cost i a + M.discount * Shared.supportFunction (M.rows a i) w :=
    ha
  have := rbr_sf_lip (M.rows a i) (M.rows_subset_simplex _ _) (M.rows_nonempty _ _) v w
  have h3 := mul_le_mul_of_nonneg_left this M.discount_nonneg
  linarith

theorem rbr_bellman_mono {n : ℕ} {A : Type} [Fintype A] [Nonempty A] (M : Model n A)
    (v w : Fin n → ℝ) (h : ∀ j, v j ≤ w j) (i : Fin n) :
    M.bellmanOp v i ≤ M.bellmanOp w i := by
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := A))
    (fun a => M.cost i a + M.discount * Shared.supportFunction (M.rows a i) w)
  have h1 : M.bellmanOp v i ≤ M.cost i a + M.discount * Shared.supportFunction (M.rows a i) v :=
    Finset.inf'_le _ (Finset.mem_univ a)
  have h2 : M.bellmanOp w i = M.cost i a + M.discount * Shared.supportFunction (M.rows a i) w :=
    ha
  have := rbr_sf_mono (M.rows a i) (M.rows_subset_simplex _ _) (M.rows_nonempty _ _) v w h
  have h3 := mul_le_mul_of_nonneg_left this M.discount_nonneg
  linarith

theorem rbr_contract {n : ℕ} (ν : ℝ) (hν0 : 0 ≤ ν) (hν1 : ν < 1)
    (K : (Fin n → ℝ) → (Fin n → ℝ))
    (h : ∀ v w i, K v i ≤ K w i + ν * ‖v - w‖) :
    ContractingWith (Real.toNNReal ν) K := by
  refine ⟨Real.toNNReal_lt_one.2 hν1, LipschitzWith.of_dist_le_mul fun v w => ?_⟩
  rw [Real.coe_toNNReal _ hν0, dist_eq_norm, dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hν0 (norm_nonneg _))).2 fun i => ?_
  rw [Real.norm_eq_abs, abs_le, Pi.sub_apply]
  have h1 := h v w i
  have h2 := h w v i
  rw [norm_sub_rev w v] at h2
  constructor <;> linarith

theorem rbr_fix_ge {n : ℕ} {ν : NNReal} (K : (Fin n → ℝ) → (Fin n → ℝ))
    (hc : ContractingWith ν K)
    (hmono : ∀ v w : Fin n → ℝ, (∀ i, v i ≤ w i) → ∀ i, K v i ≤ K w i)
    (f : Fin n → ℝ) (h : ∀ i, f i ≤ K f i) (i : Fin n) :
    f i ≤ ContractingWith.fixedPoint K hc i := by
  have hit : ∀ N : ℕ, ∀ i, f i ≤ (K^[N] f) i := by
    intro N
    induction N with
    | zero => intro i; exact le_refl _
    | succ N ih =>
      intro i
      rw [Function.iterate_succ_apply']
      exact (h i).trans (hmono _ _ ih i)
  have ht := tendsto_pi_nhds.1 (hc.tendsto_iterate_fixedPoint f) i
  exact ge_of_tendsto' ht fun N => hit N i

theorem rbr_fix_le {n : ℕ} {ν : NNReal} (K : (Fin n → ℝ) → (Fin n → ℝ))
    (hc : ContractingWith ν K)
    (hmono : ∀ v w : Fin n → ℝ, (∀ i, v i ≤ w i) → ∀ i, K v i ≤ K w i)
    (f : Fin n → ℝ) (h : ∀ i, K f i ≤ f i) (i : Fin n) :
    ContractingWith.fixedPoint K hc i ≤ f i := by
  have hit : ∀ N : ℕ, ∀ i, (K^[N] f) i ≤ f i := by
    intro N
    induction N with
    | zero => intro i; exact le_refl _
    | succ N ih =>
      intro i
      rw [Function.iterate_succ_apply']
      exact (hmono _ _ ih i).trans (h i)
  have ht := tendsto_pi_nhds.1 (hc.tendsto_iterate_fixedPoint f) i
  exact le_of_tendsto' ht fun N => hit N i

noncomputable def rbrL {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A)
    (P : M.StationaryNature) (f : Fin n → ℝ) : Fin n → ℝ :=
  fun i => M.cost i (π i) + M.discount * ∑ j, P.1 (π i) i j * f j

noncomputable def rbrPop {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A)
    (P : M.StationaryNature) (f : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j, P.1 (π i) i j * f j

theorem rbr_simplexP {n : ℕ} {A : Type} (M : Model n A) (P : M.StationaryNature) (a : A)
    (i : Fin n) : P.1 a i ∈ stdSimplex ℝ (Fin n) :=
  M.rows_subset_simplex a i (P.2 a i)

theorem rbrL_lip {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A)
    (P : M.StationaryNature) (v w : Fin n → ℝ) (i : Fin n) :
    rbrL M π P v i ≤ rbrL M π P w i + M.discount * ‖v - w‖ := by
  have := rbr_dot_lip (P.1 (π i) i) v w (rbr_simplexP M P _ _)
  have h2 := mul_le_mul_of_nonneg_left this M.discount_nonneg
  simp only [rbrL]
  linarith

theorem rbrL_mono {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A)
    (P : M.StationaryNature) (v w : Fin n → ℝ) (h : ∀ j, v j ≤ w j) (i : Fin n) :
    rbrL M π P v i ≤ rbrL M π P w i := by
  have := rbr_dot_mono (P.1 (π i) i) v w (rbr_simplexP M P _ _) h
  have h2 := mul_le_mul_of_nonneg_left this M.discount_nonneg
  simp only [rbrL]
  linarith

theorem rbrL_le_policy {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A)
    (P : M.StationaryNature) (f : Fin n → ℝ) (i : Fin n) :
    rbrL M π P f i ≤ M.policyOp π f i := by
  have := rbr_le_sf (M.rows (π i) i) (M.rows_subset_simplex _ _) f (P.1 (π i) i) (P.2 _ _)
  have h2 := mul_le_mul_of_nonneg_left this M.discount_nonneg
  simp only [rbrL, Model.policyOp]
  linarith

theorem rbr_L_contract {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A)
    (P : M.StationaryNature) : ContractingWith (Real.toNNReal M.discount) (rbrL M π P) :=
  rbr_contract _ M.discount_nonneg M.discount_lt_one _ (rbrL_lip M π P)

theorem rbr_pol_contract {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A) :
    ContractingWith (Real.toNNReal M.discount) (M.policyOp π) :=
  rbr_contract _ M.discount_nonneg M.discount_lt_one _ (rbr_policy_lip M π)

theorem rbr_bell_contract {n : ℕ} {A : Type} [Fintype A] [Nonempty A] (M : Model n A) :
    ContractingWith (Real.toNNReal M.discount) M.bellmanOp :=
  rbr_contract _ M.discount_nonneg M.discount_lt_one _ (rbr_bellman_lip M)

noncomputable def rbrFixL {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A)
    (P : M.StationaryNature) : Fin n → ℝ :=
  ContractingWith.fixedPoint _ (rbr_L_contract M π P)

noncomputable def rbrFixPol {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A) :
    Fin n → ℝ :=
  ContractingWith.fixedPoint _ (rbr_pol_contract M π)

noncomputable def rbrFixBell {n : ℕ} {A : Type} [Fintype A] [Nonempty A] (M : Model n A) :
    Fin n → ℝ :=
  ContractingWith.fixedPoint _ (rbr_bell_contract M)

theorem rbrFixL_fix {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A)
    (P : M.StationaryNature) : rbrL M π P (rbrFixL M π P) = rbrFixL M π P :=
  ContractingWith.fixedPoint_isFixedPt (rbr_L_contract M π P)

theorem rbrFixPol_fix {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A) :
    M.policyOp π (rbrFixPol M π) = rbrFixPol M π :=
  ContractingWith.fixedPoint_isFixedPt (rbr_pol_contract M π)

theorem rbrFixBell_fix {n : ℕ} {A : Type} [Fintype A] [Nonempty A] (M : Model n A) :
    M.bellmanOp (rbrFixBell M) = rbrFixBell M :=
  ContractingWith.fixedPoint_isFixedPt (rbr_bell_contract M)

theorem rbr_sd_dual {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A)
    (P : M.StationaryNature) (i₀ : Fin n) (t : ℕ) :
    ∀ f : Fin n → ℝ, ∑ i, stateDist π P.1 i₀ t i * f i = ((rbrPop M π P)^[t] f) i₀ := by
  induction t with
  | zero => intro f; simp [stateDist]
  | succ t ih =>
    intro f
    have h : ∑ j, stateDist π P.1 i₀ (t + 1) j * f j =
        ∑ i, stateDist π P.1 i₀ t i * rbrPop M π P f i := by
      simp only [stateDist, rbrPop, Finset.sum_mul, Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [h, ih, Function.iterate_succ_apply]

theorem rbr_pop_norm {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A)
    (P : M.StationaryNature) (f : Fin n → ℝ) : ‖rbrPop M π P f‖ ≤ ‖f‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  exact rbr_dot _ _ (rbr_simplexP M P _ _)

theorem rbr_pop_iter_norm {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A)
    (P : M.StationaryNature) (t : ℕ) (f : Fin n → ℝ) : ‖(rbrPop M π P)^[t] f‖ ≤ ‖f‖ := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact (rbr_pop_norm M π P _).trans ih

theorem rbr_iterL {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A)
    (P : M.StationaryNature) (N : ℕ) :
    ∀ i, ((rbrL M π P)^[N] 0) i = ∑ t ∈ Finset.range N,
      M.discount ^ t * ((rbrPop M π P)^[t] (fun j => M.cost j (π j))) i := by
  induction N with
  | zero => intro i; simp
  | succ N ih =>
    intro i
    rw [Function.iterate_succ_apply']
    show M.cost i (π i) + M.discount * ∑ j, P.1 (π i) i j * ((rbrL M π P)^[N] 0) j = _
    simp only [ih]
    rw [Finset.sum_range_succ']
    have h1 : ∀ t : ℕ, ((rbrPop M π P)^[t + 1] (fun j => M.cost j (π j))) i =
        ∑ j, P.1 (π i) i j * ((rbrPop M π P)^[t] (fun j => M.cost j (π j))) j := fun t => by
      rw [Function.iterate_succ_apply']
      rfl
    simp only [h1]
    have e1 : ∀ j, P.1 (π i) i j * ∑ t ∈ Finset.range N, M.discount ^ t *
        ((rbrPop M π P)^[t] (fun j => M.cost j (π j))) j =
        ∑ t ∈ Finset.range N, M.discount ^ t * (P.1 (π i) i j *
          ((rbrPop M π P)^[t] (fun j => M.cost j (π j))) j) := fun j => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
    have h2 : M.discount * ∑ j, P.1 (π i) i j * ∑ t ∈ Finset.range N, M.discount ^ t *
        ((rbrPop M π P)^[t] (fun j => M.cost j (π j))) j =
        ∑ t ∈ Finset.range N, M.discount ^ (t + 1) * ∑ j, P.1 (π i) i j *
          ((rbrPop M π P)^[t] (fun j => M.cost j (π j))) j := by
      simp only [e1]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h2]
    simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
    ring

theorem rbr_cost_eq {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A)
    (P : M.StationaryNature) (i₀ : Fin n) :
    M.discountedCost i₀ π P = rbrFixL M π P i₀ := by
  have hterm : ∀ t : ℕ, M.discount ^ t * ∑ i, stateDist π P.1 i₀ t i * M.cost i (π i) =
      M.discount ^ t * ((rbrPop M π P)^[t] (fun j => M.cost j (π j))) i₀ := fun t =>
    congrArg (fun x => M.discount ^ t * x)
      (rbr_sd_dual M π P i₀ t (fun j => M.cost j (π j)))
  have hsum : Summable (fun t : ℕ =>
      M.discount ^ t * ((rbrPop M π P)^[t] (fun j => M.cost j (π j))) i₀) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one M.discount_nonneg M.discount_lt_one).mul_right
        ‖fun j => M.cost j (π j)‖) fun t => ?_
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg M.discount_nonneg t)]
    exact mul_le_mul_of_nonneg_left
      ((norm_le_pi_norm _ i₀).trans (rbr_pop_iter_norm M π P t _)) (pow_nonneg M.discount_nonneg t)
  have h1 := hsum.hasSum.tendsto_sum_nat
  have h2 := tendsto_pi_nhds.1 ((rbr_L_contract M π P).tendsto_iterate_fixedPoint 0) i₀
  have h3 : (fun N => ((rbrL M π P)^[N] 0) i₀) = fun N => ∑ t ∈ Finset.range N,
      M.discount ^ t * ((rbrPop M π P)^[t] (fun j => M.cost j (π j))) i₀ :=
    funext fun N => rbr_iterL M π P N i₀
  rw [h3] at h2
  have h4 : M.discountedCost i₀ π P = ∑' t : ℕ,
      M.discount ^ t * ((rbrPop M π P)^[t] (fun j => M.cost j (π j))) i₀ := tsum_congr hterm
  rw [h4]
  exact tendsto_nhds_unique h1 h2

theorem rbr_exists_nature {n : ℕ} {A : Type} (M : Model n A) (v : Fin n → ℝ) (η : ℝ)
    (hη : 0 < η) : ∃ P : M.StationaryNature, ∀ a i,
      Shared.supportFunction (M.rows a i) v - η < ∑ j, P.1 a i j * v j := by
  have h : ∀ a i, ∃ p ∈ M.rows a i, Shared.supportFunction (M.rows a i) v - η <
      ∑ j, p j * v j := fun a i =>
    rbr_sf_approx (M.rows a i) (M.rows_nonempty a i) v η hη
  choose p hp hlt using h
  exact ⟨⟨p, hp⟩, hlt⟩

theorem rbr_near {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A)
    (v : Fin n → ℝ) (hv : ∀ i, v i ≤ M.policyOp π v i) (η δ : ℝ) (hη : 0 < η)
    (hδ : (1 - M.discount) * δ = η) (P : M.StationaryNature)
    (hP : ∀ a i, Shared.supportFunction (M.rows a i) v - η < ∑ j, P.1 a i j * v j)
    (i : Fin n) : v i - δ ≤ rbrFixL M π P i := by
  have h1ν : 0 < 1 - M.discount := sub_pos.2 M.discount_lt_one
  refine rbr_fix_ge (rbrL M π P) (rbr_L_contract M π P) (rbrL_mono M π P)
    (fun j => v j - δ) ?_ i
  intro j
  show v j - δ ≤ M.cost j (π j) + M.discount * ∑ k, P.1 (π j) j k * (v k - δ)
  rw [rbr_dot_shift (P.1 (π j) j) v δ (rbr_simplexP M P _ _)]
  have h2 := hv j
  unfold Model.policyOp at h2
  have h3 := hP (π j) j
  have h4 := mul_le_mul_of_nonneg_left h3.le M.discount_nonneg
  have h5 := mul_nonneg h1ν.le hη.le
  nlinarith

open RobustMDP RobustMDP.Discounted in
theorem solution {n : ℕ} {A : Type} [Fintype A] [Nonempty A]
    (M : Model n A) (i₀ : Fin n) :
    ∃ v : Fin n → ℝ,
      (M.bellmanOp v = v ∧ ∀ w, M.bellmanOp w = w → w = v) ∧
      (∀ v₁ : Fin n → ℝ,
        Filter.Tendsto (fun k : ℕ => M.bellmanOp^[k] v₁) Filter.atTop (nhds v)) ∧
      ((⨅ π : StationaryPolicy n A, ⨆ P : M.StationaryNature, M.discountedCost i₀ π P) = v i₀ ∧
        IsLUB (Set.range fun P : M.StationaryNature =>
          ⨅ π : StationaryPolicy n A, M.discountedCost i₀ π P) (v i₀)) ∧
      (∀ πstar : StationaryPolicy n A,
        (∀ (i : Fin n) (a : A),
          M.cost i (πstar i) + M.discount * Shared.supportFunction (M.rows (πstar i) i) v ≤
            M.cost i a + M.discount * Shared.supportFunction (M.rows a i) v) →
        IsLUB (Set.range fun P : M.StationaryNature => M.discountedCost i₀ πstar P) (v i₀)) ∧
      (∀ Pstar : M.StationaryNature,
        (∀ (a : A) (i : Fin n),
          ∑ j, Pstar.1 a i j * v j = Shared.supportFunction (M.rows a i) v) →
        (⨅ π : StationaryPolicy n A, M.discountedCost i₀ π Pstar) = v i₀) ∧
      (∀ π : StationaryPolicy n A,
        ∃ vπ : Fin n → ℝ,
          M.policyOp π vπ = vπ ∧ (∀ w, M.policyOp π w = w → w = vπ) ∧
          IsLUB (Set.range fun P : M.StationaryNature => M.discountedCost i₀ π P) (vπ i₀)) := by
  have hbc := rbr_bell_contract M
  have hfix := rbrFixBell_fix M
  have hle : ∀ (π : StationaryPolicy n A) (i : Fin n), rbrFixBell M i ≤
      M.policyOp π (rbrFixBell M) i := fun π i => by
    have h1 : M.bellmanOp (rbrFixBell M) i ≤ M.cost i (π i) +
        M.discount * Shared.supportFunction (M.rows (π i) i) (rbrFixBell M) :=
      Finset.inf'_le _ (Finset.mem_univ (π i))
    rw [hfix] at h1
    exact h1
  have hgreedy : ∀ πs : StationaryPolicy n A, (∀ (i : Fin n) (a : A),
      M.cost i (πs i) + M.discount * Shared.supportFunction (M.rows (πs i) i) (rbrFixBell M) ≤
        M.cost i a + M.discount * Shared.supportFunction (M.rows a i) (rbrFixBell M)) →
      M.policyOp πs (rbrFixBell M) = rbrFixBell M := fun πs h => by
    funext i
    apply le_antisymm
    · have h1 : M.policyOp πs (rbrFixBell M) i ≤ M.bellmanOp (rbrFixBell M) i :=
        Finset.le_inf' _ _ fun a _ => h i a
      rw [hfix] at h1
      exact h1
    · exact hle πs i
  have hex : ∃ πs : StationaryPolicy n A, ∀ (i : Fin n) (a : A),
      M.cost i (πs i) + M.discount * Shared.supportFunction (M.rows (πs i) i) (rbrFixBell M) ≤
        M.cost i a + M.discount * Shared.supportFunction (M.rows a i) (rbrFixBell M) := by
    have h : ∀ i : Fin n, ∃ a : A, ∀ b : A,
        M.cost i a + M.discount * Shared.supportFunction (M.rows a i) (rbrFixBell M) ≤
          M.cost i b + M.discount * Shared.supportFunction (M.rows b i) (rbrFixBell M) :=
      fun i => by
        obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := A))
          (fun a => M.cost i a + M.discount * Shared.supportFunction (M.rows a i) (rbrFixBell M))
        refine ⟨a, fun b => ?_⟩
        rw [← ha]
        exact Finset.inf'_le _ (Finset.mem_univ b)
    choose πs hπs using h
    exact ⟨πs, hπs⟩
  have hfixeq : ∀ πs : StationaryPolicy n A, (∀ (i : Fin n) (a : A),
      M.cost i (πs i) + M.discount * Shared.supportFunction (M.rows (πs i) i) (rbrFixBell M) ≤
        M.cost i a + M.discount * Shared.supportFunction (M.rows a i) (rbrFixBell M)) →
      rbrFixPol M πs = rbrFixBell M := fun πs h =>
    (ContractingWith.fixedPoint_unique (rbr_pol_contract M πs) (hgreedy πs h)).symm
  have hlower : ∀ (π : StationaryPolicy n A) (i : Fin n), rbrFixBell M i ≤ rbrFixPol M π i :=
    fun π i => rbr_fix_ge (M.policyOp π) (rbr_pol_contract M π) (rbr_policy_mono M π)
      (rbrFixBell M) (hle π) i
  have : Nonempty M.StationaryNature := by
    obtain ⟨P, _⟩ := rbr_exists_nature M (rbrFixBell M) 1 one_pos
    exact ⟨P⟩
  have hLUB : ∀ π : StationaryPolicy n A,
      IsLUB (Set.range fun P : M.StationaryNature => M.discountedCost i₀ π P)
        (rbrFixPol M π i₀) := fun π => by
    constructor
    · rintro _ ⟨P, rfl⟩
      show M.discountedCost i₀ π P ≤ _
      rw [rbr_cost_eq]
      refine rbr_fix_ge (M.policyOp π) (rbr_pol_contract M π) (rbr_policy_mono M π)
        (rbrFixL M π P) (fun i => ?_) i₀
      have h1 := congrFun (rbrFixL_fix M π P) i
      have h2 := rbrL_le_policy M π P (rbrFixL M π P) i
      rw [h1] at h2
      exact h2
    · intro b hb
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨P, hP⟩ := rbr_exists_nature M (rbrFixPol M π) ((1 - M.discount) * ε)
        (mul_pos (sub_pos.2 M.discount_lt_one) hε)
      have hv : ∀ i, rbrFixPol M π i ≤ M.policyOp π (rbrFixPol M π) i := fun i =>
        le_of_eq (congrFun (rbrFixPol_fix M π) i).symm
      have h1 := rbr_near M π _ hv _ ε (mul_pos (sub_pos.2 M.discount_lt_one) hε) rfl P hP i₀
      have h2 : M.discountedCost i₀ π P ≤ b := hb (Set.mem_range_self P)
      rw [rbr_cost_eq] at h2
      linarith
  obtain ⟨πs, hπs⟩ := hex
  have hbddB : ∀ P : M.StationaryNature, BddBelow (Set.range fun π : StationaryPolicy n A =>
      M.discountedCost i₀ π P) := fun P => (Set.finite_range _).bddBelow
  refine ⟨rbrFixBell M, ⟨hfix, fun w hw => ContractingWith.fixedPoint_unique hbc hw⟩,
    fun v₁ => hbc.tendsto_iterate_fixedPoint v₁, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · have hsup : ∀ π : StationaryPolicy n A,
        (⨆ P : M.StationaryNature, M.discountedCost i₀ π P) = rbrFixPol M π i₀ :=
      fun π => (hLUB π).ciSup_eq
    rw [iInf_congr hsup]
    apply le_antisymm
    · have hb : BddBelow (Set.range fun π : StationaryPolicy n A => rbrFixPol M π i₀) :=
        (Set.finite_range _).bddBelow
      have := ciInf_le hb πs
      rw [hfixeq πs hπs] at this
      exact this
    · exact le_ciInf fun π => hlower π i₀
  · constructor
    · rintro _ ⟨P, rfl⟩
      have h1 := ciInf_le (hbddB P) πs
      have h2 : M.discountedCost i₀ πs P ≤ rbrFixPol M πs i₀ :=
        (hLUB πs).1 (Set.mem_range_self P)
      rw [hfixeq πs hπs] at h2
      exact h1.trans h2
    · intro b hb
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨P, hP⟩ := rbr_exists_nature M (rbrFixBell M) ((1 - M.discount) * ε)
        (mul_pos (sub_pos.2 M.discount_lt_one) hε)
      have h1 : rbrFixBell M i₀ - ε ≤ ⨅ π : StationaryPolicy n A, M.discountedCost i₀ π P := by
        refine le_ciInf fun π => ?_
        rw [rbr_cost_eq]
        exact rbr_near M π _ (hle π) _ ε (mul_pos (sub_pos.2 M.discount_lt_one) hε) rfl P hP i₀
      have h2 : (⨅ π : StationaryPolicy n A, M.discountedCost i₀ π P) ≤ b :=
        hb (Set.mem_range_self P)
      linarith
  · intro πstar hstar
    have := hLUB πstar
    rw [hfixeq πstar hstar] at this
    exact this
  · intro Pstar hP
    have hge : ∀ π : StationaryPolicy n A, rbrFixBell M i₀ ≤ M.discountedCost i₀ π Pstar := by
      intro π
      rw [rbr_cost_eq]
      refine rbr_fix_ge (rbrL M π Pstar) (rbr_L_contract M π Pstar) (rbrL_mono M π Pstar)
        (rbrFixBell M) (fun i => ?_) i₀
      show rbrFixBell M i ≤ M.cost i (π i) +
        M.discount * ∑ j, Pstar.1 (π i) i j * rbrFixBell M j
      rw [hP (π i) i]
      exact hle π i
    have hfL : rbrFixL M πs Pstar = rbrFixBell M := by
      symm
      apply ContractingWith.fixedPoint_unique (rbr_L_contract M πs Pstar)
      funext i
      show M.cost i (πs i) + M.discount * ∑ j, Pstar.1 (πs i) i j * rbrFixBell M j =
        rbrFixBell M i
      rw [hP (πs i) i]
      exact congrFun (hgreedy πs hπs) i
    apply le_antisymm
    · have := ciInf_le (hbddB Pstar) πs
      rw [rbr_cost_eq, hfL] at this
      exact this
    · exact le_ciInf hge
  · intro π
    exact ⟨rbrFixPol M π, rbrFixPol_fix M π,
      fun w hw => ContractingWith.fixedPoint_unique (rbr_pol_contract M π) hw, hLUB π⟩
