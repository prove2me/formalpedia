-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P21.measurePrepareSimulation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:45:33.132934+00:00
-- url     : https://prove2.me/submissions/a9678350-03eb-45d9-a7c1-fdd388f2aa15

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P21
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.Elementwise

open Filter MeasureTheory

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P21

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Reuse the finite Pi-space extended norm explicitly. Matrix has the same
-- product topology, but the generic instance search did not bridge the alias.

attribute [local instance] QAlgorithms.Papers.Independent.Gap48.P21.matrixContinuousENorm

open QAlgorithms.Papers.Independent.Dependency50.P45
  (resourceCapacity standardEbit DMC shannonCapacity blockProb)

open QAlgorithms.Papers.Independent.Claimed50.P43 (finiteWeyl chaotic)

open QAlgorithms.Papers.Independent.Information100.P58 (singleErasure)

open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

-- CE uses resourceCapacity standardEbit directly; C uses the same accepted
-- operational capacity with the one-dimensional product resource.

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

instance g74e_prob (d : ℕ) : IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar d) :=
  ⟨Measure.haarMeasure_self⟩

instance g74e_haar (d : ℕ) : (QAlgorithms.Schur.unitaryHaar d).IsHaarMeasure := by
  unfold QAlgorithms.Schur.unitaryHaar; infer_instance

theorem g74e_cc {d : ℕ} (i j : Fin d) :
    Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ => (U : Matrix (Fin d) (Fin d) ℂ) i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

theorem g74e_intc {d : ℕ} {f : Matrix.unitaryGroup (Fin d) ℂ → ℂ} (hf : Continuous f) :
    Integrable f (QAlgorithms.Schur.unitaryHaar d) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

def g74e_mono {d : ℕ} (c a b k l : Fin d) (U : Matrix.unitaryGroup (Fin d) ℂ) : ℂ :=
  (U : Matrix (Fin d) (Fin d) ℂ) a c * conj ((U : Matrix (Fin d) (Fin d) ℂ) b c) *
  (U : Matrix (Fin d) (Fin d) ℂ) k c * conj ((U : Matrix (Fin d) (Fin d) ℂ) l c)

theorem g74e_mono_cont {d : ℕ} (c a b k l : Fin d) : Continuous (g74e_mono c a b k l) := by
  unfold g74e_mono
  exact (((g74e_cc a c).mul (Complex.continuous_conj.comp (g74e_cc b c))).mul
    (g74e_cc k c)).mul (Complex.continuous_conj.comp (g74e_cc l c))

def g74e_T (d : ℕ) (c a b k l : Fin d) : ℂ :=
  ∫ U, g74e_mono c a b k l U ∂QAlgorithms.Schur.unitaryHaar d

theorem g74e_mono_mul {d : ℕ} (c a b k l : Fin d) (V U : Matrix.unitaryGroup (Fin d) ℂ) :
    g74e_mono c a b k l (V * U) = ∑ l', ∑ k', ∑ b', ∑ a',
      ((V : Matrix (Fin d) (Fin d) ℂ) a a' * conj ((V : Matrix (Fin d) (Fin d) ℂ) b b') *
        (V : Matrix (Fin d) (Fin d) ℂ) k k' * conj ((V : Matrix (Fin d) (Fin d) ℂ) l l')) *
        g74e_mono c a' b' k' l' U := by
  have hc : ((V * U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) =
      (V : Matrix (Fin d) (Fin d) ℂ) * (U : Matrix (Fin d) (Fin d) ℂ) := rfl
  unfold g74e_mono
  rw [hc]
  simp only [Matrix.mul_apply, map_sum, map_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ =>
    Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))))

theorem g74e_int_sum {d : ℕ} {ι : Type*} [Fintype ι] (f : ι → Matrix.unitaryGroup (Fin d) ℂ → ℂ)
    (hf : ∀ i, Continuous (f i)) :
    ∫ U, ∑ i, f i U ∂QAlgorithms.Schur.unitaryHaar d =
      ∑ i, ∫ U, f i U ∂QAlgorithms.Schur.unitaryHaar d :=
  integral_finsetSum _ (fun i _ => g74e_intc (hf i))

theorem g74e_T_inv {d : ℕ} (V : Matrix.unitaryGroup (Fin d) ℂ) (c a b k l : Fin d) :
    g74e_T d c a b k l = ∑ l', ∑ k', ∑ b', ∑ a',
      ((V : Matrix (Fin d) (Fin d) ℂ) a a' * conj ((V : Matrix (Fin d) (Fin d) ℂ) b b') *
        (V : Matrix (Fin d) (Fin d) ℂ) k k' * conj ((V : Matrix (Fin d) (Fin d) ℂ) l l')) *
        g74e_T d c a' b' k' l' := by
  unfold g74e_T
  rw [← integral_mul_left_eq_self (μ := QAlgorithms.Schur.unitaryHaar d) _ V]
  simp_rw [g74e_mono_mul]
  have hm := g74e_mono_cont (d := d) c
  rw [g74e_int_sum _ (fun a' => by fun_prop)]
  refine Finset.sum_congr rfl (fun l' _ => ?_)
  rw [g74e_int_sum _ (fun b' => by fun_prop)]
  refine Finset.sum_congr rfl (fun k' _ => ?_)
  rw [g74e_int_sum _ (fun k' => by fun_prop)]
  refine Finset.sum_congr rfl (fun b' _ => ?_)
  rw [g74e_int_sum _ (fun l' => by fun_prop)]
  refine Finset.sum_congr rfl (fun a' _ => ?_)
  rw [integral_const_mul]

def g74e_phi {d : ℕ} (m : Fin d) (i : Fin d) : ℂ := if i = m then Complex.I else 1

theorem g74e_phi_mem {d : ℕ} (m : Fin d) :
    Matrix.diagonal (g74e_phi m) ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  simp only [g74e_phi, Pi.star_apply, Pi.one_apply]
  split_ifs
  · simp [Complex.ext_iff]
  · simp

theorem g74e_phase {d : ℕ} (m c a b k l : Fin d) :
    g74e_T d c a b k l =
      (g74e_phi m a * conj (g74e_phi m b) * g74e_phi m k * conj (g74e_phi m l)) *
        g74e_T d c a b k l := by
  have h := g74e_T_inv ⟨_, g74e_phi_mem m⟩ c a b k l
  rw [Fintype.sum_eq_single l (fun x hx => by simp [Matrix.diagonal_apply, Ne.symm hx]),
    Fintype.sum_eq_single k (fun x hx => by simp [Matrix.diagonal_apply, Ne.symm hx]),
    Fintype.sum_eq_single b (fun x hx => by simp [Matrix.diagonal_apply, Ne.symm hx]),
    Fintype.sum_eq_single a (fun x hx => by simp [Matrix.diagonal_apply, Ne.symm hx])] at h
  simpa [Matrix.diagonal_apply] using h

theorem g74e_T_zero {d : ℕ} (c a b k l : Fin d) (h : ¬((a = b ∧ k = l) ∨ (a = l ∧ k = b))) :
    g74e_T d c a b k l = 0 := by
  by_contra hT
  have e1 : g74e_phi a a * conj (g74e_phi a b) * g74e_phi a k * conj (g74e_phi a l) = 1 := by
    have h1 := g74e_phase a c a b k l
    apply mul_right_cancel₀ hT
    rw [one_mul]; exact h1.symm
  have e2 : g74e_phi k a * conj (g74e_phi k b) * g74e_phi k k * conj (g74e_phi k l) = 1 := by
    have h1 := g74e_phase k c a b k l
    apply mul_right_cancel₀ hT
    rw [one_mul]; exact h1.symm
  simp only [g74e_phi] at e1 e2
  split_ifs at e1 e2 <;> subst_vars <;> simp [Complex.ext_iff] at e1 e2 h ⊢ <;> simp_all <;> norm_num [Complex.ext_iff] at *

theorem g74e_perm_mem {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    (Matrix.of fun a b => if a = τ b then (1 : ℂ) else 0) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.star_apply, Matrix.one_apply]
  have hh : ∀ x, (b = τ x) ↔ (x = τ.symm b) := by
    intro x; constructor <;> intro h <;> subst h <;> simp
  simp [apply_ite, hh]

theorem g74e_sw {d : ℕ} (p q x : Fin d) (hx : x ≠ q) : ¬ (p = Equiv.swap q p x) := by
  intro h
  apply hx
  have := congrArg (Equiv.swap q p) h
  simp only [Equiv.swap_apply_right, Equiv.swap_apply_self] at this
  exact this.symm

theorem g74e_alpha_unif {d : ℕ} (c p q : Fin d) : g74e_T d c p p p p = g74e_T d c q q q q := by
  have h := g74e_T_inv ⟨_, g74e_perm_mem (Equiv.swap q p)⟩ c p p p p
  rw [Fintype.sum_eq_single q (fun x hx => by simp [g74e_sw p q x hx]),
    Fintype.sum_eq_single q (fun x hx => by simp [g74e_sw p q x hx]),
    Fintype.sum_eq_single q (fun x hx => by simp [g74e_sw p q x hx]),
    Fintype.sum_eq_single q (fun x hx => by simp [g74e_sw p q x hx])] at h
  simpa using h

theorem g74e_col_norm {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (c : Fin d) :
    ∑ a, (U : Matrix (Fin d) (Fin d) ℂ) a c * conj ((U : Matrix (Fin d) (Fin d) ℂ) a c) = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp U.2) c) c
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
  rw [← h]
  exact Finset.sum_congr rfl (fun _ _ => by simp [mul_comm])

theorem g74e_norm {d : ℕ} (c : Fin d) : ∑ a, ∑ k, g74e_T d c a a k k = 1 := by
  unfold g74e_T
  have hm := g74e_mono_cont (d := d) c
  rw [show (∑ a, ∑ k, ∫ U, g74e_mono c a a k k U ∂QAlgorithms.Schur.unitaryHaar d) =
      ∫ U, ∑ a, ∑ k, g74e_mono c a a k k U ∂QAlgorithms.Schur.unitaryHaar d from by
    rw [g74e_int_sum _ (fun a => continuous_finsetSum _ (fun k _ => hm a a k k))]
    exact Finset.sum_congr rfl (fun a _ => (g74e_int_sum _ (fun k => hm a a k k)).symm)]
  have : ∀ U, ∑ a, ∑ k, g74e_mono c a a k k U = 1 := by
    intro U
    unfold g74e_mono
    have h1 := g74e_col_norm U c
    calc _ = (∑ a, (U : Matrix (Fin d) (Fin d) ℂ) a c * conj ((U : Matrix (Fin d) (Fin d) ℂ) a c)) *
        (∑ a, (U : Matrix (Fin d) (Fin d) ℂ) a c * conj ((U : Matrix (Fin d) (Fin d) ℂ) a c)) := by
          rw [Finset.sum_mul_sum]
          exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
      _ = 1 := by rw [h1, one_mul]
  simp_rw [this]
  simp

def g74e_w {d : ℕ} (p q : Fin d) (m : Fin d) : ℂ := if m = p then 3/5 else if m = q then 4/5 else 0

def g74e_W {d : ℕ} (p q : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => g74e_w p q i * g74e_w p q j

theorem g74e_w_conj {d : ℕ} (p q m : Fin d) : conj (g74e_w p q m) = g74e_w p q m := by
  unfold g74e_w; split_ifs <;> simp [map_div₀, map_ofNat]

theorem g74e_w_sum {d : ℕ} (p q : Fin d) (hpq : p ≠ q) : ∑ m, g74e_w p q m * g74e_w p q m = 1 := by
  rw [Fintype.sum_eq_add p q hpq (fun x hx => by simp [g74e_w, hx.1, hx.2])]
  simp [g74e_w, Ne.symm hpq]; norm_num

theorem g74e_WW {d : ℕ} (p q : Fin d) (hpq : p ≠ q) : g74e_W p q * g74e_W p q = g74e_W p q := by
  ext i j
  simp only [g74e_W, Matrix.mul_apply, Matrix.of_apply]
  have h := g74e_w_sum p q hpq
  calc _ = g74e_w p q i * g74e_w p q j * ∑ m, g74e_w p q m * g74e_w p q m := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ = _ := by rw [h, mul_one]

theorem g74e_H_mem {d : ℕ} (p q : Fin d) (hpq : p ≠ q) :
    (1 - (2 : ℂ) • g74e_W p q) ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hs : star (g74e_W p q) = g74e_W p q := by
    ext i j
    simp [g74e_W, Matrix.star_apply, g74e_w_conj, mul_comm]
  rw [star_sub, star_one, star_smul, hs]
  simp only [star_ofNat]
  rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm,
    smul_smul, g74e_WW p q hpq]
  module

theorem g74e_H_row {d : ℕ} (p q : Fin d) (hpq : p ≠ q) (x : Fin d) :
    (1 - (2 : ℂ) • g74e_W p q) p x =
      (if x = p then (7/25 : ℂ) else 0) + (if x = q then (-24/25 : ℂ) else 0) := by
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, g74e_W, Matrix.of_apply,
    g74e_w, if_pos rfl, smul_eq_mul]
  by_cases h1 : x = p
  · subst h1; simp [hpq] ; norm_num
  · by_cases h2 : x = q
    · subst h2; simp [h1, hpq]; norm_num
    · simp [h1, h2, Ne.symm h1]

theorem g74e_T_comm1 {d : ℕ} (c p q : Fin d) : g74e_T d c q q p p = g74e_T d c p p q q := by
  unfold g74e_T; congr 1; funext U; unfold g74e_mono; ring

theorem g74e_T_comm2 {d : ℕ} (c p q : Fin d) : g74e_T d c p q q p = g74e_T d c p p q q := by
  unfold g74e_T; congr 1; funext U; unfold g74e_mono; ring

theorem g74e_T_comm3 {d : ℕ} (c p q : Fin d) : g74e_T d c q p p q = g74e_T d c p p q q := by
  unfold g74e_T; congr 1; funext U; unfold g74e_mono; ring

theorem g74e_sum_pq {d : ℕ} (p q : Fin d) (hpq : p ≠ q) (g : Fin d → ℂ) :
    ∑ x, ((if x = p then (7/25 : ℂ) else 0) + (if x = q then (-24/25 : ℂ) else 0)) * g x =
      7/25 * g p + (-24/25) * g q := by
  simp [add_mul, ite_mul, Finset.sum_add_distrib]

theorem g74e_beta {d : ℕ} (c p q : Fin d) (hpq : p ≠ q) :
    g74e_T d c p p p p = 2 * g74e_T d c p p q q := by
  have h := g74e_T_inv ⟨_, g74e_H_mem p q hpq⟩ c p p p p
  have hr := g74e_H_row p q hpq
  have hrc : ∀ x, conj ((1 - (2 : ℂ) • g74e_W p q) p x) =
      (if x = p then (7/25 : ℂ) else 0) + (if x = q then (-24/25 : ℂ) else 0) := by
    intro x; rw [hr x]; split_ifs <;> simp [map_div₀, map_ofNat, map_neg]
  dsimp only at h
  simp only [hrc] at h
  simp only [hr] at h
  have key : ∀ F : Fin d → Fin d → Fin d → Fin d → ℂ, ∀ r : Fin d → ℂ,
      (∑ l', ∑ k', ∑ b', ∑ a', r a' * r b' * r k' * r l' * F a' b' k' l') =
      ∑ l', r l' * ∑ k', r k' * ∑ b', r b' * ∑ a', r a' * F a' b' k' l' := by
    intro F r
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ =>
      Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))))
  rw [key (fun a' b' k' l' => g74e_T d c a' b' k' l')
    (fun x => (if x = p then (7/25 : ℂ) else 0) + (if x = q then (-24/25 : ℂ) else 0))] at h
  simp only [g74e_sum_pq p q hpq] at h
  have hq := g74e_alpha_unif c q p
  rw [hq, g74e_T_comm1 c p q, g74e_T_comm2 c p q, g74e_T_comm3 c p q] at h
  have hne : q ≠ p := Ne.symm hpq
  simp only [g74e_T_zero c p p p q (by simp [hpq, hne]), g74e_T_zero c p p q p (by simp [hpq, hne]),
    g74e_T_zero c p q p p (by simp [hpq, hne]), g74e_T_zero c q p p p (by simp [hpq, hne]),
    g74e_T_zero c p q p q (by simp [hpq, hne]), g74e_T_zero c q p q p (by simp [hpq, hne]),
    g74e_T_zero c q q q p (by simp [hpq, hne]), g74e_T_zero c q q p q (by simp [hpq, hne]),
    g74e_T_zero c q p q q (by simp [hpq, hne]), g74e_T_zero c p q q q (by simp [hpq, hne])] at h
  linear_combination (390625 / 56448 : ℂ) * h

theorem g74e_T_diag {d : ℕ} (c a k : Fin d) :
    g74e_T d c a a k k = g74e_T d c c c c c / 2 + (if a = k then g74e_T d c c c c c / 2 else 0) := by
  by_cases h : a = k
  · subst h; rw [g74e_alpha_unif c a c, if_pos rfl]; ring
  · rw [if_neg h, ← g74e_alpha_unif c a c, g74e_beta c a k h]; ring

theorem g74e_alpha_val {d : ℕ} (c : Fin d) :
    g74e_T d c c c c c = 2 / ((d : ℂ) * (d + 1)) := by
  have h := g74e_norm c
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun k _ => g74e_T_diag c a k))] at h
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have hd : (d : ℂ) ≠ 0 := by
    have : 0 < d := Fin.pos c
    exact_mod_cast this.ne'
  have hd1 : (d : ℂ) + 1 ≠ 0 := by
    have : ((d + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
    exact_mod_cast this
  field_simp
  linear_combination 2 * h

theorem g74e_T_val {d : ℕ} (c a b k l : Fin d) :
    g74e_T d c a b k l = ((if a = b ∧ k = l then 1 else 0) + (if a = l ∧ k = b then 1 else 0)) /
      ((d : ℂ) * (d + 1)) := by
  have hA := g74e_alpha_val c
  by_cases h1 : a = b ∧ k = l
  · obtain ⟨rfl, rfl⟩ := h1
    rw [g74e_T_diag c a k, hA]
    by_cases hak : a = k
    · subst hak; simp; ring
    · simp [hak]; rw [← mul_inv]; ring_nf
  · by_cases h2 : a = l ∧ k = b
    · obtain ⟨rfl, rfl⟩ := h2
      have hak : a ≠ k := by intro h; apply h1; exact ⟨h, h.symm⟩
      rw [g74e_T_comm2 c a k, g74e_T_diag c a k, hA]
      simp [hak, h1]; rw [← mul_inv]; ring_nf
    · rw [g74e_T_zero c a b k l (by tauto)]
      simp [h1, h2]

theorem g74e_proj {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (i a b : Fin d) :
    basisProjector U i a b =
      (U : Matrix (Fin d) (Fin d) ℂ) a i * conj ((U : Matrix (Fin d) (Fin d) ℂ) b i) := by
  simp [basisProjector, pureDensity, act, ket, Matrix.mulVec, dotProduct]

theorem g74e_rows {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (k l : Fin d) :
    ∑ j, (U : Matrix (Fin d) (Fin d) ℂ) k j * conj ((U : Matrix (Fin d) (Fin d) ℂ) l j) =
      if k = l then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp U.2) k) l
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at h
  rw [← h]
  exact Finset.sum_congr rfl (fun _ _ => by simp)

theorem g74e_tr {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (i : Fin d) (X : Matrix (Fin d) (Fin d) ℂ) :
    (basisProjector U i * X).trace = ∑ a, ∑ b,
      (U : Matrix (Fin d) (Fin d) ℂ) a i * conj ((U : Matrix (Fin d) (Fin d) ℂ) b i) * X b a := by
  simp [Matrix.trace, Matrix.mul_apply, g74e_proj]

theorem g74e_trsum {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ i, (basisProjector U i * X).trace = X.trace := by
  simp only [g74e_tr]
  rw [Finset.sum_comm]
  have : ∀ a, ∑ i, ∑ b, (U : Matrix (Fin d) (Fin d) ℂ) a i *
      conj ((U : Matrix (Fin d) (Fin d) ℂ) b i) * X b a = X a a := by
    intro a
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, g74e_rows]
    simp
  simp only [this, Matrix.trace, Matrix.diag]

theorem g74e_pt {d : ℕ} (y : ℝ) (U : Matrix.unitaryGroup (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ)
    (k l : Fin d) :
    (∑ i, ∑ j, (((randomizing y i j : ℝ) : ℂ) * (basisProjector U i * X).trace) •
        basisProjector U j) k l =
      ((1 - y : ℝ) : ℂ) * ∑ i, ∑ a, ∑ b, X b a * g74e_mono i a b k l U +
        ((y / d : ℝ) : ℂ) * X.trace * (if k = l then 1 else 0) := by
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, randomizing, Fintype.card_fin]
  have e1 : ∀ i j, ((((if i = j then 1 - y else 0) + y / d : ℝ) : ℂ) *
      (basisProjector U i * X).trace) * basisProjector U j k l =
      (if i = j then ((1 - y : ℝ) : ℂ) * ((basisProjector U i * X).trace * basisProjector U i k l)
        else 0) +
      ((y / d : ℝ) : ℂ) * ((basisProjector U i * X).trace * basisProjector U j k l) := by
    intro i j
    split_ifs with h
    · subst h; push_cast; ring
    · push_cast; ring
  simp only [e1, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Finset.mul_sum]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [g74e_tr, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [g74e_proj]; unfold g74e_mono; ring
  · simp only [← Finset.mul_sum, ← Finset.sum_mul]
    simp only [g74e_proj, g74e_rows, g74e_trsum]
    ring

theorem g74e_inner {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (k l : Fin d) :
    ∑ a, ∑ b, X b a * (((if a = b ∧ k = l then 1 else 0) + (if a = l ∧ k = b then 1 else 0)) /
      ((d : ℂ) * (d + 1))) = (X.trace * (if k = l then 1 else 0) + X k l) / ((d : ℂ) * (d + 1)) := by
  simp only [mul_div_assoc', ← Finset.sum_div, mul_add, Finset.sum_add_distrib]
  congr 1
  simp only [ite_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  by_cases h : k = l
  · subst h; simp [Matrix.trace, Matrix.diag]
  · simp [h]

theorem g74e_ent {d : ℕ} (F : Matrix.unitaryGroup (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (hF : ∀ x y, Integrable (fun U => F U x y) (QAlgorithms.Schur.unitaryHaar d)) (x y : Fin d) :
    (∫ U, F U ∂QAlgorithms.Schur.unitaryHaar d) x y =
      ∫ U, F U x y ∂QAlgorithms.Schur.unitaryHaar d := by
  have h1 : ∀ x : Fin d, Integrable (fun U => F U x) (QAlgorithms.Schur.unitaryHaar d) :=
    fun x => Integrable.of_eval (hF x)
  exact (congrFun (eval_integral h1 x) y).trans (eval_integral (hF x) y)

theorem g74e_bp_cont {d : ℕ} (i : Fin d) :
    Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ => basisProjector U i) := by
  refine continuous_matrix (fun a b => ?_)
  simp only [g74e_proj]
  exact (g74e_cc a i).mul (Complex.continuous_conj.comp (g74e_cc b i))

theorem g74e_mp_cont {d : ℕ} (P : Fin d → Fin d → ℝ) (X : Matrix (Fin d) (Fin d) ℂ) :
    Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      ∑ i, ∑ j, ((P i j : ℂ) * (basisProjector U i * X).trace) • basisProjector U j) := by
  refine continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => ?_))
  exact (continuous_const.mul ((g74e_bp_cont i).matrix_mul continuous_const).matrix_trace).smul
    (g74e_bp_cont j)

theorem g74e_mp_eq {d : ℕ} (hd : 0 < d) (x : ℝ) (X : Matrix (Fin d) (Fin d) ℂ) :
    measurePrepare d (randomizing (((d:ℝ)+1)*x-d)) X =
      QAlgorithms.QuditFidelity.depolarizingMap d hd x X := by
  ext k l
  unfold measurePrepare
  rw [g74e_ent _ (fun a b => g74e_intc ((g74e_mp_cont _ X).matrix_elem a b))]
  simp only [g74e_pt]
  have hm := g74e_mono_cont (d := d)
  rw [integral_add (g74e_intc (by fun_prop)) (g74e_intc continuous_const), integral_const_mul,
    integral_const]
  rw [g74e_int_sum _ (fun i => by fun_prop)]
  have : ∀ i, ∫ U, ∑ a, ∑ b, X b a * g74e_mono i a b k l U ∂QAlgorithms.Schur.unitaryHaar d =
      (X.trace * (if k = l then 1 else 0) + X k l) / ((d : ℂ) * (d + 1)) := by
    intro i
    rw [g74e_int_sum _ (fun a => by fun_prop)]
    rw [← g74e_inner X k l]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [g74e_int_sum _ (fun b => by fun_prop)]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [integral_const_mul]
    rw [show (∫ U, g74e_mono i a b k l U ∂QAlgorithms.Schur.unitaryHaar d) = g74e_T d i a b k l
      from rfl, g74e_T_val]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [QAlgorithms.QuditFidelity.depolarizingMap, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, probReal_univ, one_smul]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hd1 : (d : ℂ) + 1 ≠ 0 := by
    have : ((d + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
    exact_mod_cast this
  push_cast
  field_simp
  split_ifs <;> ring

theorem g74e_R_eq {d : ℕ} (y : ℝ) (a b : Fin d) :
    randomizing y a b = if a = b then 1 - y + y / d else y / d := by
  simp only [randomizing, Fintype.card_fin]; split_ifs <;> ring

theorem g74e_R_nonneg {d : ℕ} (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (a b : Fin d) :
    0 ≤ randomizing y a b := by
  rw [g74e_R_eq]; split_ifs <;> [nlinarith [div_nonneg hy0 (Nat.cast_nonneg (α := ℝ) d)]; positivity]

theorem g74e_R_row {d : ℕ} (hd : 0 < d) (y : ℝ) (a : Fin d) : ∑ b, randomizing y a b = 1 := by
  simp only [randomizing, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp; ring

theorem g74e_R_col {d : ℕ} (hd : 0 < d) (y : ℝ) (b : Fin d) : ∑ a, randomizing y a b = 1 := by
  simp only [randomizing, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp; ring

theorem g74e_term (q R r : ℝ) (hq : 0 ≤ q) (hR : 0 ≤ R) (hr : q * R ≤ r) :
    q * R * Real.logb 2 (q * R / (q * r)) = q * R * Real.logb 2 R - q * R * Real.logb 2 r := by
  rcases hq.eq_or_lt with h | h
  · subst h; simp
  rcases hR.eq_or_lt with h' | h'
  · subst h'; simp
  have hr' : 0 < r := lt_of_lt_of_le (mul_pos h h') hr
  rw [mul_div_mul_left _ _ h.ne', Real.logb_div h'.ne' hr'.ne']
  ring

theorem g74e_ent_le {d : ℕ} (hd : 0 < d) (r : Fin d → ℝ) (hr0 : ∀ b, 0 ≤ r b) (hr1 : ∑ b, r b = 1) :
    -∑ b, r b * Real.logb 2 (r b) ≤ Real.logb 2 d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have key : ∀ b, -(r b * Real.log (r b)) - r b * Real.log d ≤ 1 / d - r b := by
    intro b
    rcases (hr0 b).eq_or_lt with h | h
    · rw [← h]; simp; try positivity
    · have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 / (d * r b) by positivity)
      rw [one_div, Real.log_inv, Real.log_mul hdpos.ne' h.ne'] at h1
      have h2 : r b * (d * r b)⁻¹ = 1 / d := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left h1 h.le]
  have hs := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => key b)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.sum_mul, hr1] at hs
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp only [Real.logb, mul_div_assoc', ← Finset.sum_div, ← neg_div]
  rw [div_le_div_iff_of_pos_right hl2]
  have : (d : ℝ) * (1 / d) = 1 := by field_simp
  rw [Finset.sum_neg_distrib] at hs
  linarith

theorem g74e_mi_eq {d : ℕ} (hd : 0 < d) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (q : Fin d → ℝ) (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∑ a, q a = 1) :
    mutualInfoBits (fun xy : Fin d × Fin d => q xy.1 * randomizing y xy.1 xy.2) =
      ((1 - y + y / d) * Real.logb 2 (1 - y + y / d) + ((d : ℝ) - 1) * (y / d * Real.logb 2 (y / d))) -
        ∑ b, (∑ a, q a * randomizing y a b) * Real.logb 2 (∑ a, q a * randomizing y a b) := by
  unfold mutualInfoBits
  simp only
  have hrow : ∀ a, ∑ b', q a * randomizing y a b' = q a := by
    intro a; rw [← Finset.mul_sum, g74e_R_row hd, mul_one]
  simp only [hrow]
  have hle : ∀ a b, q a * randomizing y a b ≤ ∑ a', q a' * randomizing y a' b := by
    intro a b
    exact Finset.single_le_sum (f := fun a' => q a' * randomizing y a' b)
      (fun a' _ => mul_nonneg (hq0 a') (g74e_R_nonneg y hy0 hy1 a' b)) (Finset.mem_univ a)
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    g74e_term _ _ _ (hq0 a) (g74e_R_nonneg y hy0 hy1 a b) (hle a b)))]
  simp only [Finset.sum_sub_distrib]
  congr 1
  · have hc : ∀ a : Fin d, ∑ b, q a * randomizing y a b * Real.logb 2 (randomizing y a b) =
        q a * ((1 - y + y / d) * Real.logb 2 (1 - y + y / d) + ((d : ℝ) - 1) * (y / d * Real.logb 2 (y / d))) := by
      intro a
      have : ∀ b, q a * randomizing y a b * Real.logb 2 (randomizing y a b) =
          q a * (y / d * Real.logb 2 (y / d)) + (if a = b then q a * ((1 - y + y / d) *
            Real.logb 2 (1 - y + y / d) - y / d * Real.logb 2 (y / d)) else 0) := by
        intro b; rw [g74e_R_eq]; split_ifs <;> ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    simp only [hc, ← Finset.sum_mul, hq1, one_mul]
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun b _ => by rw [Finset.sum_mul])

theorem g74e_kcap {d : ℕ} (hd : 0 < d) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hst : QAlgorithms.Papers.Independent.Frontier30.P12.IsStochastic
      (randomizing y : Fin d → Fin d → ℝ)) :
    kernelCapacity (randomizing y : Fin d → Fin d → ℝ) = Real.logb 2 d +
      ((1 - y + y / d) * Real.logb 2 (1 - y + y / d) + ((d : ℝ) - 1) * (y / d * Real.logb 2 (y / d))) := by
  unfold kernelCapacity
  rw [dif_pos hst]
  unfold QAlgorithms.Papers.Independent.Dependency50.P45.shannonCapacity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨fun _ => 1 / d, fun _ => by positivity, ?_, ?_⟩
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · show _ = mutualInfoBits (fun xy : Fin d × Fin d => 1 / (d : ℝ) * randomizing y xy.1 xy.2)
      rw [g74e_mi_eq hd y hy0 hy1 (fun _ => 1 / (d : ℝ)) (fun _ => by positivity) (by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp)]
      have hcol : ∀ b : Fin d, ∑ a, 1 / (d : ℝ) * randomizing y a b = 1 / d := by
        intro b; rw [← Finset.mul_sum, g74e_R_col hd, mul_one]
      simp only [hcol, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [one_div, Real.logb_inv]
      field_simp
      ring
  · rintro v ⟨q, hq0, hq1, rfl⟩
    show mutualInfoBits (fun xy : Fin d × Fin d => q xy.1 * randomizing y xy.1 xy.2) ≤ _
    rw [g74e_mi_eq hd y hy0 hy1 q hq0 hq1]
    have := g74e_ent_le hd (fun b => ∑ a, q a * randomizing y a b)
      (fun b => Finset.sum_nonneg (fun a _ => mul_nonneg (hq0 a) (g74e_R_nonneg y hy0 hy1 a b)))
      (by rw [Finset.sum_comm]; simp only [← Finset.mul_sum, g74e_R_row hd, mul_one, hq1])
    linarith

/-- PDF p.2, Eq.(2): actual common-random-basis simulator, integrability and
its particular forward cost. No minimum over all simulators is asserted. -/
theorem solution (d : ℕ) (hd : 2 ≤ d) (x : ℝ)
    (hx0 : (d:ℝ)/(d+1) ≤ x) (hx1 : x ≤ 1) :
    let P : Fin d → Fin d → ℝ := randomizing (((d:ℝ)+1)*x-d)
    IsStochastic P ∧
    (∀ X : Matrix (Fin d) (Fin d) ℂ,
      Integrable (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
        ∑ i, ∑ j, ((P i j : ℂ) * (basisProjector U i * X).trace) • basisProjector U j)
        (Schur.unitaryHaar d)) ∧
    measurePrepare d P = QuditFidelity.depolarizingMap d (by omega) x ∧
    kernelCapacity P = Real.logb 2 d - symmetricEntropy d ((d:ℝ)-x*(d-(d:ℝ)⁻¹)) := by
  intro P
  have hd0 : 0 < d := by omega
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hy0 : 0 ≤ ((d:ℝ)+1)*x-d := by
    rw [div_le_iff₀ (by positivity)] at hx0; nlinarith
  have hy1 : ((d:ℝ)+1)*x-d ≤ 1 := by nlinarith
  have hstoch : IsStochastic P := by
    intro a
    exact ⟨fun b => g74e_R_nonneg _ hy0 hy1 a b, g74e_R_row hd0 _ a⟩
  refine ⟨hstoch, fun X => (g74e_mp_cont P X).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _), ?_, ?_⟩
  · funext X
    exact g74e_mp_eq (by omega) x X
  show kernelCapacity (randomizing (((d:ℝ)+1)*x-d) : Fin d → Fin d → ℝ) = _
  rw [g74e_kcap hd0 _ hy0 hy1 hstoch]
  have hdne : (d : ℝ) ≠ 0 := by positivity
  have hp : (d:ℝ) - x*(d - (d:ℝ)⁻¹) = 1 - (((d:ℝ)+1)*x-d) + (((d:ℝ)+1)*x-d) / d := by
    field_simp; ring
  rw [hp]
  unfold symmetricEntropy
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hcast]
  have h1 : (1 - (1 - (((d:ℝ)+1)*x-d) + (((d:ℝ)+1)*x-d) / d)) = ((d:ℝ) - 1) * ((((d:ℝ)+1)*x-d) / d) := by
    field_simp; ring
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  rw [h1, mul_div_cancel_left₀ _ hd1]
  ring



end
