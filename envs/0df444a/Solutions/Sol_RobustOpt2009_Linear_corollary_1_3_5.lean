-- Prove2me | solution 1 for RobustOpt2009.Linear.corollary_1_3_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:11:59.07771+00:00
-- url     : https://prove2.me/submissions/cafedacc-ac9c-4fc3-864c-a966d15ff4cb

import Mathlib
import Definitions.Def_RobustOpt2009_Linear_Model
import Theorems.Thm_LinearOptimization_farkas_inequality_form_fintype

open Matrix
open scoped BigOperators Pointwise



namespace X8RL
open RobustOpt2009.Linear

/-- dual cone over an arbitrary finite index type -/
def x8dual {ι : Type} [Fintype ι] (K : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {l | ∀ a ∈ K, 0 ≤ l ⬝ᵥ a}

/-- convex cone over an arbitrary finite index type -/
def x8IsCone {ι : Type} (K : Set (ι → ℝ)) : Prop :=
  K.Nonempty ∧ (∀ a ∈ K, ∀ a' ∈ K, a + a' ∈ K) ∧ (∀ a ∈ K, ∀ t : ℝ, 0 ≤ t → t • a ∈ K)

lemma x8_val_dot {ι : Type} [Fintype ι] {L u : ℕ} (R : Lift (ι) L u) (y : ι → ℝ) (z : Fin L → ℝ)
    (v : Fin u → ℝ) :
    y ⬝ᵥ R.value z v = ∑ l, z l * (y ⬝ᵥ R.P l) + ∑ j, v j * (y ⬝ᵥ R.Q j) + y ⬝ᵥ R.p := by
  simp only [Lift.value, dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i l => y i * (z l * R.P l i)),
    Finset.sum_comm (f := fun i j => y i * (v j * R.Q j i))]
  congr 2
  · exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  · exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

lemma x8_lin_zero {a b β : ℝ} (h : ∀ t : ℝ, t * a + b ≤ β) : a = 0 := by
  by_contra ha
  have := h ((β - b + 1) / a)
  rw [div_mul_cancel₀ _ ha] at this
  linarith

/-- an affine upper bound in `(z, v)` gives a certificate -/
lemma x8_cert {ι : Type} [Fintype ι] [DecidableEq ι] {n L u : ℕ} (D : Data n L) (R : Lift (ι) L u) (C : Set (ι → ℝ))
    (x : Fin n → ℝ) (y : ι → ℝ) (hyC : y ∈ C)
    (hy : ∀ z v, ∑ l, z l * (D.a l ⬝ᵥ x - D.b l) + y ⬝ᵥ R.value z v ≤ D.b0 - D.a0 ⬝ᵥ x) :
    Certificate D R C x y := by
  classical
  have hv := fun z v => (x8_val_dot R y z v ▸ hy z v)
  refine ⟨?_, ?_, ?_, hyC⟩
  · have := hv 0 0
    simp at this
    rw [dotProduct_comm]
    linarith
  · intro j
    have h := x8_lin_zero (a := y ⬝ᵥ R.Q j) (b := y ⬝ᵥ R.p) (β := D.b0 - D.a0 ⬝ᵥ x) (fun t => by
      have := hv 0 (Pi.single j t)
      simpa [Pi.single_apply] using this)
    rw [dotProduct_comm]; exact h
  · intro l
    have h := x8_lin_zero (a := (D.a l ⬝ᵥ x - D.b l) + y ⬝ᵥ R.P l) (b := y ⬝ᵥ R.p)
      (β := D.b0 - D.a0 ⬝ᵥ x) (fun t => by
      have := hv (Pi.single l t) 0
      simp [Pi.single_apply] at this
      linarith)
    rw [dotProduct_comm]; linarith

/-- weak duality direction -/
lemma x8_weak {ι : Type} [Fintype ι] [DecidableEq ι] {n L u : ℕ} (D : Data n L) (R : Lift (ι) L u) (K : Set (ι → ℝ))
    (x : Fin n → ℝ) (y : ι → ℝ)
    (hc : Certificate D R (x8dual K) x y) :
    Robust D (R.set K) x := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  rintro z ⟨v, hzv⟩
  have h0 := h4 _ hzv
  rw [x8_val_dot] at h0
  have hQ : ∑ j, v j * (y ⬝ᵥ R.Q j) = 0 :=
    Finset.sum_eq_zero (fun j _ => by rw [dotProduct_comm, h2 j, mul_zero])
  have hP : ∑ l, z l * (y ⬝ᵥ R.P l) = ∑ l, z l * D.b l - ∑ l, z l * (D.a l ⬝ᵥ x) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have := h3 l
    rw [dotProduct_comm] at this
    rw [← mul_sub]; congr 1; linarith
  rw [dotProduct_comm] at h1
  linarith

end X8RL



namespace X8RL
open RobustOpt2009.Linear ModernConvex.ConicDuality

lemma x8_rob {ι : Type} [Fintype ι] [DecidableEq ι] {n L u : ℕ} (D : Data n L) (R : Lift (ι) L u) (K : Set (ι → ℝ))
    (x : Fin n → ℝ) (hrob : Robust D (R.set K) x) (z : Fin L → ℝ) (v : Fin u → ℝ)
    (hzv : R.value z v ∈ K) :
    ∑ l, z l * (D.a l ⬝ᵥ x - D.b l) ≤ D.b0 - D.a0 ⬝ᵥ x := by
  have := hrob z ⟨v, hzv⟩
  simp only [mul_sub, Finset.sum_sub_distrib]
  linarith

lemma x8_convex {ι : Type} [Fintype ι] [DecidableEq ι] {K : Set (ι → ℝ)} (hK : x8IsCone K) : Convex ℝ K := by
  intro a ha b hb s t hs ht _
  exact hK.2.1 _ (hK.2.2 a ha s hs) _ (hK.2.2 b hb t ht)

lemma x8_add_int {ι : Type} [Fintype ι] [DecidableEq ι] {K : Set (ι → ℝ)} (hK : x8IsCone K) {k k1 : ι → ℝ}
    (hk : k ∈ K) (hk1 : k1 ∈ interior K) : k + k1 ∈ interior K := by
  have hsub : (fun w => k + w) '' interior K ⊆ K := by
    rintro _ ⟨w, hw, rfl⟩
    exact hK.2.1 _ hk _ (interior_subset hw)
  have hopen : IsOpen ((fun w => k + w) '' interior K) :=
    (Homeomorph.addLeft k).isOpenMap _ isOpen_interior
  exact interior_maximal hsub hopen ⟨k1, hk1, rfl⟩

lemma x8_smul_int {ι : Type} [Fintype ι] [DecidableEq ι] {K : Set (ι → ℝ)} (hK : x8IsCone K) {k : ι → ℝ}
    (hk : k ∈ interior K) {ε : ℝ} (hε : 0 < ε) : ε • k ∈ interior K := by
  have hK' : ε • K = K := by
    ext y
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hK.2.2 w hw ε hε.le
    · intro hy
      refine ⟨ε⁻¹ • y, hK.2.2 y hy _ (inv_nonneg.2 hε.le), ?_⟩
      rw [smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
  rw [← hK', interior_smul₀ hε.ne']
  exact Set.smul_mem_smul_set hk

lemma x8_repr {ι : Type} [Fintype ι] [DecidableEq ι] (f : StrongDual ℝ ((ι → ℝ) × ℝ)) (k : ι → ℝ) (r : ℝ) :
    f (k, r) = (fun i => f (Pi.single i 1, 0)) ⬝ᵥ k + r * f (0, 1) := by
  have : ((k, r) : (ι → ℝ) × ℝ) =
      ∑ i, k i • ((Pi.single i 1 : ι → ℝ), (0 : ℝ)) + r • ((0 : ι → ℝ), (1 : ℝ)) := by
    refine Prod.ext ?_ ?_
    · funext j
      simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  rw [this, map_add, map_sum, map_smul]
  simp only [map_smul, smul_eq_mul, dotProduct]
  congr 1
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

lemma x8_slater {ι : Type} [Fintype ι] [DecidableEq ι] {n L u : ℕ} (D : Data n L) (R : Lift (ι) L u) (K : Set (ι → ℝ))
    (hcone : x8IsCone K) (hs : ∃ z v, R.value z v ∈ interior K)
    (x : Fin n → ℝ) (hrob : Robust D (R.set K) x) :
    ∃ y ∈ x8dual K, ∀ z v, ∑ l, z l * (D.a l ⬝ᵥ x - D.b l) + y ⬝ᵥ R.value z v ≤
      D.b0 - D.a0 ⬝ᵥ x := by
  set c : Fin L → ℝ := fun l => D.a l ⬝ᵥ x - D.b l with hc
  set β := D.b0 - D.a0 ⬝ᵥ x with hβ
  have hconv := x8_convex hcone
  obtain ⟨k0, hk0⟩ : (interior K).Nonempty := by
    obtain ⟨z, v, h⟩ := hs
    exact ⟨_, h⟩
  let S : Set ((ι → ℝ) × ℝ) := interior K ×ˢ Set.Ioi β
  let T : Set ((ι → ℝ) × ℝ) :=
    Set.range (fun p : (Fin L → ℝ) × (Fin u → ℝ) => (R.value p.1 p.2, ∑ l, p.1 l * c l))
  have hS1 : Convex ℝ S := hconv.interior.prod (convex_Ioi β)
  have hS2 : IsOpen S := isOpen_interior.prod isOpen_Ioi
  have hT : Convex ℝ T := by
    rintro _ ⟨⟨z1, v1⟩, rfl⟩ _ ⟨⟨z2, v2⟩, rfl⟩ a b _ _ hab
    refine ⟨(a • z1 + b • z2, a • v1 + b • v2), ?_⟩
    refine Prod.ext ?_ ?_
    · funext i
      simp only [Lift.value, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Prod.fst_add,
        Prod.smul_fst, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
      linear_combination (-R.p i) * hab
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Prod.snd_add, Prod.smul_snd, add_mul,
        Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  have hdisj : Disjoint S T := by
    rw [Set.disjoint_left]
    rintro ⟨k, r⟩ ⟨hk, hr⟩ ⟨⟨z, v⟩, heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    have := x8_rob D R K x hrob z v (h1 ▸ interior_subset hk)
    simp only [Set.mem_Ioi] at hr
    rw [← h2] at hr
    exact absurd this (not_le.2 hr)
  obtain ⟨f, u0, hA, hB⟩ := geometric_hahn_banach_open hS1 hS2 hT hdisj
  set y' : ι → ℝ := fun i => f (Pi.single i 1, 0)
  set μ := f (0, 1)
  have hA' : ∀ k ∈ interior K, ∀ r, β < r → y' ⬝ᵥ k + r * μ < u0 := by
    intro k hk r hr
    rw [← x8_repr]
    exact hA _ ⟨hk, hr⟩
  have hB' : ∀ z v, u0 ≤ y' ⬝ᵥ R.value z v + (∑ l, z l * c l) * μ := by
    intro z v
    rw [← x8_repr]
    exact hB _ ⟨(z, v), rfl⟩
  -- μ ≤ 0
  have hμ0 : μ ≤ 0 := by
    by_contra h
    push Not at h
    have := hA' k0 hk0 (max (β + 1) ((u0 - y' ⬝ᵥ k0) / μ)) (by
      exact lt_of_lt_of_le (by linarith) (le_max_left _ _))
    have h2 : (u0 - y' ⬝ᵥ k0) / μ * μ ≤ max (β + 1) ((u0 - y' ⬝ᵥ k0) / μ) * μ :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) h.le
    rw [div_mul_cancel₀ _ h.ne'] at h2
    linarith
  -- μ ≠ 0 (Slater)
  have hμ : μ < 0 := by
    refine lt_of_le_of_ne hμ0 (fun h => ?_)
    obtain ⟨z, v, hzv⟩ := hs
    have h1 := hA' _ hzv (β + 1) (by linarith)
    have h2 := hB' z v
    rw [h] at h1 h2
    linarith
  -- y' ≤ 0 on K
  have hyK : ∀ k ∈ K, y' ⬝ᵥ k ≤ 0 := by
    intro k hk
    by_contra h
    push Not at h
    set M := u0 - y' ⬝ᵥ k0 - (β + 1) * μ
    have ht : 0 < (|M| + 1) / (y' ⬝ᵥ k) := div_pos (by positivity) h
    have := hA' _ (x8_add_int hcone (hcone.2.2 k hk _ ht.le) hk0) (β + 1) (by linarith)
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ h.ne'] at this
    have := le_abs_self M
    linarith
  -- u0 ≥ β μ
  have hu0 : β * μ ≤ u0 := by
    by_contra h
    push Not at h
    set δ := β * μ - u0
    have hδ : 0 < δ := by simp only [δ]; linarith
    set Cc := |y' ⬝ᵥ k0| + |μ| + 1
    have hCc : 0 < Cc := by positivity
    set ε := δ / Cc
    have hε : 0 < ε := div_pos hδ hCc
    have := hA' _ (x8_smul_int hcone hk0 hε) (β + ε) (by linarith)
    rw [dotProduct_smul, smul_eq_mul] at this
    have h1 : -(ε * Cc) ≤ ε * (y' ⬝ᵥ k0) + ε * μ := by
      have := neg_abs_le (y' ⬝ᵥ k0)
      have := neg_abs_le μ
      simp only [Cc]
      nlinarith
    have h2 : ε * Cc = δ := div_mul_cancel₀ _ hCc.ne'
    simp only [δ] at h2
    nlinarith
  refine ⟨μ⁻¹ • y', ?_, ?_⟩
  · intro k hk
    rw [smul_dotProduct, smul_eq_mul]
    exact mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.2 hμ0) (hyK k hk)
  · intro z v
    have h := hB' z v
    rw [smul_dotProduct, smul_eq_mul]
    have hinv : μ⁻¹ < 0 := inv_lt_zero.2 hμ
    have : μ⁻¹ * u0 ≥ μ⁻¹ * (y' ⬝ᵥ R.value z v + (∑ l, z l * c l) * μ) :=
      mul_le_mul_of_nonpos_left h hinv.le
    rw [mul_add, ← mul_assoc, mul_comm μ⁻¹ (∑ l, z l * c l), mul_assoc,
      inv_mul_cancel₀ hμ.ne, mul_one] at this
    have h3 : μ⁻¹ * u0 ≤ μ⁻¹ * (β * μ) := mul_le_mul_of_nonpos_left hu0 hinv.le
    rw [mul_comm β μ, ← mul_assoc, inv_mul_cancel₀ hμ.ne, one_mul] at h3
    linarith

end X8RL



namespace X8RL
open RobustOpt2009.Linear ModernConvex.ConicDuality

lemma x8_poly {ι : Type} [Fintype ι] [DecidableEq ι] {n L u m : ℕ} (D : Data n L) (R : Lift (ι) L u)
    (A : Fin m → ι → ℝ) (K : Set (ι → ℝ)) (hKA : K = {z | ∀ j, 0 ≤ A j ⬝ᵥ z})
    (hne : (R.set K).Nonempty)
    (x : Fin n → ℝ) (hrob : Robust D (R.set K) x) :
    ∃ y ∈ x8dual K, ∀ z v, ∑ l, z l * (D.a l ⬝ᵥ x - D.b l) + y ⬝ᵥ R.value z v ≤
      D.b0 - D.a0 ⬝ᵥ x := by
  classical
  set c : Fin L → ℝ := fun l => D.a l ⬝ᵥ x - D.b l with hc
  set β := D.b0 - D.a0 ⬝ᵥ x with hβ
  let M : Matrix (Fin m) (Fin (L + u)) ℝ := fun j =>
    Fin.append (fun l => -(A j ⬝ᵥ R.P l)) (fun i => -(A j ⬝ᵥ R.Q i))
  let bv : Fin m → ℝ := fun j => A j ⬝ᵥ R.p
  let cv : Fin (L + u) → ℝ := Fin.append c 0
  let zw : (Fin (L + u) → ℝ) → Fin L → ℝ := fun w l => w (Fin.castAdd u l)
  let vw : (Fin (L + u) → ℝ) → Fin u → ℝ := fun w i => w (Fin.natAdd L i)
  have hM : ∀ w j, (M *ᵥ w) j = A j ⬝ᵥ R.p - A j ⬝ᵥ R.value (zw w) (vw w) := by
    intro w j
    rw [x8_val_dot]
    simp only [M, mulVec, dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right, zw, vw]
    simp only [neg_mul, Finset.sum_neg_distrib]
    rw [show (∑ x, A j x * R.p x) = A j ⬝ᵥ R.p from rfl]
    have e1 : ∑ i : Fin L, (A j ⬝ᵥ R.P i) * w (Fin.castAdd u i) =
        ∑ l, w (Fin.castAdd u l) * (A j ⬝ᵥ R.P l) :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    have e2 : ∑ i : Fin u, (A j ⬝ᵥ R.Q i) * w (Fin.natAdd L i) =
        ∑ i, w (Fin.natAdd L i) * (A j ⬝ᵥ R.Q i) :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    simp only [dotProduct] at e1 e2 ⊢
    rw [e1, e2]
    ring
  have hcv : ∀ w, cv ⬝ᵥ w = ∑ l, zw w l * c l := by
    intro w
    simp only [cv, dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right, zw,
      Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hmemK : ∀ w, M *ᵥ w ≤ bv → R.value (zw w) (vw w) ∈ K := by
    intro w hw
    rw [hKA]
    intro j
    have := hw j
    rw [hM] at this
    simp only [bv] at this
    linarith
  have hfeas : ∃ w : Fin (L + u) → ℝ, M *ᵥ w ≤ bv := by
    obtain ⟨z, v, hzv⟩ := hne
    refine ⟨Fin.append z v, fun j => ?_⟩
    rw [hM]
    have hz : zw (Fin.append z v) = z := by funext l; simp [zw]
    have hv : vw (Fin.append z v) = v := by funext i; simp [vw]
    rw [hz, hv]
    rw [hKA] at hzv
    have := hzv j
    simp only [bv]
    linarith
  have hfar := (LinearOptimization.farkas_inequality_form_fintype M bv cv β hfeas).1 (by
    intro w hw
    rw [hcv]
    exact x8_rob D R K x hrob _ _ (hmemK w hw))
  obtain ⟨p, hp0, hpM, hpb⟩ := hfar
  refine ⟨∑ j, p j • A j, ?_, ?_⟩
  · intro k hk
    rw [hKA] at hk
    rw [sum_dotProduct]
    exact Finset.sum_nonneg (fun j _ => by
      rw [smul_dotProduct, smul_eq_mul]; exact mul_nonneg (hp0 j) (hk j))
  · intro z v
    have hz : zw (Fin.append z v) = z := by funext l; simp [zw]
    have hv : vw (Fin.append z v) = v := by funext i; simp [vw]
    have h1 : cv ⬝ᵥ Fin.append z v = p ⬝ᵥ (M *ᵥ Fin.append z v) := by
      rw [← hpM, mulVec_transpose, dotProduct_mulVec]
    rw [hcv, hz] at h1
    have h2 : p ⬝ᵥ (M *ᵥ Fin.append z v) = ∑ j, p j * (A j ⬝ᵥ R.p - A j ⬝ᵥ R.value z v) := by
      exact Finset.sum_congr rfl (fun j _ => by rw [hM, hz, hv])
    rw [h2] at h1
    have h3 : (∑ j, p j • A j) ⬝ᵥ R.value z v = ∑ j, p j * (A j ⬝ᵥ R.value z v) := by
      rw [sum_dotProduct]
      exact Finset.sum_congr rfl (fun j _ => by rw [smul_dotProduct, smul_eq_mul])
    have h4 : p ⬝ᵥ bv = ∑ j, p j * (A j ⬝ᵥ R.p) := rfl
    rw [h3, h1]
    have : ∑ j, p j * (A j ⬝ᵥ R.p - A j ⬝ᵥ R.value z v) + ∑ j, p j * (A j ⬝ᵥ R.value z v) =
        ∑ j, p j * (A j ⬝ᵥ R.p) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    linarith

end X8RL



namespace X8RL
open RobustOpt2009.Linear ModernConvex.ConicDuality

lemma x8_feas_iff {ι : Type} [Fintype ι] {n L u : ℕ} (D : Data n L) (R : Lift ι L u)
    (C : Set (ι → ℝ)) (x : Fin n → ℝ) (y : ι → ℝ) :
    (reformulation D R C).Feasible x y ↔ Certificate D R C x y := by
  simp only [ExplicitSystem.Feasible, Certificate, reformulation, Fin.forall_fin_add,
    Fin.addCases_left, Fin.addCases_right, zero_dotProduct, zero_add]
  constructor
  · rintro ⟨h1, ⟨h2, h3⟩, h4⟩
    exact ⟨by linarith, h2, fun l => by linarith [h3 l], h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by linarith, ⟨h2, fun l => by linarith [h3 l]⟩, h4⟩

lemma x8_size {n L u : ℕ} (s : ConeShape) (D : Data n L) (R : Lift s.Index L u) :
    outputSize s D R ≤ 4 * (inputSize s D R) ^ 2 := by
  simp only [outputSize, inputSize, ExplicitSystem.coefficientCount]
  generalize Fintype.card s.Index = N
  generalize s.coneSize = q
  set I := 1 + n + L + u + N + (L + 1) * (n + 1) + (L + u + 1) * N + q with hI
  have h1 : u + L + 1 ≤ I := by omega
  have h2 : n + N + 1 ≤ I := by omega
  have h3 : n + N + q ≤ I := by omega
  have h4 : (u + L + 1) * (n + N + 1) ≤ I * I := Nat.mul_le_mul h1 h2
  have h5 : I ≤ I * I := Nat.le_mul_self I
  nlinarith

/-- generic forward step -/
lemma x8_fwd {ι : Type} [Fintype ι] [DecidableEq ι] {n L u : ℕ} (D : Data n L) (R : Lift ι L u)
    (K' C : Set (ι → ℝ)) (x : Fin n → ℝ)
    (h : ∃ y ∈ x8dual K', ∀ z v, ∑ l, z l * (D.a l ⬝ᵥ x - D.b l) + y ⬝ᵥ R.value z v ≤
      D.b0 - D.a0 ⬝ᵥ x)
    (hd : ∀ y ∈ x8dual K', y ∈ C) : ∃ y, Certificate D R C x y := by
  obtain ⟨y, hy, hb⟩ := h
  exact ⟨y, x8_cert D R C x y (hd y hy) hb⟩

/-! ## Euclidean-norm facts -/

lemma x8_cs {d : ℕ} (a b : Fin d → ℝ) :
    |∑ j, a j * b j| ≤ Real.sqrt (∑ j, a j ^ 2) * Real.sqrt (∑ j, b j ^ 2) := by
  rw [← Real.sqrt_mul (Finset.sum_nonneg (fun j _ => sq_nonneg (a j)))]
  exact Real.abs_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)

lemma x8_tri {d : ℕ} (a b : Fin d → ℝ) :
    Real.sqrt (∑ j, (a j + b j) ^ 2) ≤ Real.sqrt (∑ j, a j ^ 2) + Real.sqrt (∑ j, b j ^ 2) := by
  have hA := Real.sqrt_nonneg (∑ j, a j ^ 2)
  have hB := Real.sqrt_nonneg (∑ j, b j ^ 2)
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 := x8_cs a b
  have hA2 := Real.sq_sqrt (Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg (a j)))
  have hB2 := Real.sq_sqrt (Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg (b j)))
  have : ∑ j, (a j + b j) ^ 2 = ∑ j, a j ^ 2 + ∑ j, b j ^ 2 + 2 * ∑ j, a j * b j := by
    simp only [add_sq, Finset.sum_add_distrib, Finset.mul_sum]
    ring_nf
  rw [this]
  nlinarith [le_abs_self (∑ j, a j * b j)]

lemma x8_scal {d : ℕ} (a : Fin d → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (∑ j, (t * a j) ^ 2) = t * Real.sqrt (∑ j, a j ^ 2) := by
  have : ∑ j, (t * a j) ^ 2 = t ^ 2 * ∑ j, a j ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [this, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]

/-! ## Orthant -/

lemma x8_orthant {n L u N : ℕ} (D : Data n L) (R : Lift (Fin N) L u)
    (hne : (R.set {y : Fin N → ℝ | ∀ i, 0 ≤ y i}).Nonempty) (x : Fin n → ℝ) :
    Robust D (R.set {y : Fin N → ℝ | ∀ i, 0 ≤ y i}) x ↔
      ∃ y, Certificate D R {y : Fin N → ℝ | ∀ i, 0 ≤ y i} x y := by
  classical
  have hKA : {y : Fin N → ℝ | ∀ i, 0 ≤ y i} =
      {z | ∀ j, 0 ≤ (Pi.single j 1 : Fin N → ℝ) ⬝ᵥ z} := by
    ext z; simp [single_dotProduct]
  constructor
  · intro hrob
    refine x8_fwd D R _ _ x (x8_poly D R _ _ hKA hne x hrob) (fun y hy i => ?_)
    have := hy (Pi.single i 1) (by intro j; simp [Pi.single_apply]; split_ifs <;> norm_num)
    simpa [dotProduct_single] using this
  · rintro ⟨y, h1, h2, h3, h4⟩
    refine x8_weak D R _ x y ⟨h1, h2, h3, fun a ha => ?_⟩
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (h4 i) (ha i))

/-! ## Lorentz -/

section Lorentz
variable {m : ℕ} {d : Fin m → ℕ}

/-- the product of Lorentz cones on the sigma index type -/
def x8LK (m : ℕ) (d : Fin m → ℕ) : Set (((s : Fin m) × Option (Fin (d s))) → ℝ) :=
  {y | ∀ s, Real.sqrt (∑ j, (y ⟨s, some j⟩) ^ 2) ≤ y ⟨s, none⟩}

lemma x8_lor_dot [inst : Fintype ((s : Fin m) × Option (Fin (d s)))]
    (y k : ((s : Fin m) × Option (Fin (d s))) → ℝ) :
    y ⬝ᵥ k = ∑ s, (y ⟨s, none⟩ * k ⟨s, none⟩ + ∑ j, y ⟨s, some j⟩ * k ⟨s, some j⟩) := by
  obtain rfl : inst = Sigma.instFintype := Subsingleton.elim _ _
  simp only [dotProduct, Fintype.sum_sigma, Fintype.sum_option]

lemma x8_lor_cone : x8IsCone (x8LK m d) := by
  refine ⟨⟨0, fun s => by simp⟩, ?_, ?_⟩
  · intro a ha b hb s
    exact le_trans (x8_tri (fun j => a ⟨s, some j⟩) (fun j => b ⟨s, some j⟩))
      (add_le_add (ha s) (hb s))
  · intro a ha t ht s
    have := x8_scal (fun j => a ⟨s, some j⟩) ht
    simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this]
    exact mul_le_mul_of_nonneg_left (ha s) ht

lemma x8_lor_int (y : ((s : Fin m) × Option (Fin (d s))) → ℝ)
    (hy : ∀ s, Real.sqrt (∑ j, (y ⟨s, some j⟩) ^ 2) < y ⟨s, none⟩) :
    y ∈ interior (x8LK m d) := by
  have hsub : {y : ((s : Fin m) × Option (Fin (d s))) → ℝ |
      ∀ s, Real.sqrt (∑ j, (y ⟨s, some j⟩) ^ 2) < y ⟨s, none⟩} ⊆ interior (x8LK m d) := by
    apply interior_maximal
    · intro y hy s
      exact (hy s).le
    · have : {y : ((s : Fin m) × Option (Fin (d s))) → ℝ |
          ∀ s, Real.sqrt (∑ j, (y ⟨s, some j⟩) ^ 2) < y ⟨s, none⟩} =
          ⋂ s, {y | Real.sqrt (∑ j, (y ⟨s, some j⟩) ^ 2) < y ⟨s, none⟩} := by
        ext y; simp
      rw [this]
      refine isOpen_iInter_of_finite (fun s => isOpen_lt ?_ (continuous_apply _))
      exact (continuous_finsetSum _ (fun j _ => (continuous_apply (⟨s, some j⟩ :
        (s : Fin m) × Option (Fin (d s)))).pow 2)).sqrt
  exact hsub hy

lemma x8_lor_sub_dual [Fintype ((s : Fin m) × Option (Fin (d s)))] :
    ∀ y ∈ x8LK m d, y ∈ x8dual (x8LK m d) := by
  intro y hy k hk
  rw [x8_lor_dot]
  refine Finset.sum_nonneg (fun s _ => ?_)
  have h1 := x8_cs (fun j => y ⟨s, some j⟩) (fun j => k ⟨s, some j⟩)
  have hy' : Real.sqrt (∑ j, (y ⟨s, some j⟩) ^ 2) ≤ y ⟨s, none⟩ := hy s
  have hk' : Real.sqrt (∑ j, (k ⟨s, some j⟩) ^ 2) ≤ k ⟨s, none⟩ := hk s
  have := mul_le_mul hy' hk' (Real.sqrt_nonneg _) (le_trans (Real.sqrt_nonneg _) hy')
  have := neg_abs_le (∑ j, y ⟨s, some j⟩ * k ⟨s, some j⟩)
  linarith

lemma x8_lor_dual_sub [Fintype ((s : Fin m) × Option (Fin (d s)))] :
    ∀ y ∈ x8dual (x8LK m d), y ∈ x8LK m d := by
  classical
  intro y hy s
  set w : Fin (d s) → ℝ := fun j => y ⟨s, some j⟩
  set r := Real.sqrt (∑ j, w j ^ 2) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  -- test vector 1
  let k1 : ((s : Fin m) × Option (Fin (d s))) → ℝ := fun p =>
    if p.1 = s then (match p.2 with | none => 1 | some _ => 0) else 0
  have hk1 : k1 ∈ x8LK m d := by
    intro s'
    by_cases h : s' = s
    · subst h; simp [k1]
    · simp [k1, h]
  have t1 := hy k1 hk1
  rw [x8_lor_dot, Finset.sum_eq_single s (fun b _ hb => by simp [k1, hb]) (by simp)] at t1
  simp [k1] at t1
  -- test vector 2
  let k2 : ((s : Fin m) × Option (Fin (d s))) → ℝ := fun p =>
    if p.1 = s then (match p.2 with | none => r | some _ => -y p) else 0
  have hk2 : k2 ∈ x8LK m d := by
    intro s'
    by_cases h : s' = s
    · subst h
      simp only [k2, if_true]
      simp only [neg_sq]
      exact le_rfl
    · simp [k2, h]
  have t2 := hy k2 hk2
  rw [x8_lor_dot, Finset.sum_eq_single s (fun b _ hb => by simp [k2, hb]) (by simp)] at t2
  simp only [k2, if_true] at t2
  have hsq : ∑ j, y ⟨s, some j⟩ * -y ⟨s, some j⟩ = -(r ^ 2) := by
    rw [hr, Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j _ => by simp only [w]; ring)
  rw [hsq] at t2
  show r ≤ y ⟨s, none⟩
  rcases hr0.lt_or_eq with hpos | hzero
  · nlinarith
  · rw [← hzero]; linarith

end Lorentz

end X8RL



namespace X8RL
open RobustOpt2009.Linear

section PSD
variable {k : ℕ}

def x8mat (y : Fin k × Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ := fun i j => y (i, j)
noncomputable def x8sym (y : Fin k × Fin k → ℝ) : Fin k × Fin k → ℝ := fun p => (y p + y (p.2, p.1)) / 2
def x8qf (M : Matrix (Fin k) (Fin k) ℝ) (x : Fin k → ℝ) : ℝ := ∑ i, ∑ j, x i * M i j * x j

lemma x8_qf_eq (M : Matrix (Fin k) (Fin k) ℝ) (x : Fin k → ℝ) :
    star x ⬝ᵥ (M *ᵥ x) = x8qf M x := by
  simp [x8qf, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

lemma x8_psd_iff (M : Matrix (Fin k) (Fin k) ℝ) :
    M.PosSemidef ↔ (∀ i j, M i j = M j i) ∧ ∀ x, 0 ≤ x8qf M x := by
  rw [posSemidef_iff_dotProduct_mulVec]
  have h1 : M.IsHermitian ↔ ∀ i j, M i j = M j i := by
    constructor
    · intro h i j
      simpa [conjTranspose_apply] using (congrFun (congrFun h i) j).symm
    · intro h
      ext i j
      rw [conjTranspose_apply, star_trivial, h j i]
  rw [h1]
  simp only [x8_qf_eq]

lemma x8_pd (M : Matrix (Fin k) (Fin k) ℝ) (hM : M.PosDef) :
    ∀ x, x ≠ 0 → 0 < x8qf M x := by
  intro x hx
  rw [← x8_qf_eq]
  exact (posDef_iff_dotProduct_mulVec.1 hM).2 hx

lemma x8_pdot [inst : Fintype (Fin k × Fin k)] (y z : Fin k × Fin k → ℝ) :
    y ⬝ᵥ z = ∑ i, ∑ j, y (i, j) * z (i, j) := by
  obtain rfl : inst = instFintypeProd _ _ := Subsingleton.elim _ _
  simp [dotProduct, Fintype.sum_prod_type]

def x8PK (k : ℕ) : Set (Fin k × Fin k → ℝ) := {y | (x8mat y).PosSemidef}
def x8KP (k : ℕ) : Set (Fin k × Fin k → ℝ) := {y | (x8mat (x8sym y)).PosSemidef}

lemma x8_KP_cone : x8IsCone (x8KP k) := by
  refine ⟨⟨0, ?_⟩, ?_, ?_⟩
  · show (x8mat (x8sym 0)).PosSemidef
    have : x8mat (x8sym (0 : Fin k × Fin k → ℝ)) = 0 := by
      ext i j; simp [x8mat, x8sym]
    rw [this]; exact PosSemidef.zero
  · intro a ha b hb
    show (x8mat (x8sym (a + b))).PosSemidef
    have : x8mat (x8sym (a + b)) = x8mat (x8sym a) + x8mat (x8sym b) := by
      ext i j; simp [x8mat, x8sym]; ring
    rw [this]; exact ha.add hb
  · intro a ha t ht
    show (x8mat (x8sym (t • a))).PosSemidef
    have : x8mat (x8sym (t • a)) = t • x8mat (x8sym a) := by
      ext i j; simp [x8mat, x8sym]; ring
    rw [this]; exact ha.smul ht

lemma x8_sym_of {y : Fin k × Fin k → ℝ} (hy : ∀ i j, y (i, j) = y (j, i)) : x8sym y = y := by
  funext p
  obtain ⟨i, j⟩ := p
  simp only [x8sym]
  rw [← hy i j]; ring

lemma x8_KP_dual [Fintype (Fin k × Fin k)] : ∀ y ∈ x8dual (x8KP k), y ∈ x8PK k := by
  classical
  intro y hy
  show (x8mat y).PosSemidef
  rw [x8_psd_iff]
  constructor
  · intro i j
    let k1 : Fin k × Fin k → ℝ := Pi.single (i, j) 1 - Pi.single (j, i) 1
    have hk1 : ∀ a b, k1 (a, b) + k1 (b, a) = 0 := by
      intro a b
      simp only [k1, Pi.sub_apply, Pi.single_apply, Prod.mk.injEq]
      by_cases h1 : a = i <;> by_cases h2 : b = j <;> by_cases h3 : a = j <;>
        by_cases h4 : b = i <;> simp_all
    have hs : x8sym k1 = 0 := by
      funext p; obtain ⟨a, b⟩ := p
      simp only [x8sym, Pi.zero_apply]
      rw [hk1 a b]; simp
    have hmem : ∀ t : ℝ, t • k1 ∈ x8KP k := by
      intro t
      show (x8mat (x8sym (t • k1))).PosSemidef
      have : x8mat (x8sym (t • k1)) = 0 := by
        ext a b
        have := congrFun hs (a, b)
        simp only [x8sym, Pi.zero_apply] at this
        simp only [x8mat, x8sym, Pi.smul_apply, smul_eq_mul, Matrix.zero_apply]
        rw [show t * k1 (a, b) + t * k1 (b, a) = t * (k1 (a, b) + k1 (b, a)) by ring, hk1 a b]
        simp
      rw [this]; exact PosSemidef.zero
    have e : ∀ t : ℝ, y ⬝ᵥ (t • k1) = t * (y (i, j) - y (j, i)) := by
      intro t
      simp only [k1, dotProduct_smul, dotProduct_sub, dotProduct_single, mul_one, smul_eq_mul]
    have h1 := hy _ (hmem 1)
    have h2 := hy _ (hmem (-1))
    rw [e] at h1 h2
    show y (i, j) = y (j, i)
    linarith
  · intro x
    let k2 : Fin k × Fin k → ℝ := fun p => x p.1 * x p.2
    have hk2 : k2 ∈ x8KP k := by
      show (x8mat (x8sym k2)).PosSemidef
      rw [x8_psd_iff]
      refine ⟨fun i j => by simp only [x8mat, x8sym, k2]; ring, fun w => ?_⟩
      have : x8qf (x8mat (x8sym k2)) w = (∑ i, w i * x i) ^ 2 := by
        simp only [x8qf, x8mat, x8sym, k2, sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
      rw [this]; positivity
    have := hy k2 hk2
    rw [x8_pdot] at this
    have e : ∑ i, ∑ j, y (i, j) * k2 (i, j) = x8qf (x8mat y) x := by
      simp only [x8qf, x8mat, k2]
      exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
    rw [e] at this
    exact this

lemma x8_PK_sub_dual [Fintype (Fin k × Fin k)] : ∀ y ∈ x8PK k, y ∈ x8dual (x8PK k) := by
  intro y hy z hz
  have h := (x8_psd_iff _).1 (PosSemidef.hadamard hy hz)
  have := h.2 (fun _ => 1)
  rw [x8_pdot]
  simpa [x8qf, x8mat, hadamard_apply] using this

/-- a positive definite form is coercive -/
lemma x8_coercive (M : Matrix (Fin k) (Fin k) ℝ) (hM : ∀ x, x ≠ 0 → 0 < x8qf M x) :
    ∃ c > 0, ∀ x, c * ∑ i, x i ^ 2 ≤ x8qf M x := by
  have hhom : ∀ (t : ℝ) x, x8qf M (t • x) = t ^ 2 * x8qf M x := by
    intro t x
    simp only [x8qf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  have hcont : Continuous (x8qf M) := by
    unfold x8qf
    fun_prop
  set S : Set (Fin k → ℝ) := {x | ∑ i, x i ^ 2 = 1}
  have hnorm : ∀ x : Fin k → ℝ, x ≠ 0 → (Real.sqrt (∑ i, x i ^ 2))⁻¹ • x ∈ S ∧
      0 < Real.sqrt (∑ i, x i ^ 2) := by
    intro x hx
    have hpos : 0 < ∑ i, x i ^ 2 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
      exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi)))
        (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i))
    refine ⟨?_, Real.sqrt_pos.2 hpos⟩
    show ∑ i, ((Real.sqrt (∑ i, x i ^ 2))⁻¹ • x) i ^ 2 = 1
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, inv_pow,
      Real.sq_sqrt hpos.le]
    exact inv_mul_cancel₀ hpos.ne'
  by_cases hS : S.Nonempty
  · have hcomp : IsCompact S := by
      apply Metric.isCompact_of_isClosed_isBounded
      · exact isClosed_eq (by fun_prop) continuous_const
      · refine (Metric.isBounded_closedBall (x := (0 : Fin k → ℝ)) (r := 1)).subset ?_
        intro x hx
        rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
        intro i
        rw [Real.norm_eq_abs, ← sq_le_one_iff_abs_le_one]
        have : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
          Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
        simp only [S, Set.mem_ofPred_eq] at hx
        linarith
    obtain ⟨x0, hx0, hmin⟩ := hcomp.exists_isMinOn hS hcont.continuousOn
    have hx0ne : x0 ≠ 0 := by
      rintro rfl
      simp [S] at hx0
    refine ⟨x8qf M x0, hM x0 hx0ne, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp [x8qf]
    · obtain ⟨hxS, hρ⟩ := hnorm x hx
      set ρ := Real.sqrt (∑ i, x i ^ 2)
      have h1 := hmin hxS
      simp only [Set.mem_ofPred_eq] at h1
      rw [hhom] at h1
      have hρ2 : ρ ^ 2 = ∑ i, x i ^ 2 := Real.sq_sqrt (by positivity)
      rw [← hρ2]
      have : ρ ^ 2 * (ρ⁻¹ ^ 2 * x8qf M x) = x8qf M x := by
        field_simp
      calc x8qf M x0 * ρ ^ 2 ≤ ρ ^ 2 * (ρ⁻¹ ^ 2 * x8qf M x) := by
            rw [mul_comm]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = x8qf M x := this
  · refine ⟨1, one_pos, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp [x8qf]
    · exact absurd ⟨_, (hnorm x hx).1⟩ hS

lemma x8_KP_int (y : Fin k × Fin k → ℝ) (hsym : ∀ i j, y (i, j) = y (j, i))
    (hpd : (x8mat y).PosDef) : y ∈ interior (x8KP k) := by
  obtain ⟨c, hc, hcM⟩ := x8_coercive (x8mat y) (x8_pd _ hpd)
  set δ := c / (k + 1)
  have hδ : 0 < δ := div_pos hc (by positivity)
  have hδk : δ * k ≤ c := by
    simp only [δ]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨δ, hδ, fun y' hy' => ?_⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hδ] at hy'
  show (x8mat (x8sym y')).PosSemidef
  rw [x8_psd_iff]
  refine ⟨fun i j => by simp only [x8mat, x8sym]; ring, fun x => ?_⟩
  set E : Fin k → Fin k → ℝ := fun i j => x8sym y' (i, j) - y (i, j)
  have hE : ∀ i j, |E i j| ≤ δ := by
    intro i j
    have h1 := hy' (i, j)
    have h2 := hy' (j, i)
    rw [Real.dist_eq] at h1 h2
    simp only [E, x8sym]
    rw [hsym j i] at h2
    rw [abs_le] at *
    constructor <;> nlinarith [abs_lt.1 h1, abs_lt.1 h2]
  have hsplit : x8qf (x8mat (x8sym y')) x = x8qf (x8mat y) x + ∑ i, ∑ j, x i * E i j * x j := by
    simp only [x8qf, x8mat, E, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  have hbound : -(δ * (∑ i, |x i|) ^ 2) ≤ ∑ i, ∑ j, x i * E i j * x j := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have := neg_abs_le (x i * E i j * x j)
    rw [abs_mul, abs_mul] at this
    have h3 : |x i| * |E i j| * |x j| ≤ δ * (|x i| * |x j|) := by
      have := mul_le_mul_of_nonneg_left (hE i j) (abs_nonneg (x i))
      nlinarith [abs_nonneg (x j), abs_nonneg (x i)]
    linarith
  have hcs : (∑ i, |x i|) ^ 2 ≤ k * ∑ i, x i ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |x i|)
    simpa [sq_abs] using this
  have := hcM x
  have hsum : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_left hcs hδ.le]

end PSD

end X8RL

open RobustOpt2009.Linear X8RL in
theorem solution {n L u : ℕ} (s : ConeShape) (D : Data n L)
    (R : Lift s.Index L u) (hwf : WellFormed s R)
    (hne : (R.set s.cone).Nonempty) (hq : Qualified s R) :
    (∀ x, Robust D (R.set s.cone) x ↔
      ∃ y, (reformulation D R s.cone).Feasible x y) ∧
    (∀ (f : (Fin n → ℝ) → ℝ),
      {t | ∃ x, Robust D (R.set s.cone) x ∧ t = f x} =
      {t | ∃ x y, (reformulation D R s.cone).Feasible x y ∧ t = f x}) ∧
    outputSize s D R ≤ 4 * (inputSize s D R) ^ 2 := by
  classical
  have key : ∀ x, Robust D (R.set s.cone) x ↔ ∃ y, Certificate D R s.cone x y := by
    intro x
    cases s with
    | orthant N => exact x8_orthant D R hne x
    | lorentz m d =>
      constructor
      · intro hrob
        obtain ⟨z, v, hzv⟩ := hq
        exact x8_fwd D R _ _ x
          (x8_slater D R _ x8_lor_cone ⟨z, v, x8_lor_int _ hzv⟩ x hrob) (x8_lor_dual_sub)
      · rintro ⟨y, h1, h2, h3, h4⟩
        exact x8_weak D R _ x y ⟨h1, h2, h3, x8_lor_sub_dual y h4⟩
    | psd k =>
      obtain ⟨hp, hP, hQ⟩ := hwf
      have hsymv : ∀ z v, ∀ i j, R.value z v (i, j) = R.value z v (j, i) := by
        intro z v i j
        simp only [Lift.value]
        have e1 : ∀ l, R.P l (i, j) = R.P l (j, i) := fun l => hP l i j
        have e2 : ∀ l, R.Q l (i, j) = R.Q l (j, i) := fun l => hQ l i j
        rw [hp i j]
        congr 2
        · exact Finset.sum_congr rfl (fun l _ => by rw [e1 l])
        · exact Finset.sum_congr rfl (fun l _ => by rw [e2 l])
      have hset : R.set (ConeShape.psd k).cone = R.set (x8KP k) := by
        ext z
        constructor
        · rintro ⟨v, hv⟩
          refine ⟨v, ?_⟩
          show (x8mat (x8sym (R.value z v))).PosSemidef
          rw [x8_sym_of (hsymv z v)]
          exact hv
        · rintro ⟨v, hv⟩
          refine ⟨v, ?_⟩
          have hv' : (x8mat (x8sym (R.value z v))).PosSemidef := hv
          rw [x8_sym_of (hsymv z v)] at hv'
          exact hv'
      constructor
      · intro hrob
        rw [hset] at hrob
        obtain ⟨z, v, hzv⟩ := hq
        exact x8_fwd D R _ _ x
          (x8_slater D R _ x8_KP_cone ⟨z, v, x8_KP_int _ (hsymv z v) hzv⟩ x hrob) x8_KP_dual
      · rintro ⟨y, h1, h2, h3, h4⟩
        exact x8_weak D R _ x y ⟨h1, h2, h3, x8_PK_sub_dual y h4⟩
  refine ⟨fun x => (key x).trans (exists_congr fun y => (x8_feas_iff D R _ x y).symm),
    fun f => ?_, x8_size s D R⟩
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := (key x).1 hx
    exact ⟨x, y, (x8_feas_iff D R _ x y).2 hy, rfl⟩
  · rintro ⟨x, y, hy, rfl⟩
    exact ⟨x, (key x).2 ⟨y, (x8_feas_iff D R _ x y).1 hy⟩, rfl⟩
