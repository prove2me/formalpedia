-- Prove2me | solution 1 for RobustOpt2009.Linear.theorem_1_3_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:50:11.636494+00:00
-- url     : https://prove2.me/submissions/cccabada-1b74-4b73-a741-b61f33cfd5c3

import Mathlib
import Definitions.Def_RobustOpt2009_Linear_Model
import Theorems.Thm_LinearOptimization_farkas_inequality_form_fintype

open Matrix
open scoped BigOperators Pointwise



namespace X8RL
open RobustOpt2009.Linear

lemma x8_val_dot {N L u : ℕ} (R : Lift (Fin N) L u) (y : Fin N → ℝ) (z : Fin L → ℝ)
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
lemma x8_cert {n N L u : ℕ} (D : Data n L) (R : Lift (Fin N) L u) (C : Set (Fin N → ℝ))
    (x : Fin n → ℝ) (y : Fin N → ℝ) (hyC : y ∈ C)
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
lemma x8_weak {n N L u : ℕ} (D : Data n L) (R : Lift (Fin N) L u) (K : Set (Fin N → ℝ))
    (x : Fin n → ℝ) (y : Fin N → ℝ)
    (hc : Certificate D R (ModernConvex.ConicDuality.dualCone K) x y) :
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

lemma x8_rob {n N L u : ℕ} (D : Data n L) (R : Lift (Fin N) L u) (K : Set (Fin N → ℝ))
    (x : Fin n → ℝ) (hrob : Robust D (R.set K) x) (z : Fin L → ℝ) (v : Fin u → ℝ)
    (hzv : R.value z v ∈ K) :
    ∑ l, z l * (D.a l ⬝ᵥ x - D.b l) ≤ D.b0 - D.a0 ⬝ᵥ x := by
  have := hrob z ⟨v, hzv⟩
  simp only [mul_sub, Finset.sum_sub_distrib]
  linarith

lemma x8_convex {N : ℕ} {K : Set (Fin N → ℝ)} (hK : IsConvexCone K) : Convex ℝ K := by
  intro a ha b hb s t hs ht _
  exact hK.2.1 _ (hK.2.2 a ha s hs) _ (hK.2.2 b hb t ht)

lemma x8_add_int {N : ℕ} {K : Set (Fin N → ℝ)} (hK : IsConvexCone K) {k k1 : Fin N → ℝ}
    (hk : k ∈ K) (hk1 : k1 ∈ interior K) : k + k1 ∈ interior K := by
  have hsub : (fun w => k + w) '' interior K ⊆ K := by
    rintro _ ⟨w, hw, rfl⟩
    exact hK.2.1 _ hk _ (interior_subset hw)
  have hopen : IsOpen ((fun w => k + w) '' interior K) :=
    (Homeomorph.addLeft k).isOpenMap _ isOpen_interior
  exact interior_maximal hsub hopen ⟨k1, hk1, rfl⟩

lemma x8_smul_int {N : ℕ} {K : Set (Fin N → ℝ)} (hK : IsConvexCone K) {k : Fin N → ℝ}
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

lemma x8_repr {N : ℕ} (f : StrongDual ℝ ((Fin N → ℝ) × ℝ)) (k : Fin N → ℝ) (r : ℝ) :
    f (k, r) = (fun i => f (Pi.single i 1, 0)) ⬝ᵥ k + r * f (0, 1) := by
  have : ((k, r) : (Fin N → ℝ) × ℝ) =
      ∑ i, k i • ((Pi.single i 1 : Fin N → ℝ), (0 : ℝ)) + r • ((0 : Fin N → ℝ), (1 : ℝ)) := by
    refine Prod.ext ?_ ?_
    · funext j
      simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  rw [this, map_add, map_sum, map_smul]
  simp only [map_smul, smul_eq_mul, dotProduct]
  congr 1
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

lemma x8_slater {n N L u : ℕ} (D : Data n L) (R : Lift (Fin N) L u) (K : Set (Fin N → ℝ))
    (hK : IsGoodCone K) (hs : ∃ z v, R.value z v ∈ interior K)
    (x : Fin n → ℝ) (hrob : Robust D (R.set K) x) :
    ∃ y ∈ dualCone K, ∀ z v, ∑ l, z l * (D.a l ⬝ᵥ x - D.b l) + y ⬝ᵥ R.value z v ≤
      D.b0 - D.a0 ⬝ᵥ x := by
  set c : Fin L → ℝ := fun l => D.a l ⬝ᵥ x - D.b l with hc
  set β := D.b0 - D.a0 ⬝ᵥ x with hβ
  have hcone := hK.1
  have hconv := x8_convex hcone
  obtain ⟨k0, hk0⟩ := hK.2.2.2
  let S : Set ((Fin N → ℝ) × ℝ) := interior K ×ˢ Set.Ioi β
  let T : Set ((Fin N → ℝ) × ℝ) :=
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
  set y' : Fin N → ℝ := fun i => f (Pi.single i 1, 0)
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

lemma x8_poly {n N L u m : ℕ} (D : Data n L) (R : Lift (Fin N) L u)
    (A : Fin m → Fin N → ℝ) (K : Set (Fin N → ℝ)) (hKA : K = {z | ∀ j, 0 ≤ A j ⬝ᵥ z})
    (hne : (R.set K).Nonempty)
    (x : Fin n → ℝ) (hrob : Robust D (R.set K) x) :
    ∃ y ∈ dualCone K, ∀ z v, ∑ l, z l * (D.a l ⬝ᵥ x - D.b l) + y ⬝ᵥ R.value z v ≤
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

open RobustOpt2009.Linear X8RL in
theorem solution {n L u N : ℕ} (D : Data n L) (R : Lift (Fin N) L u)
    (K : Set (Fin N → ℝ)) (hK : ModernConvex.ConicDuality.IsGoodCone K)
    (hne : (R.set K).Nonempty)
    (hqual : Polyhedral K ∨ ∃ z v, R.value z v ∈ interior K) :
    ∀ x, Robust D (R.set K) x ↔
      ∃ y, Certificate D R (ModernConvex.ConicDuality.dualCone K) x y := by
  intro x
  constructor
  · intro hrob
    rcases hqual with ⟨m, A, hKA⟩ | hs
    · obtain ⟨y, hy, h⟩ := x8_poly D R A K hKA hne x hrob
      exact ⟨y, x8_cert D R _ x y hy h⟩
    · obtain ⟨y, hy, h⟩ := x8_slater D R K hK hs x hrob
      exact ⟨y, x8_cert D R _ x y hy h⟩
  · rintro ⟨y, hy⟩
    exact x8_weak D R K x y hy
