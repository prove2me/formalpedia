-- Prove2me | solution 1 for PinningSync.Strong.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T18:55:35.630219+00:00
-- url     : https://prove2.me/submissions/b73b5f83-d804-49b7-8cc0-84f920efee4a

import Mathlib
import Definitions.Def_PinningSync_Strong_Setting

namespace RRAux_PinningSync_Strong_theorem_3_1

open Matrix Kronecker Filter Topology

lemma quad_smul {m : Type*} [Fintype m] (A : Matrix m m ℝ) (c : ℝ) (v : m → ℝ) :
    (c • v) ⬝ᵥ (A *ᵥ (c • v)) = c ^ 2 * (v ⬝ᵥ (A *ᵥ v)) := by
  simp [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring

lemma dot_le_card {m : Type*} [Fintype m] (v : m → ℝ) :
    v ⬝ᵥ v ≤ (Fintype.card m : ℝ) * ‖v‖ ^ 2 := by
  have h : ∀ p, v p * v p ≤ ‖v‖ ^ 2 := by
    intro p
    have h1 : ‖v p‖ ≤ ‖v‖ := norm_le_pi_norm v p
    rw [Real.norm_eq_abs] at h1
    have h2 : |v p| * |v p| ≤ ‖v‖ * ‖v‖ := mul_self_le_mul_self (abs_nonneg _) h1
    rw [← abs_mul] at h2
    nlinarith [le_abs_self (v p * v p)]
  calc v ⬝ᵥ v = ∑ p, v p * v p := rfl
    _ ≤ ∑ _p : m, ‖v‖ ^ 2 := Finset.sum_le_sum (fun p _ => h p)
    _ = (Fintype.card m : ℝ) * ‖v‖ ^ 2 := by simp

lemma posdef_lb {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m ℝ) (hA : A.PosDef) :
    ∃ l : ℝ, 0 < l ∧ ∀ v : m → ℝ, l * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v) := by
  have hpos : ∀ v : m → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (A *ᵥ v) := by
    intro v hv
    simpa using hA.dotProduct_mulVec_pos hv
  have hnn : ∀ v : m → ℝ, 0 ≤ v ⬝ᵥ (A *ᵥ v) := by
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · exact (hpos v hv).le
  by_cases hS : (Metric.sphere (0 : m → ℝ) 1).Nonempty
  · have hK : IsCompact (Metric.sphere (0 : m → ℝ) 1) := isCompact_sphere 0 1
    have hc : Continuous (fun v : m → ℝ => v ⬝ᵥ (A *ᵥ v)) := by
      unfold dotProduct Matrix.mulVec dotProduct; fun_prop
    obtain ⟨w, hw, hmin⟩ := hK.exists_isMinOn hS hc.continuousOn
    have hw0 : w ≠ 0 := by
      intro h; simp [h] at hw
    set μ := w ⬝ᵥ (A *ᵥ w) with hμ
    have hμpos : 0 < μ := hpos w hw0
    refine ⟨μ / ((Fintype.card m : ℝ) + 1), by positivity, ?_⟩
    intro v
    have key : μ * ‖v‖ ^ 2 ≤ v ⬝ᵥ (A *ᵥ v) := by
      by_cases hv : v = 0
      · simp [hv]
      · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
        have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : m → ℝ) 1 := by
          rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
        have := hmin hu
        simp only [Set.mem_ofPred_eq] at this
        rw [quad_smul] at this
        have h2 : (‖v‖⁻¹) ^ 2 * ‖v‖ ^ 2 = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ hn.ne', one_pow]
        calc μ * ‖v‖ ^ 2 ≤ (‖v‖⁻¹ ^ 2 * (v ⬝ᵥ (A *ᵥ v))) * ‖v‖ ^ 2 :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ = v ⬝ᵥ (A *ᵥ v) := by
              rw [mul_comm (‖v‖⁻¹ ^ 2), mul_assoc, h2, mul_one]
    have hd := dot_le_card v
    have hc1 : (0:ℝ) < (Fintype.card m : ℝ) + 1 := by positivity
    have hvv : 0 ≤ v ⬝ᵥ v := by
      unfold dotProduct; exact Finset.sum_nonneg (fun p _ => mul_self_nonneg _)
    rw [div_mul_eq_mul_div, div_le_iff₀ hc1]
    nlinarith [sq_nonneg ‖v‖]
  · refine ⟨1, one_pos, ?_⟩
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · exfalso; apply hS
      refine ⟨‖v‖⁻¹ • v, ?_⟩
      have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']

lemma decay (V V' : ℝ → ℝ) (k : ℝ)
    (hV : ∀ t, 0 ≤ t → HasDerivWithinAt V (V' t) (Set.Ici 0) t)
    (h : ∀ t, 0 ≤ t → V' t ≤ -k * V t) :
    ∀ t, 0 ≤ t → V t * Real.exp (k * t) ≤ V 0 := by
  have hW : ∀ t, 0 ≤ t → HasDerivWithinAt (fun τ => V τ * Real.exp (k * τ))
      (V' t * Real.exp (k * t) + V t * (Real.exp (k * t) * k)) (Set.Ici 0) t := by
    intro t ht
    refine (hV t ht).mul ?_
    have : HasDerivAt (fun τ => Real.exp (k * τ)) (Real.exp (k * t) * k) t := by
      simpa using ((hasDerivAt_id t).const_mul k).exp
    exact this.hasDerivWithinAt
  have hanti : AntitoneOn (fun τ => V τ * Real.exp (k * τ)) (Set.Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    · intro t ht; exact (hW t ht).continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht ⊢
      exact (hW t (le_of_lt ht)).mono Set.Ioi_subset_Ici_self
    · intro t ht
      rw [interior_Ici] at ht
      have := h t (le_of_lt ht)
      have he := Real.exp_pos (k * t)
      nlinarith
  intro t ht
  have := hanti (show (0:ℝ) ∈ Set.Ici 0 from Set.mem_Ici.mpr le_rfl) ht ht
  simpa using this

lemma kron_quad {N n : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (u : Fin N → Fin n → ℝ) :
    (fun p : Fin N × Fin n => u p.1 p.2) ⬝ᵥ ((A ⊗ₖ B) *ᵥ fun p => u p.1 p.2)
      = ∑ i, ∑ j, A i j * (u i ⬝ᵥ (B *ᵥ u j)) := by
  simp only [dotProduct, mulVec, kroneckerMap_apply, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

lemma quad_transpose {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (u w : Fin n → ℝ) :
    u ⬝ᵥ (Pᵀ *ᵥ w) = w ⬝ᵥ (P *ᵥ u) := by
  rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]

lemma sym_part {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    u ⬝ᵥ (((1 / 2 : ℝ) • (P + Pᵀ)) *ᵥ u) = u ⬝ᵥ (P *ᵥ u) := by
  rw [smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, quad_transpose, smul_eq_mul]
  ring

lemma half_sym {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γᵀ = Γ) :
    (1 / 2 : ℝ) • (Γ + Γᵀ) = Γ := by
  rw [hΓ]; ext a b; simp; ring

lemma lmi_quad {N n : ℕ} (K Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γᵀ = Γ) (c : ℝ)
    (G : Matrix (Fin N) (Fin N) ℝ) (ξ d : Fin N → ℝ) (u : Fin N → Fin n → ℝ) :
    (fun p : Fin N × Fin n => u p.1 p.2) ⬝ᵥ
        (PinningSync.Strong.lmi32 K Γ c G ξ d *ᵥ fun p => u p.1 p.2)
      = ∑ i, ξ i * (u i ⬝ᵥ ((K * Γ) *ᵥ u i))
        + c * ∑ i, ∑ j, ξ i * G i j * (u i ⬝ᵥ (Γ *ᵥ u j))
        - c * ∑ i, ξ i * d i * (u i ⬝ᵥ (Γ *ᵥ u i)) := by
  unfold PinningSync.Strong.lmi32
  rw [sub_mulVec, add_mulVec, smul_mulVec, smul_mulVec, dotProduct_sub, dotProduct_add,
    dotProduct_smul, dotProduct_smul, kron_quad, kron_quad, kron_quad, half_sym Γ hΓ,
    diagonal_mul_diagonal, smul_eq_mul, smul_eq_mul]
  have hsymm : ∀ i j, u j ⬝ᵥ (Γ *ᵥ u i) = u i ⬝ᵥ (Γ *ᵥ u j) := by
    intro i j
    rw [← quad_transpose, hΓ]
  have h1 : ∑ i, ∑ j, diagonal ξ i j * (u i ⬝ᵥ (((1 / 2 : ℝ) • (K * Γ + Γᵀ * Kᵀ)) *ᵥ u j))
      = ∑ i, ξ i * (u i ⬝ᵥ ((K * Γ) *ᵥ u i)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_eq_single i]
    · rw [diagonal_apply_eq, ← transpose_mul, sym_part]
    · intro j _ hj; rw [diagonal_apply_ne _ (Ne.symm hj), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have h3 : ∑ i, ∑ j, diagonal (fun i => ξ i * d i) i j * (u i ⬝ᵥ (Γ *ᵥ u j))
      = ∑ i, ξ i * d i * (u i ⬝ᵥ (Γ *ᵥ u i)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_eq_single i]
    · rw [diagonal_apply_eq]
    · intro j _ hj; rw [diagonal_apply_ne _ (Ne.symm hj), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have h2 : ∑ i, ∑ j, PinningSync.Strong.Ghat G ξ i j * (u i ⬝ᵥ (Γ *ᵥ u j))
      = ∑ i, ∑ j, ξ i * G i j * (u i ⬝ᵥ (Γ *ᵥ u j)) := by
    have hG : ∀ i j, PinningSync.Strong.Ghat G ξ i j = 1 / 2 * (ξ i * G i j + G j i * ξ j) := by
      intro i j
      simp [PinningSync.Strong.Ghat, diagonal_mul, mul_diagonal, transpose_apply]
    simp only [hG]
    have hsplit : ∑ i, ∑ j, 1 / 2 * (ξ i * G i j + G j i * ξ j) * (u i ⬝ᵥ (Γ *ᵥ u j))
        = 1 / 2 * ∑ i, ∑ j, ξ i * G i j * (u i ⬝ᵥ (Γ *ᵥ u j))
          + 1 / 2 * ∑ i, ∑ j, G j i * ξ j * (u i ⬝ᵥ (Γ *ᵥ u j)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      ring
    rw [hsplit, Finset.sum_comm (f := fun i j => G j i * ξ j * (u i ⬝ᵥ (Γ *ᵥ u j)))]
    have : ∑ y, ∑ x, G y x * ξ y * (u x ⬝ᵥ (Γ *ᵥ u y))
        = ∑ i, ∑ j, ξ i * G i j * (u i ⬝ᵥ (Γ *ᵥ u j)) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [hsymm]; ring
    rw [this]; ring
  rw [h1, h2, h3]

lemma hasDeriv_dot {n : ℕ} (u : ℝ → Fin n → ℝ) (u' : Fin n → ℝ) (S : Set ℝ) (t : ℝ)
    (h : HasDerivWithinAt u u' S t) :
    HasDerivWithinAt (fun τ => u τ ⬝ᵥ u τ) (2 * (u t ⬝ᵥ u')) S t := by
  have hc := hasDerivWithinAt_pi.mp h
  have := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun a _ => (hc a).mul (hc a))
  show HasDerivWithinAt (fun τ => ∑ a, u τ a * u τ a) _ S t
  refine this.congr_deriv ?_
  unfold dotProduct
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  ring

lemma deriv_side {N n : ℕ} (f : (Fin n → ℝ) → ℝ → (Fin n → ℝ))
    (K Γ : Matrix (Fin n) (Fin n) ℝ) (hA1 : PinningSync.Strong.Assumption1 f K Γ) (c : ℝ)
    (G : Matrix (Fin N) (Fin N) ℝ) (hrow : ∀ i, ∑ j, G i j = 0) (d ξ : Fin N → ℝ)
    (hξ : ∀ i, 0 ≤ ξ i) (t : ℝ) (ht : 0 ≤ t) (xs : Fin N → Fin n → ℝ) (s0 : Fin n → ℝ) :
    ∑ i, ξ i * ((xs i - s0) ⬝ᵥ (f (xs i) t + c • ∑ j, G i j • (Γ *ᵥ xs j)
        - (c * d i) • (Γ *ᵥ (xs i - s0)) - f s0 t))
      ≤ ∑ i, ξ i * ((xs i - s0) ⬝ᵥ ((K * Γ) *ᵥ (xs i - s0)))
        + c * ∑ i, ∑ j, ξ i * G i j * ((xs i - s0) ⬝ᵥ (Γ *ᵥ (xs j - s0)))
        - c * ∑ i, ξ i * d i * ((xs i - s0) ⬝ᵥ (Γ *ᵥ (xs i - s0))) := by
  have hterm : ∀ i, ξ i * ((xs i - s0) ⬝ᵥ (f (xs i) t + c • ∑ j, G i j • (Γ *ᵥ xs j)
        - (c * d i) • (Γ *ᵥ (xs i - s0)) - f s0 t))
      ≤ ξ i * ((xs i - s0) ⬝ᵥ ((K * Γ) *ᵥ (xs i - s0)))
        + c * ∑ j, ξ i * G i j * ((xs i - s0) ⬝ᵥ (Γ *ᵥ (xs j - s0)))
        - c * (ξ i * d i * ((xs i - s0) ⬝ᵥ (Γ *ᵥ (xs i - s0)))) := by
    intro i
    have hS : ∑ j, G i j • (Γ *ᵥ xs j) = ∑ j, G i j • (Γ *ᵥ (xs j - s0)) := by
      have : ∑ j, G i j • (Γ *ᵥ xs j)
          = ∑ j, G i j • (Γ *ᵥ (xs j - s0)) + ∑ j, G i j • (Γ *ᵥ s0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← smul_add, ← mulVec_add, sub_add_cancel]
      rw [this, ← Finset.sum_smul, hrow i, zero_smul, add_zero]
    have hv : f (xs i) t + c • ∑ j, G i j • (Γ *ᵥ xs j) - (c * d i) • (Γ *ᵥ (xs i - s0)) - f s0 t
        = (f (xs i) t - f s0 t) + c • ∑ j, G i j • (Γ *ᵥ (xs j - s0))
          - (c * d i) • (Γ *ᵥ (xs i - s0)) := by
      rw [hS]; abel
    rw [hv, dotProduct_sub, dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_sum]
    simp only [dotProduct_smul, smul_eq_mul]
    have hA := hA1 t ht (xs i) s0
    have hx := mul_le_mul_of_nonneg_left hA (hξ i)
    have he : ξ i * (c * ∑ j, G i j * ((xs i - s0) ⬝ᵥ (Γ *ᵥ (xs j - s0))))
        = c * ∑ j, ξ i * G i j * ((xs i - s0) ⬝ᵥ (Γ *ᵥ (xs j - s0))) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    have hexp : ξ i * ((xs i - s0) ⬝ᵥ (f (xs i) t - f s0 t)
          + c * ∑ j, G i j * ((xs i - s0) ⬝ᵥ (Γ *ᵥ (xs j - s0)))
          - c * d i * ((xs i - s0) ⬝ᵥ (Γ *ᵥ (xs i - s0))))
        = ξ i * ((xs i - s0) ⬝ᵥ (f (xs i) t - f s0 t))
          + ξ i * (c * ∑ j, G i j * ((xs i - s0) ⬝ᵥ (Γ *ᵥ (xs j - s0))))
          - c * (ξ i * d i * ((xs i - s0) ⬝ᵥ (Γ *ᵥ (xs i - s0)))) := by ring
    rw [hexp, he]
    linarith
  calc _ ≤ ∑ i, (ξ i * ((xs i - s0) ⬝ᵥ ((K * Γ) *ᵥ (xs i - s0)))
        + c * ∑ j, ξ i * G i j * ((xs i - s0) ⬝ᵥ (Γ *ᵥ (xs j - s0)))
        - c * (ξ i * d i * ((xs i - s0) ⬝ᵥ (Γ *ᵥ (xs i - s0))))) :=
          Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

lemma num_step (l Ξ V S : ℝ) (hl : 0 < l) (hΞ : 0 < Ξ) (hV : V ≤ Ξ / 2 * S) :
    -l * S ≤ -(2 * l / Ξ) * V := by
  have h1 : 2 * l / Ξ * V ≤ 2 * l / Ξ * (Ξ / 2 * S) :=
    mul_le_mul_of_nonneg_left hV (by positivity)
  have h2 : 2 * l / Ξ * (Ξ / 2 * S) = l * S := by field_simp
  linarith

lemma coord_sq_le {n : ℕ} (v : Fin n → ℝ) (a : Fin n) : v a ^ 2 ≤ v ⬝ᵥ v := by
  rw [sq]
  exact Finset.single_le_sum (f := fun b => v b * v b) (fun b _ => mul_self_nonneg (v b))
    (Finset.mem_univ a)

lemma dot_self_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg (fun b _ => mul_self_nonneg (v b))

end RRAux_PinningSync_Strong_theorem_3_1

open PinningSync.Strong in
open Matrix Filter Topology in
theorem solution {N n : ℕ} (f : (Fin n → ℝ) → ℝ → (Fin n → ℝ))
    (hf : ContDiffOn ℝ 1 (fun p : (Fin n → ℝ) × ℝ => f p.1 p.2) (Set.univ ×ˢ Set.Ici 0))
    (K Γ : Matrix (Fin n) (Fin n) ℝ) (hA1 : Assumption1 f K Γ) (hΓ : Γᵀ = Γ) (c : ℝ)
    (G : Matrix (Fin N) (Fin N) ℝ) (hG : IsCouplingMatrix G) (hsc : IsStronglyConnected G)
    (d : Fin N → ℝ) (hd : ∀ i, 0 ≤ d i)
    (ξ : Fin N → ℝ) (hξ : ∀ i, 0 < ξ i) (hΞ : ∀ i, ∑ j, Ghat G ξ i j = 0)
    (hlmi : (-(lmi32 K Γ c G ξ d)).PosDef) :
    ∀ (s : ℝ → Fin n → ℝ) (x : ℝ → Fin N → Fin n → ℝ),
      IsIsolatedSolution f s → IsControlledSolution f c G Γ d s x →
        GloballySynchronized s x := by
  intro s x hs hx
  open RRAux_PinningSync_Strong_theorem_3_1 in
  obtain ⟨l, hl, hlb⟩ := posdef_lb _ hlmi
  have hξ0 : ∀ i, 0 ≤ ξ i := fun i => (hξ i).le
  set Ξ : ℝ := ∑ j, ξ j + 1 with hΞdef
  have hΞpos : 0 < Ξ := by
    have : 0 ≤ ∑ j, ξ j := Finset.sum_nonneg (fun j _ => hξ0 j)
    linarith
  have hξle : ∀ i, ξ i ≤ Ξ := by
    intro i
    have := Finset.single_le_sum (f := ξ) (fun j _ => hξ0 j) (Finset.mem_univ i)
    linarith
  let V : ℝ → ℝ := fun t => (1 / 2 : ℝ) * ∑ i, ξ i * ((x t i - s t) ⬝ᵥ (x t i - s t))
  let V' : ℝ → ℝ := fun t => (1 / 2 : ℝ) * ∑ i, ξ i * (2 * ((x t i - s t) ⬝ᵥ
      (f (x t i) t + c • ∑ j, G i j • (Γ *ᵥ x t j) - (c * d i) • (Γ *ᵥ (x t i - s t))
        - f (s t) t)))
  have hVd : ∀ t, 0 ≤ t → HasDerivWithinAt V (V' t) (Set.Ici 0) t := by
    intro t ht
    have hi : ∀ i ∈ (Finset.univ : Finset (Fin N)), HasDerivWithinAt
        (fun τ => ξ i * ((x τ i - s τ) ⬝ᵥ (x τ i - s τ)))
        (ξ i * (2 * ((x t i - s t) ⬝ᵥ
          (f (x t i) t + c • ∑ j, G i j • (Γ *ᵥ x t j) - (c * d i) • (Γ *ᵥ (x t i - s t))
            - f (s t) t)))) (Set.Ici 0) t := by
      intro i _
      exact (RRAux_PinningSync_Strong_theorem_3_1.hasDeriv_dot (fun τ => x τ i - s τ) _ _ t
        ((hx i t ht).sub (hs t ht))).const_mul (ξ i)
    exact (HasDerivWithinAt.fun_sum hi).const_mul (1 / 2 : ℝ)
  set k : ℝ := 2 * l / Ξ with hk
  have hkpos : 0 < k := by positivity
  have hbound : ∀ t, 0 ≤ t → V' t ≤ -k * V t := by
    intro t ht
    have e1 : V' t = ∑ i, ξ i * ((x t i - s t) ⬝ᵥ
        (f (x t i) t + c • ∑ j, G i j • (Γ *ᵥ x t j) - (c * d i) • (Γ *ᵥ (x t i - s t))
          - f (s t) t)) := by
      simp only [V', Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    have e2 := RRAux_PinningSync_Strong_theorem_3_1.deriv_side f K Γ hA1 c G hG.2 d ξ hξ0 t ht
      (x t) (s t)
    have e3 := RRAux_PinningSync_Strong_theorem_3_1.lmi_quad K Γ hΓ c G ξ d
      (fun i => x t i - s t)
    have e4 := hlb (fun p : Fin N × Fin n => x t p.1 p.2 - s t p.2)
    rw [neg_mulVec, dotProduct_neg] at e4
    have e5 : (fun p : Fin N × Fin n => x t p.1 p.2 - s t p.2) ⬝ᵥ
        (fun p : Fin N × Fin n => x t p.1 p.2 - s t p.2)
        = ∑ i, ((x t i - s t) ⬝ᵥ (x t i - s t)) := by
      simp only [dotProduct, Fintype.sum_prod_type, Pi.sub_apply]
    have e6 : V t ≤ Ξ / 2 * ∑ i, ((x t i - s t) ⬝ᵥ (x t i - s t)) := by
      simp only [V, Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      have := RRAux_PinningSync_Strong_theorem_3_1.dot_self_nonneg (x t i - s t)
      have := mul_le_mul_of_nonneg_right (hξle i) this
      linarith
    have e7 := RRAux_PinningSync_Strong_theorem_3_1.num_step l Ξ (V t) _ hl hΞpos e6
    have e3' : (fun p : Fin N × Fin n => x t p.1 p.2 - s t p.2) ⬝ᵥ
        (lmi32 K Γ c G ξ d *ᵥ fun p => x t p.1 p.2 - s t p.2)
        = ∑ i, ξ i * ((x t i - s t) ⬝ᵥ ((K * Γ) *ᵥ (x t i - s t)))
        + c * ∑ i, ∑ j, ξ i * G i j * ((x t i - s t) ⬝ᵥ (Γ *ᵥ (x t j - s t)))
        - c * ∑ i, ξ i * d i * ((x t i - s t) ⬝ᵥ (Γ *ᵥ (x t i - s t))) := e3
    rw [e5] at e4
    rw [e1, hk]
    linarith
  have hdecay := RRAux_PinningSync_Strong_theorem_3_1.decay V V' k hVd hbound
  intro i
  rw [tendsto_pi_nhds]
  intro a
  rw [Pi.zero_apply]
  have hlow : ∀ t, ξ i * ((x t i - s t) ⬝ᵥ (x t i - s t)) ≤ 2 * V t := by
    intro t
    have := Finset.single_le_sum
      (f := fun j => ξ j * ((x t j - s t) ⬝ᵥ (x t j - s t)))
      (fun j _ => mul_nonneg (hξ0 j)
        (RRAux_PinningSync_Strong_theorem_3_1.dot_self_nonneg _)) (Finset.mem_univ i)
    simp only [V]
    linarith
  have hlim : Tendsto (fun t => Real.sqrt (2 / ξ i * V 0 * Real.exp (-(k * t)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t => Real.exp (-(k * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop hkpos tendsto_id)
    have h2 := (h1.const_mul (2 / ξ i * V 0)).sqrt
    simpa using h2
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  have hc := RRAux_PinningSync_Strong_theorem_3_1.coord_sq_le (x t i - s t) a
  have hd1 := hdecay t ht
  have hl1 := hlow t
  have hex := Real.exp_pos (k * t)
  have hV : V t ≤ V 0 * Real.exp (-(k * t)) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hex]; exact hd1
  have hxi := hξ i
  have : (x t i - s t) ⬝ᵥ (x t i - s t) ≤ 2 / ξ i * V 0 * Real.exp (-(k * t)) := by
    rw [mul_assoc, div_mul_eq_mul_div, le_div_iff₀ hxi]
    nlinarith
  exact le_trans hc this

#print axioms solution
