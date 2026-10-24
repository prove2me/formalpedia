-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P60.isotropic_positive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T17:51:34.239991+00:00
-- url     : https://prove2.me/submissions/e6495e52-90c7-4d11-a8a5-7fc2dc104b77

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

-- ===== P3A =====

/-! Separability of isotropic states below the threshold `1/(d+1)`,
via a finite phase-averaging (4th roots of unity) decomposition. -/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

set_option linter.unusedSectionVars false

namespace X4P3

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

lemma prod_expC {n : ℕ} {M : Type*} [Fintype M] (f : Fin n → M → ℂ) :
    ∑ x : Fin n → M, ∏ i, f i (x i) = ∏ i, ∑ a, f i a := by
  rw [Finset.prod_univ_sum (fun _ => Finset.univ) f, Fintype.piFinset_univ]

/-- separable from any finite family. -/
lemma sep_of_sum {I J T : Type*} [Fintype I] [Fintype J] [Fintype T]
    (X : Matrix (I × J) (I × J) ℂ) (w : T → ℝ) (A : T → Matrix I I ℂ) (B : T → Matrix J J ℂ)
    (hw : ∀ t, 0 ≤ w t) (hAB : ∀ t, IsDensityMatrix (A t) ∧ IsDensityMatrix (B t))
    (hX : X = ∑ t, (w t : ℂ) • Matrix.kronecker (A t) (B t)) :
    Entanglement.IsSeparablePositive X := by
  let e := Fintype.equivFin T
  refine ⟨Fintype.card T, fun j => w (e.symm j), fun j => A (e.symm j), fun j => B (e.symm j),
    fun j => hw _, fun j => hAB _, ?_⟩
  rw [hX]
  exact (Equiv.sum_comp e.symm (fun t => (w t : ℂ) • Matrix.kronecker (A t) (B t))).symm

/-- phase factor. -/
def ph (t : Fin 4) : ℂ := Complex.I ^ (t : ℕ)

lemma ph_norm (t : Fin 4) : ph t * conj (ph t) = 1 := by
  fin_cases t <;> simp [ph, pow_succ, Complex.ext_iff]

/-- the four-term phase average of one coordinate. -/
lemma ph_avg (α β γ δ : Bool) :
    ∑ t : Fin 4, (if α then ph t else 1) * (if β then ph t else 1) *
      (if γ then conj (ph t) else 1) * (if δ then conj (ph t) else 1) =
    if (α.toNat + β.toNat = γ.toNat + δ.toNat) then 4 else 0 := by
  cases α <;> cases β <;> cases γ <;> cases δ <;>
    simp [Fin.sum_univ_four, ph, pow_succ, Complex.ext_iff] <;> norm_num

lemma ph_avg' (P Q R S : Prop) [Decidable P] [Decidable Q] [Decidable R] [Decidable S] :
    ∑ t : Fin 4, (if P then ph t else 1) * (if Q then ph t else 1) *
      (if R then conj (ph t) else 1) * (if S then conj (ph t) else 1) =
    if ((if P then 1 else 0) + (if Q then 1 else 0) : ℕ) =
      (if R then 1 else 0) + (if S then 1 else 0) then 4 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> by_cases hS : S <;>
    simp [hP, hQ, hR, hS, Fin.sum_univ_four, ph, pow_succ, Complex.ext_iff] <;> norm_num

lemma comb {d : ℕ} (a b c e : Fin d) :
    (∀ j ∈ (Finset.univ : Finset (Fin d)), ((if j = a then 1 else 0) + (if j = e then 1 else 0) : ℕ) =
      (if j = b then 1 else 0) + (if j = c then 1 else 0)) ↔ ((a = b ∧ c = e) ∨ (a = c ∧ b = e)) := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have ha := h a (Finset.mem_univ _)
    have hb := h b (Finset.mem_univ _)
    have hc := h c (Finset.mem_univ _)
    have he := h e (Finset.mem_univ _)
    by_cases h1 : a = b <;> by_cases h2 : a = c <;> by_cases h3 : a = e <;> by_cases h4 : b = c <;>
      by_cases h5 : b = e <;> by_cases h6 : c = e <;> simp_all
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) j _ <;> omega

lemma avg {d : ℕ} (a b c e : Fin d) :
    ∑ θ : Fin d → Fin 4, ph (θ a) * ph (θ e) * conj (ph (θ b)) * conj (ph (θ c)) =
      if (a = b ∧ c = e) ∨ (a = c ∧ b = e) then (4 : ℂ) ^ d else 0 := by
  have h1 : ∀ θ : Fin d → Fin 4, ph (θ a) * ph (θ e) * conj (ph (θ b)) * conj (ph (θ c)) =
      ∏ j, ((if j = a then ph (θ j) else 1) * (if j = e then ph (θ j) else 1) *
        (if j = b then conj (ph (θ j)) else 1) * (if j = c then conj (ph (θ j)) else 1)) := by
    intro θ
    simp only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_congr rfl fun θ _ => h1 θ]
  rw [prod_expC (fun j t => (if j = a then ph t else 1) * (if j = e then ph t else 1) *
        (if j = b then conj (ph t) else 1) * (if j = c then conj (ph t) else 1))]
  simp only [ph_avg']
  rw [Finset.prod_ite_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  by_cases hc : (a = b ∧ c = e) ∨ (a = c ∧ b = e)
  · rw [if_pos ((comb a b c e).2 hc), if_pos hc]
  · rw [if_neg (fun h => hc ((comb a b c e).1 h)), if_neg hc]

end X4P3

-- ===== P3B =====

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

set_option linter.unusedSectionVars false

namespace X4P3

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

lemma dens_vv {n : Type*} [Fintype n] (v : n → ℂ) (h : ∑ i, v i * conj (v i) = 1) :
    IsDensityMatrix (Matrix.vecMulVec v (star v)) := by
  refine ⟨Matrix.posSemidef_vecMulVec_self_star v, ?_⟩
  rw [← h]
  simp [Matrix.trace, Matrix.vecMulVec_apply]

variable {d : ℕ}

/-- normalized phase vector. -/
def pv (θ : Fin d → Fin 4) (j : Fin d) : ℂ := ((Real.sqrt d)⁻¹ : ℝ) * ph (θ j)

/-- basis vector. -/
def bv (j : Fin d) : Fin d → ℂ := Pi.single j 1

lemma ph_norm' (t : Fin 4) : conj (ph t) * ph t = 1 := by rw [mul_comm]; exact ph_norm t

lemma pv_norm (hd : 0 < d) (θ : Fin d → Fin 4) : ∑ i, pv θ i * conj (pv θ i) = 1 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have e : ∀ i, pv θ i * conj (pv θ i) = (((Real.sqrt d)⁻¹ * (Real.sqrt d)⁻¹ : ℝ) : ℂ) := by
    intro i
    simp only [pv, map_mul, Complex.conj_ofReal]
    rw [show ((Real.sqrt d)⁻¹ : ℝ) * ph (θ i) * (((Real.sqrt d)⁻¹ : ℝ) * conj (ph (θ i))) =
      (((Real.sqrt d)⁻¹ : ℝ) * ((Real.sqrt d)⁻¹ : ℝ) : ℂ) * (ph (θ i) * conj (ph (θ i))) by ring,
      ph_norm]
    push_cast; ring
  rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← mul_inv, Real.mul_self_sqrt hd'.le]
  push_cast
  field_simp

lemma pv_norm' (hd : 0 < d) (θ : Fin d → Fin 4) :
    ∑ i, star (pv θ) i * conj (star (pv θ) i) = 1 := by
  rw [← pv_norm hd θ]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

lemma bv_norm (j : Fin d) : ∑ i, bv j i * conj (bv j i) = 1 := by
  simp [bv, Pi.single_apply]

end X4P3

-- ===== P3C =====

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

set_option linter.unusedSectionVars false

namespace X4P3

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

variable {d : ℕ}

lemma kron_ap {α β : Type*} (A : Matrix α α ℂ) (B : Matrix β β ℂ) (p q : α × β) :
    Matrix.kronecker A B p q = A p.1 q.1 * B p.2 q.2 := rfl

lemma vv_ap {n : Type*} (v w : n → ℂ) (i j : n) : Matrix.vecMulVec v w i j = v i * w j := rfl

lemma h1 (hd : 0 < d) (a b c e : Fin d) :
    ∑ θ : Fin d → Fin 4, ((((d : ℝ) / 4 ^ d : ℝ)) : ℂ) *
      (Matrix.vecMulVec (pv θ) (star (pv θ)) a c * Matrix.vecMulVec (star (pv θ)) (star (star (pv θ))) b e) =
      (((1 / d : ℝ)) : ℂ) * (if (a = b ∧ c = e) ∨ (a = c ∧ b = e) then 1 else 0) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set r : ℝ := (Real.sqrt d)⁻¹ with hr
  have hr4 : r * r * (r * r) = 1 / (d : ℝ) ^ 2 := by
    rw [hr, ← mul_inv, Real.mul_self_sqrt hd'.le]; field_simp
  have hpv : ∀ (θ : Fin d → Fin 4) j, pv θ j = (r : ℂ) * ph (θ j) := fun _ _ => rfl
  have e1 : ∀ θ : Fin d → Fin 4, ((((d : ℝ) / 4 ^ d : ℝ)) : ℂ) *
      (Matrix.vecMulVec (pv θ) (star (pv θ)) a c * Matrix.vecMulVec (star (pv θ)) (star (star (pv θ))) b e) =
      ((((d : ℝ) / 4 ^ d) * (r * r * (r * r)) : ℝ) : ℂ) *
        (ph (θ a) * ph (θ e) * conj (ph (θ b)) * conj (ph (θ c))) := by
    intro θ
    simp only [vv_ap, star_star, Pi.star_apply, hpv, Complex.star_def, map_mul, Complex.conj_ofReal]
    push_cast; ring
  rw [Finset.sum_congr rfl fun θ _ => e1 θ, ← Finset.mul_sum, avg, hr4]
  split_ifs
  · push_cast
    field_simp
  · simp

lemma om_ap (hd : 0 < d) (a b c e : Fin d) :
    omega d (a, b) * conj (omega d (c, e)) = if a = b ∧ c = e then ((1 / d : ℝ) : ℂ) else 0 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have ho : ∀ x : Fin d × Fin d, omega d x = if x.1 = x.2 then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0 := by
    intro x; simp [omega]
  rw [ho, ho]
  by_cases h1 : a = b <;> by_cases h2 : c = e <;> simp [h1, h2]
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hd'.le]
  push_cast; rfl

lemma conj_ite01 (P : Prop) [Decidable P] : conj (if P then (1 : ℂ) else 0) = if P then 1 else 0 := by
  split_ifs <;> simp

lemma bv_ap (j a : Fin d) : bv j a = if a = j then 1 else 0 := by
  simp [bv, Pi.single_apply]

theorem iso_sep (hd : 0 < d) (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1 / ((d : ℝ) + 1)) :
    Entanglement.IsSeparablePositive (isotropic d p) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hp1 : p * ((d : ℝ) + 1) ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hp; exact hp
  refine sep_of_sum (T := (Fin d → Fin 4) ⊕ (Fin d ⊕ (Fin d × Fin d))) _
    (Sum.elim (fun _ => p * ((d : ℝ) / 4 ^ d)) (Sum.elim (fun _ => p / d)
      (fun _ => (1 - p * ((d : ℝ) + 1)) / (d : ℝ) ^ 2)))
    (Sum.elim (fun θ => Matrix.vecMulVec (pv θ) (star (pv θ)))
      (Sum.elim (fun j => Matrix.vecMulVec (bv j) (star (bv j)))
        (fun jk => Matrix.vecMulVec (bv jk.1) (star (bv jk.1)))))
    (Sum.elim (fun θ => Matrix.vecMulVec (star (pv θ)) (star (star (pv θ))))
      (Sum.elim (fun j => Matrix.vecMulVec (bv j) (star (bv j)))
        (fun jk => Matrix.vecMulVec (bv jk.2) (star (bv jk.2))))) ?_ ?_ ?_
  · rintro (θ | j | jk)
    · simp only [Sum.elim_inl]; positivity
    · simp only [Sum.elim_inr, Sum.elim_inl]; positivity
    · simp only [Sum.elim_inr]
      exact div_nonneg (by linarith) (by positivity)
  · rintro (θ | j | jk)
    · exact ⟨dens_vv _ (pv_norm hd θ), dens_vv _ (pv_norm' hd θ)⟩
    · exact ⟨dens_vv _ (bv_norm j), dens_vv _ (bv_norm j)⟩
    · exact ⟨dens_vv _ (bv_norm jk.1), dens_vv _ (bv_norm jk.2)⟩
  · ext ⟨a, b⟩ ⟨c, e⟩
    rw [Matrix.sum_apply, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Matrix.smul_apply, kron_ap, smul_eq_mul]
    have s1 : ∑ θ : Fin d → Fin 4, ((p * ((d : ℝ) / 4 ^ d) : ℝ) : ℂ) *
        (Matrix.vecMulVec (pv θ) (star (pv θ)) a c *
          Matrix.vecMulVec (star (pv θ)) (star (star (pv θ))) b e) =
        (p : ℂ) * ((((1 / d : ℝ)) : ℂ) * (if (a = b ∧ c = e) ∨ (a = c ∧ b = e) then 1 else 0)) := by
      rw [← h1 hd a b c e, Finset.mul_sum]
      refine Finset.sum_congr rfl fun θ _ => ?_
      push_cast; ring
    rw [s1]
    simp only [vv_ap, Pi.star_apply, bv_ap, Complex.star_def, conj_ite01]
    unfold isotropic
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, pureDensity, Matrix.of_apply,
      om_ap hd, Matrix.one_apply, Prod.mk.injEq]
    by_cases h1 : a = b <;> by_cases h2 : c = e <;> by_cases h3 : a = c <;> by_cases h4 : b = e <;>
      simp_all <;> push_cast <;> field_simp <;> ring

end X4P3

-- ===== P3D =====

/-! Strict Klein inequality for (possibly singular) density matrices with support inclusion. -/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

set_option linter.unusedSectionVars false

namespace X4P3

/-- scalar Klein gap. -/
def kg (r s : ℝ) : ℝ := r * Real.log r - r * Real.log s - (r - s)

lemma kg_nonneg {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (h0 : s = 0 → r = 0) :
    0 ≤ kg r s ∧ (kg r s = 0 → r = s) := by
  unfold kg
  rcases hs.lt_or_eq with hs' | hs'
  · rcases hr.lt_or_eq with hr' | hr'
    · have key : Real.log (s / r) ≤ s / r - 1 := Real.log_le_sub_one_of_pos (div_pos hs' hr')
      rw [Real.log_div hs'.ne' hr'.ne'] at key
      have e : r * (s / r - 1) = s - r := by field_simp
      constructor
      · nlinarith [mul_le_mul_of_nonneg_left key hr]
      · intro h
        by_contra hne
        have hne' : s / r ≠ 1 := by
          intro h'; apply hne; field_simp at h'; linarith
        have key' := Real.log_lt_sub_one_of_pos (div_pos hs' hr') hne'
        rw [Real.log_div hs'.ne' hr'.ne'] at key'
        nlinarith [mul_lt_mul_of_pos_left key' hr']
    · subst hr'
      simp only [Real.log_zero, mul_zero, zero_mul, sub_zero, zero_sub, neg_neg, sub_self]
      exact ⟨hs'.le, fun h => by linarith⟩
  · subst hs'
    have := h0 rfl
    subst this
    simp [kg]

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma normSq_rows {W : Matrix n n ℂ} (hW : W * Wᴴ = 1) (i : n) :
    ∑ j, Complex.normSq (W i j) = 1 := by
  have := congrFun (congrFun hW i) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at this
  have h2 : ∑ j, W i j * star (W i j) = ((∑ j, Complex.normSq (W i j) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [RCLike.star_def, Complex.mul_conj]
  rw [h2] at this
  exact_mod_cast this

lemma normSq_cols {W : Matrix n n ℂ} (hW : Wᴴ * W = 1) (j : n) :
    ∑ i, Complex.normSq (W i j) = 1 := by
  have := congrFun (congrFun hW j) j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at this
  have h2 : ∑ i, star (W i j) * W i j = ((∑ i, Complex.normSq (W i j) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, RCLike.star_def, Complex.mul_conj]
  rw [h2] at this
  exact_mod_cast this

/-- the abstract strict Klein inequality in eigen-coordinates. -/
lemma klein_coord (W : Matrix n n ℂ) (hW1 : W * Wᴴ = 1) (hW2 : Wᴴ * W = 1) (r s : n → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hs : ∀ j, 0 ≤ s j) (hrs : ∑ i, r i = ∑ j, s j)
    (hsupp : ∀ i j, W i j ≠ 0 → s j = 0 → r i = 0) :
    0 ≤ ∑ i, r i * Real.log (r i) - ∑ i, ∑ j, Complex.normSq (W i j) * (r i * Real.log (s j)) ∧
    (∑ i, r i * Real.log (r i) - ∑ i, ∑ j, Complex.normSq (W i j) * (r i * Real.log (s j)) ≤ 0 →
      ∀ i j, W i j ≠ 0 → r i = s j) := by
  have hk : ∀ i j, 0 ≤ kg (r i) (s j) ∨ W i j = 0 := by
    intro i j
    by_cases h : W i j = 0
    · exact Or.inr h
    · exact Or.inl (kg_nonneg (hr i) (hs j) (hsupp i j h)).1
  have ht : ∀ i j, 0 ≤ Complex.normSq (W i j) * kg (r i) (s j) := by
    intro i j
    rcases hk i j with h | h
    · exact mul_nonneg (Complex.normSq_nonneg _) h
    · simp [h]
  have hD : ∑ i, r i * Real.log (r i) - ∑ i, ∑ j, Complex.normSq (W i j) * (r i * Real.log (s j)) =
      ∑ i, ∑ j, Complex.normSq (W i j) * kg (r i) (s j) := by
    have e1 : ∀ i, r i * Real.log (r i) = ∑ j, Complex.normSq (W i j) * (r i * Real.log (r i)) := by
      intro i; rw [← Finset.sum_mul, normSq_rows hW1, one_mul]
    have e2 : ∑ i, ∑ j, Complex.normSq (W i j) * (r i - s j) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [Finset.sum_comm (f := fun i j => Complex.normSq (W i j) * s j)]
      simp only [← Finset.sum_mul, normSq_rows hW1, normSq_cols hW2, one_mul, hrs, sub_self]
    have e3 : ∑ i, ∑ j, Complex.normSq (W i j) * kg (r i) (s j) =
        ∑ i, ∑ j, Complex.normSq (W i j) * (r i * Real.log (r i) - r i * Real.log (s j)) -
          ∑ i, ∑ j, Complex.normSq (W i j) * (r i - s j) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold kg; ring
    rw [e3, e2, sub_zero, Finset.sum_congr rfl fun i _ => e1 i, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hD]
  refine ⟨Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ht i j, fun hle i j hij => ?_⟩
  have h0 : ∑ i, ∑ j, Complex.normSq (W i j) * kg (r i) (s j) = 0 :=
    le_antisymm hle (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ht i j)
  have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => ht i j).1 h0 i (Finset.mem_univ _)
  have hij0 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => ht i j).1 hi j (Finset.mem_univ _)
  have hn : Complex.normSq (W i j) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  have hkg : kg (r i) (s j) = 0 := (mul_eq_zero.1 hij0).resolve_left hn
  exact (kg_nonneg (hr i) (hs j) (hsupp i j hij)).2 hkg

end X4P3

-- ===== P3E =====

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

set_option linter.unusedSectionVars false

namespace X4P3

open QAlgorithms

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma cfc_eq_spec {Y : Matrix n n ℂ} (hY : Y.IsHermitian) (f : ℝ → ℝ) :
    cfc f Y = (hY.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => ((f (hY.eigenvalues i) : ℝ) : ℂ)) *
        star (hY.eigenvectorUnitary : Matrix n n ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

lemma spec_eq {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    Y = (hY.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => ((hY.eigenvalues i : ℝ) : ℂ)) *
        star (hY.eigenvectorUnitary : Matrix n n ℂ) := by
  conv_lhs => rw [hY.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rfl

lemma tr_cfc {Y : Matrix n n ℂ} (hY : Y.IsHermitian) (f : ℝ → ℝ) :
    (cfc f Y).trace.re = ∑ i, f (hY.eigenvalues i) := by
  rw [cfc_eq_spec hY, Matrix.trace_mul_cycle, Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2,
    one_mul, Matrix.trace_diagonal, Complex.re_sum]
  simp

theorem klein_strict (ρ σ : Matrix n n ℂ) (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ)
    (hker : LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin) (hne : ρ ≠ σ) :
    0 < (cfc (fun x : ℝ => x * Real.log x) ρ - ρ * cfc Real.log σ).trace.re := by
  have hA := hρ.1.isHermitian
  have hB := hσ.1.isHermitian
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  set V : Matrix n n ℂ := (hB.eigenvectorUnitary : Matrix n n ℂ) with hV
  set r := hA.eigenvalues with hr
  set s := hB.eigenvalues with hs
  have hU1 : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hU2 : star U * U = 1 := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  have hV1 : V * star V = 1 := Unitary.mul_star_self_of_mem hB.eigenvectorUnitary.2
  have hV2 : star V * V = 1 := Unitary.star_mul_self_of_mem hB.eigenvectorUnitary.2
  set R := Matrix.diagonal (fun i => ((r i : ℝ) : ℂ)) with hR
  set S := Matrix.diagonal (fun i => ((s i : ℝ) : ℂ)) with hS
  set Λ := Matrix.diagonal (fun i => ((Real.log (s i) : ℝ) : ℂ)) with hΛ
  have eρ : ρ = U * R * star U := spec_eq hA
  have eσ : σ = V * S * star V := spec_eq hB
  have eL : cfc Real.log σ = V * Λ * star V := cfc_eq_spec hB Real.log
  set W := star U * V with hW
  have hW1 : W * Wᴴ = 1 := by
    rw [hW, Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose,
      star_star]
    calc star U * V * (star V * U) = star U * (V * star V) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hV1, Matrix.mul_one, hU2]
  have hW2 : Wᴴ * W = 1 := by
    rw [hW, Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose,
      star_star]
    calc star V * U * (star U * V) = star V * (U * star U) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU1, Matrix.mul_one, hV2]
  have hr0 : ∀ i, 0 ≤ r i := hρ.1.eigenvalues_nonneg
  have hs0 : ∀ j, 0 ≤ s j := hσ.1.eigenvalues_nonneg
  have hrs : ∑ i, r i = ∑ j, s j := by
    have h1 := hA.trace_eq_sum_eigenvalues
    have h2 := hB.trace_eq_sum_eigenvalues
    rw [hρ.2] at h1; rw [hσ.2] at h2
    have h1' : (1 : ℝ) = ∑ i, r i := by
      have := congrArg Complex.re h1; simpa [hr] using this
    have h2' : (1 : ℝ) = ∑ i, s i := by
      have := congrArg Complex.re h2; simpa [hs] using this
    rw [← h1', ← h2']
  -- trace of the cross term
  have htr : (ρ * cfc Real.log σ).trace.re =
      ∑ i, ∑ j, Complex.normSq (W i j) * (r i * Real.log (s j)) := by
    have e : ρ * cfc Real.log σ = U * (R * W * Λ * Wᴴ) * star U := by
      rw [eρ, eL, hW, Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose,
        ← Matrix.star_eq_conjTranspose, star_star]
      calc U * R * star U * (V * Λ * star V) = U * R * star U * (V * Λ * star V) * (U * star U) := by
            rw [hU1, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hU2, Matrix.one_mul, Matrix.trace,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag, Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hΛ, Matrix.mul_diagonal, hR, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
    rw [show (r i : ℂ) * W i j * (Real.log (s j) : ℂ) * star (W i j) =
      ((r i * Real.log (s j) : ℝ) : ℂ) * (W i j * conj (W i j)) by
        rw [Complex.star_def]; push_cast; ring, Complex.mul_conj, ← Complex.ofReal_mul,
      Complex.ofReal_re, mul_comm]
  -- support condition
  have hsupp : ∀ i j, W i j ≠ 0 → s j = 0 → r i = 0 := by
    intro i j hij hsj
    set v : n → ℂ := fun k => V k j with hv
    have hσV : σ * V = V * S := by
      rw [eσ]
      calc V * S * star V * V = V * S * (star V * V) := by simp only [Matrix.mul_assoc]
        _ = V * S := by rw [hV2, Matrix.mul_one]
    have hσv : σ *ᵥ v = 0 := by
      ext k
      have := congrFun (congrFun hσV k) j
      rw [hS, Matrix.mul_diagonal, hsj, Complex.ofReal_zero, mul_zero] at this
      change (σ * V) k j = 0
      exact this
    have hρv : ρ *ᵥ v = 0 := by
      have : v ∈ LinearMap.ker σ.mulVecLin := by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hσv]
      have h2 := hker this
      rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h2
    -- (V* ρ V)_jj = Σ_i r_i |W_ij|²
    have hq : (star V * ρ * V) j j = ((∑ i, r i * Complex.normSq (W i j) : ℝ) : ℂ) := by
      have e : star V * ρ * V = Wᴴ * R * W := by
        rw [eρ, hW, Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose,
          ← Matrix.star_eq_conjTranspose, star_star]
        simp only [Matrix.mul_assoc]
      rw [e, Matrix.mul_apply]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hR, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
      rw [show star (W i j) * (r i : ℂ) * W i j = (r i : ℂ) * (W i j * conj (W i j)) by
        rw [Complex.star_def]; ring, Complex.mul_conj]
    have hq0 : (star V * ρ * V) j j = 0 := by
      rw [Matrix.mul_assoc, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      have : (ρ * V) k j = 0 := congrFun hρv k
      rw [this, mul_zero]
    rw [hq0] at hq
    have hsum : ∑ i, r i * Complex.normSq (W i j) = 0 := by exact_mod_cast hq.symm
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      mul_nonneg (hr0 i) (Complex.normSq_nonneg _)).1 hsum i (Finset.mem_univ _)
    have hn : Complex.normSq (W i j) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
    exact (mul_eq_zero.1 this).resolve_right hn
  obtain ⟨h0, heq⟩ := klein_coord W hW1 hW2 r s hr0 hs0 hrs hsupp
  rw [Matrix.trace_sub, Complex.sub_re, tr_cfc hA, htr]
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    apply hne
    have hRW : R * W = W * S := by
      ext i j
      simp only [hR, hS, Matrix.diagonal_mul, Matrix.mul_diagonal]
      by_cases hij : W i j = 0
      · rw [hij]; ring
      · rw [heq h.symm.le i j hij, mul_comm]
    have hVUW : V = U * W := by
      rw [hW, ← Matrix.mul_assoc, hU1, Matrix.one_mul]
    rw [eρ, eσ, hVUW, star_mul, Matrix.star_eq_conjTranspose W]
    calc U * R * star U = U * R * (W * Wᴴ) * star U := by rw [hW1, Matrix.mul_one]
      _ = U * (R * W) * Wᴴ * star U := by simp only [Matrix.mul_assoc]
      _ = U * W * S * Wᴴ * star U := by rw [hRW]; simp only [Matrix.mul_assoc]
      _ = U * W * S * (Wᴴ * star U) := by simp only [Matrix.mul_assoc]

end X4P3

-- ===== P3F =====

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

set_option linter.unusedSectionVars false

namespace X4P3

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

variable {d : ℕ}

lemma idT_ap (Φ : Maps d d) (τ : Mat (Fin d × Fin d)) (p q : Fin d × Fin d) :
    idTensorSuperop (R := Fin d) (Φ : Superop (Fin d) (Fin d)) τ p q =
      Φ (Matrix.of fun i i' => τ (p.1, i) (q.1, i')) p.2 q.2 := rfl

/-- block `(a,b)` of an operator on reference ⊗ input. -/
def blk (τ : Mat (Fin d × Fin d)) (a b : Fin d) : Mat (Fin d) := Matrix.of fun i i' => τ (a, i) (b, i')

lemma omega_ap (a i : Fin d) :
    omega d (a, i) = if a = i then (((Real.sqrt d)⁻¹ : ℝ) : ℂ) else 0 := by
  simp [omega]

lemma blk_iso (hd : 0 < d) (p : ℝ) (a b : Fin d) :
    blk (isotropic d p) a b = ((p / d : ℝ) : ℂ) • Matrix.single a b 1 +
      (if a = b then (((1 - p) / (d : ℝ) ^ 2 : ℝ) : ℂ) else 0) • (1 : Mat (Fin d)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  ext i i'
  simp only [blk, isotropic, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    pureDensity, omega_ap, Matrix.one_apply, Prod.mk.injEq, Matrix.single_apply]
  by_cases h1 : a = i <;> by_cases h2 : b = i' <;> by_cases h3 : a = b <;> by_cases h4 : i = i' <;>
    simp_all
  all_goals
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    push_cast; ring

/-- trace over the reference. -/
def ptr (τ : Mat (Fin d × Fin d)) : Mat (Fin d) := ∑ a, blk τ a a

lemma ptr_idT (Φ : Maps d d) (τ : Mat (Fin d × Fin d)) :
    ptr (idTensorSuperop (R := Fin d) (Φ : Superop (Fin d) (Fin d)) τ) = Φ (ptr τ) := by
  unfold ptr
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ext i j
  rfl

lemma ptr_iso (hd : 0 < d) (p : ℝ) : ptr (isotropic d p) = ((1 / d : ℝ) : ℂ) • (1 : Mat (Fin d)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold ptr
  simp only [blk_iso hd, if_true, Finset.sum_add_distrib, ← Finset.sum_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply,
    smul_eq_mul, Matrix.one_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  by_cases h : i = j
  · subst h
    simp only [and_self, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, nsmul_eq_mul]
    push_cast
    field_simp
    ring
  · simp only [h, if_false, mul_zero, add_zero]
    exact Finset.sum_eq_zero fun x _ => by
      rw [if_neg (fun (h' : x = i ∧ x = j) => h (h'.1 ▸ h'.2)), mul_zero]

lemma blk_idT (Φ : Maps d d) (τ : Mat (Fin d × Fin d)) (a b : Fin d) :
    blk (idTensorSuperop (R := Fin d) (Φ : Superop (Fin d) (Fin d)) τ) a b = Φ (blk τ a b) := by
  ext i j; rfl

theorem out_ne (hd : 0 < d) (p : ℝ) (hp : p ≠ 0) (Φ N : Maps d d)
    (h : idTensorSuperop (R := Fin d) (Φ : Superop (Fin d) (Fin d)) (isotropic d p) =
      idTensorSuperop (R := Fin d) (N : Superop (Fin d) (Fin d)) (isotropic d p)) : Φ = N := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : Φ 1 = N 1 := by
    have := congrArg ptr h
    rw [ptr_idT, ptr_idT, ptr_iso hd, map_smul, map_smul] at this
    have hc : ((1 / d : ℝ) : ℂ) ≠ 0 := by
      have : (1 / d : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    exact smul_right_injective _ hc this
  have h2 : ∀ a b, Φ (Matrix.single a b 1) = N (Matrix.single a b 1) := by
    intro a b
    have := congrArg (fun τ => blk τ a b) h
    simp only [blk_idT, blk_iso hd, map_add, map_smul, h1] at this
    have hc : ((p / d : ℝ) : ℂ) ≠ 0 := by
      have : (p / d : ℝ) ≠ 0 := div_ne_zero hp hd'.ne'
      exact_mod_cast this
    exact smul_right_injective _ hc (add_right_cancel this)
  apply ContinuousLinearMap.ext
  intro X
  rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [show Matrix.single a b (X a b) = X a b • Matrix.single a b (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, map_smul, h2]

end X4P3

-- ===== HA =====

noncomputable section
set_option linter.unusedSectionVars false
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace X4H
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

/-! isometric padding along an injective index map -/

section pad
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J]
  [DecidableEq K]

def Vm (e : I → J) : Matrix J I ℂ := Matrix.of fun j i => if j = e i then 1 else 0

def pad (e : I → J) (X : Matrix I I ℂ) : Matrix J J ℂ := Vm e * X * (Vm e)ᴴ

lemma Vm_iso {e : I → J} (he : Function.Injective e) : (Vm e)ᴴ * Vm e = 1 := by
  ext i i'
  simp only [Vm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (e i)]
  · by_cases h : i = i'
    · subst h; simp
    · simp [h, he.ne h]
  · intro j _ hj; simp [hj]
  · simp

lemma pad_apply (e : I → J) (X : Matrix I I ℂ) (j j' : J) :
    pad e X j j' = ∑ i, ∑ i', (if j = e i then 1 else 0) * X i i' * (if j' = e i' then 1 else 0) := by
  simp only [pad, Vm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

lemma pad_ee {e : I → J} (he : Function.Injective e) (X : Matrix I I ℂ) (i i' : I) :
    pad e X (e i) (e i') = X i i' := by
  rw [pad_apply, Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i']
    · simp
    · intro b _ hb; simp [(he.ne hb).symm]
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun c _ => ?_
    have : e i ≠ e b := he.ne (Ne.symm hb)
    simp [this]
  · simp

lemma pad_out {e : I → J} (X : Matrix I I ℂ) (j j' : J)
    (h : j ∉ Set.range e ∨ j' ∉ Set.range e) : pad e X j j' = 0 := by
  rw [pad_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun i' _ => ?_
  rcases h with h | h
  · have : j ≠ e i := fun hh => h ⟨i, hh.symm⟩
    simp [this]
  · have : j' ≠ e i' := fun hh => h ⟨i', hh.symm⟩
    simp [this]

lemma pad_ext {e : I → J} (he : Function.Injective e) {X : Matrix I I ℂ} {Z : Matrix J J ℂ}
    (h1 : ∀ i i', Z (e i) (e i') = X i i')
    (h2 : ∀ j j', (j ∉ Set.range e ∨ j' ∉ Set.range e) → Z j j' = 0) : Z = pad e X := by
  ext j j'
  by_cases hj : j ∈ Set.range e
  · by_cases hj' : j' ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj; obtain ⟨i', rfl⟩ := hj'
      rw [h1, pad_ee he]
    · rw [h2 _ _ (Or.inr hj'), pad_out _ _ _ (Or.inr hj')]
  · rw [h2 _ _ (Or.inl hj), pad_out _ _ _ (Or.inl hj)]

lemma pad_ext_surj {e : I → J} (he : Function.Bijective e) {X : Matrix I I ℂ} {Z : Matrix J J ℂ}
    (h1 : ∀ i i', Z (e i) (e i') = X i i') : Z = pad e X :=
  pad_ext he.1 h1 fun j j' h => by
    rcases h with h | h
    · exact absurd (he.2 j) (by simpa [Set.mem_range] using h)
    · exact absurd (he.2 j') (by simpa [Set.mem_range] using h)

lemma pad_pad {e : I → J} {f : J → K} (he : Function.Injective e) (hf : Function.Injective f)
    (X : Matrix I I ℂ) : pad f (pad e X) = pad (f ∘ e) X :=
  pad_ext (hf.comp he) (fun i i' => by simp only [Function.comp, pad_ee hf, pad_ee he])
    fun j j' h => by
      by_cases hj : j ∈ Set.range f
      · by_cases hj' : j' ∈ Set.range f
        · obtain ⟨a, rfl⟩ := hj; obtain ⟨a', rfl⟩ := hj'
          rw [pad_ee hf]
          refine pad_out _ _ _ ?_
          rcases h with h | h
          · left; rintro ⟨i, rfl⟩; exact h ⟨i, rfl⟩
          · right; rintro ⟨i, rfl⟩; exact h ⟨i, rfl⟩
        · exact pad_out _ _ _ (Or.inr hj')
      · exact pad_out _ _ _ (Or.inl hj)

lemma trace_pad {e : I → J} (he : Function.Injective e) (X : Matrix I I ℂ) :
    (pad e X).trace = X.trace := by
  rw [pad, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Vm_iso he, Matrix.one_mul]

lemma pad_psd (e : I → J) {X : Matrix I I ℂ} (hX : X.PosSemidef) : (pad e X).PosSemidef :=
  hX.mul_mul_conjTranspose_same _

lemma pad_density {e : I → J} (he : Function.Injective e) {X : Matrix I I ℂ}
    (hX : IsDensityMatrix X) : IsDensityMatrix (pad e X) :=
  ⟨pad_psd e hX.1, by rw [trace_pad he, hX.2]⟩

lemma effectProb_pad {e : I → J} (he : Function.Injective e) (T Z : Matrix I I ℂ) :
    effectProb (pad e T) (pad e Z) = effectProb T Z := by
  unfold effectProb pad
  congr 1
  have h := Vm_iso he
  calc (Vm e * T * (Vm e)ᴴ * (Vm e * Z * (Vm e)ᴴ)).trace
      = (Vm e * (T * ((Vm e)ᴴ * Vm e) * Z) * (Vm e)ᴴ).trace := by
        simp only [Matrix.mul_assoc]
    _ = (T * Z).trace := by
        rw [h, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h, Matrix.one_mul]

lemma one_sub_pad {e : I → J} (he : Function.Injective e) (T : Matrix I I ℂ) :
    (1 - pad e T) = pad e (1 - T) + (1 - Vm e * (Vm e)ᴴ) := by
  simp only [pad, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  abel

lemma proj_psd {e : I → J} (he : Function.Injective e) :
    (1 - Vm e * (Vm e)ᴴ : Matrix J J ℂ).PosSemidef := by
  have hP : (1 - Vm e * (Vm e)ᴴ : Matrix J J ℂ) =
      (1 - Vm e * (Vm e)ᴴ)ᴴ * (1 - Vm e * (Vm e)ᴴ) := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one]
    have : Vm e * (Vm e)ᴴ * (Vm e * (Vm e)ᴴ) = Vm e * (Vm e)ᴴ := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Vm e)ᴴ, Vm_iso he, Matrix.one_mul]
    rw [this]; abel
  rw [hP]; exact Matrix.posSemidef_conjTranspose_mul_self _

lemma pad_effect {e : I → J} (he : Function.Injective e) {T : Matrix I I ℂ} (hT : IsEffect T) :
    IsEffect (pad e T) :=
  ⟨pad_psd e hT.1, by rw [one_sub_pad he]; exact (pad_psd e hT.2).add (proj_psd he)⟩

lemma effectProb_one_sub_pad {e : I → J} (he : Function.Injective e) (T Z : Matrix I I ℂ) :
    effectProb (1 - pad e T) (pad e Z) = effectProb (1 - T) Z := by
  have h1 : (1 : Matrix J J ℂ) - pad e T = pad e (1 - T) + (1 - Vm e * (Vm e)ᴴ) := one_sub_pad he T
  have h0 : effectProb (1 - Vm e * (Vm e)ᴴ : Matrix J J ℂ) (pad e Z) = 0 := by
    unfold effectProb pad
    have : (1 - Vm e * (Vm e)ᴴ) * (Vm e * Z * (Vm e)ᴴ) = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.mul_assoc (Vm e) (Vm e)ᴴ, Vm_iso he, Matrix.mul_one, sub_self]
    rw [this]; simp
  rw [h1]
  unfold effectProb at *
  rw [Matrix.add_mul, Matrix.trace_add, Complex.add_re, h0, add_zero]
  exact effectProb_pad he _ _

/-- tests transport along isometric paddings. -/
lemma testing_pad {e : I → J} (he : Function.Injective e) (S : Set (Matrix I I ℂ))
    (S' : Set (Matrix J J ℂ)) (hS : ∀ Y ∈ S', ∃ Z ∈ S, Y = pad e Z) (σ : Matrix I I ℂ)
    (eps : ℝ) : testingBits S σ eps ≤ testingBits S' (pad e σ) eps := by
  unfold testingBits
  refine iSup_le fun T => ?_
  obtain ⟨T, hTe, hT1⟩ := T
  refine le_iSup_of_le ⟨pad e T, pad_effect he hTe, ?_⟩ (le_of_eq ?_)
  · intro ρ hρ
    obtain ⟨Z, hZ, rfl⟩ := hS ρ hρ
    rw [effectProb_one_sub_pad he]; exact hT1 Z hZ
  · simp only [effectProb_pad he]

end pad

section sq
open scoped Matrix.Norms.L2Operator MatrixOrder
set_option backward.isDefEq.respectTransparency false in
lemma psd_factor {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (h : X.PosSemidef) :
    ∃ B : Matrix n n ℂ, X = Bᴴ * B := by
  have h0 : 0 ≤ X := h.nonneg
  refine ⟨CFC.sqrt X, ?_⟩
  have hs : IsSelfAdjoint (CFC.sqrt X) := (CFC.sqrt_nonneg X).isSelfAdjoint
  rw [← Matrix.star_eq_conjTranspose, hs.star_eq, CFC.sqrt_mul_sqrt_self X h0]
end sq

end X4H

-- ===== HB =====

noncomputable section
set_option linter.unusedSectionVars false
open scoped Matrix ComplexConjugate ComplexOrder ENNReal Kronecker

namespace X4H
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

/-! copies over an arbitrary finite index type -/

section copies
variable {I : Type*} [Fintype I] [DecidableEq I]

def copiesT (V : Type*) [Fintype V] (X : Matrix I I ℂ) : Matrix (V → I) (V → I) ℂ :=
  Matrix.of fun x y => ∏ v, X (x v) (y v)

lemma copies_eq (m : ℕ) (X : Matrix I I ℂ) : copies m X = copiesT (Fin m) X := rfl

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma copies_pad {J : Type*} [Fintype J] [DecidableEq J] {e : I → J}
    (he : Function.Injective e) (X : Matrix I I ℂ) :
    copiesT V (pad e X) = pad (fun x v => e (x v)) (copiesT V X) := by
  have hinj : Function.Injective (fun (x : V → I) v => e (x v)) :=
    fun x y h => funext fun v => he (congrFun h v)
  refine pad_ext hinj (fun x y => by simp [copiesT, pad_ee he]) fun y y' h => ?_
  have key : ∀ z : V → J, z ∉ Set.range (fun (x : V → I) v => e (x v)) → ∃ v, z v ∉ Set.range e := by
    intro z hz
    by_contra hc
    push Not at hc
    exact hz ⟨fun v => (hc v).choose, funext fun v => (hc v).choose_spec⟩
  simp only [copiesT, Matrix.of_apply]
  rcases h with h | h
  · obtain ⟨v, hv⟩ := key y h
    exact Finset.prod_eq_zero (Finset.mem_univ v) (pad_out _ _ _ (Or.inl hv))
  · obtain ⟨v, hv⟩ := key y' h
    exact Finset.prod_eq_zero (Finset.mem_univ v) (pad_out _ _ _ (Or.inr hv))

/-- reindexing `V × U ≃ W` for plain functions. -/
def eW {U W : Type*} (φ : V × U ≃ W) (α : Type*) : (V → U → α) ≃ (W → α) :=
  (Equiv.curry V U α).symm.trans (Equiv.arrowCongr φ (Equiv.refl α))

lemma eW_apply {U W α : Type*} (φ : V × U ≃ W) (g : V → U → α) (w : W) :
    eW φ α g w = g (φ.symm w).1 (φ.symm w).2 := rfl

lemma eW_symm_apply {U W α : Type*} (φ : V × U ≃ W) (c : W → α) (v : V) (u : U) :
    (eW φ α).symm c v u = c (φ (v, u)) := rfl

lemma copies_copies {U W : Type*} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    (φ : V × U ≃ W) (Y : Matrix I I ℂ) :
    copiesT V (copiesT U Y) = pad (eW φ I).symm (copiesT W Y) := by
  refine pad_ext_surj (eW φ I).symm.bijective fun c c' => ?_
  simp only [copiesT, Matrix.of_apply, eW_symm_apply]
  rw [← Fintype.prod_prod_type' (f := fun v u => Y (c (φ (v, u))) (c' (φ (v, u))))]
  exact φ.prod_comp (fun w => Y (c w) (c' w))

lemma copies_psd {X : Matrix I I ℂ} (hX : X.PosSemidef) : (copiesT V X).PosSemidef := by
  obtain ⟨B, rfl⟩ := psd_factor hX
  have : copiesT V (Bᴴ * B) = (copiesT V B)ᴴ * copiesT V B := by
    ext x y
    simp only [copiesT, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.prod_mul_distrib, star_prod]
  rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _

lemma copies_trace (X : Matrix I I ℂ) : (copiesT V X).trace = X.trace ^ Fintype.card V := by
  simp only [Matrix.trace, Matrix.diag, copiesT, Matrix.of_apply]
  rw [← Fintype.prod_sum (fun (_ : V) i => X i i), Finset.prod_const, Finset.card_univ]

lemma copies_density {X : Matrix I I ℂ} (hX : IsDensityMatrix X) : IsDensityMatrix (copiesT V X) :=
  ⟨copies_psd hX.1, by rw [copies_trace, hX.2, one_pow]⟩

end copies

/-! block outputs over an arbitrary finite set of uses -/

section outT
variable {r a b : ℕ}

abbrev RegT (U : Type*) (r a : ℕ) := (U → Fin r) × (U → Fin a)

def ker (Φ : Superop (Fin a) (Fin b)) (u u' : Fin a) (v v' : Fin b) : ℂ :=
  Φ (Matrix.single u u' 1) v v'

def outT (U : Type*) [Fintype U] [DecidableEq U] (Φ : Superop (Fin a) (Fin b)) (X : Mat (RegT U r a)) :
    Mat (RegT U r b) :=
  Matrix.of fun p q => ∑ x : U → Fin a, ∑ x' : U → Fin a,
    X (p.1, x) (q.1, x') * ∏ u, ker Φ (x u) (x' u) (p.2 u) (q.2 u)

lemma output_eq {k : ℕ} (Φ : Maps a b) (X : Mat (Reg r a k)) :
    output r k Φ X = outT (Fin k) (Φ : Superop (Fin a) (Fin b)) X := rfl

variable {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
  [Fintype W] [DecidableEq W]

def blk (φ : V × U ≃ W) (r a : ℕ) (F : V → RegT U r a) : RegT W r a :=
  (eW φ _ (fun v => (F v).1), eW φ _ (fun v => (F v).2))

lemma blk_bij (φ : V × U ≃ W) (r a : ℕ) : Function.Bijective (blk φ r a) :=
  ((Equiv.arrowProdEquivProdArrow V (fun _ => U → Fin r) (fun _ => U → Fin a)).trans
    (Equiv.prodCongr (eW φ _) (eW φ _))).bijective

lemma outT_blk (φ : V × U ≃ W) (Φ : Superop (Fin a) (Fin b)) (X : Mat (RegT U r a)) :
    outT W Φ (pad (blk φ r a) (copiesT V X)) = pad (blk φ r b) (copiesT V (outT U Φ X)) := by
  refine pad_ext_surj (blk_bij φ r b) fun F F' => ?_
  simp only [outT, copiesT, Matrix.of_apply]
  rw [Fintype.prod_sum]
  simp only [Fintype.prod_sum]
  rw [← (eW φ (Fin a)).bijective.sum_comp]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← (eW φ (Fin a)).bijective.sum_comp]
  refine Finset.sum_congr rfl fun g' _ => ?_
  have h1 : ((blk φ r b F).1, eW φ (Fin a) g) = blk φ r a (fun v => ((F v).1, g v)) := rfl
  have h2 : ((blk φ r b F').1, eW φ (Fin a) g') = blk φ r a (fun v => ((F' v).1, g' v)) := rfl
  rw [h1, h2, pad_ee (blk_bij φ r a).1, Matrix.of_apply, Finset.prod_mul_distrib]
  congr 1
  refine (Fintype.prod_equiv φ.symm _
    (fun p : V × U => ker Φ (g p.1 p.2) (g' p.1 p.2) ((F p.1).2 p.2) ((F' p.1).2 p.2))
    (fun w => rfl)).trans ?_
  exact Fintype.prod_prod_type _

/-- reindexing `U ⊕ U' ≃ W` for plain functions. -/
def eS {U' : Type*} (φ : U ⊕ U' ≃ W) (α : Type*) : (U → α) × (U' → α) ≃ (W → α) :=
  (Equiv.sumArrowEquivProdArrow U U' α).symm.trans (Equiv.arrowCongr φ (Equiv.refl α))

lemma eS_inl {U' α : Type*} (φ : U ⊕ U' ≃ W) (g : U → α) (h : U' → α) (u : U) :
    eS φ α (g, h) (φ (Sum.inl u)) = g u := by simp [eS]

lemma eS_inr {U' α : Type*} (φ : U ⊕ U' ≃ W) (g : U → α) (h : U' → α) (u : U') :
    eS φ α (g, h) (φ (Sum.inr u)) = h u := by simp [eS]

variable {U' : Type*} [Fintype U'] [DecidableEq U']

def blk2 (φ : U ⊕ U' ≃ W) (r a : ℕ) (P : RegT U r a × RegT U' r a) : RegT W r a :=
  (eS φ _ (P.1.1, P.2.1), eS φ _ (P.1.2, P.2.2))

lemma blk2_bij (φ : U ⊕ U' ≃ W) (r a : ℕ) : Function.Bijective (blk2 φ r a) :=
  ((Equiv.prodProdProdComm _ _ _ _).trans (Equiv.prodCongr (eS φ _) (eS φ _))).bijective

lemma outT_sum (φ : U ⊕ U' ≃ W) (Φ : Superop (Fin a) (Fin b)) (X : Mat (RegT U r a))
    (Z : Mat (RegT U' r a)) :
    outT W Φ (pad (blk2 φ r a) (X ⊗ₖ Z)) = pad (blk2 φ r b) (outT U Φ X ⊗ₖ outT U' Φ Z) := by
  refine pad_ext_surj (blk2_bij φ r b) fun P P' => ?_
  simp only [outT, Matrix.kroneckerMap_apply, Matrix.of_apply, Finset.sum_mul_sum]
  rw [← (eS φ (Fin a)).bijective.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => ?_
  rw [← (eS φ (Fin a)).bijective.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun g' _ => Finset.sum_congr rfl fun h' _ => ?_
  have h1 : ((blk2 φ r b P).1, eS φ (Fin a) (g, h)) = blk2 φ r a ((P.1.1, g), (P.2.1, h)) := rfl
  have h2 : ((blk2 φ r b P').1, eS φ (Fin a) (g', h')) =
    blk2 φ r a ((P'.1.1, g'), (P'.2.1, h')) := rfl
  rw [h1, h2, pad_ee (blk2_bij φ r a).1, Matrix.kroneckerMap_apply]
  rw [← φ.prod_comp, Fintype.prod_sum_type]
  simp only [blk2, eS_inl, eS_inr]
  ring

lemma trace_outT (Φ : Superop (Fin a) (Fin b))
    (hΦ : ∀ u u', ∑ v, ker Φ u u' v v = if u = u' then 1 else 0)
    (X : Mat (RegT U r a)) : (outT U Φ X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, outT, Matrix.of_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have : ∀ x' : U → Fin a, ∑ y : U → Fin b, ∏ u, ker Φ (x u) (x' u) (y u) (y u) =
      if x = x' then 1 else 0 := by
    intro x'
    rw [← Fintype.prod_sum (fun u j => ker Φ (x u) (x' u) j j)]
    simp only [hΦ, Finset.prod_boole, Finset.mem_univ, true_implies, funext_iff, forall_const]
  simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma chan_trace {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] {Φ : Superop I K}
    (hΦ : IsChannel Φ) (A : Matrix I I ℂ) : (Φ A).trace = A.trace := by
  obtain ⟨m, E, hE, hΦ⟩ := hΦ
  rw [hΦ, krausApply, Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_comm _ (E _)ᴴ, ← Matrix.mul_assoc]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hE, Matrix.one_mul]

lemma chan_single {Φ : Superop (Fin a) (Fin b)} (hΦ : IsChannel Φ) (u u' : Fin a) :
    ∑ v, ker Φ u u' v v = if u = u' then 1 else 0 := by
  have := chan_trace hΦ (Matrix.single u u' 1)
  simp only [Matrix.trace, Matrix.diag] at this
  simp only [ker, this, Matrix.single_apply]
  by_cases h : u = u'
  · simp [h]
  · simp [h, Ne.symm h]

end outT

/-! tests ignoring a tensor factor -/

section kron
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

lemma effectProb_kron (T Z : Matrix I I ℂ) (B : Matrix K K ℂ) (hB : B.trace = 1) :
    effectProb (T ⊗ₖ (1 : Matrix K K ℂ)) (Z ⊗ₖ B) = effectProb T Z := by
  unfold effectProb
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.trace_kronecker, hB, mul_one]

lemma testing_kron (S : Set (Matrix I I ℂ)) (S' : Set (Matrix (I × K) (I × K) ℂ))
    (hS : ∀ Y ∈ S', ∃ Z ∈ S, ∃ B : Matrix K K ℂ, B.trace = 1 ∧ Y = Z ⊗ₖ B) (σ : Matrix I I ℂ)
    (B0 : Matrix K K ℂ) (hB0 : B0.trace = 1) (eps : ℝ) :
    testingBits S σ eps ≤ testingBits S' (σ ⊗ₖ B0) eps := by
  unfold testingBits
  refine iSup_le fun T => ?_
  obtain ⟨T, hTe, hT1⟩ := T
  have hsub : (1 : Matrix (I × K) (I × K) ℂ) - T ⊗ₖ (1 : Matrix K K ℂ) = (1 - T) ⊗ₖ 1 := by
    rw [← Matrix.one_kronecker_one, sub_eq_iff_eq_add, ← Matrix.add_kronecker, sub_add_cancel]
  refine le_iSup_of_le ⟨T ⊗ₖ (1 : Matrix K K ℂ), ⟨hTe.1.kronecker Matrix.PosSemidef.one, by
    rw [hsub]; exact hTe.2.kronecker Matrix.PosSemidef.one⟩, ?_⟩ (le_of_eq ?_)
  · intro ρ hρ
    obtain ⟨Z, hZ, B, hB, rfl⟩ := hS ρ hρ
    rw [hsub, effectProb_kron _ _ _ hB]; exact hT1 Z hZ
  · simp only [effectProb_kron _ _ _ hB0]

lemma kron_density {Z : Matrix I I ℂ} {B : Matrix K K ℂ} (hZ : IsDensityMatrix Z)
    (hB : IsDensityMatrix B) : IsDensityMatrix (Z ⊗ₖ B) :=
  ⟨hZ.1.kronecker hB.1, by rw [Matrix.trace_kronecker, hZ.2, hB.2, one_mul]⟩

end kron

end X4H

-- ===== HC =====

noncomputable section
set_option linter.unusedSectionVars false
open scoped Matrix ComplexConjugate ComplexOrder ENNReal Kronecker
open Filter Topology

namespace X4H
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

section rates
variable {a b : ℕ}

lemma op_mono {g g' : ℕ → ℝ → ℝ≥0∞} (h : ∀ m eps, g m eps ≤ g' m eps) :
    operational g ≤ operational g' := by
  unfold operational
  exact liminf_le_liminf (Eventually.of_forall fun eps =>
    liminf_le_liminf (Eventually.of_forall fun m => h m eps))

lemma liminf_comp_ge {g : ℕ → ℝ≥0∞} {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    liminf g atTop ≤ liminf (fun m => g (φ m)) atTop := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
  exact le_liminf_of_le (by isBoundedDefault)
    ((hφ.eventually (eventually_lt_of_lt_liminf hc)).mono fun m h => h.le)

lemma op_sub {g g' : ℕ → ℝ → ℝ≥0∞} {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (h : ∀ m eps, g (φ m) eps ≤ g' m eps) : operational g ≤ operational g' := by
  unfold operational
  exact liminf_le_liminf (Eventually.of_forall fun eps =>
    (liminf_comp_ge (g := fun n => g n eps) hφ).trans
      (liminf_le_liminf (Eventually.of_forall fun m => h m eps)))

lemma rate_set {r k : ℕ} (R : Set (Maps a b)) (N : Maps a b) {P P' : Set (Mat (Reg r a k))}
    (hP : P ⊆ P') (m : ℕ) (eps : ℝ) :
    blockRate r R N k P m eps ≤ blockRate r R N k P' m eps := by
  unfold blockRate
  refine ENNReal.div_le_div_right (iSup_le fun X => ?_) _
  exact le_iSup (fun Y : P' => testingBits {Y' | ∃ Phi ∈ R, Y' = copies (m + 1) (output r k Phi Y.1)}
    (copies (m + 1) (output r k N Y.1)) eps) ⟨X.1, hP X.2⟩

lemma adm_ps {r k : ℕ} : admissible r a k .product ⊆ admissible r a k .separable := by
  rintro X ⟨hX, tau, htau, rfl⟩
  exact ⟨hX, 1, fun _ => 1, fun _ => tau, fun _ => zero_le_one, by simp, fun _ i => htau i,
    by simp⟩

lemma adm_su {r k : ℕ} : admissible r a k .separable ⊆ admissible r a k .unrestricted :=
  fun _ hX => ⟨hX.1, trivial⟩

end rates

/-! reference padding `r = 1 ↦ r = a` -/

section ref
variable {a b k : ℕ}

def eR (ha : 0 < a) (k c : ℕ) : Reg 1 c k → Reg a c k := fun p => (fun _ => ⟨0, ha⟩, p.2)

lemma eR_inj (ha : 0 < a) (k c : ℕ) : Function.Injective (eR ha k c) := fun p q h =>
  Prod.ext (Subsingleton.elim _ _) (by have := congrArg Prod.snd h; exact this)

lemma eR_range (ha : 0 < a) {c : ℕ} (j : Reg a c k) :
    j ∈ Set.range (eR ha k c) ↔ j.1 = fun _ => ⟨0, ha⟩ :=
  ⟨by rintro ⟨p, rfl⟩; rfl, fun h => ⟨(fun _ => 0, j.2), Prod.ext h.symm rfl⟩⟩

lemma out_eR (ha : 0 < a) (Φ : Maps a b) (X : Mat (Reg 1 a k)) :
    output a k Φ (pad (eR ha k a) X) = pad (eR ha k b) (output 1 k Φ X) := by
  rw [output_eq, output_eq]
  refine pad_ext (eR_inj ha k b) (fun p q => ?_) (fun j j' h => ?_)
  · simp only [outT, Matrix.of_apply]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
    rw [show ((eR ha k b p).1, x) = eR ha k a (p.1, x) from rfl,
      show ((eR ha k b q).1, x') = eR ha k a (q.1, x') from rfl, pad_ee (eR_inj ha k a)]
    rfl
  · simp only [outT, Matrix.of_apply]
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun x' _ => ?_
    rw [pad_out, zero_mul]
    rcases h with h | h
    · left; rw [eR_range] at h ⊢; exact h
    · right; rw [eR_range] at h ⊢; exact h

def e1 (ha : 0 < a) : Fin 1 × Fin a → Fin a × Fin a := fun p => (⟨0, ha⟩, p.2)

lemma e1_inj (ha : 0 < a) : Function.Injective (e1 ha) := fun p q h =>
  Prod.ext (Subsingleton.elim _ _) (by have := congrArg Prod.snd h; exact this)

lemma pp_pad (ha : 0 < a) (tau : Fin k → Mat (Fin 1 × Fin a)) :
    pad (eR ha k a) (productProbe tau) = productProbe (fun i => pad (e1 ha) (tau i)) := by
  symm
  refine pad_ext (eR_inj ha k a) (fun p q => ?_) (fun j j' h => ?_)
  · simp only [productProbe, Matrix.of_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show ((eR ha k a p).1 i, (eR ha k a p).2 i) = e1 ha (p.1 i, p.2 i) from rfl,
      show ((eR ha k a q).1 i, (eR ha k a q).2 i) = e1 ha (q.1 i, q.2 i) from rfl,
      pad_ee (e1_inj ha)]
  · have key : ∀ jj : Reg a a k, jj ∉ Set.range (eR ha k a) →
        ∃ i, (jj.1 i, jj.2 i) ∉ Set.range (e1 ha) := by
      intro jj hj
      rw [eR_range] at hj
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hj
      exact ⟨i, by rintro ⟨p, hp⟩; exact hi (congrArg Prod.fst hp).symm⟩
    simp only [productProbe, Matrix.of_apply]
    rcases h with h | h
    · obtain ⟨i, hi⟩ := key j h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (pad_out _ _ _ (Or.inl hi))
    · obtain ⟨i, hi⟩ := key j' h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (pad_out _ _ _ (Or.inr hi))

lemma pad_sum_smul {I J ι : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Fintype ι] (e : I → J) (w : ι → ℂ) (P : ι → Matrix I I ℂ) :
    pad e (∑ j, w j • P j) = ∑ j, w j • pad e (P j) := by
  simp only [pad, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

lemma adm_pad (ha : 0 < a) {c : Correlation} {X : Mat (Reg 1 a k)}
    (hX : X ∈ admissible 1 a k c) : pad (eR ha k a) X ∈ admissible a a k c := by
  refine ⟨pad_density (eR_inj ha k a) hX.1, ?_⟩
  obtain ⟨-, h⟩ := hX
  cases c with
  | unrestricted => trivial
  | product =>
    obtain ⟨tau, htau, rfl⟩ := h
    exact ⟨fun i => pad (e1 ha) (tau i), fun i => pad_density (e1_inj ha) (htau i), pp_pad ha tau⟩
  | separable =>
    obtain ⟨q, w, tau, h0, h1, ht, rfl⟩ := h
    refine ⟨q, w, fun j i => pad (e1 ha) (tau j i), h0, h1,
      fun j i => pad_density (e1_inj ha) (ht j i), ?_⟩
    rw [pad_sum_smul]
    simp only [pp_pad]

lemma rate_ref (ha : 0 < a) (R : Set (Maps a b)) (N : Maps a b) (c : Correlation) (m : ℕ)
    (eps : ℝ) :
    blockRate 1 R N k (admissible 1 a k c) m eps ≤ blockRate a R N k (admissible a a k c) m eps := by
  unfold blockRate
  refine ENNReal.div_le_div_right (iSup_le fun X => ?_) _
  refine le_iSup_of_le (⟨pad (eR ha k a) X.1, adm_pad ha X.2⟩ : admissible a a k c) ?_
  have hE : Function.Injective (fun (x : Fin (m + 1) → Reg 1 b k) v => eR ha k b (x v)) :=
    fun x y h => funext fun v => eR_inj ha k b (congrFun h v)
  have key : ∀ Φ : Maps a b, copies (m + 1) (output a k Φ (pad (eR ha k a) X.1)) =
      pad (fun (x : Fin (m + 1) → Reg 1 b k) v => eR ha k b (x v))
        (copies (m + 1) (output 1 k Φ X.1)) := fun Φ => by
    rw [out_eR, copies_eq, copies_pad (eR_inj ha k b)]; rfl
  simp only
  rw [key N]
  refine testing_pad hE _ _ ?_ _ _
  rintro Y ⟨Φ, hΦ, rfl⟩
  exact ⟨_, ⟨Φ, hΦ, rfl⟩, key Φ⟩

lemma exp_ref (ha : 0 < a) (R : Set (Maps a b)) (N : Maps a b) (c : Correlation) :
    blockExponent 1 R N k c ≤ blockExponent a R N k c :=
  op_mono fun m eps => rate_ref ha R N c m eps

end ref

/-! regrouping `ℓ` blocks of `k` uses -/

section regroup
variable {a b k r : ℕ}

lemma rate_blk (R : Set (Maps a b)) (N : Maps a b) {ℓ : ℕ} (hℓ : 0 < ℓ) (m : ℕ) (eps : ℝ) :
    blockRate r R N k (admissible r a k .unrestricted) (ℓ * (m + 1) - 1) eps ≤
      blockRate r R N (ℓ * k) (admissible r a (ℓ * k) .unrestricted) m eps := by
  set n := ℓ * (m + 1) - 1 with hn0
  have hn : n + 1 = (m + 1) * ℓ := by
    have : 1 ≤ ℓ * (m + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [hn0, Nat.sub_add_cancel this, mul_comm]
  have hd : k * (n + 1) = ℓ * k * (m + 1) := by rw [hn]; ring
  unfold blockRate
  rw [hd]
  refine ENNReal.div_le_div_right (iSup_le fun X => ?_) _
  let φ : Fin ℓ × Fin k ≃ Fin (ℓ * k) := finProdFinEquiv
  let ψ : Fin (m + 1) × Fin ℓ ≃ Fin (n + 1) := finProdFinEquiv.trans (finCongr hn.symm)
  have hX' : pad (blk φ r a) (copiesT (Fin ℓ) X.1) ∈ admissible r a (ℓ * k) .unrestricted :=
    ⟨pad_density (blk_bij φ r a).1 (copies_density X.2.1), trivial⟩
  refine le_iSup_of_le (⟨_, hX'⟩ : admissible r a (ℓ * k) .unrestricted) ?_
  have hE1 : Function.Injective (fun (x : Fin (m + 1) → Fin ℓ → Reg r b k) v => blk φ r b (x v)) :=
    fun x y h => funext fun v => (blk_bij φ r b).1 (congrFun h v)
  have hE : Function.Injective
      ((fun (x : Fin (m + 1) → Fin ℓ → Reg r b k) v => blk φ r b (x v)) ∘
        (eW ψ (Reg r b k)).symm) := hE1.comp (eW ψ _).symm.injective
  have key : ∀ Φ : Maps a b,
      copies (m + 1) (output r (ℓ * k) Φ (pad (blk φ r a) (copiesT (Fin ℓ) X.1))) =
      pad ((fun (x : Fin (m + 1) → Fin ℓ → Reg r b k) v => blk φ r b (x v)) ∘
        (eW ψ (Reg r b k)).symm) (copies (n + 1) (output r k Φ X.1)) := fun Φ => by
    rw [output_eq, outT_blk, ← output_eq, copies_eq, copies_pad (blk_bij φ r b).1,
      copies_copies ψ, pad_pad (eW ψ _).symm.injective hE1, copies_eq]
  simp only
  rw [key N]
  refine testing_pad hE _ _ ?_ _ _
  rintro Y ⟨Φ, hΦ, rfl⟩
  exact ⟨_, ⟨Φ, hΦ, rfl⟩, key Φ⟩

lemma exp_blk (R : Set (Maps a b)) (N : Maps a b) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    blockExponent r R N k .unrestricted ≤ blockExponent r R N (ℓ * k) .unrestricted := by
  refine op_sub (φ := fun m => ℓ * (m + 1) - 1) ?_ fun m eps => rate_blk R N hℓ m eps
  refine tendsto_atTop_mono (fun m => ?_) tendsto_id
  have : m + 1 ≤ ℓ * (m + 1) := Nat.le_mul_of_pos_left _ hℓ
  simp only [id]; omega

end regroup

end X4H

-- ===== HD =====

noncomputable section
set_option linter.unusedSectionVars false
open scoped Matrix ComplexConjugate ComplexOrder ENNReal Kronecker
open Filter Topology

namespace X4H
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

section arb
variable {a b k r : ℕ}

lemma vv_density {I : Type*} [Fintype I] [DecidableEq I] (p : I) :
    IsDensityMatrix (Matrix.vecMulVec (Pi.single p (1 : ℂ)) (star (Pi.single p (1 : ℂ)))) := by
  refine ⟨Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
  simp [Matrix.trace, Matrix.vecMulVec_apply, Pi.single_apply]

lemma num_le {R : Set (Maps a b)} {N : Maps a b} (h : Setting R N) (hr : 0 < r) {n q : ℕ}
    (hq : (q + 1) * k ≤ n + 1) (eps : ℝ) :
    (⨆ X : admissible r a k .unrestricted, testingBits
        {Y | ∃ Phi ∈ R, Y = copies (q + 1) (output r k Phi X.1)}
        (copies (q + 1) (output r k N X.1)) eps) ≤
      (⨆ X : admissible r a (n + 1) .unrestricted, testingBits
        {Y | ∃ Phi ∈ R, Y = output r (n + 1) Phi X.1} (output r (n + 1) N X.1) eps) := by
  refine iSup_le fun X => ?_
  obtain ⟨ha, -, -, -, -, hR, hN, -⟩ := h
  set s := n + 1 - (q + 1) * k
  have hN' : (q + 1) * k + s = n + 1 := by omega
  let φ1 : Fin (q + 1) × Fin k ≃ Fin ((q + 1) * k) := finProdFinEquiv
  let φ2 : Fin ((q + 1) * k) ⊕ Fin s ≃ Fin (n + 1) := finSumFinEquiv.trans (finCongr hN')
  let p0 : RegT (Fin s) r a := (fun _ => ⟨0, hr⟩, fun _ => ⟨0, ha⟩)
  let ω : Mat (RegT (Fin s) r a) :=
    Matrix.vecMulVec (Pi.single p0 (1 : ℂ)) (star (Pi.single p0 (1 : ℂ)))
  have hω : IsDensityMatrix ω := vv_density p0
  let X1 := pad (blk φ1 r a) (copiesT (Fin (q + 1)) X.1)
  have hX' : pad (blk2 φ2 r a) (X1 ⊗ₖ ω) ∈ admissible r a (n + 1) .unrestricted :=
    ⟨pad_density (blk2_bij φ2 r a).1 (kron_density
      (pad_density (blk_bij φ1 r a).1 (copies_density X.2.1)) hω), trivial⟩
  refine le_iSup_of_le (⟨_, hX'⟩ : admissible r a (n + 1) .unrestricted) ?_
  have key : ∀ Φ : Maps a b, output r (n + 1) Φ (pad (blk2 φ2 r a) (X1 ⊗ₖ ω)) =
      pad (blk2 φ2 r b) (pad (blk φ1 r b) (copies (q + 1) (output r k Φ X.1)) ⊗ₖ
        outT (Fin s) (Φ : Superop (Fin a) (Fin b)) ω) := fun Φ => by
    rw [output_eq, outT_sum, outT_blk]; rfl
  have htr : ∀ Φ : Maps a b, IsChannel (Φ : Superop (Fin a) (Fin b)) →
      (outT (Fin s) (Φ : Superop (Fin a) (Fin b)) ω).trace = 1 := fun Φ hΦ => by
    rw [trace_outT _ (chan_single hΦ), hω.2]
  simp only
  rw [key N]
  refine le_trans (testing_pad (blk_bij φ1 r b).1 _
    {Y | ∃ Phi ∈ R, Y = pad (blk φ1 r b) (copies (q + 1) (output r k Phi X.1))} ?_ _ eps) ?_
  · rintro Y ⟨Φ, hΦ, rfl⟩; exact ⟨_, ⟨Φ, hΦ, rfl⟩, rfl⟩
  refine le_trans (testing_kron _
    {Y | ∃ Phi ∈ R, Y = pad (blk φ1 r b) (copies (q + 1) (output r k Phi X.1)) ⊗ₖ
        outT (Fin s) (Phi : Superop (Fin a) (Fin b)) ω} ?_ _ _ (htr N hN) eps) ?_
  · rintro Y ⟨Φ, hΦ, rfl⟩; exact ⟨_, ⟨Φ, hΦ, rfl⟩, _, htr Φ (hR Φ hΦ), rfl⟩
  refine testing_pad (blk2_bij φ2 r b).1 _ _ ?_ _ eps
  rintro Y ⟨Φ, hΦ, rfl⟩; exact ⟨_, ⟨Φ, hΦ, rfl⟩, key Φ⟩

lemma asym (hk : 0 < k) (T S : ℕ → ℝ≥0∞) (hTS : ∀ n q, (q + 1) * k ≤ n + 1 → T q ≤ S n) :
    liminf (fun m => T m / ((k * (m + 1) : ℕ) : ℝ≥0∞)) atTop ≤
      liminf (fun n => S n / ((n + 1 : ℕ) : ℝ≥0∞)) atTop := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
  refine ENNReal.le_of_forall_lt_one_mul_le fun δ hδ => ?_
  refine le_liminf_of_le (by isBoundedDefault) ?_
  let qf : ℕ → ℕ := fun n => (n + 1) / k - 1
  have hq : Tendsto qf atTop atTop := by
    refine tendsto_atTop_atTop.2 fun B => ⟨(B + 1) * k, fun n hn => ?_⟩
    have : B + 1 ≤ (n + 1) / k := (Nat.le_div_iff_mul_le hk).2 (by omega)
    simp only [qf]; omega
  have h1 := hq.eventually (eventually_lt_of_lt_liminf hc)
  have hδt : δ ≠ ⊤ := ne_top_of_lt (hδ.trans ENNReal.one_lt_top)
  set t := δ.toReal with ht
  have ht1 : t < 1 := by
    have := (ENNReal.toReal_lt_toReal hδt ENNReal.one_ne_top).2 hδ
    simpa [ht] using this
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  obtain ⟨N0, hN0⟩ := exists_nat_gt ((k : ℝ) / (1 - t))
  have h2 : ∀ᶠ n in atTop, N0 ≤ n ∧ k ≤ n + 1 :=
    (eventually_ge_atTop (N0 + k)).mono fun n hn => ⟨by omega, by omega⟩
  filter_upwards [h1, h2] with n h1 h2
  obtain ⟨hn0, hkn⟩ := h2
  have hQ : qf n + 1 = (n + 1) / k := by
    have : 1 ≤ (n + 1) / k := (Nat.le_div_iff_mul_le hk).2 (by omega)
    simp only [qf]; omega
  have hqk : (qf n + 1) * k ≤ n + 1 := by rw [hQ]; exact Nat.div_mul_le_self _ _
  -- real inequality δ (n+1) ≤ k (q+1)
  have hreal : t * ((n + 1 : ℕ) : ℝ) ≤ ((k * (qf n + 1) : ℕ) : ℝ) := by
    have hdm := Nat.div_add_mod (n + 1) k
    have hmod := Nat.mod_lt (n + 1) hk
    rw [hQ]
    have e1 : ((n + 1 : ℕ) : ℝ) = (k * ((n + 1) / k) : ℕ) + ((n + 1) % k : ℕ) := by
      rw [← Nat.cast_add, hdm]
    have e2 : (((n + 1) % k : ℕ) : ℝ) ≤ k := by exact_mod_cast hmod.le
    have hpos : 0 < 1 - t := by linarith
    have e3 : (k : ℝ) < (1 - t) * ((n + 1 : ℕ) : ℝ) := by
      have : (k : ℝ) / (1 - t) < ((n + 1 : ℕ) : ℝ) := by
        refine hN0.trans_le ?_; push_cast; exact_mod_cast (by omega : N0 ≤ n + 1)
      rwa [div_lt_iff₀ hpos, mul_comm] at this
    nlinarith
  have h2' : δ * ((n + 1 : ℕ) : ℝ≥0∞) ≤ ((k * (qf n + 1) : ℕ) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_toReal hδt, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul ht0]
    exact ENNReal.ofReal_le_ofReal hreal
  have hn1 : ((n + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have hn2 : ((n + 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc δ * c ≤ δ * (T (qf n) / ((k * (qf n + 1) : ℕ) : ℝ≥0∞)) := by gcongr
    _ ≤ T (qf n) / ((n + 1 : ℕ) : ℝ≥0∞) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_left_comm]
      gcongr _ * ?_
      have : δ ≤ ((k * (qf n + 1) : ℕ) : ℝ≥0∞) * ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
        calc δ = δ * ((n + 1 : ℕ) : ℝ≥0∞) * ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
              rw [mul_assoc, ENNReal.mul_inv_cancel hn1 hn2, mul_one]
          _ ≤ _ := by gcongr
      calc δ * ((k * (qf n + 1) : ℕ) : ℝ≥0∞)⁻¹
          ≤ ((k * (qf n + 1) : ℕ) : ℝ≥0∞) * ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ *
              ((k * (qf n + 1) : ℕ) : ℝ≥0∞)⁻¹ := by gcongr
        _ ≤ ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
          rw [mul_comm, ← mul_assoc]
          exact mul_le_of_le_one_left' (ENNReal.inv_mul_le_one _)
    _ ≤ S n / ((n + 1 : ℕ) : ℝ≥0∞) := ENNReal.div_le_div_right (hTS n _ hqk) _

lemma exp_arb {R : Set (Maps a b)} {N : Maps a b} (h : Setting R N) (hr : 0 < r) (hk : 0 < k) :
    blockExponent r R N k .unrestricted ≤ arbitraryExponent r R N .unrestricted := by
  unfold blockExponent arbitraryExponent operational
  refine liminf_le_liminf (Eventually.of_forall fun eps => ?_)
  unfold blockRate arbitraryRate
  exact asym hk _ _ fun n q hq => num_le h hr hq eps

end arb

end X4H

-- ===== HE =====

noncomputable section
set_option linter.unusedSectionVars false
open scoped Matrix ComplexConjugate ComplexOrder ENNReal Kronecker
open Filter Topology

namespace X4H
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

/-! product operators and product measurements -/

section kpT
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

def kpT (A : V → Matrix J J ℂ) : Matrix (V → J) (V → J) ℂ := Matrix.of fun x y => ∏ v, A v (x v) (y v)

lemma kpT_psd {A : V → Matrix J J ℂ} (h : ∀ v, (A v).PosSemidef) : (kpT A).PosSemidef := by
  choose B hB using fun v => psd_factor (h v)
  have : kpT A = (kpT B)ᴴ * kpT B := by
    ext x y
    simp only [kpT, Matrix.of_apply, hB, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.prod_mul_distrib, star_prod]
  rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _

lemma sum_kpT {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (P : Ω → Matrix J J ℂ) :
    ∑ s : V → Ω, kpT (fun v => P (s v)) = kpT (fun _ => ∑ ω, P ω) := by
  ext x y
  simp only [kpT, Matrix.sum_apply, Matrix.of_apply]
  rw [Fintype.prod_sum]

lemma kpT_one : kpT (fun _ : V => (1 : Matrix J J ℂ)) = 1 := by
  ext x y
  simp only [kpT, Matrix.of_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy; simp
  · obtain ⟨v, hv⟩ := Function.ne_iff.mp hxy
    rw [if_neg hxy]
    exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])

lemma trace_kpT_copies (A : V → Matrix J J ℂ) (ρ : Matrix J J ℂ) :
    (kpT A * copiesT V ρ).trace = ∏ v, (A v * ρ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, kpT, copiesT, Matrix.of_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_mul_distrib]

lemma trace_im_zero {P ρ : Matrix J J ℂ} (hP : P.IsHermitian) (hρ : ρ.IsHermitian) :
    (P * ρ).trace.im = 0 := by
  have : star (P * ρ).trace = (P * ρ).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hP.eq, hρ.eq, Matrix.trace_mul_comm]
  have h2 := congrArg Complex.im this
  simp only [Complex.star_def, Complex.conj_im] at h2
  linarith

lemma re_prod_of_im {z : V → ℂ} (h : ∀ v, (z v).im = 0) : (∏ v, z v).re = ∏ v, (z v).re := by
  have : ∀ v, z v = ((z v).re : ℂ) := fun v => Complex.ext rfl (by simp [h v])
  rw [Finset.prod_congr rfl fun v _ => this v, ← Complex.ofReal_prod, Complex.ofReal_re]

lemma effectProb_kpT {A : V → Matrix J J ℂ} (hA : ∀ v, (A v).IsHermitian) {ρ : Matrix J J ℂ}
    (hρ : ρ.IsHermitian) : effectProb (kpT A) (copiesT V ρ) = ∏ v, effectProb (A v) ρ := by
  unfold effectProb
  rw [trace_kpT_copies, re_prod_of_im fun v => trace_im_zero (hA v) hρ]

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- the product-measurement test accepting the strings in `acc`. -/
def ptest (P : Ω → Matrix J J ℂ) (acc : (V → Ω) → Prop) [DecidablePred acc] :
    Matrix (V → J) (V → J) ℂ :=
  ∑ s, if acc s then kpT (fun v => P (s v)) else 0

lemma ptest_compl (P : Ω → Matrix J J ℂ) (hP1 : ∑ ω, P ω = 1) (acc : (V → Ω) → Prop)
    [DecidablePred acc] : 1 - ptest P acc = ptest P (fun s => ¬ acc s) := by
  have h1 : (1 : Matrix (V → J) (V → J) ℂ) = ∑ s : V → Ω, kpT (fun v => P (s v)) := by
    rw [sum_kpT, hP1, kpT_one]
  rw [h1, ptest, ptest, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : acc s <;> simp [h]

lemma ptest_psd {P : Ω → Matrix J J ℂ} (hP : ∀ ω, (P ω).PosSemidef) (acc : (V → Ω) → Prop)
    [DecidablePred acc] : (ptest P acc).PosSemidef := by
  refine Matrix.posSemidef_sum _ fun s _ => ?_
  split_ifs
  · exact kpT_psd fun v => hP _
  · exact Matrix.PosSemidef.zero

lemma ptest_effect {P : Ω → Matrix J J ℂ} (hP : ∀ ω, (P ω).PosSemidef) (hP1 : ∑ ω, P ω = 1)
    (acc : (V → Ω) → Prop) [DecidablePred acc] : IsEffect (ptest P acc) :=
  ⟨ptest_psd hP acc, by rw [ptest_compl P hP1]; exact ptest_psd hP _⟩

lemma effectProb_ptest {P : Ω → Matrix J J ℂ} (hP : ∀ ω, (P ω).IsHermitian) {ρ : Matrix J J ℂ}
    (hρ : ρ.IsHermitian) (acc : (V → Ω) → Prop) [DecidablePred acc] :
    effectProb (ptest P acc) (copiesT V ρ) =
      ∑ s, if acc s then ∏ v, effectProb (P (s v)) ρ else 0 := by
  unfold ptest
  simp only [effectProb, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs
  · exact effectProb_kpT (fun v => hP _) hρ
  · simp

end kpT

/-! Chernoff bounds for empirical counts -/

section chernoff
variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω] [DecidableEq Ω]

def cnt (ω0 : Ω) (s : V → Ω) : ℝ := ∑ v, if s v = ω0 then (1 : ℝ) else 0

lemma mgf_bound (q : Ω → ℝ) (hq0 : ∀ ω, 0 ≤ q ω) (hq1 : ∑ ω, q ω = 1) (ω0 : Ω) (μ : ℝ) :
    ∑ s : V → Ω, Real.exp (μ * cnt ω0 s) * ∏ v, q (s v) ≤
      Real.exp (Fintype.card V * q ω0 * (Real.exp μ - 1)) := by
  have : ∀ s : V → Ω, Real.exp (μ * cnt ω0 s) * ∏ v, q (s v) =
      ∏ v, (Real.exp (μ * if s v = ω0 then 1 else 0) * q (s v)) := fun s => by
    rw [cnt, Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  simp only [this]
  rw [← Fintype.prod_sum (fun (_ : V) ω => Real.exp (μ * if ω = ω0 then 1 else 0) * q ω),
    Finset.prod_const, Finset.card_univ]
  have hs : ∑ ω, Real.exp (μ * if ω = ω0 then 1 else 0) * q ω = 1 + q ω0 * (Real.exp μ - 1) := by
    have : ∀ ω, Real.exp (μ * if ω = ω0 then 1 else 0) * q ω =
        q ω + if ω = ω0 then q ω0 * (Real.exp μ - 1) else 0 := fun ω => by
      split_ifs with h
      · subst h; ring
      · simp
    simp only [this, Finset.sum_add_distrib, hq1, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hs]
  have hb : 0 ≤ 1 + q ω0 * (Real.exp μ - 1) := by
    have hq : q ω0 ≤ 1 := hq1 ▸ Finset.single_le_sum (fun ω _ => hq0 ω) (Finset.mem_univ ω0)
    nlinarith [Real.exp_pos μ, hq0 ω0]
  calc (1 + q ω0 * (Real.exp μ - 1)) ^ Fintype.card V
      ≤ (Real.exp (q ω0 * (Real.exp μ - 1))) ^ Fintype.card V :=
        pow_le_pow_left₀ hb (by linarith [Real.add_one_le_exp (q ω0 * (Real.exp μ - 1))]) _
    _ = _ := by rw [← Real.exp_nat_mul]; ring_nf

lemma tail_up (q : Ω → ℝ) (hq0 : ∀ ω, 0 ≤ q ω) (hq1 : ∑ ω, q ω = 1) (ω0 : Ω) {d : ℝ}
    (hd0 : 0 < d) (hd1 : d ≤ 2) :
    ∑ s : V → Ω, (if Fintype.card V * (q ω0 + d) ≤ cnt ω0 s then ∏ v, q (s v) else 0) ≤
      Real.exp (-(Fintype.card V * d ^ 2 / 4)) := by
  set M := (Fintype.card V : ℝ)
  set l0 := d / 2 with hl0
  have hl0p : 0 ≤ l0 := by rw [hl0]; linarith
  have hq : q ω0 ≤ 1 := hq1 ▸ Finset.single_le_sum (fun ω _ => hq0 ω) (Finset.mem_univ ω0)
  have hprod : ∀ s : V → Ω, 0 ≤ ∏ v, q (s v) := fun s => Finset.prod_nonneg fun v _ => hq0 _
  calc _ ≤ ∑ s : V → Ω, Real.exp (-(l0 * (M * (q ω0 + d)))) *
        (Real.exp (l0 * cnt ω0 s) * ∏ v, q (s v)) := by
        refine Finset.sum_le_sum fun s _ => ?_
        split_ifs with h
        · rw [← mul_assoc, ← Real.exp_add]
          refine le_mul_of_one_le_left (hprod s) (Real.one_le_exp ?_)
          nlinarith [mul_nonneg hl0p (sub_nonneg.2 h)]
        · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (hprod s))
    _ = Real.exp (-(l0 * (M * (q ω0 + d)))) *
        ∑ s : V → Ω, Real.exp (l0 * cnt ω0 s) * ∏ v, q (s v) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(l0 * (M * (q ω0 + d)))) * Real.exp (M * q ω0 * (Real.exp l0 - 1)) :=
        mul_le_mul_of_nonneg_left (mgf_bound q hq0 hq1 ω0 l0) (Real.exp_pos _).le
    _ ≤ _ := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have hl : |l0| ≤ 1 := by rw [abs_le]; constructor <;> linarith
        have h1 := Real.abs_exp_sub_one_sub_id_le hl
        have h2 : Real.exp l0 - 1 - l0 ≤ l0 ^ 2 := (abs_le.mp h1).2
        have h3 : 0 ≤ Real.exp l0 - 1 - l0 := by linarith [Real.add_one_le_exp l0]
        have hM : 0 ≤ M := Nat.cast_nonneg _
        have : M * q ω0 * (Real.exp l0 - 1 - l0) ≤ M * l0 ^ 2 := by
          have := mul_le_mul hq h2 h3 zero_le_one
          nlinarith [mul_le_mul_of_nonneg_left this hM]
        simp only [l0] at this ⊢
        nlinarith

lemma tail_down (q : Ω → ℝ) (hq0 : ∀ ω, 0 ≤ q ω) (hq1 : ∑ ω, q ω = 1) (ω0 : Ω) {d : ℝ}
    (hd0 : 0 < d) (hd1 : d ≤ 2) :
    ∑ s : V → Ω, (if cnt ω0 s ≤ Fintype.card V * (q ω0 - d) then ∏ v, q (s v) else 0) ≤
      Real.exp (-(Fintype.card V * d ^ 2 / 4)) := by
  set M := (Fintype.card V : ℝ)
  set l0 := d / 2 with hl0
  have hl0p : 0 ≤ l0 := by rw [hl0]; linarith
  have hq : q ω0 ≤ 1 := hq1 ▸ Finset.single_le_sum (fun ω _ => hq0 ω) (Finset.mem_univ ω0)
  have hprod : ∀ s : V → Ω, 0 ≤ ∏ v, q (s v) := fun s => Finset.prod_nonneg fun v _ => hq0 _
  calc _ ≤ ∑ s : V → Ω, Real.exp (l0 * (M * (q ω0 - d))) *
        (Real.exp (-l0 * cnt ω0 s) * ∏ v, q (s v)) := by
        refine Finset.sum_le_sum fun s _ => ?_
        split_ifs with h
        · rw [← mul_assoc, ← Real.exp_add]
          refine le_mul_of_one_le_left (hprod s) (Real.one_le_exp ?_)
          nlinarith [mul_nonneg hl0p (sub_nonneg.2 h)]
        · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (hprod s))
    _ = Real.exp (l0 * (M * (q ω0 - d))) *
        ∑ s : V → Ω, Real.exp (-l0 * cnt ω0 s) * ∏ v, q (s v) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (l0 * (M * (q ω0 - d))) * Real.exp (M * q ω0 * (Real.exp (-l0) - 1)) :=
        mul_le_mul_of_nonneg_left (mgf_bound q hq0 hq1 ω0 (-l0)) (Real.exp_pos _).le
    _ ≤ _ := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have hl : |-l0| ≤ 1 := by rw [abs_le]; constructor <;> linarith
        have h1 := Real.abs_exp_sub_one_sub_id_le hl
        have h2 : Real.exp (-l0) - 1 - (-l0) ≤ (-l0) ^ 2 := (abs_le.mp h1).2
        have h3 : 0 ≤ Real.exp (-l0) - 1 - (-l0) := by linarith [Real.add_one_le_exp (-l0)]
        have hM : 0 ≤ M := Nat.cast_nonneg _
        have : M * q ω0 * (Real.exp (-l0) - 1 + l0) ≤ M * l0 ^ 2 := by
          have := mul_le_mul hq h2 h3 zero_le_one
          nlinarith [mul_le_mul_of_nonneg_left this hM]
        simp only [l0] at this ⊢
        nlinarith

end chernoff

end X4H

-- ===== HF =====

noncomputable section
set_option linter.unusedSectionVars false
open scoped Matrix ComplexConjugate ComplexOrder ENNReal Kronecker
open Filter Topology

namespace X4H
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

section gt
variable {J ι : Type*} [Fintype J] [DecidableEq J] [Fintype ι] [DecidableEq ι]

lemma ep_nonneg {P ρ : Matrix J J ℂ} (hP : P.PosSemidef) (hρ : ρ.PosSemidef) :
    0 ≤ effectProb P ρ := by
  obtain ⟨B, rfl⟩ := psd_factor hP
  unfold effectProb
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  exact (Complex.le_def.mp (hρ.mul_mul_conjTranspose_same B).trace_nonneg).1

/-- the POVM: pick `j` uniformly, then measure `F j`. -/
def povm (F : ι → Matrix J J ℂ) (ω : ι × Bool) : Matrix J J ℂ :=
  ((Fintype.card ι : ℂ)⁻¹) • (if ω.2 then F ω.1 else 1 - F ω.1)

lemma povm_sum [Nonempty ι] (F : ι → Matrix J J ℂ) : ∑ ω, povm F ω = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [povm, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, ← smul_add,
    add_sub_cancel, Finset.sum_const, Finset.card_univ]
  have : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ this, one_smul]

lemma povm_psd {F : ι → Matrix J J ℂ} (hF : ∀ j, IsEffect (F j)) (ω : ι × Bool) :
    (povm F ω).PosSemidef := by
  unfold povm
  refine Matrix.PosSemidef.smul ?_ (by positivity)
  split_ifs
  · exact (hF _).1
  · exact (hF _).2

lemma ep_povm (F : ι → Matrix J J ℂ) (ρ : Matrix J J ℂ) (j : ι) :
    effectProb (povm F (j, true)) ρ = effectProb (F j) ρ / Fintype.card ι := by
  simp only [povm, if_true, effectProb, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul, div_eq_inv_mul]

lemma q_sum [Nonempty ι] (F : ι → Matrix J J ℂ) {ρ : Matrix J J ℂ} (hρ : IsDensityMatrix ρ) :
    ∑ ω, effectProb (povm F ω) ρ = 1 := by
  simp only [effectProb, ← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, povm_sum,
    Matrix.one_mul, hρ.2, Complex.one_re]

lemma le_two_ite {P : ℝ} {A B : Prop} [Decidable A] [Decidable B] (hP : 0 ≤ P) (h : A ∨ B) :
    P ≤ (if A then P else 0) + (if B then P else 0) := by
  rcases h with h | h <;> split_ifs <;> linarith

lemma ite_nn {P : ℝ} {A : Prop} [Decidable A] (hP : 0 ≤ P) : 0 ≤ if A then P else 0 := by
  split_ifs <;> linarith

variable [Nonempty ι]

/-- tomography-type test: exponentially small errors in the number of copies. -/
lemma GT {α : Type*} (F : ι → Matrix J J ℂ) (hF : ∀ j, IsEffect (F j)) (σ : Matrix J J ℂ)
    (hσ : IsDensityMatrix σ) (R : Set α) (ρ : α → Matrix J J ℂ)
    (hρ : ∀ x ∈ R, IsDensityMatrix (ρ x)) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ x ∈ R, ∃ j, δ ≤ |effectProb (F j) (ρ x) - effectProb (F j) σ|) :
    ∃ κ > 0, ∀ eps > 0, ∀ᶠ m : ℕ in atTop, ENNReal.ofReal (κ * (m + 1)) ≤
      testingBits {Y | ∃ x ∈ R, Y = copies (m + 1) (ρ x)} (copies (m + 1) σ) eps := by
  set L := (Fintype.card ι : ℝ) with hL
  have hL0 : 0 < L := by rw [hL]; exact_mod_cast Fintype.card_pos
  have hL1 : 1 ≤ L := by rw [hL]; exact_mod_cast Fintype.card_pos
  set d := δ / (2 * L) with hd
  have hd0 : 0 < d := by positivity
  have hd2 : d ≤ 2 := by
    rw [hd, div_le_iff₀ (by positivity)]; nlinarith
  set c := d ^ 2 / 4 with hc
  have hc0 : 0 < c := by positivity
  refine ⟨c / (2 * Real.log 2), by positivity, fun eps heps => ?_⟩
  -- choose the number of copies large enough
  obtain ⟨M1, hM1⟩ := exists_nat_gt (Real.log (2 / eps) / c)
  obtain ⟨M2, hM2⟩ := exists_nat_gt (2 * Real.log (2 * L) / c)
  filter_upwards [eventually_ge_atTop (M1 + M2)] with m hm
  set M := ((m + 1 : ℕ) : ℝ) with hM
  have hMc : (Fintype.card (Fin (m + 1)) : ℝ) = M := by simp [hM]
  have hMge1 : (M1 : ℝ) ≤ M := by rw [hM]; exact_mod_cast (by omega : M1 ≤ m + 1)
  have hMge2 : (M2 : ℝ) ≤ M := by rw [hM]; exact_mod_cast (by omega : M2 ≤ m + 1)
  have hMpos : 0 < M := by rw [hM]; positivity
  let P := povm F
  have hPh : ∀ ω, (P ω).IsHermitian := fun ω => (povm_psd hF ω).1
  let u : ι → ℝ := fun j => effectProb (P (j, true)) σ
  let acc : (Fin (m + 1) → ι × Bool) → Prop :=
    fun s => ∃ j, M * d < |cnt (j, true) s - M * u j|
  classical
  let T := ptest P acc
  have hexp : Real.exp (-(M * d ^ 2 / 4)) = Real.exp (-(c * M)) := by rw [hc]; ring_nf
  -- type I
  have hI : ∀ x ∈ R, effectProb (1 - T) (copies (m + 1) (ρ x)) ≤ eps := by
    intro x hx
    obtain ⟨j0, hj0⟩ := hsep x hx
    have hρx := hρ x hx
    let q : ι × Bool → ℝ := fun ω => effectProb (P ω) (ρ x)
    have hq0 : ∀ ω, 0 ≤ q ω := fun ω => ep_nonneg (povm_psd hF ω) hρx.1
    have hq1 : ∑ ω, q ω = 1 := q_sum F hρx
    have hv : 2 * d ≤ |q (j0, true) - u j0| := by
      simp only [q, u, P, ep_povm, ← sub_div, abs_div, abs_of_pos hL0, ← hL]
      rw [le_div_iff₀ hL0, hd]; field_simp; linarith
    rw [ptest_compl P (povm_sum F), copies_eq, effectProb_ptest hPh hρx.1.1]
    calc _ ≤ ∑ s : Fin (m + 1) → ι × Bool,
          ((if M * (q (j0, true) + d) ≤ cnt (j0, true) s then
              ∏ v, q (s v) else 0) +
            (if cnt (j0, true) s ≤ M * (q (j0, true) - d) then
              ∏ v, q (s v) else 0)) := by
          refine Finset.sum_le_sum fun s _ => ?_
          have hp : 0 ≤ ∏ v, q (s v) := Finset.prod_nonneg fun v _ => hq0 _
          by_cases hs : acc s
          · simp only [hs, not_true_eq_false, if_false]
            exact add_nonneg (ite_nn hp) (ite_nn hp)
          · simp only [hs, not_false_eq_true, if_true]
            have hs' : |cnt (j0, true) s - M * u j0| ≤ M * d := by
              by_contra hc'; exact hs ⟨j0, lt_of_not_ge hc'⟩
            rcases le_abs'.mp hv with hv | hv
            · have : M * (q (j0, true) + d) ≤ cnt (j0, true) s := by
                have := (abs_le.mp hs').1
                nlinarith [mul_nonneg hMpos.le (by linarith : 0 ≤ u j0 - 2 * d - q (j0, true))]
              exact le_two_ite hp (Or.inl this)
            · have : cnt (j0, true) s ≤ M * (q (j0, true) - d) := by
                have := (abs_le.mp hs').2
                nlinarith [mul_nonneg hMpos.le (by linarith : 0 ≤ q (j0, true) - 2 * d - u j0)]
              exact le_two_ite hp (Or.inr this)
      _ ≤ Real.exp (-(M * d ^ 2 / 4)) + Real.exp (-(M * d ^ 2 / 4)) := by
          rw [Finset.sum_add_distrib]
          have h1 := tail_up (V := Fin (m + 1)) q hq0 hq1 (j0, true) hd0 hd2
          have h2 := tail_down (V := Fin (m + 1)) q hq0 hq1 (j0, true) hd0 hd2
          rw [hMc] at h1 h2
          exact add_le_add h1 h2
      _ ≤ eps := by
          rw [hexp, ← two_mul]
          have : Real.log (2 / eps) < c * M := by
            rw [div_lt_iff₀ hc0] at hM1; nlinarith
          have h3 : 2 / eps < Real.exp (c * M) := by
            rw [← Real.exp_log (by positivity : 0 < 2 / eps)]; exact Real.exp_lt_exp.mpr this
          rw [Real.exp_neg]
          rw [div_lt_iff₀ heps] at h3
          have := Real.exp_pos (c * M)
          rw [mul_inv_le_iff₀ this]; linarith
  -- type II
  have hII : effectProb T (copies (m + 1) σ) ≤ 2 * L * Real.exp (-(c * M)) := by
    let q : ι × Bool → ℝ := fun ω => effectProb (P ω) σ
    have hq0 : ∀ ω, 0 ≤ q ω := fun ω => ep_nonneg (povm_psd hF ω) hσ.1
    have hq1 : ∑ ω, q ω = 1 := q_sum F hσ
    rw [copies_eq, effectProb_ptest hPh hσ.1.1]
    calc _ ≤ ∑ s : Fin (m + 1) → ι × Bool, ∑ j : ι,
          ((if M * (q (j, true) + d) ≤ cnt (j, true) s then
              ∏ v, q (s v) else 0) +
            (if cnt (j, true) s ≤ M * (q (j, true) - d) then
              ∏ v, q (s v) else 0)) := by
          refine Finset.sum_le_sum fun s _ => ?_
          have hp : 0 ≤ ∏ v, q (s v) := Finset.prod_nonneg fun v _ => hq0 _
          have hnn : ∀ j : ι, 0 ≤
              ((if M * (q (j, true) + d) ≤ cnt (j, true) s then
                ∏ v, q (s v) else 0) +
              (if cnt (j, true) s ≤ M * (q (j, true) - d) then
                ∏ v, q (s v) else 0)) := fun j => add_nonneg (ite_nn hp) (ite_nn hp)
          by_cases hs : acc s
          · simp only [hs, if_true]
            obtain ⟨j, hj⟩ := hs
            refine le_trans ?_ (Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ j))
            rcases lt_abs.mp hj with h | h
            · have : M * (q (j, true) + d) ≤ cnt (j, true) s := by simp only [q, u] at h ⊢; linarith
              exact le_two_ite hp (Or.inl this)
            · have : cnt (j, true) s ≤ M * (q (j, true) - d) := by simp only [q, u] at h ⊢; linarith
              exact le_two_ite hp (Or.inr this)
          · simp only [hs, if_false]
            exact Finset.sum_nonneg fun j _ => hnn j
      _ = ∑ j : ι, (∑ s : Fin (m + 1) → ι × Bool,
            (if M * (q (j, true) + d) ≤ cnt (j, true) s then
              ∏ v, q (s v) else 0) +
          ∑ s : Fin (m + 1) → ι × Bool,
            (if cnt (j, true) s ≤ M * (q (j, true) - d) then
              ∏ v, q (s v) else 0)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_add_distrib
      _ ≤ ∑ j : ι, (Real.exp (-(M * d ^ 2 / 4)) + Real.exp (-(M * d ^ 2 / 4))) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h1 := tail_up (V := Fin (m + 1)) q hq0 hq1 (j, true) hd0 hd2
          have h2 := tail_down (V := Fin (m + 1)) q hq0 hq1 (j, true) hd0 hd2
          rw [hMc] at h1 h2
          exact add_le_add h1 h2
      _ = 2 * L * Real.exp (-(c * M)) := by
          rw [hexp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hL]; ring
  -- conclusion
  have hTe : IsEffect T := ptest_effect (fun ω => povm_psd hF ω) (povm_sum F) acc
  unfold testingBits
  refine le_iSup_of_le ⟨T, hTe, ?_⟩ ?_
  · rintro Y ⟨x, hx, rfl⟩; exact hI x hx
  · simp only
    split_ifs with h0
    · exact le_top
    · have hp0 : 0 < effectProb T (copies (m + 1) σ) :=
        lt_of_le_of_ne (ep_nonneg hTe.1 (copies_density hσ).1) (Ne.symm h0)
      refine ENNReal.ofReal_le_ofReal ?_
      have hlog : Real.logb 2 (effectProb T (copies (m + 1) σ)) ≤
          Real.logb 2 (2 * L * Real.exp (-(c * M))) :=
        Real.logb_le_logb_of_le (by norm_num) hp0 hII
      have h2 : Real.logb 2 (2 * L * Real.exp (-(c * M))) =
          (Real.log (2 * L) - c * M) / Real.log 2 := by
        rw [Real.logb, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]; ring
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h3 : Real.log (2 * L) ≤ c * M / 2 := by
        rw [div_lt_iff₀ hc0] at hM2; nlinarith
      rw [h2] at hlog
      have : c / (2 * Real.log 2) * M ≤ -((Real.log (2 * L) - c * M) / Real.log 2) := by
        have e : c / (2 * Real.log 2) * M = (c * M / 2) / Real.log 2 := by field_simp
        rw [e, neg_div', neg_sub]
        exact div_le_div_of_nonneg_right (by linarith) hl2.le
      have hM' : (m : ℝ) + 1 = M := by rw [hM]; push_cast; ring
      rw [hM']
      linarith

end gt

end X4H

-- ===== HG =====

noncomputable section
set_option linter.unusedSectionVars false
open scoped Matrix ComplexConjugate ComplexOrder ENNReal Kronecker
open Filter Topology

namespace X4H
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

section kraus
variable {a b r k m : ℕ}

def ent {m n : Type*} (A : Matrix m n ℂ) (i : m) (j : n) : ℂ := A i j

lemma ker_kraus {Φ : Superop (Fin a) (Fin b)} {E : Fin m → Matrix (Fin b) (Fin a) ℂ}
    (hΦ : ∀ ρ, Φ ρ = krausApply E ρ) (u u' : Fin a) (v v' : Fin b) :
    ker Φ u u' v v' = ∑ j, ent (E j) v u * star (ent (E j) v' u') := by
  simp only [ker, ent, hΦ, krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
    Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single u']
  · rw [Finset.sum_eq_single u]
    · simp
    · intro y _ hy; simp [Ne.symm hy]
    · simp
  · intro y _ hy; simp [Ne.symm hy]
  · simp

lemma sum4 {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [DecidableEq A]
    [DecidableEq C] (a0 : A) (c0 : C) (g : A → B → C → D → ℂ) :
    (∑ x1, ∑ x2, ∑ x3, ∑ x4, if c0 = x3 then (if a0 = x1 then g x1 x2 x3 x4 else 0) else 0) =
      ∑ x2, ∑ x4, g a0 x2 c0 x4 := by
  rw [Finset.sum_eq_single a0 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  refine Finset.sum_congr rfl fun x2 _ => ?_
  rw [Finset.sum_eq_single c0 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

def KJ (E : Fin m → Matrix (Fin b) (Fin a) ℂ) (J : Fin k → Fin m) :
    Matrix (Reg r b k) (Reg r a k) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then ∏ i, ent (E (J i)) (p.2 i) (q.2 i) else 0

lemma conj_apply {I K : Type*} [Fintype K] (A : Matrix I K ℂ) (X : Matrix K K ℂ) (p p' : I) :
    (A * X * Aᴴ) p p' = ∑ q, ∑ q', A p q * X q q' * star (A p' q') := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma out_kraus {Φ : Superop (Fin a) (Fin b)} {E : Fin m → Matrix (Fin b) (Fin a) ℂ}
    (hΦ : ∀ ρ, Φ ρ = krausApply E ρ) (X : Mat (Reg r a k)) :
    outT (Fin k) Φ X = ∑ J : Fin k → Fin m,
      ((KJ (r := r) E J * X : Matrix (Reg r b k) (Reg r a k) ℂ) * (KJ (r := r) E J)ᴴ :
        Matrix (Reg r b k) (Reg r b k) ℂ) := by
  set f : Reg r a k → Reg r a k → ℂ := fun p q => X p q
  have hX : X = Matrix.of f := rfl
  rw [hX]
  refine Matrix.ext fun p p' => ?_
  rw [Matrix.sum_apply]
  conv_rhs => enter [2, J]; rw [conj_apply]
  have st : ∀ (c : Prop) [Decidable c] (z : ℂ), star (if c then z else 0) = if c then star z else 0 :=
    fun c _ z => by split_ifs <;> simp
  simp only [outT, KJ, Matrix.of_apply, ker_kraus hΦ, st, Fintype.sum_prod_type, ite_mul, zero_mul,
    mul_ite, mul_zero]
  simp only [sum4]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [Fintype.prod_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.prod_mul_distrib, star_prod]
  ring

lemma out_psd {Φ : Superop (Fin a) (Fin b)} (hΦ : IsChannel Φ) {X : Mat (Reg r a k)}
    (hX : X.PosSemidef) : (outT (Fin k) Φ X).PosSemidef := by
  obtain ⟨m, E, -, hE⟩ := hΦ
  rw [out_kraus hE]
  exact Matrix.posSemidef_sum _ fun J _ => hX.mul_mul_conjTranspose_same _

lemma out_density {Φ : Maps a b} (hΦ : IsChannel (Φ : Superop (Fin a) (Fin b)))
    {X : Mat (Reg r a k)} (hX : IsDensityMatrix X) : IsDensityMatrix (output r k Φ X) := by
  rw [output_eq]
  exact ⟨out_psd hΦ hX.1, by rw [trace_outT _ (chan_single hΦ), hX.2]⟩

end kraus

/-! compactness of the null class -/

section compact
variable {a b : ℕ}

def coord : Maps a b →ₗ[ℂ] (Fin a × Fin a × Fin b × Fin b → ℂ) where
  toFun Φ p := Φ (Matrix.single p.1 p.2.1 1) p.2.2.1 p.2.2.2
  map_add' Φ Ψ := by ext p; simp
  map_smul' c Φ := by ext p; simp

lemma clm_entry' (Ψ : Maps a b) (A : Mat (Fin a)) (y y' : Fin b) :
    Ψ A y y' = ∑ z, ∑ z', A z z' * Ψ (Matrix.single z z' 1) y y' := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => ?_
  rw [show Matrix.single z z' (A z z') = A z z' • Matrix.single z z' (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, Matrix.smul_apply, smul_eq_mul]

lemma coord_inj : (coord : Maps a b →ₗ[ℂ] _).ker = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro Φ hΦ
  ext A y y'
  rw [clm_entry' Φ A y y']
  refine Finset.sum_eq_zero fun z _ => Finset.sum_eq_zero fun z' _ => ?_
  have := congrFun hΦ (z, z', y, y')
  simp only [coord, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
  rw [this, mul_zero]

lemma kraus_entry_bound {m : ℕ} {E : Fin m → Matrix (Fin b) (Fin a) ℂ} (hE : IsKrausFamily E)
    (u u' : Fin a) (v v' : Fin b) : ‖∑ j, ent (E j) v u * star (ent (E j) v' u')‖ ≤ 1 := by
  simp only [ent]
  have hcol : ∀ u : Fin a, ∑ j, ∑ w, ‖E j w u‖ ^ 2 = 1 := by
    intro u
    have := congrFun (congrFun hE u) u
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at this
    have h2 : ∀ j w, star (E j w u) * E j w u = ((‖E j w u‖ ^ 2 : ℝ) : ℂ) := fun j w => by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    simp only [h2] at this
    exact_mod_cast this
  have hle : ∀ u : Fin a, ∀ w : Fin b, ∑ j, ‖E j w u‖ ^ 2 ≤ 1 := by
    intro u w
    rw [← hcol u, Finset.sum_comm]
    exact Finset.single_le_sum (f := fun w => ∑ j, ‖E j w u‖ ^ 2)
      (fun w _ => Finset.sum_nonneg fun j _ => by positivity) (Finset.mem_univ w)
  calc ‖∑ j, E j v u * star (E j v' u')‖ ≤ ∑ j, ‖E j v u‖ * ‖E j v' u'‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp only [norm_mul, norm_star]
    _ ≤ ∑ j, (‖E j v u‖ ^ 2 + ‖E j v' u'‖ ^ 2) / 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        nlinarith [sq_nonneg (‖E j v u‖ - ‖E j v' u'‖)]
    _ ≤ 1 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib]
        linarith [hle u v, hle u' v']

lemma R_compact {R : Set (Maps a b)} (hR : IsClosed R)
    (hch : ∀ Φ ∈ R, IsChannel (Φ : Superop (Fin a) (Fin b))) : IsCompact R := by
  have hemb := LinearMap.isClosedEmbedding_of_injective (𝕜 := ℂ) (coord_inj (a := a) (b := b))
  have hK : IsCompact (coord '' R) := by
    refine Metric.isCompact_of_isClosed_isBounded (hemb.isClosedMap _ hR) ?_
    refine (Metric.isBounded_closedBall (x := (0 : Fin a × Fin a × Fin b × Fin b → ℂ)) (r := 1)).subset ?_
    rintro _ ⟨Φ, hΦ, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro p
    obtain ⟨m, E, hE, hEq⟩ := hch Φ hΦ
    have := kraus_entry_bound hE p.1 p.2.1 p.2.2.1 p.2.2.2
    rw [← ker_kraus hEq] at this
    exact this
  have := hemb.isCompact_preimage hK
  rwa [Set.preimage_image_eq _ hemb.injective] at this

lemma cont_entry (A : Mat (Fin a)) (y y' : Fin b) : Continuous fun Φ : Maps a b => Φ A y y' := by
  let f : Maps a b →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => Φ A y y', map_add' := fun _ _ => by simp, map_smul' := fun _ _ => by simp }
  exact LinearMap.continuous_of_finiteDimensional f

lemma cont_output {r k : ℕ} (X : Mat (Reg r a k)) :
    Continuous fun Φ : Maps a b => output r k Φ X := by
  refine continuous_matrix fun p q => ?_
  simp only [output_eq, outT, Matrix.of_apply, ker]
  refine continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun x' _ => ?_
  exact continuous_const.mul (continuous_finsetProd _ fun i _ => cont_entry _ _ _)

lemma cont_ep {r k : ℕ} (F : Mat (Reg r b k)) (X : Mat (Reg r a k)) :
    Continuous fun Φ : Maps a b => effectProb F (output r k Φ X) := by
  unfold effectProb
  exact Complex.continuous_re.comp (continuous_const.matrix_mul (cont_output X)).matrix_trace

end compact

end X4H

-- ===== HH =====

noncomputable section
set_option linter.unusedSectionVars false
open scoped Matrix ComplexConjugate ComplexOrder ENNReal Kronecker
open Filter Topology

namespace X4H
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

section span
variable {J : Type*} [Fintype J] [DecidableEq J]

lemma proj_effect {P : Matrix J J ℂ} (hH : Pᴴ = P) (hP : P * P = P) : IsEffect P := by
  refine ⟨?_, ?_⟩
  · have : P = Pᴴ * P := by rw [hH, hP]
    rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _
  · have : (1 - P) = (1 - P)ᴴ * (1 - P) := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hH, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hP]
      abel
    rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _

def ev (p : J) : J → ℂ := Pi.single p 1

def uv (p q : J) (w : ℂ) : J → ℂ := ev p + w • ev q

def fam : J ⊕ (J × J × Bool) → Matrix J J ℂ
  | .inl p => Matrix.vecMulVec (ev p) (star (ev p))
  | .inr (p, q, t) => if p = q then Matrix.vecMulVec (ev p) (star (ev p)) else
      (1 / 2 : ℂ) • Matrix.vecMulVec (uv p q (if t then 1 else Complex.I))
        (star (uv p q (if t then 1 else Complex.I)))

lemma dot_ev (p : J) : star (ev p) ⬝ᵥ ev p = 1 := by
  simp [ev, dotProduct, Pi.single_apply]

lemma dot_uv {p q : J} (hpq : p ≠ q) {w : ℂ} (hw : star w * w = 1) :
    star (uv p q w) ⬝ᵥ uv p q w = 2 := by
  simp only [uv, ev, dotProduct, Pi.add_apply, Pi.smul_apply, Pi.star_apply, star_add, star_smul,
    smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_add_of_mem p q (Finset.mem_univ _) (Finset.mem_univ _) hpq]
  · simp [hpq, Ne.symm hpq]
    rw [show (starRingEnd ℂ) w * w = 1 from hw]; norm_num
  · intro c _ hc; simp [hc.1, hc.2]

lemma vv_effect {v : J → ℂ} {s : ℂ} (hs : star s = s) (hv : s * (star v ⬝ᵥ v) = 1) :
    IsEffect (s • Matrix.vecMulVec v (star v)) := by
  refine proj_effect ?_ ?_
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_vecMulVec, star_star, hs]
  · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, smul_smul,
      Matrix.vecMulVec_smul, smul_smul, mul_assoc, hv, mul_one]

lemma fam_effect (j : J ⊕ (J × J × Bool)) : IsEffect (fam j) := by
  have h1 : ∀ p : J, IsEffect (Matrix.vecMulVec (ev p) (star (ev p))) := fun p => by
    have := vv_effect (v := ev p) (s := 1) (by simp) (by rw [dot_ev, one_mul])
    rwa [one_smul] at this
  rcases j with p | ⟨p, q, t⟩
  · exact h1 p
  · simp only [fam]
    split_ifs with hpq ht
    · exact h1 p
    · refine vv_effect (by simp) ?_
      rw [dot_uv hpq (by simp)]; norm_num
    · refine vv_effect (by simp) ?_
      rw [dot_uv hpq (by simp [Complex.ext_iff])]; norm_num

lemma ep_vv (v : J → ℂ) (D : Matrix J J ℂ) :
    effectProb (Matrix.vecMulVec v (star v)) D = (∑ a, ∑ b, star (v a) * D a b * v b).re := by
  unfold effectProb
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma ep_sub (F ρ σ : Matrix J J ℂ) : effectProb F ρ - effectProb F σ = effectProb F (ρ - σ) := by
  simp [effectProb, Matrix.mul_sub, Matrix.trace_sub]

lemma quad_uv (Df : J → J → ℂ) {p q : J} (hpq : p ≠ q) (w : ℂ) (hp : Df p p = 0)
    (hq : Df q q = 0) :
    ∑ a, ∑ b, star (uv p q w a) * Df a b * uv p q w b = w * Df p q + star w * Df q p := by
  have hu : ∀ a, uv p q w a = (if a = p then 1 else 0) + w * (if a = q then 1 else 0) := by
    intro a; simp [uv, ev, Pi.single_apply]
  have hsu : ∀ a, star (uv p q w a) =
      (if a = p then 1 else 0) + star w * (if a = q then 1 else 0) := by
    intro a; rw [hu]; split_ifs <;> simp
  simp only [hsu]
  simp only [hu, add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite, one_mul,
    mul_one, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const_zero]
  rw [hp, hq]
  simp [hpq, Ne.symm hpq]
  ring

lemma span_sep {D : Matrix J J ℂ} (hD : D.IsHermitian)
    (h0 : ∀ j, effectProb (fam j) D = 0) : D = 0 := by
  have hdiag : ∀ p, D p p = 0 := by
    intro p
    have h := h0 (.inl p)
    simp only [fam, ep_vv, ev, Pi.single_apply] at h
    simp at h
    have him : (D p p).im = 0 := by
      have := congrFun (congrFun hD p) p
      simp only [Matrix.conjTranspose_apply, Complex.star_def] at this
      have := congrArg Complex.im this
      simp at this; linarith
    exact Complex.ext h him
  ext p q
  by_cases hpq : p = q
  · subst hpq; simpa using hdiag p
  have hconj : D q p = star (D p q) := by
    have := congrFun (congrFun hD q) p
    simpa [Matrix.conjTranspose_apply] using this.symm
  have key : ∀ w : ℂ, effectProb (Matrix.vecMulVec (uv p q w) (star (uv p q w))) D =
      (w * D p q + star w * D q p).re := by
    intro w
    rw [ep_vv]
    congr 1
    exact quad_uv (fun a b => D a b) hpq w (hdiag p) (hdiag q)
  have h1 := h0 (.inr (p, q, true))
  have h2 := h0 (.inr (p, q, false))
  simp only [fam, hpq, if_false, if_true, Bool.false_eq_true] at h1 h2
  have e : ∀ (M : Matrix J J ℂ), effectProb ((1 / 2 : ℂ) • M) D = effectProb M D / 2 := by
    intro M
    simp only [effectProb, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]; ring
  rw [e, key] at h1 h2
  rw [hconj] at h1 h2
  simp only [one_mul, star_one] at h1
  have hre : (D p q).re = 0 := by
    simp [Complex.add_re, Complex.conj_re] at h1; linarith
  have him : (D p q).im = 0 := by
    simp [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im] at h2; linarith
  exact Complex.ext hre him

lemma exists_sep {ρ σ : Matrix J J ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (hne : ρ ≠ σ) :
    ∃ j, effectProb (fam j) ρ ≠ effectProb (fam j) σ := by
  by_contra hc
  push Not at hc
  exact hne (sub_eq_zero.mp (span_sep (hρ.sub hσ) fun j => by rw [← ep_sub, hc j, sub_self]))

end span

end X4H

-- ===== HI =====

noncomputable section
set_option linter.unusedSectionVars false
open scoped Matrix ComplexConjugate ComplexOrder ENNReal Kronecker
open Filter Topology

namespace X4H
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

section exps
variable {a b r k : ℕ}

lemma exp_pos {R : Set (Maps a b)} {N : Maps a b} (h : Setting R N) (hr : 0 < r) (hk : 0 < k)
    {c : Correlation} {X : Mat (Reg r a k)} (hX : X ∈ admissible r a k c)
    (hne : ∀ Φ ∈ R, output r k Φ X ≠ output r k N X) : 0 < blockExponent r R N k c := by
  classical
  obtain ⟨ha, hb, hRne, hRc, -, hR, hN, -⟩ := h
  set σ := output r k N X with hσdef
  have hσ : IsDensityMatrix σ := out_density hN hX.1
  have : Nonempty (Reg r b k ⊕ (Reg r b k × Reg r b k × Bool)) :=
    ⟨.inl (fun _ => ⟨0, hr⟩, fun _ => ⟨0, hb⟩)⟩
  let G : Maps a b → ℝ := fun Φ =>
    ∑ j, |effectProb (fam j) (output r k Φ X) - effectProb (fam j) σ|
  have hG : Continuous G :=
    continuous_finsetSum _ fun j _ => ((cont_ep _ X).sub continuous_const).abs
  obtain ⟨Φ0, hΦ0, hmin⟩ := (R_compact hRc hR).exists_isMinOn hRne hG.continuousOn
  have hpos : 0 < G Φ0 := by
    obtain ⟨j, hj⟩ := exists_sep (out_density (hR Φ0 hΦ0) hX.1).1.1 hσ.1.1 (hne Φ0 hΦ0)
    exact lt_of_lt_of_le (abs_pos.2 (sub_ne_zero.2 hj))
      (Finset.single_le_sum (f := fun j => |effectProb (fam j) (output r k Φ0 X) -
        effectProb (fam j) σ|) (fun j _ => abs_nonneg _) (Finset.mem_univ j))
  set L := (Fintype.card (Reg r b k ⊕ (Reg r b k × Reg r b k × Bool)) : ℝ) with hL
  have hL0 : 0 < L := by rw [hL]; exact_mod_cast Fintype.card_pos
  set δ := min (G Φ0 / L) 1 with hδ
  have hδ0 : 0 < δ := lt_min (div_pos hpos hL0) one_pos
  have hsep : ∀ Φ ∈ R, ∃ j, δ ≤ |effectProb (fam j) (output r k Φ X) - effectProb (fam j) σ| := by
    intro Φ hΦ
    by_contra hc
    push Not at hc
    have h1 : G Φ < ∑ _j : Reg r b k ⊕ (Reg r b k × Reg r b k × Bool), G Φ0 / L :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun j _ =>
        lt_of_lt_of_le (hc j) (min_le_left _ _)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hL, mul_div_cancel₀ _ hL0.ne'] at h1
    exact absurd (hmin hΦ) (not_le.mpr h1)
  obtain ⟨κ, hκ, hT⟩ := GT fam fam_effect σ hσ R (fun Φ => output r k Φ X)
    (fun Φ hΦ => out_density (hR Φ hΦ) hX.1) hδ0 (min_le_right _ _) hsep
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  refine lt_of_lt_of_le (ENNReal.ofReal_pos.2 (div_pos hκ hk')) ?_
  unfold blockExponent operational
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [self_mem_nhdsWithin] with eps heps
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [hT eps heps.1] with m hm
  unfold blockRate
  have hden : ENNReal.ofReal (κ / k) =
      ENNReal.ofReal (κ * (m + 1)) / ((k * (m + 1) : ℕ) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1; push_cast; field_simp
  rw [hden]
  refine ENNReal.div_le_div_right (hm.trans ?_) _
  exact le_iSup (fun Y : admissible r a k c => testingBits
    {Y' | ∃ Phi ∈ R, Y' = copies (m + 1) (output r k Phi Y.1)}
    (copies (m + 1) (output r k N Y.1)) eps) ⟨X, hX⟩

lemma exp_zero {R : Set (Maps a b)} {N : Maps a b} (h : Setting R N) (hk : 0 < k) {c : Correlation}
    (hsim : ∀ X ∈ admissible r a k c, ∃ Φ ∈ R, output r k Φ X = output r k N X) :
    blockExponent r R N k c = 0 := by
  obtain ⟨-, -, -, -, -, -, hN, -⟩ := h
  refine le_antisymm ?_ zero_le
  unfold blockExponent operational
  have hnb : (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (by rw [closure_Ioo zero_ne_one]; exact ⟨le_rfl, zero_le_one⟩)
  refine liminf_le_of_frequently_le' (Eventually.frequently ?_)
  filter_upwards [self_mem_nhdsWithin] with eps heps
  obtain ⟨he0, he1⟩ := heps
  set C := ENNReal.ofReal (-Real.logb 2 (1 - eps))
  have hb : ∀ m, blockRate r R N k (admissible r a k c) m eps ≤ C / ((k * (m + 1) : ℕ) : ℝ≥0∞) := by
    intro m
    unfold blockRate
    refine ENNReal.div_le_div_right (iSup_le fun X => ?_) _
    obtain ⟨Φ, hΦ, he⟩ := hsim X.1 X.2
    have hσd : IsDensityMatrix (copies (m + 1) (output r k N X.1)) :=
      copies_density (out_density hN X.2.1)
    unfold testingBits
    refine iSup_le fun T => ?_
    obtain ⟨T, hTe, hT1⟩ := T
    have h1 := hT1 _ ⟨Φ, hΦ, by rw [he]⟩
    have hsum : effectProb T (copies (m + 1) (output r k N X.1)) +
        effectProb (1 - T) (copies (m + 1) (output r k N X.1)) = 1 := by
      unfold effectProb
      rw [← Complex.add_re, ← Matrix.trace_add, ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul,
        hσd.2, Complex.one_re]
    have hp : 1 - eps ≤ effectProb T (copies (m + 1) (output r k N X.1)) := by linarith
    have hp0 : 0 < effectProb T (copies (m + 1) (output r k N X.1)) := by linarith
    simp only [hp0.ne', if_false]
    refine ENNReal.ofReal_le_ofReal (neg_le_neg ?_)
    exact Real.logb_le_logb_of_le (by norm_num) (by linarith) hp
  refine (liminf_le_liminf (Eventually.of_forall hb)).trans (le_of_eq ?_)
  have ht : Tendsto (fun m : ℕ => C / ((k * (m + 1) : ℕ) : ℝ≥0∞)) atTop (𝓝 0) := by
    simp only [div_eq_mul_inv]
    have h1 : Tendsto (fun m : ℕ => ((k * (m + 1) : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
      rw [← ENNReal.inv_top]
      refine tendsto_inv_iff.2 ?_
      refine ENNReal.tendsto_nat_nhds_top.comp (tendsto_atTop_mono (fun m => ?_) tendsto_id)
      simp only [id]; nlinarith
    have := ENNReal.Tendsto.const_mul (a := C) h1 (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  exact ht.liminf_eq

end exps

end X4H

-- ===== HJ =====

noncomputable section
set_option linter.unusedSectionVars false
open scoped Matrix ComplexConjugate ComplexOrder ENNReal Kronecker
open Filter Topology

namespace X4H
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

section pp
variable {a b r k : ℕ}

lemma sum_split {c : ℕ} (g : Fin k → Fin r × Fin c → ℂ) :
    ∑ y : Reg r c k, ∏ i, g i (y.1 i, y.2 i) = ∏ i, ∑ P, g i P := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun y1 _ => ?_
  rw [Fintype.prod_sum]

def ppf {c : ℕ} (g : Fin k → Fin r × Fin c → Fin r × Fin c → ℂ) : Mat (Reg r c k) :=
  Matrix.of fun x y => ∏ i, g i (x.1 i, x.2 i) (y.1 i, y.2 i)

lemma pp_eq {c : ℕ} (τ : Fin k → Mat (Fin r × Fin c)) :
    productProbe τ = ppf (fun i P Q => ent (τ i) P Q) := rfl

lemma pp_mul {c : ℕ} (B ω : Fin k → Mat (Fin r × Fin c)) :
    productProbe B * productProbe ω = productProbe (fun i => B i * ω i) := by
  rw [pp_eq, pp_eq, pp_eq]
  ext x z
  simp only [ppf, Matrix.mul_apply, Matrix.of_apply]
  simp only [← Finset.prod_mul_distrib]
  rw [sum_split (fun i P => ent (B i) (x.1 i, x.2 i) P * ent (ω i) P (z.1 i, z.2 i))]
  simp only [ent, Matrix.mul_apply]

lemma trace_pp {c : ℕ} (Z : Fin k → Mat (Fin r × Fin c)) :
    (productProbe Z).trace = ∏ i, (Z i).trace := by
  rw [pp_eq]
  simp only [Matrix.trace, Matrix.diag, ppf, Matrix.of_apply]
  rw [sum_split (fun i P => ent (Z i) P P)]
  rfl

lemma pp_ct {c : ℕ} (B : Fin k → Mat (Fin r × Fin c)) :
    (productProbe B)ᴴ = productProbe (fun i => (B i)ᴴ) := by
  rw [pp_eq, pp_eq]
  ext x z
  simp only [ppf, Matrix.conjTranspose_apply, Matrix.of_apply, star_prod, ent]

lemma pp_density {c : ℕ} {τ : Fin k → Mat (Fin r × Fin c)} (h : ∀ i, IsDensityMatrix (τ i)) :
    IsDensityMatrix (productProbe τ) := by
  choose B hB using fun i => psd_factor (h i).1
  refine ⟨?_, by rw [trace_pp]; simp [fun i => (h i).2]⟩
  have : productProbe τ = (productProbe B)ᴴ * productProbe B := by
    rw [pp_ct, pp_mul]; congr 1; funext i; exact hB i
  rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _

lemma idT_entry (Φ : Maps a b) (τ : Mat (Fin r × Fin a)) (P Q : Fin r × Fin b) :
    ent (idTensorSuperop (R := Fin r) (Φ : Superop (Fin a) (Fin b)) τ) P Q =
      ∑ u, ∑ u', ent τ (P.1, u) (Q.1, u') * ker (Φ : Superop (Fin a) (Fin b)) u u' P.2 Q.2 := by
  simp only [ent, idTensorSuperop, Matrix.of_apply, ker]
  rw [clm_entry']
  rfl

lemma out_pp (Φ : Maps a b) (τ : Fin k → Mat (Fin r × Fin a)) :
    output r k Φ (productProbe τ) =
      productProbe (fun i => idTensorSuperop (R := Fin r) (Φ : Superop (Fin a) (Fin b)) (τ i)) := by
  rw [pp_eq, pp_eq, output_eq]
  ext p q
  simp only [outT, ppf, Matrix.of_apply, idT_entry]
  simp only [← Finset.prod_mul_distrib]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.prod_sum]

lemma tr_idT {Φ : Superop (Fin a) (Fin b)} (hΦ : IsChannel Φ) (τ : Mat (Fin r × Fin a)) :
    (idTensorSuperop (R := Fin r) Φ τ).trace = τ.trace := by
  simp only [Matrix.trace, Matrix.diag, idTensorSuperop, Matrix.of_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  have := chan_trace hΦ (Matrix.of fun i i' => τ (s, i) (s, i'))
  simpa [Matrix.trace] using this

lemma trace_single_mul {I : Type*} [Fintype I] [DecidableEq I] (P Q : I) (M : Matrix I I ℂ) :
    (Matrix.single P Q (1 : ℂ) * M).trace = M Q P := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma marg {c : ℕ} {ω ω' : Fin k → Mat (Fin r × Fin c)} (h1 : ∀ i, (ω i).trace = 1)
    (h2 : ∀ i, (ω' i).trace = 1) (h : productProbe ω = productProbe ω') : ω = ω' := by
  funext i
  ext P Q
  let B : Fin k → Mat (Fin r × Fin c) := Function.update (fun _ => 1) i (Matrix.single Q P 1)
  have key : ∀ ω'' : Fin k → Mat (Fin r × Fin c), (∀ j, (ω'' j).trace = 1) →
      (productProbe B * productProbe ω'').trace = ω'' i P Q := by
    intro ω'' hω
    rw [pp_mul, trace_pp]
    have : ∀ j, (B j * ω'' j).trace = if j = i then ω'' i P Q else 1 := by
      intro j
      by_cases hj : j = i
      · subst hj; simp [B, trace_single_mul]
      · simp [B, hj, hω j]
    simp only [this, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  rw [← key ω h1, ← key ω' h2, h]

end pp

end X4H


-- ===== P60A =====

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

variable {d : ℕ}

lemma kraus_psd {N : Superop (Fin d) (Fin d)} (hN : IsChannel N) {X : Mat (Fin d)}
    (hX : X.PosSemidef) : (N X).PosSemidef := by
  obtain ⟨m, E, -, hE⟩ := hN
  rw [hE, krausApply]
  exact Matrix.posSemidef_sum _ fun j _ => hX.mul_mul_conjTranspose_same (E j)

lemma kraus_trace {N : Superop (Fin d) (Fin d)} (hN : IsChannel N) (X : Mat (Fin d)) :
    (N X).trace = X.trace := by
  obtain ⟨m, E, hK, hE⟩ := hN
  rw [hE, krausApply, Matrix.trace_sum]
  have : ∀ j, (E j * X * (E j)ᴴ).trace = ((E j)ᴴ * E j * X).trace := fun j => by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp_rw [this, ← Matrix.trace_sum, ← Finset.sum_mul]
  rw [show (∑ j, (E j)ᴴ * E j) = 1 from hK, Matrix.one_mul]

lemma perm_unitary (σ : Equiv.Perm (Fin d)) :
    (σ.permMatrix ℂ) ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
    ← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

lemma perm_conj_diag (σ : Equiv.Perm (Fin d)) (l : Fin d → ℂ) :
    σ.permMatrix ℂ * Matrix.diagonal l * (σ.permMatrix ℂ)ᴴ = Matrix.diagonal (l ∘ σ) := by
  rw [Matrix.conjTranspose_permMatrix, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp [Matrix.diagonal_apply, Equiv.Perm.inv_def, σ.injective.eq_iff]


lemma single_psd (j : Fin d) : (Matrix.single j j (1 : ℂ)).PosSemidef := by
  rw [← Matrix.diagonal_single]
  refine Matrix.PosSemidef.diagonal fun i => ?_
  by_cases h : i = j
  · subst h; simp
  · simp [h]

lemma unital_sim (N : Maps d d) (hN : IsChannel (N : Superop (Fin d) (Fin d))) (hu : N 1 = 1)
    (ρ : Mat (Fin d)) (hρ : ρ.PosSemidef) :
    ∃ c : Equiv.Perm (Fin d) → ℝ, ∃ U : Equiv.Perm (Fin d) → Matrix.unitaryGroup (Fin d) ℂ,
      (∀ σ, 0 ≤ c σ) ∧ ∑ σ, c σ = 1 ∧
      N ρ = ∑ σ, (c σ : ℂ) • ((U σ : Mat (Fin d)) * ρ * (U σ : Mat (Fin d))ᴴ) := by
  have hH := hρ.1
  have hS := (kraus_psd hN hρ).1
  have hVm := hH.eigenvectorUnitary.2
  have hWm := hS.eigenvectorUnitary.2
  set V : Mat (Fin d) := (hH.eigenvectorUnitary : Mat (Fin d)) with hV
  set W : Mat (Fin d) := (hS.eigenvectorUnitary : Mat (Fin d)) with hW
  set l := hH.eigenvalues
  set μ := hS.eigenvalues
  have hVV : Vᴴ * V = 1 := Unitary.coe_star_mul_self _
  have hVV' : V * Vᴴ = 1 := Unitary.coe_mul_star_self _
  have hWW : Wᴴ * W = 1 := Unitary.coe_star_mul_self _
  have hWW' : W * Wᴴ = 1 := Unitary.coe_mul_star_self _
  have hρV : ρ = V * Matrix.diagonal (RCLike.ofReal ∘ l) * Vᴴ := by
    have := hH.spectral_theorem; rw [Unitary.conjStarAlgAut_apply] at this; exact this
  have hNW : Wᴴ * N ρ * W = Matrix.diagonal (RCLike.ofReal ∘ μ) := by
    have := hS.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this; exact this
  set Mx : Fin d → Mat (Fin d) := fun j => Wᴴ * N (V * Matrix.single j j 1 * Vᴴ) * W with hMx
  have hMpsd : ∀ j, (Mx j).PosSemidef := fun j =>
    (kraus_psd hN ((single_psd j).mul_mul_conjTranspose_same V)).conjTranspose_mul_mul_same W
  have hsum : ∑ j, Mx j = 1 := by
    simp only [hMx, ← Finset.sum_mul, ← Finset.mul_sum, ← map_sum]
    rw [Matrix.sum_single_one, Matrix.mul_one, hVV', hu, Matrix.mul_one, hWW]
  have htr : ∀ j, (Mx j).trace = 1 := fun j => by
    simp only [hMx]
    rw [Matrix.trace_mul_cycle, hWW', Matrix.one_mul, kraus_trace hN, Matrix.trace_mul_cycle,
      hVV, Matrix.one_mul, Matrix.trace_single_eq_same]
  have hdec : Wᴴ * N ρ * W = ∑ j, ((l j : ℝ) : ℂ) • Mx j := by
    have : ρ = ∑ j, ((l j : ℝ) : ℂ) • (V * Matrix.single j j 1 * Vᴴ) := by
      rw [hρV, ← Matrix.sum_single_eq_diagonal]
      simp only [Matrix.mul_sum, Matrix.sum_mul, Function.comp_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hs : ∀ a : ℂ, Matrix.single j j a = a • Matrix.single j j (1:ℂ) := fun a => by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [hs, Matrix.mul_smul, Matrix.smul_mul]
      rfl
    rw [this, map_sum]
    simp only [map_smul, Matrix.mul_sum, Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_smul, hMx]
  have hμ : ∀ i, μ i = ∑ j, l j * (Mx j i i).re := fun i => by
    have := congrArg (fun A => (A i i).re) (hNW.symm.trans hdec)
    simpa [Matrix.sum_apply] using this
  set D : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => (Mx j i i).re with hD
  have hDs : D ∈ doublyStochastic ℝ (Fin d) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
    · exact (Complex.nonneg_iff.mp ((hMpsd j).diag_nonneg)).1
    · have := congrArg (fun A => (A i i).re) hsum
      simpa [hD, Matrix.sum_apply] using this
    · have := congrArg Complex.re (htr j)
      simpa [hD, Matrix.trace] using this
  obtain ⟨c, hc0, hc1, hcD⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hDs
  have hμ' : ∀ i, μ i = ∑ σ, c σ * l (σ i) := fun i => by
    rw [hμ]
    have : ∀ j, (Mx j i i).re = D i j := fun j => rfl
    simp_rw [this, ← hcD, Matrix.sum_apply, Matrix.smul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, mul_comm]
  have hUm : ∀ σ : Equiv.Perm (Fin d), W * σ.permMatrix ℂ * Vᴴ ∈ Matrix.unitaryGroup (Fin d) ℂ :=
    fun σ => Submonoid.mul_mem _ (Submonoid.mul_mem _ hWm (perm_unitary σ))
      (by rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem hVm)
  refine ⟨c, fun σ => ⟨_, hUm σ⟩, hc0, hc1, ?_⟩
  have hNρ : N ρ = W * Matrix.diagonal (RCLike.ofReal ∘ μ) * Wᴴ := by
    rw [← hNW, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hWW', Matrix.one_mul, Matrix.mul_assoc,
      hWW', Matrix.mul_one]
  have hterm : ∀ σ : Equiv.Perm (Fin d),
      (W * σ.permMatrix ℂ * Vᴴ) * ρ * (W * σ.permMatrix ℂ * Vᴴ)ᴴ =
        W * Matrix.diagonal ((RCLike.ofReal ∘ l) ∘ σ) * Wᴴ := fun σ => by
    rw [← perm_conj_diag, hρV]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V, hVV, Matrix.one_mul, ← Matrix.mul_assoc Vᴴ V, hVV,
      Matrix.one_mul]
  have hdiag : Matrix.diagonal (RCLike.ofReal ∘ μ : Fin d → ℂ) =
      ∑ σ, ((c σ : ℝ) : ℂ) • Matrix.diagonal ((RCLike.ofReal ∘ l : Fin d → ℂ) ∘ σ) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply, Function.comp_apply]
    split_ifs with h
    · rw [hμ']
      push_cast
      simp [smul_eq_mul]
    · simp
  simp only [hterm]
  rw [hNρ, hdiag, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]

end X4P60

-- ===== P60B =====

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Filter Topology

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

variable {d : ℕ}

/-- The mixed-unitary map as a continuous linear map. -/
def mixMap (c : Equiv.Perm (Fin d) → ℝ) (U : Equiv.Perm (Fin d) → Matrix.unitaryGroup (Fin d) ℂ) :
    Maps d d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ∑ σ, (c σ : ℂ) • ((U σ : Mat (Fin d)) * X * (U σ : Mat (Fin d))ᴴ)
      map_add' := fun X Y => by
        simp only [Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib]
      map_smul' := fun a X => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [smul_comm] }

lemma mixMap_apply (c : Equiv.Perm (Fin d) → ℝ)
    (U : Equiv.Perm (Fin d) → Matrix.unitaryGroup (Fin d) ℂ) (X : Mat (Fin d)) :
    mixMap c U X = ∑ σ, (c σ : ℂ) • ((U σ : Mat (Fin d)) * X * (U σ : Mat (Fin d))ᴴ) := rfl

lemma mixMap_mem (c : Equiv.Perm (Fin d) → ℝ)
    (U : Equiv.Perm (Fin d) → Matrix.unitaryGroup (Fin d) ℂ) (hc0 : ∀ σ, 0 ≤ c σ)
    (hc1 : ∑ σ, c σ = 1) : mixMap c U ∈ MU d := by
  set e := (Fintype.equivFin (Equiv.Perm (Fin d))).symm
  refine ⟨?_, Fintype.card (Equiv.Perm (Fin d)), c ∘ e, U ∘ e, fun j => hc0 _, ?_, fun X => ?_⟩
  · refine ⟨Fintype.card (Equiv.Perm (Fin d)),
      fun j => ((Real.sqrt (c (e j)) : ℝ) : ℂ) • (U (e j) : Mat (Fin d)), ?_, fun X => ?_⟩
    · rw [IsKrausFamily]
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have : ∀ j, (U (e j) : Mat (Fin d))ᴴ * (U (e j) : Mat (Fin d)) = 1 := fun j =>
        Unitary.coe_star_mul_self _
      simp only [this, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (hc0 _)]
      rw [← Finset.sum_smul, Equiv.sum_comp e (fun σ => ((c σ : ℝ) : ℂ))]
      rw [← Complex.ofReal_sum, hc1]; simp
    · rw [mixMap_apply, krausApply, ← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hc0 _)]
  · simp only [Function.comp_apply]
    rw [Equiv.sum_comp e c, hc1]
  · rw [mixMap_apply, ← Equiv.sum_comp e]
    rfl

/-- embedding of `Fin d` into the registers for `r = k = 1`. -/
def fe (a : Fin d) : Reg 1 d 1 := (fun _ => 0, fun _ => a)
def ge (p : Reg 1 d 1) : Fin d := p.2 0

lemma ge_fe (a : Fin d) : ge (fe a) = a := rfl
lemma fe_ge (p : Reg 1 d 1) : fe (ge p) = p := by
  obtain ⟨p1, p2⟩ := p
  refine Prod.ext (Subsingleton.elim _ _) ?_
  funext i
  rw [Subsingleton.elim i 0]
  rfl

def eq1 : Fin d ≃ Reg 1 d 1 where
  toFun := fe
  invFun := ge
  left_inv := ge_fe
  right_inv := fe_ge

lemma output_eq (Φ : Maps d d) (X : Mat (Reg 1 d 1)) :
    output 1 1 Φ X = (Φ (X.submatrix fe fe)).submatrix ge ge := by
  ext p q
  rw [← fe_ge p, ← fe_ge q]
  simp only [output, idTensorSuperop, piSuperop, Matrix.of_apply, Matrix.submatrix_apply,
    Fin.prod_univ_one]
  conv_rhs => rw [Matrix.matrix_eq_sum_single (X.submatrix fe fe)]
  rw [map_sum, Matrix.sum_apply, ← (Equiv.funUnique (Fin 1) (Fin d)).symm.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum, Matrix.sum_apply, ← (Equiv.funUnique (Fin 1) (Fin d)).symm.sum_comp]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hs : Matrix.single a b (X.submatrix fe fe a b) = (X.submatrix fe fe a b) • Matrix.single a b 1 := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hs, map_smul, Matrix.smul_apply, smul_eq_mul]
  rfl

lemma trace_ge (A : Mat (Fin d)) : (A.submatrix ge ge).trace = A.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Fintype.sum_equiv eq1.symm _ _ (fun p => rfl)

lemma trace_fe (A : Mat (Reg 1 d 1)) : (A.submatrix fe fe).trace = A.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Fintype.sum_equiv eq1 _ _ (fun p => rfl)

lemma trace_copies {I : Type*} [Fintype I] [DecidableEq I] (m : ℕ) (Y : Mat I) :
    (copies m Y).trace = Y.trace ^ m := by
  simp only [Matrix.trace, Matrix.diag, copies, Matrix.of_apply]
  rw [← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]

end X4P60

-- ===== P60C =====

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Filter Topology

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

variable {d : ℕ}

lemma sim_output (N : Maps d d) (hN : IsChannel (N : Superop (Fin d) (Fin d))) (hu : N 1 = 1)
    (X : Mat (Reg 1 d 1)) (hX : X.PosSemidef) :
    ∃ Phi ∈ MU d, output 1 1 Phi X = output 1 1 N X := by
  obtain ⟨c, U, hc0, hc1, h⟩ := unital_sim N hN hu _ (hX.submatrix fe)
  refine ⟨mixMap c U, mixMap_mem c U hc0 hc1, ?_⟩
  rw [output_eq, output_eq, mixMap_apply, h]

lemma trace_output (N : Maps d d) (hN : IsChannel (N : Superop (Fin d) (Fin d)))
    (X : Mat (Reg 1 d 1)) : (output 1 1 N X).trace = X.trace := by
  rw [output_eq, trace_ge, kraus_trace hN, trace_fe]

lemma rate_bound (N : Maps d d) (hN : IsChannel (N : Superop (Fin d) (Fin d))) (hu : N 1 = 1)
    (m : ℕ) (eps : ℝ) (he1 : eps < 1) :
    blockRate 1 (MU d) N 1 (admissible 1 d 1 .unrestricted) m eps ≤
      ENNReal.ofReal (-Real.logb 2 (1 - eps)) / ((1 * (m + 1) : ℕ) : ℝ≥0∞) := by
  unfold blockRate
  refine ENNReal.div_le_div_right (iSup_le fun X => ?_) _
  obtain ⟨Phi, hPhi, hout⟩ := sim_output N hN hu X.1 X.2.1.1
  unfold testingBits
  refine iSup_le fun T => ?_
  have hmem : copies (m + 1) (output 1 1 N X.1) ∈
      {Y | ∃ Phi ∈ MU d, Y = copies (m + 1) (output 1 1 Phi X.1)} := ⟨Phi, hPhi, by rw [hout]⟩
  have h1 := T.2.2 _ hmem
  have htr : (copies (m + 1) (output 1 1 N X.1)).trace = 1 := by
    rw [trace_copies, trace_output N hN, X.2.1.2, one_pow]
  have hp : 1 - eps ≤ effectProb T.1 (copies (m + 1) (output 1 1 N X.1)) := by
    unfold effectProb at h1 ⊢
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, htr] at h1
    simp only [Complex.one_re] at h1
    linarith
  rw [if_neg (by linarith)]
  apply ENNReal.ofReal_le_ofReal
  exact neg_le_neg (Real.logb_le_logb_of_le (by norm_num) (by linarith) hp)

lemma liminf_zero (N : Maps d d) (hN : IsChannel (N : Superop (Fin d) (Fin d))) (hu : N 1 = 1)
    (eps : ℝ) (he1 : eps < 1) :
    liminf (fun m => blockRate 1 (MU d) N 1 (admissible 1 d 1 .unrestricted) m eps) atTop = 0 := by
  refine le_antisymm ?_ (zero_le)
  set C := ENNReal.ofReal (-Real.logb 2 (1 - eps))
  have ht : Tendsto (fun m : ℕ => C / ((1 * (m + 1) : ℕ) : ℝ≥0∞)) atTop (𝓝 0) := by
    have h0 := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    have h2 := ENNReal.Tendsto.const_mul h0 (Or.inr ENNReal.ofReal_ne_top) (a := C)
    rw [mul_zero] at h2
    refine h2.congr fun m => ?_
    simp [div_eq_mul_inv]
  calc _ ≤ liminf (fun m : ℕ => C / ((1 * (m + 1) : ℕ) : ℝ≥0∞)) atTop :=
        liminf_le_liminf (Eventually.of_forall fun m => rate_bound N hN hu m eps he1)
    _ = 0 := ht.liminf_eq

theorem main (N : Maps d d) (hN : IsChannel (N : Superop (Fin d) (Fin d))) (hu : N 1 = 1) :
    blockExponent 1 (MU d) N 1 .unrestricted = 0 := by
  unfold blockExponent operational
  have : NeBot (𝓝[Set.Ioo (0:ℝ) 1] 0) := left_nhdsWithin_Ioo_neBot one_pos
  rw [liminf_congr (eventually_nhdsWithin_of_forall fun eps he =>
    liminf_zero N hN hu eps he.2 : ∀ᶠ eps in 𝓝[Set.Ioo (0:ℝ) 1] 0, _ = (fun _ => (0:ℝ≥0∞)) eps)]
  exact liminf_const 0

end X4P60


-- ===== P60D =====

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Filter Topology

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

variable {d : ℕ}

/-- mixed-unitary map over an arbitrary finite index. -/
def mixI {ι : Type} [Fintype ι] (c : ι → ℝ) (U : ι → Matrix.unitaryGroup (Fin d) ℂ) : Maps d d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ∑ σ, (c σ : ℂ) • ((U σ : Mat (Fin d)) * X * (U σ : Mat (Fin d))ᴴ)
      map_add' := fun X Y => by
        simp only [Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib]
      map_smul' := fun a X => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [smul_comm] }

lemma mixI_apply {ι : Type} [Fintype ι] (c : ι → ℝ) (U : ι → Matrix.unitaryGroup (Fin d) ℂ)
    (X : Mat (Fin d)) :
    mixI c U X = ∑ σ, (c σ : ℂ) • ((U σ : Mat (Fin d)) * X * (U σ : Mat (Fin d))ᴴ) := rfl

lemma mixI_mem {ι : Type} [Fintype ι] (c : ι → ℝ) (U : ι → Matrix.unitaryGroup (Fin d) ℂ)
    (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∑ σ, c σ = 1) : mixI c U ∈ MU d := by
  set e := (Fintype.equivFin ι).symm
  refine ⟨?_, Fintype.card ι, c ∘ e, U ∘ e, fun j => hc0 _, ?_, fun X => ?_⟩
  · refine ⟨Fintype.card ι,
      fun j => ((Real.sqrt (c (e j)) : ℝ) : ℂ) • (U (e j) : Mat (Fin d)), ?_, fun X => ?_⟩
    · rw [IsKrausFamily]
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have : ∀ j, (U (e j) : Mat (Fin d))ᴴ * (U (e j) : Mat (Fin d)) = 1 := fun j =>
        Unitary.coe_star_mul_self _
      simp only [this, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (hc0 _)]
      rw [← Finset.sum_smul, Equiv.sum_comp e (fun σ => ((c σ : ℝ) : ℂ))]
      rw [← Complex.ofReal_sum, hc1]; simp
    · rw [mixI_apply, krausApply, ← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hc0 _)]
  · simp only [Function.comp_apply]
    rw [Equiv.sum_comp e c, hc1]
  · rw [mixI_apply, ← Equiv.sum_comp e]
    rfl

/-! Depolarizing channel on qutrits as a unitary mixture. -/

def sgn (b : Bool) : ℂ := if b then -1 else 1

def signD (b : Bool × Bool × Bool) : Mat (Fin 3) :=
  Matrix.diagonal ![sgn b.1, sgn b.2.1, sgn b.2.2]

def rotP (a : Fin 3) : Mat (Fin 3) := ((finRotate 3) ^ (a : ℕ)).permMatrix ℂ

lemma signD_mem (b : Bool × Bool × Bool) : signD b ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, signD,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> cases b.1 <;> cases b.2.1 <;> cases b.2.2 <;> simp [sgn]

lemma sign_twirl (M : Mat (Fin 3)) :
    ∑ b, signD b * M * (signD b)ᴴ = (8 : ℂ) • Matrix.diagonal (fun i => M i i) := by
  ext i j
  simp only [Matrix.sum_apply, signD, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Matrix.smul_apply, Matrix.diagonal_apply, Fintype.sum_prod_type,
    Fintype.sum_bool]
  fin_cases i <;> fin_cases j <;> simp [sgn] <;> ring

lemma rot_sum (m : Fin 3 → ℂ) (i : Fin 3) : ∑ a : Fin 3, m (((finRotate 3) ^ (a : ℕ)) i) = ∑ j, m j := by
  have h1 : (finRotate 3) 0 = 1 := rfl
  have h2 : (finRotate 3) 1 = 2 := rfl
  have h3 : (finRotate 3) 2 = 0 := rfl
  fin_cases i <;> simp [Fin.sum_univ_three, pow_succ, Equiv.Perm.mul_apply, h1, h2, h3] <;> ring

lemma depol (M : Mat (Fin 3)) :
    ∑ p : Fin 3 × (Bool × Bool × Bool),
      (rotP p.1 * signD p.2) * M * (rotP p.1 * signD p.2)ᴴ = (8 * M.trace) • (1 : Mat (Fin 3)) := by
  rw [Fintype.sum_prod_type]
  have : ∀ a : Fin 3, ∑ b, (rotP a * signD b) * M * (rotP a * signD b)ᴴ =
      (8 : ℂ) • Matrix.diagonal ((fun i => M i i) ∘ ((finRotate 3 ^ (a : ℕ)))) := by
    intro a
    have : ∀ b, (rotP a * signD b) * M * (rotP a * signD b)ᴴ =
        rotP a * (signD b * M * (signD b)ᴴ) * (rotP a)ᴴ := fun b => by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    simp only [this]
    rw [← Finset.sum_mul, ← Finset.mul_sum, sign_twirl, Matrix.mul_smul, Matrix.smul_mul, rotP,
      perm_conj_diag]
  simp only [this]
  rw [← Finset.smul_sum]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.diagonal_apply, Function.comp_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs with h
  · subst h; rw [rot_sum (fun i => M i i) i, Matrix.trace]; simp
  · simp

end X4P60

-- ===== P60Q =====

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

/-! Tensor powers of matrices (`kp`) and the block-output of a mixed-unitary channel. -/

/-- tensor product of a family of square matrices. -/
def kp {n : ℕ} {I : Type*} (U : Fin n → Matrix I I ℂ) : Matrix (Fin n → I) (Fin n → I) ℂ :=
  Matrix.of fun y x => ∏ l, U l (y l) (x l)

section kp
variable {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

lemma kp_apply (U : Fin n → Matrix I I ℂ) (y x : Fin n → I) : kp U y x = ∏ l, U l (y l) (x l) := rfl

lemma kp_mul (U V : Fin n → Matrix I I ℂ) : kp U * kp V = kp (fun l => U l * V l) := by
  ext y x
  simp only [kp, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.prod_mul_distrib]

lemma kp_conjTranspose (U : Fin n → Matrix I I ℂ) : (kp U)ᴴ = kp (fun l => (U l)ᴴ) := by
  ext y x
  simp [kp, Matrix.conjTranspose_apply]

lemma kp_one : kp (fun _ : Fin n => (1 : Matrix I I ℂ)) = 1 := by
  ext y x
  simp only [kp, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.prod_boole]
  simp [funext_iff]

lemma kp_unitary (U : Fin n → Matrix I I ℂ) (hU : ∀ l, U l ∈ Matrix.unitaryGroup I ℂ) :
    kp U ∈ Matrix.unitaryGroup (Fin n → I) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, kp_conjTranspose, kp_mul]
  have : ∀ l, (U l)ᴴ * U l = 1 := fun l => by
    have := (Matrix.mem_unitaryGroup_iff'.1 (hU l)); rwa [Matrix.star_eq_conjTranspose] at this
  simp only [this]
  exact kp_one

lemma kp_smul (c : Fin n → ℂ) (U : Fin n → Matrix I I ℂ) :
    kp (fun l => c l • U l) = (∏ l, c l) • kp U := by
  ext y x
  simp [kp, Finset.prod_mul_distrib]

lemma kp_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (f : Fin n → ι → Matrix I I ℂ) :
    kp (fun l => ∑ j, f l j) = ∑ L : Fin n → ι, kp (fun l => f l (L l)) := by
  ext y x
  simp only [kp, Matrix.of_apply, Matrix.sum_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

lemma copies_eq_kp (m : ℕ) (X : Matrix I I ℂ) : copies m X = kp (fun _ => X) := rfl

/-- tensor powers of a unitary mixture form a unitary mixture. -/
lemma copies_mix {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) (W : ι → Matrix I I ℂ)
    (Y : Matrix I I ℂ) (m : ℕ) :
    copies m (∑ j, (c j : ℂ) • (W j * Y * (W j)ᴴ)) =
      ∑ L : Fin m → ι, ((∏ l, c (L l) : ℝ) : ℂ) •
        (kp (fun l => W (L l)) * copies m Y * (kp (fun l => W (L l)))ᴴ) := by
  rw [copies_eq_kp, kp_sum]
  refine Finset.sum_congr rfl fun L _ => ?_
  rw [kp_smul, copies_eq_kp, kp_conjTranspose, kp_mul, kp_mul]
  push_cast
  rfl

end kp

/-- matrices on the reference ⊗ system register acting trivially on the reference. -/
def lift {r d k : ℕ} (A : Mat (Fin k → Fin d)) : Mat (Reg r d k) :=
  Matrix.of fun p q => if p.1 = q.1 then A p.2 q.2 else 0

section lift
variable {r d k : ℕ}

lemma lift_apply (A : Mat (Fin k → Fin d)) (p q : Reg r d k) :
    (lift A : Mat (Reg r d k)) p q = if p.1 = q.1 then A p.2 q.2 else 0 := rfl

lemma lift_mul (A B : Mat (Fin k → Fin d)) :
    (lift A : Mat (Reg r d k)) * lift B = lift (A * B) := by
  ext p q
  rw [Matrix.mul_apply, Fintype.sum_prod_type, lift_apply]
  simp only [lift_apply, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Fintype.sum_eq_single q.1 (fun x hx => by simp [hx])]
  simp only [if_true]
  by_cases h : p.1 = q.1
  · simp only [h, if_true]; rw [Matrix.mul_apply]
  · simp [h]

lemma lift_conjTranspose (A : Mat (Fin k → Fin d)) :
    (lift A : Mat (Reg r d k))ᴴ = lift Aᴴ := by
  ext p q
  rw [Matrix.conjTranspose_apply, lift_apply, lift_apply]
  by_cases h : p.1 = q.1
  · simp [h]
  · simp [h, Ne.symm h]

lemma lift_one : (lift (1 : Mat (Fin k → Fin d)) : Mat (Reg r d k)) = 1 := by
  ext p q
  rw [lift_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> simp [h1, h2, Prod.ext_iff]

lemma lift_unitary (A : Mat (Fin k → Fin d)) (hA : A ∈ Matrix.unitaryGroup _ ℂ) :
    (lift A : Mat (Reg r d k)) ∈ Matrix.unitaryGroup _ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, lift_conjTranspose, lift_mul]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hA
  rw [hA, lift_one]

end lift

section outmix
variable {r d k q : ℕ}

lemma conj_single_apply (U : Mat (Fin d)) (a b c c' : Fin d) :
    ((U * Matrix.single a b (1 : ℂ) * Uᴴ : Mat (Fin d))) c c' = U c a * conj (U c' b) := by
  rw [Matrix.mul_apply]
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and]

lemma lift_conj_apply (A : Mat (Fin k → Fin d)) (X : Mat (Reg r d k)) (p p' : Reg r d k) :
    (((lift A : Mat (Reg r d k)) * X * (lift A)ᴴ : Mat (Reg r d k))) p p' =
      ∑ x, ∑ x', A p.2 x * X (p.1, x) (p'.1, x') * conj (A p'.2 x') := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.conjTranspose_apply, lift_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hs : ∀ (x : Fin k → Fin r) (y : Fin k → Fin d), star (if p'.1 = x then A p'.2 y else 0) =
      if p'.1 = x then star (A p'.2 y) else 0 := by intros; split_ifs <;> simp
  simp only [hs, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul]
  rfl

/-- the block output of a mixed-unitary channel. -/
lemma out_mix (Q : Maps d d) (w : Fin q → ℝ) (U : Fin q → Matrix.unitaryGroup (Fin d) ℂ)
    (hQ : ∀ X, Q X = ∑ j, (w j : ℂ) • ((U j : Mat (Fin d)) * X * (U j : Mat (Fin d))ᴴ))
    (X : Mat (Reg r d k)) :
    output r k Q X = ∑ J : Fin k → Fin q, ((∏ i, w (J i) : ℝ) : ℂ) •
      (lift (kp (fun i => (U (J i) : Mat (Fin d)))) * X *
        (lift (kp (fun i => (U (J i) : Mat (Fin d)))))ᴴ) := by
  ext p p'
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, lift_conj_apply, kp_apply]
  simp only [output, idTensorSuperop, piSuperop, Matrix.of_apply, hQ, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, conj_single_apply]
  simp only [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  conv_lhs => enter [2, x]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun x' _ => ?_
  rw [map_prod, Complex.ofReal_prod, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

end outmix

end X4P60

-- ===== P60R =====

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

/-! Heisenberg-picture tests, composition of block outputs, closure of MU. -/

section heis
variable {I ι : Type*} [Fintype I] [DecidableEq I] [Fintype ι]

lemma effectProb_heis (c : ι → ℝ) (V : ι → Matrix I I ℂ) (T Z : Matrix I I ℂ) :
    effectProb (∑ L, (c L : ℂ) • ((V L)ᴴ * T * V L)) Z =
      effectProb T (∑ L, (c L : ℂ) • (V L * Z * (V L)ᴴ)) := by
  simp only [effectProb, Finset.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_smul]
  congr 1
  refine Finset.sum_congr rfl fun L _ => ?_
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc]

lemma heis_sub (c : ι → ℝ) (V : ι → Matrix I I ℂ) (hV : ∀ L, (V L)ᴴ * V L = 1)
    (hc1 : ∑ L, c L = 1) (T : Matrix I I ℂ) :
    1 - ∑ L, (c L : ℂ) • ((V L)ᴴ * T * V L) = ∑ L, (c L : ℂ) • ((V L)ᴴ * (1 - T) * V L) := by
  have h1 : (1 : Matrix I I ℂ) = ∑ L, (c L : ℂ) • ((V L)ᴴ * 1 * V L) := by
    simp only [Matrix.mul_one, hV, ← Finset.sum_smul]
    rw [← Complex.ofReal_sum, hc1]; simp
  conv_lhs => rw [h1]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun L _ => ?_
  rw [← smul_sub, Matrix.mul_sub, Matrix.sub_mul]

lemma heis_psd (c : ι → ℝ) (V : ι → Matrix I I ℂ) (hc0 : ∀ L, 0 ≤ c L) {T : Matrix I I ℂ}
    (hT : T.PosSemidef) : (∑ L, (c L : ℂ) • ((V L)ᴴ * T * V L)).PosSemidef := by
  refine Matrix.posSemidef_sum _ fun L _ => ?_
  have := hT.conjTranspose_mul_mul_same (V L)
  exact this.smul (by exact_mod_cast hc0 L)

lemma heis_effect (c : ι → ℝ) (V : ι → Matrix I I ℂ) (hV : ∀ L, (V L)ᴴ * V L = 1)
    (hc0 : ∀ L, 0 ≤ c L) (hc1 : ∑ L, c L = 1) {T : Matrix I I ℂ} (hT : IsEffect T) :
    IsEffect (∑ L, (c L : ℂ) • ((V L)ᴴ * T * V L)) :=
  ⟨heis_psd c V hc0 hT.1, by rw [heis_sub c V hV hc1]; exact heis_psd c V hc0 hT.2⟩

lemma mix_density (c : ι → ℝ) (V : ι → Matrix I I ℂ) (hV : ∀ L, (V L)ᴴ * V L = 1)
    (hc0 : ∀ L, 0 ≤ c L) (hc1 : ∑ L, c L = 1) {X : Matrix I I ℂ} (hX : IsDensityMatrix X) :
    IsDensityMatrix (∑ L, (c L : ℂ) • (V L * X * (V L)ᴴ)) := by
  refine ⟨Matrix.posSemidef_sum _ fun L _ => (hX.1.mul_mul_conjTranspose_same (V L)).smul
    (by exact_mod_cast hc0 L), ?_⟩
  rw [Matrix.trace_sum]
  have : ∀ L, ((c L : ℂ) • (V L * X * (V L)ᴴ)).trace = (c L : ℂ) * X.trace := fun L => by
    rw [Matrix.trace_smul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul, smul_eq_mul]
  simp only [this, hX.2, mul_one]
  exact_mod_cast hc1

end heis

/-! composition of block outputs -/

lemma clm_entry {a b : ℕ} (Ψ : Maps a b) (A : Mat (Fin a)) (y y' : Fin b) :
    Ψ A y y' = ∑ z, ∑ z', A z z' * Ψ (Matrix.single z z' 1) y y' := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => ?_
  rw [show Matrix.single z z' (A z z') = A z z' • Matrix.single z z' (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, Matrix.smul_apply, smul_eq_mul]

lemma pi_comp {d k : ℕ} (Ψ Φ : Maps d d) (Y : Mat (Fin k → Fin d)) :
    piSuperop (fun _ : Fin k => ((Ψ.comp Φ : Maps d d) : Superop (Fin d) (Fin d))) Y =
      piSuperop (fun _ : Fin k => (Ψ : Superop (Fin d) (Fin d)))
        (piSuperop (fun _ : Fin k => (Φ : Superop (Fin d) (Fin d))) Y) := by
  ext y y'
  simp only [piSuperop, Matrix.of_apply, ContinuousLinearMap.comp_apply]
  simp only [clm_entry Ψ (Φ _)]
  simp only [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => enter [2, z]; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  conv_rhs => enter [2, z]; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  refine Finset.sum_congr rfl fun Z _ => Finset.sum_congr rfl fun Z' _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

lemma out_comp {r d k : ℕ} (Ψ Φ : Maps d d) (X : Mat (Reg r d k)) :
    output r k (Ψ.comp Φ) X = output r k Ψ (output r k Φ X) := by
  ext p q
  simp only [output, idTensorSuperop, Matrix.of_apply]
  rw [pi_comp]
  rfl

/-! closure of MU under composition -/

lemma mu_comp {d : ℕ} {P Q : Maps d d} (hP : P ∈ MU d) (hQ : Q ∈ MU d) : Q.comp P ∈ MU d := by
  obtain ⟨-, q1, w1, U1, h01, h11, e1⟩ := hP
  obtain ⟨-, q2, w2, U2, h02, h12, e2⟩ := hQ
  have : Q.comp P = mixI (fun o : Fin q2 × Fin q1 => w2 o.1 * w1 o.2) (fun o => U2 o.1 * U1 o.2) := by
    ext1 X
    rw [ContinuousLinearMap.comp_apply, mixI_apply, e2, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [e1]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul, Submonoid.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    refine Finset.sum_congr rfl fun b _ => ?_
    push_cast; rfl
  rw [this]
  refine mixI_mem _ _ (fun o => mul_nonneg (h02 _) (h01 _)) ?_
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, h11, mul_one, h12]

end X4P60

-- ===== P60S =====

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

/-! MU preprocessing preserves each admissible probe class. -/

section adm
variable {r d k q : ℕ}

lemma sum_prod_w {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ) (h : ∑ j, w j = 1) :
    ∑ J : Fin n → ι, ∏ i, w (J i) = 1 := by
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
  simp [h]

lemma prod_w_nonneg {n : ℕ} (w : Fin q → ℝ) (h : ∀ j, 0 ≤ w j) (J : Fin n → Fin q) :
    0 ≤ ∏ i, w (J i) := Finset.prod_nonneg fun i _ => h _

/-- `1 ⊗ U` on reference × system. -/
def L1 (U : Mat (Fin d)) : Mat (Fin r × Fin d) := (1 : Mat (Fin r)) ⊗ₖ U

lemma L1_unitary (U : Mat (Fin d)) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    (L1 U : Mat (Fin r × Fin d))ᴴ * L1 U = 1 := by
  rw [L1, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one,
    Matrix.one_mul]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU
  rw [hU, Matrix.one_kronecker_one]

def EE : Reg r d k ≃ (Fin k → Fin r × Fin d) := (Equiv.arrowProdEquivProdArrow _ _ _).symm

lemma pp_eq (τ : Fin k → Mat (Fin r × Fin d)) :
    productProbe τ = (kp τ).submatrix EE EE := rfl

lemma lift_eq (V : Fin k → Mat (Fin d)) :
    (lift (kp V) : Mat (Reg r d k)) = (kp (fun i => (L1 (V i) : Mat (Fin r × Fin d)))).submatrix EE EE := by
  ext p p'
  rw [lift_apply, Matrix.submatrix_apply, kp_apply, kp_apply]
  simp only [L1, Matrix.kronecker_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul]
  by_cases h : p.1 = p'.1
  · simp [EE, h]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, p.1 i ≠ p'.1 i := by
      by_contra hc; push_neg at hc; exact h (funext hc)
    refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
    simp [EE, hi]

lemma prod_out (P : Maps d d) (w : Fin q → ℝ) (U : Fin q → Matrix.unitaryGroup (Fin d) ℂ)
    (hP : ∀ X, P X = ∑ j, (w j : ℂ) • ((U j : Mat (Fin d)) * X * (U j : Mat (Fin d))ᴴ))
    (τ : Fin k → Mat (Fin r × Fin d)) :
    output r k P (productProbe τ) = productProbe (fun i => ∑ j, (w j : ℂ) •
      (L1 (U j : Mat (Fin d)) * τ i * (L1 (U j : Mat (Fin d)))ᴴ)) := by
  rw [out_mix P w U hP, pp_eq, pp_eq, kp_sum]
  simp only [lift_eq, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, kp_conjTranspose,
    kp_mul, kp_smul]
  ext p p'
  simp only [Matrix.sum_apply, Matrix.submatrix_apply, Matrix.smul_apply, Complex.ofReal_prod]

lemma out_lin (P : Maps d d) (w : Fin q → ℝ) (U : Fin q → Matrix.unitaryGroup (Fin d) ℂ)
    (hP : ∀ X, P X = ∑ j, (w j : ℂ) • ((U j : Mat (Fin d)) * X * (U j : Mat (Fin d))ᴴ))
    {ι : Type*} [Fintype ι] (a : ι → ℂ) (X : ι → Mat (Reg r d k)) :
    output r k P (∑ j, a j • X j) = ∑ j, a j • output r k P (X j) := by
  simp only [out_mix P w U hP, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun J _ => ?_
  rw [mul_comm]

lemma W_unitary (V : Fin k → Matrix.unitaryGroup (Fin d) ℂ) :
    (lift (kp fun i => (V i : Mat (Fin d))) : Mat (Reg r d k))ᴴ *
      lift (kp fun i => (V i : Mat (Fin d))) = 1 := by
  have := lift_unitary (r := r) _ (kp_unitary (fun i => (V i : Mat (Fin d))) (fun i => (V i).2))
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at this
  exact this

lemma adm_out {P : Maps d d} (hP : P ∈ MU d) {c : Correlation} {X : Mat (Reg r d k)}
    (hX : X ∈ admissible r d k c) : output r k P X ∈ admissible r d k c := by
  obtain ⟨-, q, w, U, h0, h1, e⟩ := hP
  have hden : ∀ {Y : Mat (Reg r d k)}, IsDensityMatrix Y → IsDensityMatrix (output r k P Y) := by
    intro Y hY
    rw [out_mix P w U e]
    exact mix_density _ _ (fun J => W_unitary _) (fun J => prod_w_nonneg w h0 J)
      (sum_prod_w w h1) hY
  have hτ : ∀ {τ : Mat (Fin r × Fin d)}, IsDensityMatrix τ → IsDensityMatrix (∑ j, (w j : ℂ) •
      (L1 (U j : Mat (Fin d)) * τ * (L1 (U j : Mat (Fin d)))ᴴ)) := fun hτ =>
    mix_density _ _ (fun j => L1_unitary _ (U j).2) h0 h1 hτ
  refine ⟨hden hX.1, ?_⟩
  obtain ⟨-, hX2⟩ := hX
  cases c with
  | unrestricted => trivial
  | product =>
    obtain ⟨τ, hτd, rfl⟩ := hX2
    exact ⟨_, fun i => hτ (hτd i), prod_out P w U e τ⟩
  | separable =>
    obtain ⟨q', w', τ, h0', h1', hτd, rfl⟩ := hX2
    refine ⟨q', w', _, h0', h1', fun j i => hτ (hτd j i), ?_⟩
    rw [out_lin P w U e]
    simp only [prod_out P w U e]

end adm

end X4P60

-- ===== P60TLib =====

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Filter Topology

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

section mono
variable {d : ℕ}

/-- the tests of the `M` problem pull back to tests of the `N` problem. -/
lemma testing_mono {r k m : ℕ} {N M P Q : Maps d d} (hP : P ∈ MU d) (hQ : Q ∈ MU d)
    (hM : M = Q.comp (N.comp P)) (X : Mat (Reg r d k)) (eps : ℝ) :
    testingBits {Y | ∃ Phi ∈ MU d, Y = copies (m + 1) (output r k Phi X)}
        (copies (m + 1) (output r k M X)) eps ≤
      testingBits {Y | ∃ Phi ∈ MU d, Y = copies (m + 1) (output r k Phi (output r k P X))}
        (copies (m + 1) (output r k N (output r k P X))) eps := by
  obtain ⟨-, q, w, U, h0, h1, e⟩ := id hQ
  set W : (Fin k → Fin q) → Mat (Reg r d k) := fun J => lift (kp fun i => (U (J i) : Mat (Fin d)))
  set cJ : (Fin k → Fin q) → ℝ := fun J => ∏ i, w (J i)
  set cc : (Fin (m + 1) → Fin k → Fin q) → ℝ := fun L => ∏ l, cJ (L l)
  set VV : (Fin (m + 1) → Fin k → Fin q) → Mat (Fin (m + 1) → Reg r d k) :=
    fun L => kp fun l => W (L l)
  have hVV : ∀ L, (VV L)ᴴ * VV L = 1 := fun L => by
    simp only [VV, kp_conjTranspose, kp_mul, W, W_unitary, kp_one]
  have hcc0 : ∀ L, 0 ≤ cc L := fun L => Finset.prod_nonneg fun l _ => prod_w_nonneg w h0 _
  have hcc1 : ∑ L, cc L = 1 := sum_prod_w cJ (sum_prod_w w h1)
  have hQY : ∀ Y : Mat (Reg r d k), copies (m + 1) (output r k Q Y) =
      ∑ L, (cc L : ℂ) • (VV L * copies (m + 1) Y * (VV L)ᴴ) := fun Y => by
    rw [out_mix Q w U e, copies_mix]
  have key : ∀ (T : Mat (Fin (m + 1) → Reg r d k)) (Y : Mat (Reg r d k)),
      effectProb (∑ L, (cc L : ℂ) • ((VV L)ᴴ * T * VV L)) (copies (m + 1) Y) =
        effectProb T (copies (m + 1) (output r k Q Y)) := fun T Y => by
    rw [effectProb_heis, hQY]
  unfold testingBits
  refine iSup_le fun T => ?_
  obtain ⟨T, hTe, hT1⟩ := T
  refine le_iSup_of_le ⟨∑ L, (cc L : ℂ) • ((VV L)ᴴ * T * VV L),
    heis_effect cc VV hVV hcc0 hcc1 hTe, ?_⟩ (le_of_eq ?_)
  · rintro ρ ⟨Phi, hPhi, rfl⟩
    rw [heis_sub cc VV hVV hcc1, key]
    exact hT1 _ ⟨Q.comp (Phi.comp P), mu_comp (mu_comp hP hPhi) hQ, by rw [out_comp, out_comp]⟩
  · simp only
    rw [key, hM, out_comp, out_comp]

lemma rate_mono {r k : ℕ} {N M P Q : Maps d d} (hP : P ∈ MU d) (hQ : Q ∈ MU d)
    (hM : M = Q.comp (N.comp P)) (c : Correlation) (m : ℕ) (eps : ℝ) :
    blockRate r (MU d) M k (admissible r d k c) m eps ≤
      blockRate r (MU d) N k (admissible r d k c) m eps := by
  unfold blockRate
  refine ENNReal.div_le_div_right ?_ _
  refine iSup_le fun X => ?_
  exact le_iSup_of_le ⟨output r k P X.1, adm_out hP X.2⟩ (testing_mono hP hQ hM X.1 eps)

lemma exp_mono {r k : ℕ} {N M : Maps d d} (h : MUConvertible N M) (c : Correlation) :
    blockExponent r (MU d) M k c ≤ blockExponent r (MU d) N k c := by
  obtain ⟨P, hP, Q, hQ, hM⟩ := h
  have hM' : M = Q.comp (N.comp P) := by ext1 X; exact hM X
  unfold blockExponent operational
  refine liminf_le_liminf (Eventually.of_forall fun eps => ?_)
  exact liminf_le_liminf (Eventually.of_forall fun m => rate_mono hP hQ hM' c m eps)

lemma ad_mem (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ∃ P ∈ MU d, ∀ X, P X = (U : Mat (Fin d)) * X * (U : Mat (Fin d))ᴴ :=
  ⟨mixI (fun _ : Unit => 1) (fun _ => U), mixI_mem _ _ (fun _ => zero_le_one) (by simp),
    fun X => by simp [mixI_apply]⟩

lemma conv_of_ue {N M : Maps d d} (h : UnitaryEquivalent N M) :
    MUConvertible N M ∧ MUConvertible M N := by
  obtain ⟨U, V, hUV⟩ := h
  obtain ⟨P, hP, eP⟩ := ad_mem U
  obtain ⟨Q, hQ, eQ⟩ := ad_mem V
  obtain ⟨P', hP', eP'⟩ := ad_mem (star U)
  obtain ⟨Q', hQ', eQ'⟩ := ad_mem (star V)
  have hU : (U : Mat (Fin d)) * (U : Mat (Fin d))ᴴ = 1 := by
    have := Unitary.coe_mul_star_self U; exact this
  have hV : (V : Mat (Fin d))ᴴ * (V : Mat (Fin d)) = 1 := by
    have := Unitary.coe_star_mul_self V; exact this
  refine ⟨⟨P, hP, Q, hQ, fun X => by rw [hUV X, eP, eQ]⟩, ⟨P', hP', Q', hQ', fun X => ?_⟩⟩
  rw [eP', eQ', Unitary.coe_star, Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have : M ((U : Mat (Fin d))ᴴ * X * (U : Mat (Fin d))) = (V : Mat (Fin d)) * N X * (V : Mat (Fin d))ᴴ := by
    rw [hUV]
    congr 2
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one]
  rw [this, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.mul_assoc, hV,
    Matrix.mul_one]

end mono

end X4P60


-- ===== HK =====

noncomputable section
set_option linter.unusedSectionVars false
open scoped Matrix ComplexConjugate ComplexOrder ENNReal Kronecker
open Filter Topology

namespace X4H
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

section mucompact
variable {d : ℕ}

abbrev CE (d : ℕ) := Fin d × Fin d × Fin d × Fin d → ℂ

def adU (U : Matrix (Fin d) (Fin d) ℂ) : CE d := fun p => U p.2.2.1 p.1 * star (U p.2.2.2 p.2.1)

lemma adU_cont : Continuous (adU (d := d)) := by
  refine continuous_pi fun p => ?_
  exact ((continuous_id.matrix_elem _ _).mul (continuous_star.comp (continuous_id.matrix_elem _ _)))

lemma unitary_entry_le (A : Matrix (Fin d) (Fin d) ℂ) (hA : A ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (i j : Fin d) : ‖A i j‖ ≤ 1 := by
  have h : ∑ k, A i k * star (A i k) = 1 := by
    have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hA) i) i
    rw [Matrix.mul_apply] at this
    simpa [Matrix.star_apply] using this
  have h2 : ∀ k, A i k * star (A i k) = ((‖A i k‖ ^ 2 : ℝ) : ℂ) := fun k => by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [h2] at h
  have h3 : ∑ k, ‖A i k‖ ^ 2 = 1 := by exact_mod_cast h
  have h4 : ‖A i j‖ ^ 2 ≤ 1 := h3 ▸ Finset.single_le_sum (f := fun k => ‖A i k‖ ^ 2)
    (fun k _ => by positivity) (Finset.mem_univ j)
  nlinarith [norm_nonneg (A i j)]

lemma unitary_compact : IsCompact (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) := by
  have hbox : IsCompact (Set.pi Set.univ fun _ : Fin d =>
      Set.pi Set.univ fun _ : Fin d => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hcl : IsClosed (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) := by
    have : (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) =
        {A | A * star A = 1} := by ext A; exact Matrix.mem_unitaryGroup_iff
    rw [this]
    exact isClosed_eq (continuous_id.matrix_mul continuous_star) continuous_const
  refine hbox.of_isClosed_subset hcl fun A hA => ?_
  exact Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => by
    simpa using unitary_entry_le A hA i j

lemma coord_mixI {ι : Type} [Fintype ι] (c : ι → ℝ) (U : ι → Matrix.unitaryGroup (Fin d) ℂ) :
    coord (X4P60.mixI c U) = ∑ i, c i • adU (U i : Matrix (Fin d) (Fin d) ℂ) := by
  funext p
  simp only [coord, LinearMap.coe_mk, AddHom.coe_mk, X4P60.mixI_apply, Matrix.sum_apply,
    Matrix.smul_apply, Finset.sum_apply, Pi.smul_apply, adU, smul_eq_mul, Complex.real_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

def SU (d : ℕ) : Set (CE d) := adU '' (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ))

def fcomb (n : ℕ) (q : (Fin n → ℝ) × (Fin n → CE d)) : CE d := ∑ i, q.1 i • q.2 i

lemma MU_coord_sub : coord '' (MU d) ⊆ convexHull ℝ (SU d) := by
  rintro _ ⟨Φ, ⟨-, q, w, U, h0, h1, he⟩, rfl⟩
  have : coord Φ = ∑ j, w j • adU (U j : Matrix (Fin d) (Fin d) ℂ) := by
    have hΦ : Φ = X4P60.mixI w U := by
      ext1 X; rw [he X, X4P60.mixI_apply]
    rw [hΦ, coord_mixI]
  rw [this]
  exact (convex_convexHull ℝ _).sum_mem (fun j _ => h0 j) h1
    (fun j _ => subset_convexHull ℝ _ ⟨U j, (U j).2, rfl⟩)

lemma hull_sub (hd : 0 < d) :
    convexHull ℝ (SU d) ⊆ fcomb (Module.finrank ℝ (CE d) + 1) ''
      (stdSimplex ℝ (Fin (Module.finrank ℝ (CE d) + 1)) ×ˢ Set.univ.pi fun _ => SU d) := by
  intro x hx
  obtain ⟨ι, _, z, w, hz, hai, hw0, hw1, hx⟩ := eq_pos_convex_span_of_mem_convexHull hx
  set n := Module.finrank ℝ (CE d) + 1
  have hcard : Fintype.card ι ≤ n := by
    exact hai.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  classical
  let e : ι ↪ Fin n := (Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb hcard)
  have hz0 : adU (1 : Matrix (Fin d) (Fin d) ℂ) ∈ SU d := ⟨1, one_mem _, rfl⟩
  let w' : Fin n → ℝ := fun k => if h : ∃ i, e i = k then w h.choose else 0
  let z' : Fin n → CE d := fun k => if h : ∃ i, e i = k then z h.choose else adU 1
  have hw' : ∀ i, w' (e i) = w i := fun i => by
    have h : ∃ i', e i' = e i := ⟨i, rfl⟩
    simp only [w', dif_pos h]; rw [e.injective h.choose_spec]
  have hz' : ∀ i, z' (e i) = z i := fun i => by
    have h : ∃ i', e i' = e i := ⟨i, rfl⟩
    simp only [z', dif_pos h]; rw [e.injective h.choose_spec]
  have hout : ∀ k, (¬ ∃ i, e i = k) → w' k = 0 := fun k hk => by simp [w', hk]
  have hsum : ∀ g : Fin n → CE d, (∀ k, (¬ ∃ i, e i = k) → g k = 0) →
      ∑ k, g k = ∑ i, g (e i) := by
    intro g hg
    rw [← Finset.sum_map Finset.univ e]
    refine (Finset.sum_subset (Finset.subset_univ _) fun k _ hk => hg k ?_).symm
    rintro ⟨i, rfl⟩; exact hk (Finset.mem_map_of_mem _ (Finset.mem_univ i))
  have hsumR : ∀ g : Fin n → ℝ, (∀ k, (¬ ∃ i, e i = k) → g k = 0) →
      ∑ k, g k = ∑ i, g (e i) := by
    intro g hg
    rw [← Finset.sum_map Finset.univ e]
    refine (Finset.sum_subset (Finset.subset_univ _) fun k _ hk => hg k ?_).symm
    rintro ⟨i, rfl⟩; exact hk (Finset.mem_map_of_mem _ (Finset.mem_univ i))
  refine ⟨(w', z'), ⟨⟨fun k => ?_, ?_⟩, fun k _ => ?_⟩, ?_⟩
  · show 0 ≤ w' k
    by_cases h : ∃ i, e i = k
    · obtain ⟨i, rfl⟩ := h; rw [hw']; exact (hw0 i).le
    · rw [hout k h]
  · show ∑ k, w' k = 1
    rw [hsumR w' hout]; simp only [hw']; exact hw1
  · show z' k ∈ SU d
    by_cases h : ∃ i, e i = k
    · obtain ⟨i, rfl⟩ := h; rw [hz']; exact hz ⟨i, rfl⟩
    · simp only [z', dif_neg h]; exact hz0
  · simp only [fcomb]
    rw [hsum (fun k => w' k • z' k) (fun k hk => by simp [hout k hk])]
    simp only [hw', hz']
    exact hx

lemma comb_sub {n : ℕ} :
    fcomb n '' (stdSimplex ℝ (Fin n) ×ˢ Set.univ.pi fun _ => SU d) ⊆ coord '' (MU d) := by
  rintro _ ⟨⟨w, z⟩, ⟨⟨h0, h1⟩, hz⟩, rfl⟩
  have hz' : ∀ k, ∃ U : Matrix.unitaryGroup (Fin d) ℂ, adU (U : Matrix (Fin d) (Fin d) ℂ) = z k :=
    fun k => by obtain ⟨U, hU, he⟩ := hz k (Set.mem_univ k); exact ⟨⟨U, hU⟩, he⟩
  choose U hU using hz'
  refine ⟨X4P60.mixI w U, X4P60.mixI_mem w U h0 h1, ?_⟩
  rw [coord_mixI]
  simp only [fcomb, hU]

lemma MU_compact (hd : 0 < d) : IsCompact (MU d) := by
  have hSU : IsCompact (SU d) := unitary_compact.image adU_cont
  set n := Module.finrank ℝ (CE d) + 1
  have hK : IsCompact (fcomb (d := d) n '' (stdSimplex ℝ (Fin n) ×ˢ Set.univ.pi fun _ => SU d)) := by
    refine ((isCompact_stdSimplex ℝ (Fin n)).prod (isCompact_univ_pi fun _ => hSU)).image ?_
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp continuous_fst).smul ((continuous_apply i).comp continuous_snd)
  have heq : coord '' (MU d) = fcomb n '' (stdSimplex ℝ (Fin n) ×ˢ Set.univ.pi fun _ => SU d) :=
    Set.Subset.antisymm (MU_coord_sub.trans (hull_sub hd)) comb_sub
  have hemb := LinearMap.isClosedEmbedding_of_injective (𝕜 := ℂ) (coord_inj (a := d) (b := d))
  have := hemb.isCompact_preimage (heq ▸ hK)
  rwa [Set.preimage_image_eq _ hemb.injective] at this

end mucompact

end X4H

-- ===== P3G =====

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

namespace X4P3

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

variable {d : ℕ}

/-- `1 ⊗ E` as a matrix on reference ⊗ input. -/
def lft (E : Mat (Fin d)) : Mat (Fin d × Fin d) := Matrix.of fun p x => if p.1 = x.1 then E p.2 x.2 else 0

lemma lft_mul (E : Mat (Fin d)) (τ : Mat (Fin d × Fin d)) (p z : Fin d × Fin d) :
    (lft E * τ) p z = ∑ y, E p.2 y * τ (p.1, y) z := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single p.1]
  · simp [lft]
  · intro b _ hb
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [lft, Ne.symm hb]
  · simp

lemma mul_lft (E : Mat (Fin d)) (M : Mat (Fin d × Fin d)) (p q : Fin d × Fin d) :
    (M * (lft E)ᴴ) p q = ∑ x, M p (q.1, x) * star (E q.2 x) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single q.1]
  · simp [lft, Matrix.conjTranspose_apply]
  · intro b _ hb
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [lft, Matrix.conjTranspose_apply, Ne.symm hb]
  · simp

lemma idT_krausApply {m : ℕ} (E : Fin m → Mat (Fin d)) (τ : Mat (Fin d × Fin d)) :
    idTensorSuperop (R := Fin d) (krausApply E) τ = ∑ i, lft (E i) * τ * (lft (E i))ᴴ := by
  ext p q
  simp only [idTensorSuperop, krausApply, Matrix.of_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_lft]
  simp only [lft_mul]
  simp only [Finset.sum_mul, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]

lemma out_density (Φ : Maps d d) (hΦ : IsChannel (Φ : Superop (Fin d) (Fin d)))
    (τ : Mat (Fin d × Fin d)) (hτ : IsDensityMatrix τ) :
    IsDensityMatrix (idTensorSuperop (R := Fin d) (Φ : Superop (Fin d) (Fin d)) τ) := by
  refine ⟨?_, by rw [X4H.tr_idT hΦ, hτ.2]⟩
  obtain ⟨m, E, -, hE⟩ := hΦ
  have e : idTensorSuperop (R := Fin d) (Φ : Superop (Fin d) (Fin d)) τ =
      idTensorSuperop (R := Fin d) (krausApply E) τ := by
    ext p q; simp only [idTensorSuperop, Matrix.of_apply, hE]
  rw [e, idT_krausApply]
  exact Matrix.posSemidef_sum _ fun i _ => hτ.1.mul_mul_conjTranspose_same _

lemma cont_out (τ : Mat (Fin d × Fin d)) :
    Continuous fun Φ : Maps d d => idTensorSuperop (R := Fin d) (Φ : Superop (Fin d) (Fin d)) τ := by
  refine continuous_matrix fun p q => ?_
  exact X4H.cont_entry _ _ _

lemma spec_sub {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : IsDensityMatrix X) :
    spectrum ℝ X ⊆ Set.Icc 0 1 := by
  have hH := hX.1.isHermitian
  rw [hH.spectrum_real_eq_range_eigenvalues]
  rintro x ⟨i, rfl⟩
  refine ⟨hX.1.eigenvalues_nonneg i, ?_⟩
  have htr := hH.trace_eq_sum_eigenvalues
  rw [hX.2] at htr
  have h1 : (1 : ℝ) = ∑ j, hH.eigenvalues j := by
    have := congrArg Complex.re htr; simpa using this
  rw [h1]
  exact Finset.single_le_sum (fun j _ => hX.1.eigenvalues_nonneg j) (Finset.mem_univ i)

section cont
open scoped Matrix.Norms.L2Operator

lemma cont_g {n : Type*} [Fintype n] [DecidableEq n] {X : Type*} [TopologicalSpace X]
    (σ : Matrix n n ℂ) (S : Set X) (F : X → Matrix n n ℂ) (hF : ContinuousOn F S)
    (hd : ∀ x ∈ S, IsDensityMatrix (F x)) :
    ContinuousOn (fun x => (cfc (fun t : ℝ => t * Real.log t) (F x) -
      F x * cfc Real.log σ).trace.re) S := by
  have h1 : ContinuousOn (fun x => cfc (fun t : ℝ => t * Real.log t) (F x)) S :=
    hF.cfc' isCompact_Icc (fun t : ℝ => t * Real.log t) (fun x hx => spec_sub _ (hd x hx))
      (fun x hx => (hd x hx).1.isHermitian.isSelfAdjoint)
      (Real.continuous_mul_log.continuousOn)
  have h2 : ContinuousOn (fun x => F x * cfc Real.log σ) S := hF.mul continuousOn_const
  have hT : Continuous (fun M : Matrix n n ℂ => M.trace.re) :=
    Complex.continuous_re.comp (continuous_id.matrix_trace)
  exact hT.comp_continuousOn (h1.sub h2)

end cont

lemma rb_eq {n : Type*} [Fintype n] [DecidableEq n] (X σ : Matrix n n ℂ) (hX : IsDensityMatrix X)
    (hσ : IsDensityMatrix σ) :
    relativeBits X σ = if LinearMap.ker σ.mulVecLin ≤ LinearMap.ker X.mulVecLin then
      ENNReal.ofReal (cfc (fun t : ℝ => t * Real.log t) X - X * cfc Real.log σ).trace.re /
        ENNReal.ofReal (Real.log 2) else ⊤ := by
  unfold relativeBits
  rw [dif_pos ⟨hX, hσ⟩]
  unfold QuantumLoss.umegakiEntropy
  split_ifs
  · rfl
  · exact ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top

end X4P3

-- ===== P3H =====

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

namespace X4P3

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

variable {d : ℕ}

theorem attain (hd : 0 < d) (N : Maps d d) (hN : IsChannel (N : Superop (Fin d) (Fin d)))
    (ρ : Mat (Fin d × Fin d)) (hρ : IsDensityMatrix ρ) :
    ∃ Φ0 ∈ MU d, ∀ Ψ ∈ MU d,
      relativeBits (idTensorSuperop (R := Fin d) (Φ0 : Superop (Fin d) (Fin d)) ρ)
          (idTensorSuperop (R := Fin d) (N : Superop (Fin d) (Fin d)) ρ) ≤
        relativeBits (idTensorSuperop (R := Fin d) (Ψ : Superop (Fin d) (Fin d)) ρ)
          (idTensorSuperop (R := Fin d) (N : Superop (Fin d) (Fin d)) ρ) := by
  set σ := idTensorSuperop (R := Fin d) (N : Superop (Fin d) (Fin d)) ρ with hσdef
  have hσ : IsDensityMatrix σ := out_density N hN ρ hρ
  set X : Maps d d → Mat (Fin d × Fin d) :=
    fun Φ => idTensorSuperop (R := Fin d) (Φ : Superop (Fin d) (Fin d)) ρ with hXdef
  have hX : ∀ Φ ∈ MU d, IsDensityMatrix (X Φ) := fun Φ hΦ => out_density Φ hΦ.1 ρ hρ
  set Kg : Set (Maps d d) := {Φ | LinearMap.ker σ.mulVecLin ≤ LinearMap.ker (X Φ).mulVecLin}
    with hKg
  have hKc : IsClosed Kg := by
    have e : Kg = ⋂ v : LinearMap.ker σ.mulVecLin, {Φ : Maps d d | X Φ *ᵥ (v : Fin d × Fin d → ℂ) = 0} := by
      ext Φ
      simp only [hKg, Set.mem_setOf_eq, Set.mem_iInter, SetLike.le_def, LinearMap.mem_ker,
        Matrix.mulVecLin_apply, Subtype.forall]
    rw [e]
    exact isClosed_iInter fun v => isClosed_eq ((cont_out ρ).matrix_mulVec continuous_const)
      continuous_const
  by_cases hne : (MU d ∩ Kg).Nonempty
  · have hS : IsCompact (MU d ∩ Kg) := (X4H.MU_compact hd).inter_right hKc
    have hG := cont_g σ (MU d ∩ Kg) X (cont_out ρ).continuousOn (fun Φ hΦ => hX Φ hΦ.1)
    obtain ⟨Φ0, hΦ0, hmin⟩ := hS.exists_isMinOn hne hG
    refine ⟨Φ0, hΦ0.1, fun Ψ hΨ => ?_⟩
    rw [rb_eq _ _ (hX Φ0 hΦ0.1) hσ, rb_eq _ _ (hX Ψ hΨ) hσ, if_pos (show LinearMap.ker σ.mulVecLin ≤ LinearMap.ker (X Φ0).mulVecLin from hΦ0.2)]
    by_cases hΨK : Ψ ∈ Kg
    · rw [if_pos (show LinearMap.ker σ.mulVecLin ≤ LinearMap.ker (X Ψ).mulVecLin from hΨK)]
      exact ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal (isMinOn_iff.mp hmin Ψ ⟨hΨ, hΨK⟩)) _
    · rw [if_neg (show ¬ (LinearMap.ker σ.mulVecLin ≤ LinearMap.ker (X Ψ).mulVecLin) from hΨK)]; exact le_top
  · obtain ⟨Φ0, hΦ0, -⟩ := X4P60.ad_mem (d := d) 1
    refine ⟨Φ0, hΦ0, fun Ψ hΨ => ?_⟩
    have h0 : Φ0 ∉ Kg := fun h => hne ⟨Φ0, hΦ0, h⟩
    have h1 : Ψ ∉ Kg := fun h => hne ⟨Ψ, hΨ, h⟩
    rw [rb_eq _ _ (hX Φ0 hΦ0) hσ, rb_eq _ _ (hX Ψ hΨ) hσ, if_neg (show ¬ (LinearMap.ker σ.mulVecLin ≤ LinearMap.ker (X Φ0).mulVecLin) from h0),
      if_neg (show ¬ (LinearMap.ker σ.mulVecLin ≤ LinearMap.ker (X Ψ).mulVecLin) from h1)]

lemma iso_density (hd : 0 < d) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    IsDensityMatrix (isotropic d p) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hpd : pureDensity (omega d) = Matrix.vecMulVec (fun x => omega d x) (star fun x => omega d x) := by
    ext a b; simp [pureDensity, Matrix.vecMulVec_apply]
  have hsm : ((1 - p) / (d : ℝ) ^ 2 : ℝ) • (1 : Mat (Fin d × Fin d)) =
      (((1 - p) / (d : ℝ) ^ 2 : ℝ) : ℂ) • (1 : Mat (Fin d × Fin d)) := by
    ext a b; simp
  unfold isotropic
  rw [hsm]
  refine ⟨?_, ?_⟩
  · refine Matrix.PosSemidef.add ?_ ?_
    · rw [hpd]
      exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast hp)
    · refine Matrix.PosSemidef.one.smul ?_
      have : (0 : ℝ) ≤ (1 - p) / (d : ℝ) ^ 2 := div_nonneg (by linarith) (by positivity)
      exact_mod_cast this
  · rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one]
    have htr : (pureDensity (omega d)).trace = 1 := by
      simp only [Matrix.trace, Matrix.diag, pureDensity, Matrix.of_apply, omega_ap,
        Fintype.sum_prod_type]
      simp only [apply_ite, map_zero, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      simp only [Complex.conj_ofReal, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hd'.le]
      push_cast
      field_simp
    rw [htr]
    simp only [Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
    push_cast
    field_simp
    ring

theorem main (hd : 0 < d) (N : Maps d d) (hN : IsChannel N) (hn : N ∉ MU d) (p : ℝ) (hp : 0 < p)
    (hp1 : p ≤ 1) :
    IsDensityMatrix (isotropic d p) ∧ SingleMinimumAttained N (isotropic d p) ∧
    0 < singleValue N (isotropic d p) ∧
    (p ≤ 1 / (d + 1 : ℝ) → Entanglement.IsSeparablePositive (isotropic d p)) := by
  have hρ := iso_density hd p hp.le hp1
  obtain ⟨Φ0, hΦ0, hmin⟩ := attain hd N hN (isotropic d p) hρ
  refine ⟨hρ, ⟨Φ0, hΦ0, hmin⟩, ?_, fun h => iso_sep hd p hp.le h⟩
  set σ := idTensorSuperop (R := Fin d) (N : Superop (Fin d) (Fin d)) (isotropic d p)
  have hσ : IsDensityMatrix σ := out_density N hN _ hρ
  have hX0 := out_density Φ0 hΦ0.1 _ hρ
  have hle : relativeBits (idTensorSuperop (R := Fin d) (Φ0 : Superop (Fin d) (Fin d))
      (isotropic d p)) σ ≤ singleValue N (isotropic d p) :=
    le_iInf fun Ψ => hmin Ψ.1 Ψ.2
  refine lt_of_lt_of_le ?_ hle
  rw [rb_eq _ _ hX0 hσ]
  split_ifs with hk
  · have hne : idTensorSuperop (R := Fin d) (Φ0 : Superop (Fin d) (Fin d)) (isotropic d p) ≠ σ := by
      intro h
      exact hn (out_ne hd p hp.ne' Φ0 N h ▸ hΦ0)
    have hpos := klein_strict _ σ hX0 hσ hk hne
    apply ENNReal.div_pos_iff.mpr
    exact ⟨(ENNReal.ofReal_pos.mpr hpos).ne', ENNReal.ofReal_ne_top⟩
  · exact ENNReal.zero_lt_top

end X4P3

-- ===== P3Sol =====

noncomputable section

open scoped Matrix ComplexConjugate ENNReal
open Filter Topology

attribute [local instance] Classical.propDecidable Classical.decEq

section
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

theorem solution (d : ℕ) (hd : 0 < d) (N : Maps d d)
    (hN : IsChannel N) (hn : N ∉ MU d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    IsDensityMatrix (isotropic d p) ∧ SingleMinimumAttained N (isotropic d p) ∧
    0 < singleValue N (isotropic d p) ∧
    (p ≤ 1 / (d + 1 : ℝ) → Entanglement.IsSeparablePositive (isotropic d p)) :=
  X4P3.main hd N hN hn p hp hp1

end

end
