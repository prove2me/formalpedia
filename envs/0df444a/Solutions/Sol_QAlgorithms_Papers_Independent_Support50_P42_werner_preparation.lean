-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P42.werner_preparation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:05:46.52337+00:00
-- url     : https://prove2.me/submissions/674103fc-57cb-4b78-9179-a1afe6b8cf89

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

-- ===== WPA =====

noncomputable section

namespace X4WP
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P42
open QAlgorithms.Papers.Independent.Dependency50.P42 (copyIndex)
open scoped Matrix ComplexConjugate

variable {n : ℕ} (z : Fin n → Bool)

abbrev T := {i : Fin n // z i = true}

lemma card_T : Fintype.card (T z) = downCount z := by
  simp [T, downCount, Fintype.card_subtype]

lemma card_F : (Finset.univ.filter fun i => ¬ z i = true).card = n - downCount z := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => z i = true)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  unfold downCount; omega

lemma dc_le : downCount z ≤ n := by
  unfold downCount
  exact (Finset.card_filter_le _ _).trans (by simp)

def σ : T z ≃ Fin (downCount z) := Fintype.equivFinOfCardEq (card_T z)

/-- agreement of two Alice/Bob labels off the singlet positions. -/
def B (x y : Fin (2 ^ n)) : ℂ :=
  if ∀ i, z i = false → (copyIndex 2 n).symm x i = (copyIndex 2 n).symm y i then 1 else 0

def π (x : Fin (2 ^ n)) : Fin (2 ^ downCount z) :=
  copyIndex 2 (downCount z) (fun j => (copyIndex 2 n).symm x ((σ z).symm j))

def c (n : ℕ) : ℝ := (Real.sqrt (2 ^ n))⁻¹

def K (r : Fin (2 ^ n)) : Matrix (Fin (2 ^ n)) (Fin (2 ^ downCount z)) ℂ :=
  fun x p => if p = π z x then (c n : ℂ) * B z x r else 0

lemma B_conj (x y : Fin (2 ^ n)) : conj (B z x y) = B z x y := by
  unfold B; split_ifs <;> simp

lemma B_sq (x y : Fin (2 ^ n)) : B z x y * B z x y = B z x y := by
  unfold B; split_ifs <;> simp

lemma K_conj (r x : Fin (2 ^ n)) (p) : conj (K z r x p) = K z r x p := by
  unfold K; split_ifs <;> simp [B_conj]

lemma c_sq : (c n : ℂ) * c n = ((2 : ℂ) ^ n)⁻¹ := by
  have : c n * c n = ((2 : ℝ) ^ n)⁻¹ := by
    unfold c; rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  rw [← Complex.ofReal_mul, this]; push_cast; ring

/-- product form of a sum over all labels. -/
lemma sum_label (F : (Fin n → Fin 2) → ℂ) : ∑ x : Fin (2 ^ n), F ((copyIndex 2 n).symm x) = ∑ g, F g :=
  Equiv.sum_comp (copyIndex 2 n).symm F

lemma prod_two (P : Fin n → Prop) [DecidablePred P] :
    ∏ i, (if z i = true then (2 : ℂ) else if P i then 1 else 0) =
      2 ^ downCount z * (if ∀ i, z i = false → P i then 1 else 0) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_boole]
  congr 1
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true]

lemma count_B (x y : Fin (2 ^ n)) : ∑ r, B z x r * B z y r = 2 ^ downCount z * B z x y := by
  unfold B
  set X := (copyIndex 2 n).symm x
  set Y := (copyIndex 2 n).symm y
  rw [sum_label (fun g => (if ∀ i, z i = false → X i = g i then (1:ℂ) else 0) *
    (if ∀ i, z i = false → Y i = g i then 1 else 0))]
  have e : ∀ g : Fin n → Fin 2, (if ∀ i, z i = false → X i = g i then (1:ℂ) else 0) *
      (if ∀ i, z i = false → Y i = g i then 1 else 0) =
      ∏ i, ((if (z i = false → X i = g i) then (1:ℂ) else 0) *
        (if (z i = false → Y i = g i) then 1 else 0)) := by
    intro g
    rw [Finset.prod_mul_distrib, Finset.prod_boole, Finset.prod_boole]
    simp
  simp_rw [e]
  rw [← Fintype.prod_sum (fun i b => (if (z i = false → X i = b) then (1:ℂ) else 0) *
        (if (z i = false → Y i = b) then 1 else 0))]
  rw [← prod_two z (fun i => X i = Y i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases h : z i
  · simp only [Bool.false_eq_true, if_false, forall_const]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    by_cases hxy : X i = Y i
    · simp [hxy]
    · simp [hxy, Ne.symm hxy]
  · simp

lemma count_fiber (p : Fin (2 ^ downCount z)) :
    ∑ x : Fin (2 ^ n), (if π z x = p then (1:ℂ) else 0) = 2 ^ (n - downCount z) := by
  set u := (copyIndex 2 (downCount z)).symm p
  have e1 : ∀ x : Fin (2 ^ n), (π z x = p) ↔
      ∀ i (h : z i = true), (copyIndex 2 n).symm x i = u (σ z ⟨i, h⟩) := by
    intro x
    unfold π
    rw [← Equiv.eq_symm_apply, funext_iff]
    constructor
    · intro hx i h
      have := hx (σ z ⟨i, h⟩)
      simpa using this
    · intro hx j
      have := hx ((σ z).symm j).1 ((σ z).symm j).2
      simpa using this
  simp_rw [e1]
  rw [sum_label (fun g => if ∀ i (h : z i = true), g i = u (σ z ⟨i, h⟩) then (1:ℂ) else 0)]
  have e : ∀ g : Fin n → Fin 2, (if ∀ i (h : z i = true), g i = u (σ z ⟨i, h⟩) then (1:ℂ) else 0) =
      ∏ i, (if (∀ h : z i = true, g i = u (σ z ⟨i, h⟩)) then (1:ℂ) else 0) := by
    intro g; rw [Finset.prod_boole]; simp
  simp_rw [e]
  rw [← Fintype.prod_sum (fun i b => if (∀ h : z i = true, b = u (σ z ⟨i, h⟩)) then (1:ℂ) else 0)]
  rw [← card_F z, ← Finset.prod_const, ← Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun i => z i = true)]
  rw [Finset.prod_eq_one, one_mul]
  · refine Finset.prod_congr rfl fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at hi
    simp [hi]
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [hi]

lemma K_kraus : IsKrausFamily (K z) := by
  unfold IsKrausFamily
  ext p q
  rw [Matrix.sum_apply]
  simp only [Matrix.mul_apply, conjTranspose_apply, RCLike.star_def, K_conj]
  rw [Finset.sum_comm]
  have e : ∀ x : Fin (2 ^ n), ∑ r, K z r x p * K z r x q =
      (if p = q then (1:ℂ) else 0) * ((c n : ℂ) * c n * 2 ^ downCount z) *
        (if π z x = p then (1:ℂ) else 0) := by
    intro x
    unfold K
    by_cases hp : p = π z x
    · subst hp
      by_cases hq : q = π z x
      · subst hq
        have hB1 : B z x x = 1 := by simp [B]
        have hc := count_B z x x
        rw [hB1, mul_one] at hc
        simp only [if_true, one_mul, mul_one]
        rw [← hc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [← B_sq z x r]; ring
      · simp [hq, Ne.symm hq]
    · simp [hp, Ne.symm hp]
  simp_rw [e, ← Finset.mul_sum]
  rw [count_fiber, Matrix.one_apply]
  have h2 : (2:ℂ) ^ downCount z * 2 ^ (n - downCount z) = 2 ^ n := by
    rw [← pow_add, Nat.add_sub_cancel' (dc_le z)]
  split_ifs
  · rw [c_sq, one_mul, mul_assoc, h2, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)]
  · simp

end X4WP

-- ===== WPB =====

noncomputable section

namespace X4WP
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P42
open QAlgorithms.Papers.Independent.Dependency50.P42 (copyIndex singletState singletVector singlets
  dimensionedPower)
open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)
open scoped Matrix ComplexConjugate Kronecker

lemma kronL {a b h : ℕ} (E : Matrix (Fin h) (Fin a) ℂ) (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (xa ya : Fin h) (xb yb : Fin b) :
    ((Matrix.kronecker E (1 : Matrix (Fin b) (Fin b) ℂ) * X : Matrix (Fin h × Fin b) (Fin a × Fin b) ℂ) *
      (Matrix.kronecker E (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ) (xa, xb) (ya, yb) =
      ∑ pa, ∑ qa, E xa pa * X (pa, xb) (qa, yb) * conj (E ya qa) := by
  simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.kronecker, kroneckerMap_apply,
    Fintype.sum_prod_type, one_apply, RCLike.star_def, mul_ite, ite_mul, mul_one, mul_zero,
    zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_one, map_zero,
    apply_ite (starRingEnd ℂ), Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

lemma kronR {a b h : ℕ} (E : Matrix (Fin h) (Fin b) ℂ) (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (xa ya : Fin a) (xb yb : Fin h) :
    ((Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) E * X : Matrix (Fin a × Fin h) (Fin a × Fin b) ℂ) *
      (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) E)ᴴ) (xa, xb) (ya, yb) =
      ∑ pb, ∑ qb, E xb pb * X (xa, pb) (ya, qb) * conj (E yb qb) := by
  simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.kronecker, kroneckerMap_apply,
    Fintype.sum_prod_type, one_apply, RCLike.star_def, mul_ite, ite_mul, mul_one, mul_zero,
    zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_one, map_zero, one_mul,
    apply_ite (starRingEnd ℂ), Finset.sum_mul, Finset.mul_sum, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  exact Finset.sum_comm

variable {n : ℕ} (z : Fin n → Bool)

lemma collapse2 (r x y : Fin (2 ^ n)) (Φ : Fin (2 ^ downCount z) → Fin (2 ^ downCount z) → ℂ) :
    ∑ p, ∑ q, K z r x p * Φ p q * conj (K z r y q) =
      ((c n : ℂ) * c n) * (B z x r * B z y r) * Φ (π z x) (π z y) := by
  simp only [K_conj]
  unfold K
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
  ring

lemma main_entry (xa xb ya yb : Fin (2 ^ n))
    (X : Matrix (Fin (2 ^ downCount z) × Fin (2 ^ downCount z))
      (Fin (2 ^ downCount z) × Fin (2 ^ downCount z)) ℂ) :
    ∑ i, ∑ j, ∑ pb, ∑ qb, K z j xb pb *
      (∑ pa, ∑ qa, K z i xa pa * X (pa, pb) (qa, qb) * conj (K z i ya qa)) * conj (K z j yb qb) =
      ((c n : ℂ) * c n) ^ 2 * (2 ^ downCount z * B z xa ya) * (2 ^ downCount z * B z xb yb) *
        X (π z xa, π z xb) (π z ya, π z yb) := by
  have h1 : ∀ i pb qb, ∑ pa, ∑ qa, K z i xa pa * X (pa, pb) (qa, qb) * conj (K z i ya qa) =
      ((c n : ℂ) * c n) * (B z xa i * B z ya i) * X (π z xa, pb) (π z ya, qb) :=
    fun i pb qb => collapse2 z i xa ya (fun p q => X (p, pb) (q, qb))
  simp_rw [h1]
  have h2 : ∀ i j, ∑ pb, ∑ qb, K z j xb pb *
      (((c n : ℂ) * c n) * (B z xa i * B z ya i) * X (π z xa, pb) (π z ya, qb)) * conj (K z j yb qb) =
      ((c n : ℂ) * c n) * (B z xb j * B z yb j) *
        (((c n : ℂ) * c n) * (B z xa i * B z ya i) * X (π z xa, π z xb) (π z ya, π z yb)) := by
    intro i j
    have := collapse2 z j xb yb
      (fun p q => ((c n : ℂ) * c n) * (B z xa i * B z ya i) * X (π z xa, p) (π z ya, q))
    beta_reduce at this
    rw [← this]
  simp_rw [h2]
  rw [← count_B z xa ya, ← count_B z xb yb, mul_assoc (((c n : ℂ) * c n) ^ 2), Finset.sum_mul_sum,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma scal : ((c n : ℂ) * c n) ^ 2 * 2 ^ downCount z * 2 ^ downCount z = (1 / 4 : ℂ) ^ (n - downCount z) := by
  rw [c_sq]
  have h2 : (2:ℂ) ^ downCount z * 2 ^ (n - downCount z) = 2 ^ n := by
    rw [← pow_add, Nat.add_sub_cancel' (dc_le z)]
  rw [← h2]
  have : (2:ℂ) ^ (n - downCount z) ≠ 0 := pow_ne_zero _ two_ne_zero
  have : (2:ℂ) ^ downCount z ≠ 0 := pow_ne_zero _ two_ne_zero
  have h4 : (1 / 4 : ℂ) ^ (n - downCount z) = ((2 ^ (n - downCount z)) ^ 2)⁻¹ := by
    rw [one_div, inv_pow]; congr 1; rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4]
  field_simp

lemma singlets_entry (xa xb ya yb : Fin (2 ^ n)) :
    singlets (downCount z) (π z xa, π z xb) (π z ya, π z yb) =
      ∏ j, singletState ((copyIndex 2 n).symm xa ((σ z).symm j), (copyIndex 2 n).symm xb ((σ z).symm j))
        ((copyIndex 2 n).symm ya ((σ z).symm j), (copyIndex 2 n).symm yb ((σ z).symm j)) := by
  simp [singlets, dimensionedPower, QAlgorithms.Papers.Independent.Information100.P80.groupedPower, π]

lemma wb_entry (xa xb ya yb : Fin (2 ^ n)) :
    wernerBranch n z (xa, xb) (ya, yb) = (1 / 4 : ℂ) ^ (n - downCount z) * B z xa ya * B z xb yb *
      ∏ j, singletState ((copyIndex 2 n).symm xa ((σ z).symm j), (copyIndex 2 n).symm xb ((σ z).symm j))
        ((copyIndex 2 n).symm ya ((σ z).symm j), (copyIndex 2 n).symm yb ((σ z).symm j)) := by
  unfold wernerBranch
  beta_reduce
  set α := (copyIndex 2 n).symm
  rw [Finset.prod_congr rfl (fun i _ => (apply_ite (fun M : Op (Fin 2 × Fin 2) =>
    M (α xa i, α xb i) (α ya i, α yb i)) (z i = true) singletState ((1/4:ℂ) • 1)))]
  rw [Finset.prod_ite]
  have e1 : ∏ i ∈ Finset.univ.filter (fun i => z i = true),
      singletState (α xa i, α xb i) (α ya i, α yb i) =
      ∏ j, singletState (α xa ((σ z).symm j), α xb ((σ z).symm j))
        (α ya ((σ z).symm j), α yb ((σ z).symm j)) := by
    rw [Finset.prod_subtype (p := fun i => z i = true) _ (by simp)
      (fun i => singletState (α xa i, α xb i) (α ya i, α yb i))]
    exact (Equiv.prod_comp (σ z).symm
      (fun t : T z => singletState (α xa t, α xb t) (α ya t, α yb t))).symm
  have e2 : ∏ i ∈ Finset.univ.filter (fun i => ¬ z i = true),
      ((1 / 4 : ℂ) • (1 : Op (Fin 2 × Fin 2))) (α xa i, α xb i) (α ya i, α yb i) =
      (1 / 4 : ℂ) ^ (n - downCount z) * B z xa ya * B z xb yb := by
    simp only [Matrix.smul_apply, one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [← card_F z, ← Finset.prod_const]
    have : ∀ i ∈ Finset.univ.filter (fun i => ¬ z i = true),
        (if (α xa i, α xb i) = (α ya i, α yb i) then (1 / 4 : ℂ) else 0) =
          (1 / 4 : ℂ) * (if (α xa i = α ya i ∧ α xb i = α yb i) then 1 else 0) := by
      intro i _; simp only [Prod.mk.injEq]; split_ifs <;> simp
    rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_boole, mul_assoc]
    congr 1
    unfold B
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true]
    by_cases hA : ∀ i, z i = false → α xa i = α ya i ∧ α xb i = α yb i
    · rw [if_pos hA, if_pos (fun i hi => (hA i hi).1), if_pos (fun i hi => (hA i hi).2)]; simp
    · rw [if_neg hA]; push Not at hA; obtain ⟨i, hi, h⟩ := hA
      by_cases h1 : α xa i = α ya i
      · rw [if_neg (show ¬ ∀ i, z i = false → α xb i = α yb i from fun H => h h1 (H i hi))]; simp
      · rw [if_neg (show ¬ ∀ i, z i = false → α xa i = α ya i from fun H => h1 (H i hi))]; simp
  rw [e1, e2]; ring

end X4WP

-- ===== WPC =====

noncomputable section

namespace X4WP
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P42
open QAlgorithms.Papers.Independent.Dependency50.P42 (copyIndex singletState singletVector singlets
  dimensionedPower)
open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)
open scoped Matrix ComplexConjugate Kronecker ComplexOrder

lemma sv_norm : ∑ p, singletVector p * conj (singletVector p) = 1 := by
  have h : ((Real.sqrt 2 / 2 : ℝ) : ℂ) * ((Real.sqrt 2 / 2 : ℝ) : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_mul]
    have : Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) = 1 / 2 := by
      rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]; norm_num
    rw [this]; push_cast; ring
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, singletVector, PiLp.toLp_apply]
  simp [Complex.conj_ofReal]
  rw [show (starRingEnd ℂ) 2 = 2 from map_ofNat _ 2]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  linear_combination (1 / 2 : ℂ) * hs

lemma singlet_psd : singletState.PosSemidef := by
  have : singletState = vecMulVec (singletVector : Fin 2 × Fin 2 → ℂ) (star (singletVector : Fin 2 × Fin 2 → ℂ)) := by
    ext a b; simp [singletState, pureDensity, vecMulVec]
  rw [this]; exact posSemidef_vecMulVec_self_star _

lemma singlet_trace : singletState.trace = 1 := by
  rw [← sv_norm]; simp [Matrix.trace, singletState, pureDensity]

lemma werner_density : IsDensityMatrix wernerState := by
  refine ⟨?_, ?_⟩
  · unfold wernerState
    have h8 : (0 : ℂ) ≤ 1 / 8 := by
      rw [show (1 / 8 : ℂ) = ((1 / 8 : ℝ) : ℂ) by push_cast; ring]; exact_mod_cast (by norm_num : (0:ℝ) ≤ 1 / 8)
    have h2 : (0 : ℂ) ≤ 1 / 2 := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]; exact_mod_cast (by norm_num : (0:ℝ) ≤ 1 / 2)
    exact (PosSemidef.one.smul h8).add (singlet_psd.smul h2)
  · unfold wernerState
    rw [trace_add, trace_smul, trace_smul, singlet_trace, trace_one]
    simp; norm_num

lemma werner_avg (n : ℕ) :
    (((2 : ℝ) ^ n)⁻¹ : ℂ) • (∑ z : Fin n → Bool, wernerBranch n z) = dimensionedPower wernerState n := by
  ext x y
  rw [Matrix.smul_apply, Matrix.sum_apply]
  simp only [wernerBranch, dimensionedPower, QAlgorithms.Papers.Independent.Information100.P80.groupedPower]
  set α := (copyIndex 2 n).symm
  rw [← Fintype.prod_sum (fun i (b : Bool) => (if b = true then singletState else (1 / 4 : ℂ) • (1 : Op (Fin 2 × Fin 2)))
    (α x.1 i, α x.2 i) (α y.1 i, α y.2 i))]
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
  rw [smul_eq_mul, show (((2 : ℝ) ^ n)⁻¹ : ℂ) = ∏ _i : Fin n, (1 / 2 : ℂ) by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]; push_cast; rw [one_div, inv_pow], ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [wernerState, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

def flip (n : ℕ) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun z i := !z i
  invFun z i := !z i
  left_inv z := by funext i; simp
  right_inv z := by funext i; simp

lemma dc_flip {n : ℕ} (z : Fin n → Bool) : downCount z + downCount (flip n z) = n := by
  unfold downCount
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (fun i => z i = true)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  convert this using 3
  ext i; simp [flip]

lemma dc_avg (n : ℕ) : ((2 : ℝ) ^ n)⁻¹ * (∑ z : Fin n → Bool, (downCount z : ℝ)) = (n : ℝ) / 2 := by
  have h1 : ∑ z : Fin n → Bool, (downCount (flip n z) : ℝ) = ∑ z : Fin n → Bool, (downCount z : ℝ) :=
    Equiv.sum_comp (flip n) (fun z => (downCount z : ℝ))
  have h2 : ∑ z : Fin n → Bool, ((downCount z : ℝ) + downCount (flip n z)) = (2 : ℝ) ^ n * n := by
    simp_rw [← Nat.cast_add, dc_flip]
    simp [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
  rw [Finset.sum_add_distrib, h1] at h2
  have : ∑ z : Fin n → Bool, (downCount z : ℝ) = (2 : ℝ) ^ n * n / 2 := by linarith
  rw [this]; field_simp

end X4WP

-- ===== WPSol =====

noncomputable section

section
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P42
open QAlgorithms.Papers.Independent.Information100.P21 (Op Vec FiniteLOCC)
open QAlgorithms.Papers.Independent.Dependency50.P42 (dimensionedPower singlets)
open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (n : ℕ) :
    IsDensityMatrix wernerState ∧
    (((2 : ℝ)^n)⁻¹ : ℂ) • (∑ z : Fin n → Bool, wernerBranch n z)=dimensionedPower wernerState n ∧
    ((2 : ℝ)^n)⁻¹*(∑ z : Fin n → Bool, (downCount z : ℝ))=(n : ℝ)/2 ∧
    (∀ z : Fin n → Bool, downCount z≤n ∧
      ∃ L : Superop (Fin (2^(downCount z)) × Fin (2^(downCount z))) (Fin (2^n) × Fin (2^n)),
        FiniteLOCC L ∧ L (singlets (downCount z))=wernerBranch n z) := by
  refine ⟨X4WP.werner_density, X4WP.werner_avg n, X4WP.dc_avg n, fun z => ⟨X4WP.dc_le z, ?_⟩⟩
  refine ⟨_, FiniteLOCC.alice (X4WP.K z) (X4WP.K_kraus z) _
    (fun i => FiniteLOCC.bob (X4WP.K z) (X4WP.K_kraus z) _ (fun _ => FiniteLOCC.identity _ _)), ?_⟩
  ext ⟨xa, xb⟩ ⟨ya, yb⟩
  simp only [Matrix.sum_apply]
  simp only [X4WP.kronR, X4WP.kronL]
  rw [X4WP.main_entry, X4WP.wb_entry, X4WP.singlets_entry, ← X4WP.scal z]
  ring

end
end
