-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P42.schmidt_coding
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:27:27.541802+00:00
-- url     : https://prove2.me/submissions/04f0229f-bf4f-4381-8eae-d27e64708eb9

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

-- ===== P42Lib =====

noncomputable section

namespace X4P42L
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P42
open scoped BigOperators Matrix ComplexConjugate
open Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

lemma card_down (n k : ℕ) :
    (Finset.univ.filter fun x : Fin n → Bool => downCount x = k).card = n.choose k := by
  rw [show n.choose k = ((Finset.univ : Finset (Fin n)).powersetCard k).card by simp]
  refine Finset.card_bij (fun x _ => Finset.univ.filter fun i => x i = true) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, Finset.card_fin]
    simpa [downCount] using hx
  · intro x _ y _ h
    funext i
    have := congrArg (fun s => i ∈ s) h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
    cases hx : x i <;> cases hy : y i <;> simp_all
  · intro s hs
    refine ⟨fun i => decide (i ∈ s), ?_, ?_⟩
    · simp only [Finset.mem_powersetCard, Finset.card_fin] at hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold downCount
      simpa using hs
    · ext i; simp

lemma down_le {n : ℕ} (x : Fin n → Bool) : downCount x ≤ n := by
  unfold downCount
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma prod_amp {n : ℕ} (a b : ℂ) (x : Fin n → Bool) :
    ∏ i, (if x i then a else b) = a ^ downCount x * b ^ (n - downCount x) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  congr 2
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (fun i => x i = true)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  unfold downCount
  simp only [Bool.not_eq_true] at h ⊢
  omega

/-- Diagonal Kronecker products act pointwise. -/
lemma act_kron_diag {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (d : I → ℂ) (e : J → ℂ)
    (v : EuclideanSpace ℂ (I × J)) (z : I × J) :
    act (Matrix.kronecker (diagonal d) (diagonal e)) v z = d z.1 * e z.2 * v z := by
  simp only [act, Matrix.kronecker, Matrix.diagonal_kronecker_diagonal, PiLp.toLp_apply,
    mulVec_diagonal]

lemma proj_eq (n k : ℕ) :
    schmidtTypeProjector n k = diagonal fun x => if downCount x = k then (1 : ℂ) else 0 := rfl

lemma one_eq (I : Type*) [Fintype I] [DecidableEq I] :
    (1 : Matrix I I ℂ) = diagonal fun _ => (1 : ℂ) := (diagonal_one).symm

/-- Amplitude of a Schmidt block entry. -/
def amp (n k : ℕ) (p : ℝ) : ℂ := (Real.sqrt p : ℂ) ^ k * (Real.sqrt (1 - p) : ℂ) ^ (n - k)

lemma block_apply (n : ℕ) (p : ℝ) (z : (Fin n → Bool) × (Fin n → Bool)) :
    schmidtBlock n p z = if z.1 = z.2 then amp n (downCount z.1) p else 0 := by
  simp only [schmidtBlock, PiLp.toLp_apply, amp]
  split_ifs <;> simp [prod_amp]

lemma normSq_amp (n k : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ‖amp n k p‖ ^ 2 = p ^ k * (1 - p) ^ (n - k) := by
  simp only [amp, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, ← pow_mul]
  rw [mul_comm k 2, mul_comm (n - k) 2, pow_mul, pow_mul, Real.sq_sqrt hp,
    Real.sq_sqrt (by linarith)]

/-- Sum over pairs supported on the diagonal with a given down-count. -/
lemma sum_diag_type {n : ℕ} (k : ℕ) (f : (Fin n → Bool) → ℝ) :
    ∑ z : (Fin n → Bool) × (Fin n → Bool), (if z.1 = z.2 ∧ downCount z.1 = k then f z.1 else 0) =
      ∑ x, if downCount x = k then f x else 0 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy; simp [Ne.symm hy]
  · simp

lemma sum_type_const {n : ℕ} (k : ℕ) (c : ℝ) :
    ∑ x : Fin n → Bool, (if downCount x = k then c else 0) = n.choose k * c := by
  rw [← Finset.sum_filter, Finset.sum_const, card_down, nsmul_eq_mul]

/-- The type-k branch. -/
lemma branch_apply (n k l : ℕ) (p : ℝ) (z : (Fin n → Bool) × (Fin n → Bool)) :
    act (Matrix.kronecker (schmidtTypeProjector n k) (schmidtTypeProjector n l))
      (schmidtBlock n p) z =
      if z.1 = z.2 ∧ downCount z.1 = k ∧ downCount z.2 = l then amp n k p else 0 := by
  rw [proj_eq, proj_eq, act_kron_diag, block_apply]
  obtain ⟨a, b⟩ := z
  simp only
  by_cases h : a = b
  · subst h
    by_cases hk : downCount a = k
    · subst hk; by_cases hl : downCount a = l <;> simp [hl]
    · simp [hk]
  · simp [h]

lemma branch1_apply (n k : ℕ) (p : ℝ) (z : (Fin n → Bool) × (Fin n → Bool)) :
    act (Matrix.kronecker (schmidtTypeProjector n k) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
      (schmidtBlock n p) z =
      if z.1 = z.2 ∧ downCount z.1 = k then amp n k p else 0 := by
  rw [proj_eq, one_eq, act_kron_diag, block_apply]
  obtain ⟨a, b⟩ := z
  simp only
  by_cases h : a = b
  · subst h
    by_cases hk : downCount a = k
    · subst hk; simp
    · simp [hk]
  · simp [h]

lemma norm_branch1 (n k : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ‖act (Matrix.kronecker (schmidtTypeProjector n k) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
      (schmidtBlock n p)‖ ^ 2 = schmidtOutcomeWeight n p k := by
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [branch1_apply]
  have : ∀ z : (Fin n → Bool) × (Fin n → Bool),
      ‖(if z.1 = z.2 ∧ downCount z.1 = k then amp n k p else 0)‖ ^ 2 =
        if z.1 = z.2 ∧ downCount z.1 = k then p ^ k * (1 - p) ^ (n - k) else 0 := by
    intro z; split_ifs <;> simp [normSq_amp n k p hp hp1]
  simp_rw [this]
  rw [sum_diag_type k (fun _ => p ^ k * (1 - p) ^ (n - k)), sum_type_const, schmidtOutcomeWeight]
  ring

lemma kraus_proj (n : ℕ) :
    IsKrausFamily (fun k : Fin (n+1) => schmidtTypeProjector n k.val) := by
  unfold IsKrausFamily
  simp only [proj_eq, diagonal_conjTranspose, diagonal_mul_diagonal]
  rw [← diagonal_one]
  ext x y
  rw [Matrix.sum_apply]
  simp only [diagonal_apply]
  split_ifs with hxy
  · subst hxy
    rw [Finset.sum_eq_single ⟨downCount x, Nat.lt_succ_of_le (down_le x)⟩]
    · simp
    · intro b _ hb
      have : downCount x ≠ b.val := fun h => hb (Fin.ext h.symm)
      simp [this]
    · simp
  · simp

lemma weight_pos_le {n k : ℕ} {p : ℝ} (h : 0 < schmidtOutcomeWeight n p k) : k ≤ n := by
  by_contra hk
  push Not at hk
  simp [schmidtOutcomeWeight, Nat.choose_eq_zero_of_lt hk] at h

lemma normalized_branch (n k : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hw : 0 < schmidtOutcomeWeight n p k) :
    ((Real.sqrt (schmidtOutcomeWeight n p k))⁻¹ : ℂ) •
      act (Matrix.kronecker (schmidtTypeProjector n k) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
        (schmidtBlock n p) = typeState n k := by
  have hkn := weight_pos_le hw
  have hC : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
  -- amp is a nonnegative real number
  set q : ℝ := p ^ k * (1 - p) ^ (n - k)
  have hq : 0 < q := by
    have : schmidtOutcomeWeight n p k = n.choose k * q := by
      simp only [schmidtOutcomeWeight, q]; ring
    rw [this] at hw
    exact pos_of_mul_pos_right hw hC.le
  have hamp : amp n k p = (Real.sqrt q : ℂ) := by
    simp only [amp, q]
    have h0 : Real.sqrt q = Real.sqrt p ^ k * Real.sqrt (1 - p) ^ (n - k) := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
      have e1 := Real.sq_sqrt hp
      have e2 := Real.sq_sqrt (show 0 ≤ 1 - p by linarith)
      rw [show q = (Real.sqrt p ^ 2) ^ k * (Real.sqrt (1 - p) ^ 2) ^ (n - k) by rw [e1, e2]]
      ring
    rw [h0]; push_cast; ring
  have hw' : schmidtOutcomeWeight n p k = n.choose k * q := by
    simp only [schmidtOutcomeWeight, q]; ring
  ext z
  simp only [PiLp.smul_apply, smul_eq_mul, branch1_apply, typeState, PiLp.toLp_apply]
  split_ifs with h
  · rw [hamp, hw', Real.sqrt_mul hC.le]
    have h1 : (Real.sqrt q : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hq).ne'
    have h2 : (Real.sqrt (n.choose k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hC).ne'
    push_cast
    field_simp
  · simp

lemma cfc_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (f (d i) : ℂ)) := by
  classical
  let S : Finset ℝ := Finset.univ.image d
  let p : Polynomial ℝ := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (r := f) (Set.injOn_id _) hx
  have hD : IsSelfAdjoint (diagonal (fun i => (d i : ℂ))) := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, diagonal_conjTranspose]
    congr 1; funext i; simp
  have hspec : ∀ x ∈ spectrum ℝ (diagonal (fun i => (d i : ℂ))), x ∈ S := by
    intro x hx
    rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage, spectrum_diagonal] at hx
    obtain ⟨i, hi⟩ := hx
    have : d i = x := by simpa using hi
    simp [S, ← this]
  rw [cfc_congr (g := fun x => p.eval x) (fun x hx => (hp x (hspec x hx)).symm),
    cfc_polynomial p _ hD]
  have : Polynomial.aeval (diagonal (fun i => (d i : ℂ))) p =
      diagonal (Polynomial.aeval (fun i => (d i : ℂ)) p) :=
    (Polynomial.aeval_algHom_apply (diagonalAlgHom ℝ) (fun i => (d i : ℂ)) p)
  rw [this, Polynomial.aeval_pi_apply]
  congr 1; funext i
  have h := Polynomial.aeval_algebraMap_apply ℂ (d i) p
  simp only [Complex.coe_algebraMap] at h
  rw [h, Polynomial.coe_aeval_eq_eval, hp _ (by simp [S] : d i ∈ S)]

lemma sum_by_down {n : ℕ} (g : ℕ → ℝ) :
    ∑ x : Fin n → Bool, g (downCount x) = ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) * g k := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := downCount) (t := Finset.range (n+1))
    (fun x _ => Finset.mem_range.2 (Nat.lt_succ_of_le (down_le x)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2]),
    Finset.sum_const, card_down, nsmul_eq_mul]

lemma norm_block (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : ‖schmidtBlock n p‖ = 1 := by
  have h2 : ‖schmidtBlock n p‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp_rw [block_apply]
    rw [Fintype.sum_prod_type]
    have : ∀ x : Fin n → Bool, ∑ y : Fin n → Bool,
        ‖(if (x, y).1 = (x, y).2 then amp n (downCount (x, y).1) p else 0)‖ ^ 2 =
          p ^ downCount x * (1 - p) ^ (n - downCount x) := by
      intro x
      rw [Finset.sum_eq_single x]
      · simp [normSq_amp _ _ p hp hp1]
      · intro y _ hy; simp [Ne.symm hy]
      · simp
    simp_rw [this]
    rw [sum_by_down (fun k => p ^ k * (1 - p) ^ (n - k))]
    have := (add_pow p (1 - p) n).symm
    rw [show p + (1 - p) = 1 by ring, one_pow] at this
    refine Eq.trans ?_ this
    exact Finset.sum_congr rfl fun k _ => by ring
  have h0 := norm_nonneg (schmidtBlock n p)
  nlinarith [h2]

lemma norm_branch2 (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (k l : ℕ) :
    ‖act (Matrix.kronecker (schmidtTypeProjector n k) (schmidtTypeProjector n l))
        (schmidtBlock n p)‖ ^ 2 = if k = l then schmidtOutcomeWeight n p k else 0 := by
  split_ifs with hkl
  · subst hkl
    rw [← norm_branch1 n k p hp hp1]
    congr 2
    ext z
    rw [branch_apply, branch1_apply]
    obtain ⟨a, b⟩ := z
    by_cases h : a = b
    · subst h; simp
    · simp [h]
  · rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [branch_apply]
    obtain ⟨a, b⟩ := z
    by_cases h : a = b
    · subst h
      by_cases hk : downCount a = k
      · have : ¬ downCount a = l := fun h => hkl (hk.symm.trans h)
        simp [this]
      · simp [hk]
    · simp [h]

lemma typeState_apply (n k : ℕ) (z : (Fin n → Bool) × (Fin n → Bool)) :
    typeState n k z = if z.1 = z.2 ∧ downCount z.1 = k then
      ((Real.sqrt (n.choose k : ℝ))⁻¹ : ℂ) else 0 := rfl

lemma norm_typeState (n k : ℕ) (hk : k ≤ n) : ‖typeState n k‖ = 1 := by
  have hC : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  have h2 : ‖typeState n k‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp_rw [typeState_apply]
    have : ∀ z : (Fin n → Bool) × (Fin n → Bool),
        ‖(if z.1 = z.2 ∧ downCount z.1 = k then ((Real.sqrt (n.choose k : ℝ))⁻¹ : ℂ) else 0)‖ ^ 2 =
          if z.1 = z.2 ∧ downCount z.1 = k then ((n.choose k : ℝ))⁻¹ else 0 := by
      intro z
      split_ifs
      · rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
          inv_pow, Real.sq_sqrt hC.le]
      · simp
    simp_rw [this]
    rw [sum_diag_type k (fun _ => ((n.choose k : ℝ))⁻¹), sum_type_const]
    field_simp
  have h0 := norm_nonneg (typeState n k)
  nlinarith [h2]

lemma traceLeft_typeState (n k : ℕ) (hk : k ≤ n) :
    traceLeft (pureDensity (typeState n k)) =
      ((n.choose k : ℂ)⁻¹) • schmidtTypeProjector n k := by
  have hC : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  ext b b'
  simp only [traceLeft, pureDensity, Matrix.of_apply, typeState_apply, Matrix.smul_apply,
    proj_eq, diagonal_apply, smul_eq_mul]
  rw [Finset.sum_eq_single b]
  · by_cases hbb : b = b'
    · subst hbb
      by_cases hk' : downCount b = k
      · simp only [hk', and_self, if_true, map_inv₀, Complex.conj_ofReal]
        rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hC.le]
        simp
      · simp [hk']
    · simp [hbb]
  · intro a _ hab; simp [hab]
  · simp

lemma vn_typeState (n k : ℕ) (hk : k ≤ n) :
    vnEntropy (traceLeft (pureDensity (typeState n k))) = Real.logb 2 (n.choose k : ℝ) := by
  have hC : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  rw [traceLeft_typeState n k hk, proj_eq, ← diagonal_smul]
  have : ((n.choose k : ℂ)⁻¹ • fun x : Fin n → Bool => if downCount x = k then (1 : ℂ) else 0) =
      fun x => ((if downCount x = k then ((n.choose k : ℝ))⁻¹ else 0 : ℝ) : ℂ) := by
    funext x; simp only [Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp
  rw [this, vnEntropy, cfc_diag, trace_diagonal]
  have : ∀ x : Fin n → Bool,
      (((fun t : ℝ => t * Real.logb 2 t) (if downCount x = k then ((n.choose k : ℝ))⁻¹ else 0) : ℝ) : ℂ) =
        ((if downCount x = k then ((n.choose k : ℝ))⁻¹ * Real.logb 2 ((n.choose k : ℝ))⁻¹ else 0 : ℝ) : ℂ) := by
    intro x; split_ifs <;> simp
  simp_rw [this]
  rw [← Complex.ofReal_sum, Complex.ofReal_re, sum_type_const, Real.logb_inv]
  field_simp

end X4P42L

-- ===== SCLim =====

noncomputable section
open Complex Filter Topology intervalIntegral MeasureTheory

namespace X4SC

lemma int_exp (m : ℤ) :
    ∫ θ in (0:ℝ)..2 * Real.pi, Complex.exp (m * I * θ) = if m = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  split_ifs with h
  · subst h; simp
  · have hc : (m : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast h) I_ne_zero
    rw [integral_exp_mul_complex hc]
    have : Complex.exp (m * I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [show (m : ℂ) * I * ((2 * Real.pi : ℝ) : ℂ) = m * (2 * Real.pi * I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I m
    rw [this]; simp

lemma parseval (N : ℕ) (b : ℕ → ℝ) :
    ∫ θ in (0:ℝ)..2 * Real.pi, ‖∑ k ∈ Finset.range N, (b k : ℂ) * Complex.exp (k * I * θ)‖ ^ 2 =
      2 * Real.pi * ∑ k ∈ Finset.range N, b k ^ 2 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have h : ∀ θ : ℝ, ((‖∑ k ∈ Finset.range N, (b k : ℂ) * Complex.exp (k * I * θ)‖ ^ 2 : ℝ) : ℂ) =
      ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
        ((b k * b l : ℝ) : ℂ) * Complex.exp ((((k : ℤ) - (l : ℤ) : ℤ) : ℂ) * I * θ) := by
    intro θ
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    have : (b k : ℂ) * Complex.exp (k * I * θ) * ((b l : ℂ) * Complex.exp ((starRingEnd ℂ) (l * I * θ)))
        = ((b k * b l : ℝ) : ℂ) * (Complex.exp (k * I * θ) * Complex.exp ((starRingEnd ℂ) (l * I * θ))) := by
      push_cast; ring
    rw [this, ← Complex.exp_add]
    congr 2
    simp only [map_mul, Complex.conj_natCast, Complex.conj_I, Complex.conj_ofReal]
    push_cast; ring
  simp_rw [h]
  rw [intervalIntegral.integral_finset_sum]
  · have e : ∀ k ∈ Finset.range N, ∫ θ in (0:ℝ)..2 * Real.pi, ∑ l ∈ Finset.range N,
        ((b k * b l : ℝ) : ℂ) * Complex.exp ((((k : ℤ) - (l : ℤ) : ℤ) : ℂ) * I * θ) =
        ((2 * Real.pi * b k ^ 2 : ℝ) : ℂ) := by
      intro k hk
      rw [intervalIntegral.integral_finset_sum
        (fun l _ => (by fun_prop : Continuous _).intervalIntegrable _ _)]
      simp_rw [intervalIntegral.integral_const_mul, int_exp]
      rw [Finset.sum_eq_single k]
      · simp; ring
      · intro l _ hl
        have : ((k : ℤ) - (l : ℤ)) ≠ 0 := by omega
        simp [this]
      · intro h; exact absurd hk h
    rw [Finset.sum_congr rfl e]
    push_cast
    rw [Finset.mul_sum]
  · intro k _
    exact (by fun_prop : Continuous _).intervalIntegrable _ _

lemma base_normSq (p θ : ℝ) :
    Complex.normSq ((1 - p : ℝ) + p * Complex.exp (θ * I)) =
      1 - 2 * p * (1 - p) * (1 - Real.cos θ) := by
  rw [Complex.normSq_apply]
  simp only [add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  linear_combination (p ^ 2) * Real.sin_sq_add_cos_sq θ

lemma base_nonneg (p θ : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    0 ≤ 1 - 2 * p * (1 - p) * (1 - Real.cos θ) := by
  have hpq : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
  have : p * (1 - p) * (1 - Real.cos θ) ≤ 1 / 4 * 2 :=
    mul_le_mul hpq (by linarith [Real.neg_one_le_cos θ]) (by linarith [Real.cos_le_one θ])
      (by norm_num)
  linarith

lemma binom_sq_tendsto (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N + 1),
      ((N.choose k : ℝ) * p ^ k * (1 - p) ^ (N - k)) ^ 2) atTop (𝓝 0) := by
  set F : ℕ → ℝ → ℝ := fun N θ =>
    Complex.normSq ((1 - p : ℝ) + p * Complex.exp (θ * I)) ^ N
  have hF : ∀ N, ∫ θ in (0:ℝ)..2 * Real.pi, F N θ = 2 * Real.pi * ∑ k ∈ Finset.range (N + 1),
      ((N.choose k : ℝ) * p ^ k * (1 - p) ^ (N - k)) ^ 2 := by
    intro N
    rw [← parseval]
    congr 1; ext θ
    simp only [F]
    rw [← map_pow, Complex.normSq_eq_norm_sq, add_comm, add_pow]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow, ← Complex.exp_nat_mul]
    push_cast
    rw [show (k : ℂ) * (θ * I) = k * I * θ by ring]; ring
  have hlim : Tendsto (fun N => ∫ θ in (0:ℝ)..2 * Real.pi, F N θ) atTop (𝓝 0) := by
    have := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (a := 0) (b := 2 * Real.pi) (l := atTop) (F := F) (f := fun _ => (0 : ℝ)) (fun _ => 1)
      (Eventually.of_forall fun N => (by fun_prop : Continuous (F N)).aestronglyMeasurable)
      (Eventually.of_forall fun N => Eventually.of_forall fun θ _ => by
        simp only [F, base_normSq, Real.norm_eq_abs]
        have h1 := base_nonneg p θ hp hp1
        have h2 : 1 - 2 * p * (1 - p) * (1 - Real.cos θ) ≤ 1 := by
          nlinarith [Real.cos_le_one θ, mul_pos hp (sub_pos.2 hp1)]
        rw [abs_of_nonneg (pow_nonneg h1 _)]
        exact pow_le_one₀ h1 h2)
      intervalIntegrable_const
      (by
        have hne : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 2 * Real.pi := by
          rw [ae_iff]; simp
        filter_upwards [hne] with θ hθ hmem
        rw [Set.uIoc_of_le (by positivity)] at hmem
        obtain ⟨h0, h2⟩ := hmem
        have hcos : Real.cos θ < 1 := by
          refine lt_of_le_of_ne (Real.cos_le_one θ) fun h => ?_
          rw [Real.cos_eq_one_iff_of_lt_of_lt (by linarith) (lt_of_le_of_ne h2 hθ)] at h
          linarith
        simp only [F, base_normSq]
        apply tendsto_pow_atTop_nhds_zero_of_lt_one
        · exact base_nonneg p θ hp hp1
        · nlinarith [mul_pos hp (sub_pos.2 hp1)])
    simpa using this
  have : Tendsto (fun N : ℕ => (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi, F N θ) atTop (𝓝 0) := by
    simpa using hlim.const_mul (2 * Real.pi)⁻¹
  refine this.congr fun N => ?_
  rw [hF, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

end X4SC

-- ===== SC =====

noncomputable section

namespace X4SC

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P42 X4P42L
open scoped BigOperators Matrix ComplexConjugate InnerProductSpace
open Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

lemma prod_real {n : ℕ} (a b : ℝ) (x : Fin n → Bool) :
    ∏ i, (if x i then a else b) = a ^ downCount x * b ^ (n - downCount x) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  congr 2
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => x i = true)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  unfold downCount
  simp only [Bool.not_eq_true] at h ⊢
  omega

lemma ket_neg {n : ℕ} (p : ℝ) (x z : Fin n → Bool) :
    sourceKet p (fun i => !(x i)) z = (-1) ^ downCount z * sourceKet p x z := by
  have h := prod_amp (-1 : ℂ) 1 z
  rw [one_pow, mul_one] at h
  simp only [sourceKet, PiLp.toLp_apply]
  rw [← h, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h1 : z i <;> by_cases h2 : x i <;> simp [h1, h2]

lemma ket_norm_sq {n : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (x z : Fin n → Bool) :
    ‖sourceKet p x z‖ ^ 2 = p ^ downCount z * (1 - p) ^ (n - downCount z) := by
  have h1 : ‖sourceKet p x z‖ = ∏ i, (if z i then Real.sqrt p else Real.sqrt (1 - p)) := by
    simp only [sourceKet, PiLp.toLp_apply, norm_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    cases h1 : z i <;> cases h2 : x i <;> simp [abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [h1, prod_real, mul_pow, ← pow_mul, ← pow_mul, mul_comm _ 2, mul_comm (n - _) 2, pow_mul,
    pow_mul, Real.sq_sqrt hp, Real.sq_sqrt (by linarith)]

lemma sum_down {n : ℕ} (f : ℕ → ℝ) :
    ∑ z : Fin n → Bool, f (downCount z) = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * f k :=
  sum_by_down f

lemma ket_norm {n : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (x : Fin n → Bool) :
    ‖sourceKet p x‖ = 1 := by
  have : ‖sourceKet p x‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp_rw [ket_norm_sq p hp hp1]
    rw [sum_down (fun k => p ^ k * (1 - p) ^ (n - k))]
    calc _ = (p + (1 - p)) ^ n := by
          rw [add_pow]; exact Finset.sum_congr rfl fun k _ => by ring
      _ = 1 := by rw [show p + (1 - p) = 1 by ring, one_pow]
  have h0 := norm_nonneg (sourceKet p x)
  nlinarith

lemma ket_overlap {n : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (x : Fin n → Bool) :
    ‖⟪sourceKet p x, sourceKet p (fun i => !(x i))⟫_ℂ‖ = |1 - 2 * p| ^ n := by
  have e : ⟪sourceKet p x, sourceKet p (fun i => !(x i))⟫_ℂ =
      ((∑ z : Fin n → Bool, (-1 : ℝ) ^ downCount z * ‖sourceKet p x z‖ ^ 2 : ℝ) : ℂ) := by
    rw [PiLp.inner_apply]
    push_cast
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [ket_neg, RCLike.inner_apply, ← Complex.conj_mul']
    simp only [starRingEnd_apply]; ring
  rw [e]
  simp_rw [ket_norm_sq p hp hp1]
  rw [sum_down (fun k => (-1 : ℝ) ^ k * (p ^ k * (1 - p) ^ (n - k)))]
  have := add_pow (-p) (1 - p) n
  rw [show -p + (1 - p) = 1 - 2 * p by ring] at this
  rw [show ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * ((-1) ^ k * (p ^ k * (1 - p) ^ (n - k)))
      = (1 - 2 * p) ^ n by
    rw [this]; refine Finset.sum_congr rfl fun k _ => ?_; rw [neg_pow]; ring]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_pow]

/-! Generic: pure-sum fidelity and the pair bound. -/

section gen
variable {ι : Type*} [Fintype ι]

lemma tr_pp (v w : EuclideanSpace ℂ ι) :
    (pureDensity v * pureDensity w).trace = ((‖⟪v, w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  have : ∑ a, v a * conj (w a) = conj ⟪v, w⟫_ℂ := by
    rw [PiLp.inner_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [RCLike.inner_apply]; simp [mul_comm]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_conj, ← this, ← Complex.mul_conj, map_sum]
  simp only [map_mul, Complex.conj_conj, Finset.sum_mul_sum, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, pureDensity, Matrix.of_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma fid_sum {J : Type*} [Fintype J] (ψ : EuclideanSpace ℂ ι) (w : J → EuclideanSpace ℂ ι) :
    Papers.Independent.Dependency50.P48.pureFidelity ψ (∑ j, pureDensity (w j)) = ∑ j, ‖⟪ψ, w j⟫_ℂ‖ ^ 2 := by
  simp only [Papers.Independent.Dependency50.P48.pureFidelity, effectProb, Matrix.mul_sum, Matrix.trace_sum, tr_pp,
    Complex.re_sum, Complex.ofReal_re]

lemma conj_pure {κ : Type*} [Fintype κ] (A : Matrix κ ι ℂ) (v : EuclideanSpace ℂ ι) :
    A * pureDensity v * Aᴴ = pureDensity (WithLp.toLp 2 (A *ᵥ (WithLp.ofLp v))) := by
  ext p q
  simp only [pureDensity, Matrix.mul_apply, Matrix.of_apply, conjTranspose_apply,
    PiLp.toLp_apply, mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    RCLike.star_def]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

omit [Fintype ι] in
lemma norm_sq_dot {τ : Type*} [Fintype τ] (v : EuclideanSpace ℂ τ) :
    ((‖v‖ ^ 2 : ℝ) : ℂ) = star (WithLp.ofLp v) ⬝ᵥ WithLp.ofLp v := by
  rw [EuclideanSpace.norm_sq_eq]; push_cast
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.conj_mul']

lemma kraus_norm {κ : Type*} [Fintype κ] [DecidableEq ι] {m : ℕ} (K : Fin m → Matrix κ ι ℂ)
    (hK : IsKrausFamily K) (u : EuclideanSpace ℂ ι) :
    ∑ l, ‖(WithLp.toLp 2 (K l *ᵥ WithLp.ofLp u) : EuclideanSpace ℂ κ)‖ ^ 2 = ‖u‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  simp_rw [norm_sq_dot]
  simp only [WithLp.ofLp_toLp, star_mulVec, dotProduct_mulVec, vecMul_vecMul]
  rw [← sum_dotProduct, ← vecMul_sum]
  unfold IsKrausFamily at hK
  rw [hK, vecMul_one]

lemma pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (ψ φ w : E)
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    ‖⟪ψ, w⟫_ℂ‖ ^ 2 + ‖⟪φ, w⟫_ℂ‖ ^ 2 ≤ (1 + ‖⟪ψ, φ⟫_ℂ‖) * ‖w‖ ^ 2 := by
  set a := ⟪ψ, w⟫_ℂ
  set b := ⟪φ, w⟫_ℂ
  set c := ⟪ψ, φ⟫_ℂ
  set S := ‖a‖ ^ 2 + ‖b‖ ^ 2
  set v := a • ψ + b • φ
  have hvw : ⟪v, w⟫_ℂ = (S : ℂ) := by
    simp only [v, inner_add_left, inner_smul_left, S, a, b]
    push_cast
    rw [← Complex.conj_mul', ← Complex.conj_mul']
  have hS : S ≤ ‖v‖ * ‖w‖ := by
    have := norm_inner_le_norm (𝕜 := ℂ) v w
    rw [hvw, Complex.norm_real, Real.norm_eq_abs] at this
    exact (le_abs_self S).trans this
  have hab : (⟪a • ψ, b • φ⟫_ℂ).re ≤ ‖a‖ * ‖b‖ * ‖c‖ := by
    refine (Complex.re_le_norm _).trans (le_of_eq ?_)
    rw [inner_smul_left, inner_smul_right, norm_mul, norm_mul, Complex.norm_conj]; ring
  have hv : ‖v‖ ^ 2 ≤ S * (1 + ‖c‖) := by
    have e := norm_add_sq (𝕜 := ℂ) (a • ψ) (b • φ)
    rw [norm_smul, norm_smul, hψ, hφ] at e
    have h2 : 2 * (‖a‖ * ‖b‖) ≤ S := by nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
    have hc := norm_nonneg c
    simp only [v]; rw [e]
    have hre : RCLike.re ⟪a • ψ, b • φ⟫_ℂ = (⟪a • ψ, b • φ⟫_ℂ).re := rfl
    rw [hre, mul_one, mul_one]
    nlinarith [mul_le_mul_of_nonneg_right h2 hc]
  have hS0 : 0 ≤ S := by positivity
  rcases hS0.lt_or_eq with hpos | hzero
  · have : S * S ≤ S * ((1 + ‖c‖) * ‖w‖ ^ 2) := by
      calc S * S ≤ (‖v‖ * ‖w‖) ^ 2 := by nlinarith
        _ = ‖v‖ ^ 2 * ‖w‖ ^ 2 := by ring
        _ ≤ S * (1 + ‖c‖) * ‖w‖ ^ 2 := by gcongr
        _ = _ := by ring
    exact le_of_mul_le_mul_left this hpos
  · rw [← hzero]; positivity

end gen

/-! Encoders as sums of pure densities. -/

def uvec {n : ℕ} (k : Fin (n + 1)) (ψ : EuclideanSpace ℂ (Fin n → Bool)) :
    EuclideanSpace ℂ (Fin (n + 1) × (Fin n → Bool)) :=
  WithLp.toLp 2 fun w => if w.1 = k ∧ downCount w.2 = k.val then ψ w.2 else 0

def pvec {n : ℕ} (k : ℕ) (ψ : EuclideanSpace ℂ (Fin n → Bool)) :
    EuclideanSpace ℂ (Fin n → Bool) :=
  WithLp.toLp 2 fun z => if downCount z = k then ψ z else 0

lemma flag_eq {n : ℕ} (ψ : EuclideanSpace ℂ (Fin n → Bool)) :
    flaggedEncoder n (pureDensity ψ) = ∑ k, pureDensity (uvec k ψ) := by
  ext ⟨j, a⟩ ⟨j', b⟩
  simp only [flaggedEncoder, proj_eq, diagonal_mul, mul_diagonal, pureDensity, of_apply,
    Matrix.sum_apply, uvec, PiLp.toLp_apply]
  by_cases h : j = j'
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single j]
    · by_cases h1 : downCount a = j.val <;> by_cases h2 : downCount b = j.val <;>
        simp [h1, h2]
    · intro k _ hk; simp [Ne.symm hk]
    · simp
  · rw [if_neg h]; symm
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : j = k
    · subst hk
      have : j' ≠ j := Ne.symm h
      simp [this]
    · simp [hk]

lemma bare_eq {n : ℕ} (ψ : EuclideanSpace ℂ (Fin n → Bool)) :
    bareEncoder n (pureDensity ψ) = ∑ k : Fin (n + 1), pureDensity (pvec k.val ψ) := by
  simp only [bareEncoder]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hP : (schmidtTypeProjector n k.val)ᴴ = schmidtTypeProjector n k.val := by
    rw [proj_eq, diagonal_conjTranspose]
    congr 1; funext z; by_cases h : downCount z = k.val <;> simp [h]
  conv_lhs => rw [← hP]
  rw [hP]
  nth_rewrite 2 [← hP]
  rw [conj_pure]
  congr 1
  ext z
  simp [pvec, proj_eq, mulVec_diagonal]

lemma uvec_norm {n : ℕ} (ψ : EuclideanSpace ℂ (Fin n → Bool)) :
    ∑ k, ‖uvec k ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, uvec, PiLp.toLp_apply]
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have : ∀ j : Fin (n + 1), ∑ k : Fin (n + 1), ∑ z : Fin n → Bool,
      ‖(if (j, z).1 = k ∧ downCount (j, z).2 = k.val then ψ z else 0)‖ ^ 2 =
      ∑ z : Fin n → Bool, if downCount z = j.val then ‖ψ z‖ ^ 2 else 0 := by
    intro j
    rw [Finset.sum_eq_single j]
    · refine Finset.sum_congr rfl fun z _ => ?_
      by_cases h : downCount z = j.val <;> simp [h]
    · intro k _ hk; refine Finset.sum_eq_zero fun z _ => ?_; simp [Ne.symm hk]
    · simp
  rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_eq_single ⟨downCount z, Nat.lt_succ_of_le (down_le z)⟩]
  · simp
  · intro k _ hk; rw [if_neg]; intro h; exact hk (Fin.ext h.symm)
  · simp

/-! The three parts. -/

lemma part1 {n : ℕ} (p : ℝ) (x : Fin n → Bool) :
    flaggedEncoder n (pureDensity (sourceKet p x)) =
      flaggedEncoder n (pureDensity (sourceKet p (fun i => !(x i)))) := by
  ext u v
  simp only [flaggedEncoder, proj_eq, diagonal_mul, mul_diagonal, pureDensity, of_apply]
  split_ifs with h h1 h2 <;> try simp
  rw [ket_neg, ket_neg]
  simp only [map_mul, map_pow, map_neg, map_one]
  rw [show downCount u.2 = downCount v.2 by rw [← h1] at *; simp_all]
  ring_nf
  rw [Even.neg_one_pow ⟨downCount v.2, by ring⟩, mul_one]

lemma pair_fid {n : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ)
    (K : Fin m → Matrix (Fin n → Bool) (Fin (n + 1) × (Fin n → Bool)) ℂ) (hK : IsKrausFamily K)
    (x : Fin n → Bool) :
    Papers.Independent.Dependency50.P48.pureFidelity (sourceKet p x)
        (krausApply K (flaggedEncoder n (pureDensity (sourceKet p x)))) +
      Papers.Independent.Dependency50.P48.pureFidelity (sourceKet p (fun i => !(x i)))
        (krausApply K (flaggedEncoder n (pureDensity (sourceKet p x)))) ≤
      1 + |1 - 2 * p| ^ n := by
  set ψ := sourceKet p x
  set φ := sourceKet p (fun i => !(x i))
  have hσ : krausApply K (flaggedEncoder n (pureDensity ψ)) =
      ∑ lk : Fin m × Fin (n + 1),
        pureDensity (WithLp.toLp 2 (K lk.1 *ᵥ WithLp.ofLp (uvec lk.2 ψ))) := by
    rw [flag_eq, krausApply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun k _ => conj_pure _ _
  rw [hσ, fid_sum, fid_sum, ← Finset.sum_add_distrib]
  have hψ := ket_norm p hp hp1 x
  have hφ := ket_norm p hp hp1 (fun i => !(x i))
  have hc := ket_overlap p hp hp1 x
  calc _ ≤ ∑ lk : Fin m × Fin (n + 1), (1 + |1 - 2 * p| ^ n) *
        ‖(WithLp.toLp 2 (K lk.1 *ᵥ WithLp.ofLp (uvec lk.2 ψ)) : EuclideanSpace ℂ _)‖ ^ 2 := by
        refine Finset.sum_le_sum fun lk _ => ?_
        rw [← hc]; exact pair _ _ _ hψ hφ
    _ = (1 + |1 - 2 * p| ^ n) * ∑ k, ∑ l,
        ‖(WithLp.toLp 2 (K l *ᵥ WithLp.ofLp (uvec k ψ)) : EuclideanSpace ℂ _)‖ ^ 2 := by
        rw [← Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_comm]
    _ = 1 + |1 - 2 * p| ^ n := by
        simp_rw [kraus_norm K hK]
        rw [uvec_norm, hψ]; ring

lemma part2 {n : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (D : Superop (Fin (n + 1) × (Fin n → Bool)) (Fin n → Bool)) (hD : IsChannel D) :
    codingFidelity n p D ≤ (1 + |1 - 2 * p| ^ n) / 2 := by
  obtain ⟨m, K, hK, hDK⟩ := hD
  set F : (Fin n → Bool) → ℝ := fun x => Papers.Independent.Dependency50.P48.pureFidelity
    (sourceKet p x) (D (flaggedEncoder n (pureDensity (sourceKet p x))))
  have hneg : ∑ x : Fin n → Bool, F (fun i => !(x i)) = ∑ x, F x := by
    have hinv : Function.Involutive (fun (x : Fin n → Bool) (i : Fin n) => !(x i)) :=
      fun x => by funext i; simp
    exact Fintype.sum_bijective _ hinv.bijective _ _ fun x => rfl
  have hpair : ∀ x : Fin n → Bool, F x + F (fun i => !(x i)) ≤ 1 + |1 - 2 * p| ^ n := by
    intro x
    simp only [F]
    rw [← part1 p x, hDK]
    exact pair_fid p hp hp1 m K hK x
  have hsum : 2 * ∑ x, F x ≤ 2 ^ n * (1 + |1 - 2 * p| ^ n) := by
    calc 2 * ∑ x, F x = ∑ x, (F x + F (fun i => !(x i))) := by
          rw [Finset.sum_add_distrib, hneg]; ring
      _ ≤ ∑ _x : Fin n → Bool, (1 + |1 - 2 * p| ^ n) := Finset.sum_le_sum fun x _ => hpair x
      _ = 2 ^ n * (1 + |1 - 2 * p| ^ n) := by simp; ring
  simp only [codingFidelity]
  change ((2 : ℝ) ^ n)⁻¹ * ∑ x, F x ≤ _
  rw [inv_mul_le_iff₀ (by positivity)]
  linarith

lemma bare_fid {n : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (x : Fin n → Bool) :
    Papers.Independent.Dependency50.P48.pureFidelity (sourceKet p x)
        (bareEncoder n (pureDensity (sourceKet p x))) =
      ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)) ^ 2 := by
  rw [bare_eq, fid_sum, ← Fin.sum_univ_eq_sum_range
    (fun k => ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)) ^ 2)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : ⟪sourceKet p x, pvec k.val (sourceKet p x)⟫_ℂ =
      ((∑ z : Fin n → Bool, if downCount z = k.val then ‖sourceKet p x z‖ ^ 2 else 0 : ℝ) : ℂ) := by
    rw [PiLp.inner_apply]; push_cast
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [pvec, PiLp.toLp_apply, RCLike.inner_apply]
    split_ifs
    · rw [Complex.mul_conj', Complex.ofReal_pow]
    · simp
  rw [e]
  simp_rw [ket_norm_sq p hp hp1]
  have : ∑ z : Fin n → Bool, (if downCount z = k.val then
      p ^ downCount z * (1 - p) ^ (n - downCount z) else 0) =
      ∑ z : Fin n → Bool, (if downCount z = k.val then p ^ k.val * (1 - p) ^ (n - k.val) else 0) :=
    Finset.sum_congr rfl fun z _ => by split_ifs with h <;> simp [h]
  rw [this, sum_type_const, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

lemma part3 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (fun n : ℕ => ((2 : ℝ) ^ (n + 3))⁻¹ * ∑ x : Fin (n + 3) → Bool,
      Papers.Independent.Dependency50.P48.pureFidelity (sourceKet p x)
        (bareEncoder (n + 3) (pureDensity (sourceKet p x)))) Filter.atTop (nhds (0 : ℝ)) := by
  have h := (binom_sq_tendsto p hp hp1).comp (Filter.tendsto_add_atTop_nat 3)
  refine h.congr fun n => ?_
  simp only [Function.comp, bare_fid p hp.le hp1.le, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

end X4SC

-- ===== SCSol =====

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact accepted objects, without introducing same-name aliases.

open Information100.P21 (Op Vec FiniteLOCC)

open Dependency50.P42 (dimensionedPower singlets)

open Dependency50.P48 (pureFidelity)

open Gap48.P32 (pairOfState)

open Next46.P39 (rectAct)

/-- PDF pp.13--14: complement erasure even with the classical outcome,
bare-fidelity limit zero, and a uniform bound for every decoder channel.
The decoder receives the entire classical-quantum output, never the unknown x. -/
theorem _root_.solution (p : ℝ) (hp : 0<p) (hp1 : p<1) :
    (∀ (n : ℕ), 2<n → ∀ x : Fin n → Bool,
      flaggedEncoder n (pureDensity (sourceKet p x))=
        flaggedEncoder n (pureDensity (sourceKet p (fun i => !(x i))))) ∧
    (∀ (n : ℕ) (D : Superop (Fin (n+1) × (Fin n → Bool)) (Fin n → Bool)),
      2<n → IsChannel D → codingFidelity n p D≤(1+|1-2*p|^n)/2) ∧
    Filter.Tendsto (fun n : ℕ => ((2 : ℝ)^(n+3))⁻¹*∑ x : Fin (n+3) → Bool,
      pureFidelity (sourceKet p x) (bareEncoder (n+3) (pureDensity (sourceKet p x))))
      Filter.atTop (nhds (0 : ℝ)) :=
  ⟨fun _ _ x => X4SC.part1 p x, fun _ D _ hD => X4SC.part2 p hp.le hp1.le D hD,
    X4SC.part3 p hp hp1⟩

end QAlgorithms.Papers.Independent.Support50.P42

end
