-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P42.schmidt_projection
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T23:40:22.264186+00:00
-- url     : https://prove2.me/submissions/79d76107-3228-407b-bdc8-d93a7fcd7f28

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

-- ===== P42SP =====

noncomputable section

open scoped BigOperators Matrix ComplexConjugate
open MeasureTheory ProbabilityTheory
open QAlgorithms QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Support50.P42
open Information100.P21 (Op Vec FiniteLOCC)

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (n : ℕ) (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    ‖schmidtBlock n p‖=1 ∧
    IsKrausFamily (fun k : Fin (n+1) => schmidtTypeProjector n k.val) ∧
    (∀ k l : Fin (n+1),
      ‖act (Matrix.kronecker (schmidtTypeProjector n k.val) (schmidtTypeProjector n l.val))
        (schmidtBlock n p)‖^2=if k=l then schmidtOutcomeWeight n p k.val else 0) ∧
    (∀ k : Fin (n+1), 0<schmidtOutcomeWeight n p k.val →
      ((Real.sqrt (schmidtOutcomeWeight n p k.val))⁻¹ : ℂ) •
        act (Matrix.kronecker (schmidtTypeProjector n k.val) (1 : Op (Fin n → Bool)))
          (schmidtBlock n p)=typeState n k.val ∧
      ‖typeState n k.val‖=1 ∧
      traceLeft (pureDensity (typeState n k.val))=
        ((n.choose k.val : ℂ)⁻¹) • schmidtTypeProjector n k.val ∧
      vnEntropy (traceLeft (pureDensity (typeState n k.val)))=Real.logb 2 (n.choose k.val : ℝ)) := by
  refine ⟨X4P42L.norm_block n p hp hp1, X4P42L.kraus_proj n, fun k l => ?_, fun k hw => ?_⟩
  · rw [X4P42L.norm_branch2 n p hp hp1]
    simp only [Fin.val_inj]
  · have hk := X4P42L.weight_pos_le hw
    exact ⟨X4P42L.normalized_branch n k p hp hp1 hw, X4P42L.norm_typeState n k hk,
      X4P42L.traceLeft_typeState n k hk, X4P42L.vn_typeState n k hk⟩

end

#print axioms solution
