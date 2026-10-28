-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P46.five_party_xor_monogamy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:20:04.273764+00:00
-- url     : https://prove2.me/submissions/08e599a8-f7cd-4a15-9036-5d2d0e383d0d

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P46

-- ===== P46A =====

open scoped BigOperators ComplexConjugate
open Matrix Polynomial QAlgorithms

namespace X4P46

lemma cfc_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (f (d i) : ℂ)) := by
  classical
  let S : Finset ℝ := Finset.univ.image d
  let p : ℝ[X] := Lagrange.interpolate S id f
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
  have : aeval (diagonal (fun i => (d i : ℂ))) p = diagonal (aeval (fun i => (d i : ℂ)) p) :=
    (aeval_algHom_apply (diagonalAlgHom ℝ) (fun i => (d i : ℂ)) p)
  rw [this, aeval_pi_apply]
  congr 1; funext i
  have h := aeval_algebraMap_apply ℂ (d i) p
  simp only [Complex.coe_algebraMap] at h
  rw [h, coe_aeval_eq_eval, hp _ (by simp [S] : d i ∈ S)]

lemma vn_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) :
    vnEntropy (diagonal (fun i => (d i : ℂ))) = -∑ i, d i * Real.logb 2 (d i) := by
  rw [vnEntropy, cfc_diag, trace_diagonal]
  simp

end X4P46

-- ===== P46B =====

open scoped BigOperators ComplexConjugate
open Matrix QAlgorithms

namespace X4P46

/-- Double sums of a pure density over a relation that, on the support, is the diagonal. -/
lemma core {X T : Type*} [Fintype X] [Fintype T] (e : T → X) (he : Function.Injective e)
    (c : ℂ) (ψ : X → ℂ) (h0 : ∀ x ∉ Set.range e, ψ x = 0) (h1 : ∀ t, ψ (e t) = c)
    (P : X → X → Prop) {_ : ∀ x y, Decidable (P x y)} (Q : T → Prop) [DecidablePred Q]
    (hP : ∀ t t', P (e t) (e t') ↔ t = t' ∧ Q t) :
    ∑ x, ∑ y, (if P x y then ψ x * conj (ψ y) else 0) =
      ∑ t, if Q t then c * conj c else 0 := by
  classical
  symm
  refine Fintype.sum_of_injective e he _ _ ?_ ?_
  · intro x hx; simp [h0 x hx]
  intro t
  symm
  rw [← Fintype.sum_of_injective e he (fun t' => if P (e t) (e t') then ψ (e t) * conj (ψ (e t'))
    else 0) _ (fun y hy => by simp [h0 y hy]) (fun _ => rfl)]
  rw [Finset.sum_eq_single t]
  · have := hP t t; by_cases hq : Q t <;> simp_all
  · intro t' _ ht'; have := hP t t'; simp_all [Ne.symm ht']
  · simp

lemma marg {X T K F : Type*} [Fintype X] [Fintype T] [Fintype K] [DecidableEq K]
    (e : T → X) (he : Function.Injective e)
    (ψ : EuclideanSpace ℂ X) (h0 : ∀ x ∉ Set.range e, ψ x = 0) (h1 : ∀ t, ψ (e t) = (1/2 : ℂ))
    (keep : X → K) (forget : X → F) (hf : ∀ t t', forget (e t) = forget (e t') → t = t') :
    QAlgorithms.Papers.Independent.Gap48.P20.redistributionMarginal (pureDensity ψ) keep forget =
      diagonal (fun a => ((∑ t, if keep (e t) = a then (1/4 : ℝ) else 0 : ℝ) : ℂ)) := by
  classical
  ext a b
  unfold QAlgorithms.Papers.Independent.Gap48.P20.redistributionMarginal pureDensity
  simp only [Matrix.of_apply]
  refine (core e he (1/2) _ h0 h1 _ (fun t => keep (e t) = a ∧ keep (e t) = b) ?_).trans ?_
  rotate_left
  · by_cases hab : a = b
    · subst hab; simp only [diagonal_apply_eq, and_self]; push_cast
      refine Finset.sum_congr rfl fun t _ => ?_
      split_ifs <;> simp [Complex.ext_iff]; norm_num
    · rw [diagonal_apply_ne _ hab]
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [if_neg]; rintro ⟨h1, h2⟩; exact hab (h1.symm.trans h2)
  · intro t t'
    constructor
    · rintro ⟨h1, h2, h3⟩; obtain rfl := hf t t' h3; exact ⟨rfl, h1, h2⟩
    · rintro ⟨rfl, h1, h2⟩; exact ⟨h1, h2, rfl⟩

lemma vn_diag' {ι : Type*} [Fintype ι] {i1 i2 : DecidableEq ι} (d : ι → ℝ) :
    @vnEntropy ι _ i1 (@diagonal _ _ i2 _ (fun i => (d i : ℂ))) = -∑ i, d i * Real.logb 2 (d i) := by
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  exact vn_diag d

lemma ent_eval {T K : Type*} [Fintype T] [Fintype K] [DecidableEq K] (g : T → K) (q : ℝ) :
    -∑ a, (∑ t, if g t = a then q else 0) * Real.logb 2 (∑ t, if g t = a then q else 0) =
      -∑ t, q * Real.logb 2 (q * (Finset.univ.filter (fun t' => g t' = g t)).card) := by
  congr 1
  have hw : ∀ a, (∑ t, if g t = a then q else 0) = q * (Finset.univ.filter (fun t' => g t' = a)).card := by
    intro a; rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  simp_rw [hw]
  have : ∀ a, q * ((Finset.univ.filter (fun t' => g t' = a)).card : ℝ) *
      Real.logb 2 (q * (Finset.univ.filter (fun t' => g t' = a)).card) =
      ∑ t, if g t = a then q * Real.logb 2 (q * (Finset.univ.filter (fun t' => g t' = g t)).card)
        else 0 := by
    intro a
    rw [← Finset.sum_filter, Finset.sum_congr rfl (g := fun _ => q * Real.logb 2
      (q * (Finset.univ.filter (fun t' => g t' = a)).card))]
    · rw [Finset.sum_const, nsmul_eq_mul]; ring
    · intro t ht; rw [(Finset.mem_filter.mp ht).2]
  simp_rw [this]
  rw [Finset.sum_comm]
  simp

end X4P46

-- ===== P46C =====

open scoped BigOperators ComplexConjugate
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Support50.P46

namespace X4P46

def emb (t : Bool × Bool) : Qubits 6 := ![t.1, t.1, t.2, t.2, xor t.1 t.2, xor t.1 t.2]

lemma emb_inj : Function.Injective emb := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h0 := congrFun h 0; have h2 := congrFun h 2
  simp [emb] at h0 h2; simp [h0, h2]

lemma h0 : ∀ x ∉ Set.range emb, copiedSixVector x = 0 := by
  intro x hx
  simp only [copiedSixVector]
  rw [if_neg]
  rintro ⟨h01, h23, h45, h4⟩
  apply hx
  refine ⟨(x 0, x 2), funext fun i => ?_⟩
  fin_cases i <;> simp [emb, ← h01, ← h23, ← h45, h4]

lemma h1 : ∀ t, copiedSixVector (emb t) = (1/2 : ℂ) := by
  rintro ⟨a, b⟩
  simp [copiedSixVector, emb]

lemma ent (s : Finset (Fin 6))
    (hf : ∀ t t', (fun i : {i // i ∉ s} => emb t i.val) = (fun i => emb t' i.val) → t = t') :
    Papers.Independent.Gap48.P20.subsystemEntropy copiedSixDensity
      (fun x => fun i : {i // i ∈ s} => x i.val) (fun x => fun i : {i // i ∉ s} => x i.val) =
      -∑ t, (1/4 : ℝ) * Real.logb 2 ((1/4 : ℝ) * (Finset.univ.filter
        (fun t' => (fun i : {i // i ∈ s} => emb t' i.val) = (fun i => emb t i.val))).card) := by
  unfold Papers.Independent.Gap48.P20.subsystemEntropy copiedSixDensity
  rw [marg emb emb_inj _ h0 h1 _ _ hf, vn_diag', ent_eval]

lemma val (cnt : Bool × Bool → ℕ) (n : ℕ) (hc : ∀ t, cnt t = n) :
    -∑ t, (1/4 : ℝ) * Real.logb 2 ((1/4 : ℝ) * (cnt t : ℝ)) = -Real.logb 2 (n / 4) := by
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool]
  simp; ring_nf

lemma lb4 : Real.logb 2 ((1 : ℕ) / 4 : ℝ) = -2 := by
  rw [show ((1 : ℕ) / 4 : ℝ) = 2 ^ (-2 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]

lemma lb2 : Real.logb 2 ((2 : ℕ) / 4 : ℝ) = -1 := by
  rw [show ((2 : ℕ) / 4 : ℝ) = 2 ^ (-1 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]

lemma i3 : tripartiteInformation copiedSixDensity {0} {1} {2, 4} = 1 := by
  simp only [tripartiteInformation]
  rw [ent {0} (by decide), ent {1} (by decide), ent {2, 4} (by decide), ent ({0} ∪ {1}) (by decide),
    ent ({1} ∪ {2, 4}) (by decide), ent ({0} ∪ {2, 4}) (by decide),
    ent ({0} ∪ {1} ∪ {2, 4}) (by decide)]
  rw [val _ 2 (by decide), val _ 2 (by decide), val _ 1 (by decide), val _ 2 (by decide),
    val _ 1 (by decide), val _ 1 (by decide), val _ 1 (by decide)]
  rw [lb4, lb2]; norm_num

end X4P46

-- ===== P46E =====

open scoped BigOperators ComplexConjugate
open Matrix Polynomial QAlgorithms

namespace X4P46

theorem tr_aeval {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (p : ℝ[X]) :
    (aeval M p).trace = ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℂ) * (M ^ i).trace := by
  rw [aeval_eq_sum_range, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul]
  simp [Complex.real_smul]

theorem tr_cfc_eq {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M1 : Matrix ι ι ℂ) (M2 : Matrix κ κ ℂ) (h1 : M1.IsHermitian) (h2 : M2.IsHermitian)
    (h : ∀ k : ℕ, 1 ≤ k → (M1 ^ k).trace = (M2 ^ k).trace) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f M1).trace = (cfc f M2).trace := by
  classical
  let S : Finset ℝ := Finset.univ.image h1.eigenvalues ∪ Finset.univ.image h2.eigenvalues ∪ {0}
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (r := f) (Set.injOn_id _) hx
  have e1 : cfc f M1 = cfc (fun x => p.eval x) M1 := by
    apply cfc_congr
    intro x hx
    rw [h1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (by simp [S])).symm
  have e2 : cfc f M2 = cfc (fun x => p.eval x) M2 := by
    apply cfc_congr
    intro x hx
    rw [h2.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (by simp [S])).symm
  have h0 : p.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, hp 0 (by simp [S]), hf]
  rw [e1, e2, cfc_polynomial p M1, cfc_polynomial p M2, tr_aeval, tr_aeval]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [h0]
  · rw [h i hi]

theorem pow_mul' {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (W : Matrix κ ι ℂ) (k : ℕ) :
    (V * W) ^ (k + 1) = V * (W * V) ^ k * W := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

theorem tr_pow_swap {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (W : Matrix κ ι ℂ) (k : ℕ) (hk : 1 ≤ k) :
    ((V * W) ^ k).trace = ((W * V) ^ k).trace := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [pow_mul', Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ]

theorem ent_swap {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) :
    vnEntropy (V * Vᴴ) = vnEntropy ((Vᴴ * V)ᵀ) := by
  unfold vnEntropy
  rw [tr_cfc_eq (V * Vᴴ) ((Vᴴ * V)ᵀ) (isHermitian_mul_conjTranspose_self V)
    (isHermitian_conjTranspose_mul_self V).transpose _ _ (by simp)]
  intro k hk
  rw [← Matrix.transpose_pow, Matrix.trace_transpose, tr_pow_swap _ _ k hk]

lemma L {X K F : Type*} [Fintype X] [Fintype K] [Fintype F] (keep : X → K) (forget : X → F)
    (e : X ≃ K × F) (he : ∀ x, e x = (keep x, forget x)) (ψ : X → ℂ) (a b : K)
    {_ : ∀ x y, Decidable (keep x = a ∧ keep y = b ∧ forget x = forget y)} :
    ∑ x, ∑ y, (if keep x = a ∧ keep y = b ∧ forget x = forget y then ψ x * conj (ψ y) else 0) =
      ∑ f, ψ (e.symm (a, f)) * conj (ψ (e.symm (b, f))) := by
  classical
  have hk : ∀ p, keep (e.symm p) = p.1 := fun p => by
    have := he (e.symm p); rw [Equiv.apply_symm_apply] at this; exact (congrArg Prod.fst this).symm
  have hf : ∀ p, forget (e.symm p) = p.2 := fun p => by
    have := he (e.symm p); rw [Equiv.apply_symm_apply] at this; exact (congrArg Prod.snd this).symm
  rw [← Equiv.sum_comp e.symm]
  simp_rw [← Equiv.sum_comp e.symm (fun y => if keep (e.symm _) = a ∧ keep y = b ∧ _ then _ else _)]
  simp only [hk, hf]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun f _ => ?_
    rw [Finset.sum_eq_single b, Finset.sum_eq_single f]
    · simp
    · intro f' _ hf'; rw [if_neg]; exact fun h => hf' h.2.2.symm
    · simp
    · intro b' _ hb'; exact Finset.sum_eq_zero fun f' _ => by rw [if_neg]; exact fun h => hb' h.2.1
    · simp
  · intro a' _ ha'; exact Finset.sum_eq_zero fun f _ => Finset.sum_eq_zero fun b' _ =>
      Finset.sum_eq_zero fun f' _ => by rw [if_neg]; exact fun h => ha' h.1
  · simp

open QAlgorithms.Papers.Independent.Gap48.P20 in
lemma swap {X K F : Type*} [Fintype X] [Fintype K] [Fintype F]
    (keep : X → K) (forget : X → F) (hb : Function.Bijective (fun x => (keep x, forget x)))
    (ψ : EuclideanSpace ℂ X) :
    subsystemEntropy (pureDensity ψ) keep forget = subsystemEntropy (pureDensity ψ) forget keep := by
  classical
  let e := Equiv.ofBijective _ hb
  let M : Matrix K F ℂ := Matrix.of fun k f => ψ (e.symm (k, f))
  have A : redistributionMarginal (pureDensity ψ) keep forget = M * Mᴴ := by
    ext a b
    unfold redistributionMarginal pureDensity
    simp only [Matrix.of_apply]
    refine (L keep forget e (fun _ => rfl) _ a b).trans ?_
    simp [Matrix.mul_apply, M, Matrix.conjTranspose_apply]
  have B : redistributionMarginal (pureDensity ψ) forget keep = (Mᴴ * M)ᵀ := by
    ext a b
    unfold redistributionMarginal pureDensity
    simp only [Matrix.of_apply]
    refine (L forget keep (e.trans (Equiv.prodComm _ _)) (fun _ => rfl) _ a b).trans ?_
    simp [Matrix.mul_apply, M, Matrix.conjTranspose_apply, mul_comm]
  unfold subsystemEntropy
  rw [A, B]
  convert ent_swap M

end X4P46

-- ===== P46F =====

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Support50.P46

namespace X4P46

def emb5 (t : Bool × Bool) : Qubits 5 := ![t.1, t.1, t.2, t.2, xor t.1 t.2]

lemma emb5_inj : Function.Injective emb5 := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h0 := congrFun h 0; have h2 := congrFun h 2
  simp [emb5] at h0 h2; simp [h0, h2]

lemma g0 : ∀ x ∉ Set.range emb5, copiedFiveVector x = 0 := by
  intro x hx
  simp only [copiedFiveVector]
  rw [if_neg]
  rintro ⟨h01, h23, h4⟩
  apply hx
  refine ⟨(x 0, x 2), funext fun i => ?_⟩
  fin_cases i <;> simp [emb5, ← h01, ← h23, h4]

lemma g1 : ∀ t, copiedFiveVector (emb5 t) = (1/2 : ℂ) := by
  rintro ⟨a, b⟩
  simp [copiedFiveVector, emb5]

lemma ent5 {K F : Type*} [Fintype K] [Fintype F] [DecidableEq K] (keep : Qubits 5 → K)
    (forget : Qubits 5 → F) (hf : ∀ t t', forget (emb5 t) = forget (emb5 t') → t = t') :
    Papers.Independent.Gap48.P20.subsystemEntropy copiedFiveDensity keep forget =
      -∑ t, (1/4 : ℝ) * Real.logb 2 ((1/4 : ℝ) * (Finset.univ.filter
        (fun t' => keep (emb5 t') = keep (emb5 t))).card) := by
  unfold Papers.Independent.Gap48.P20.subsystemEntropy copiedFiveDensity
  rw [marg emb5 emb5_inj _ g0 g1 _ _ hf, vn_diag', ent_eval]

def r5 (s : Finset (Fin 5)) : ℕ :=
  min 2 ((if 0 ∈ s ∨ 1 ∈ s then 1 else 0) + (if 2 ∈ s ∨ 3 ∈ s then 1 else 0) + (if 4 ∈ s then 1 else 0))
def rr5 (s : Finset (Fin 5)) : ℕ := min (r5 s) (r5 (Finset.univ \ s))

lemma rr5_le (s : Finset (Fin 5)) : rr5 s ≤ 2 := (min_le_left _ _).trans (min_le_left _ _)

lemma hcnt1 : ∀ s : Finset (Fin 5),
    (∀ t t', (fun i : {i // i ∉ s} => emb5 t i.val) = (fun i => emb5 t' i.val) → t = t') →
    ∀ t, (Finset.univ.filter (fun t' => (fun i : {i // i ∈ s} => emb5 t' i.val) =
      (fun i => emb5 t i.val))).card = 2 ^ (2 - rr5 s) := by decide

lemma hinj : ∀ s : Finset (Fin 5),
    ¬ (∀ t t', (fun i : {i // i ∉ s} => emb5 t i.val) = (fun i => emb5 t' i.val) → t = t') →
    ∀ t t', (fun i : {i // i ∈ s} => emb5 t i.val) = (fun i => emb5 t' i.val) → t = t' := by decide

lemma hcnt2 : ∀ s : Finset (Fin 5),
    ¬ (∀ t t', (fun i : {i // i ∉ s} => emb5 t i.val) = (fun i => emb5 t' i.val) → t = t') →
    ∀ t, (Finset.univ.filter (fun t' => (fun i : {i // i ∉ s} => emb5 t' i.val) =
      (fun i => emb5 t i.val))).card = 2 ^ (2 - rr5 s) := by decide

lemma lbk (k : ℕ) (hk : k ≤ 2) : -Real.logb 2 (((2 ^ (2 - k) : ℕ) : ℝ) / 4) = k := by
  interval_cases k
  · norm_num
  · rw [show (((2 ^ (2 - 1) : ℕ) : ℝ) / 4) = 2 ^ (-1 : ℝ) by norm_num,
      Real.logb_rpow (by norm_num) (by norm_num)]; norm_num
  · rw [show (((2 ^ (2 - 2) : ℕ) : ℝ) / 4) = 2 ^ (-2 : ℝ) by norm_num,
      Real.logb_rpow (by norm_num) (by norm_num)]; norm_num

lemma Sval (s : Finset (Fin 5)) :
    Papers.Independent.Gap48.P20.subsystemEntropy copiedFiveDensity
      (fun x => fun i : {i // i ∈ s} => x i.val) (fun x => fun i : {i // i ∉ s} => x i.val) =
      (rr5 s : ℝ) := by
  by_cases hc : ∀ t t', (fun i : {i // i ∉ s} => emb5 t i.val) = (fun i => emb5 t' i.val) → t = t'
  · rw [ent5 _ _ hc, val _ _ (hcnt1 s hc), lbk _ (rr5_le s)]
  · have hd : copiedFiveDensity = pureDensity copiedFiveVector := rfl
    rw [hd, X4P46.swap _ _ (Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) _).bijective, ← hd,
      ent5 _ _ (hinj s hc), val _ _ (hcnt2 s hc), lbk _ (rr5_le s)]

set_option maxRecDepth 100000 in
theorem tN : ∀ a b c : Finset (Fin 5), Disjoint a b → Disjoint a c → Disjoint b c →
    rr5 a + rr5 b + rr5 c + rr5 (a ∪ b ∪ c) ≤ rr5 (a ∪ b) + rr5 (b ∪ c) + rr5 (a ∪ c) := by
  decide +kernel

theorem tN' (inst : DecidableEq (Fin 5)) (a b c : Finset (Fin 5)) (h1 : Disjoint a b)
    (h2 : Disjoint a c) (h3 : Disjoint b c) :
    rr5 a + rr5 b + rr5 c + rr5 (@Union.union _ (@Finset.instUnion _ inst)
      (@Union.union _ (@Finset.instUnion _ inst) a b) c) ≤
      rr5 (@Union.union _ (@Finset.instUnion _ inst) a b) +
      rr5 (@Union.union _ (@Finset.instUnion _ inst) b c) +
      rr5 (@Union.union _ (@Finset.instUnion _ inst) a c) := by
  obtain rfl : inst = instDecidableEqFin 5 := Subsingleton.elim _ _
  exact tN a b c h1 h2 h3

end X4P46

-- ===== P46G =====

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Support50.P46

namespace X4P46

lemma state5 : IsState copiedFiveVector := by
  rw [IsState, EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  rw [← Fintype.sum_of_injective emb5 emb5_inj (fun t => ‖copiedFiveVector (emb5 t)‖ ^ 2) _
    (fun x hx => by simp [g0 x hx]) (fun _ => rfl)]
  simp only [g1]; simp; norm_num

lemma dens5 : IsDensityMatrix copiedFiveDensity := by
  refine ⟨?_, ?_⟩
  · have : copiedFiveDensity = vecMulVec (fun x => copiedFiveVector x) (star fun x => copiedFiveVector x) := by
      ext x y; simp [copiedFiveDensity, pureDensity, vecMulVec]
    rw [this]; exact posSemidef_vecMulVec_self_star _
  · rw [Matrix.trace]
    simp only [copiedFiveDensity, pureDensity, Matrix.diag, Matrix.of_apply]
    rw [← Fintype.sum_of_injective emb5 emb5_inj (fun t => copiedFiveVector (emb5 t) * conj (copiedFiveVector (emb5 t))) _
      (fun x hx => by simp [g0 x hx]) (fun _ => rfl)]
    simp only [g1, map_div₀, map_one, map_ofNat]; norm_num

lemma cnt3' : ∀ u v : Qubits 3, (Finset.univ.filter (fun t : Bool × Bool =>
    (∀ j : Fin 3, emb5 t (![0, 2, 4] j) = u j) ∧ (∀ j : Fin 3, emb5 t (![0, 2, 4] j) = v j))).card =
    if u = v ∧ u 2 = xor (u 0) (u 1) then 1 else 0 := by decide

lemma three5 : threeMarginal copiedFiveDensity ![0, 2, 4] = xorClassical := by
  ext u v
  unfold threeMarginal copiedFiveDensity pureDensity
  simp only [Matrix.of_apply]
  refine (core emb5 emb5_inj (1/2) _ g0 g1 _ (fun t => (∀ j : Fin 3, emb5 t (![0, 2, 4] j) = u j) ∧
    (∀ j : Fin 3, emb5 t (![0, 2, 4] j) = v j)) ?_).trans ?_
  · rintro ⟨a, b⟩ ⟨c, d⟩
    constructor
    · rintro ⟨hu, hv, hr⟩
      have e1 := hr 1 (by decide); have e3 := hr 3 (by decide)
      simp [emb5] at e1 e3; subst e1; subst e3; exact ⟨rfl, hu, hv⟩
    · rintro ⟨h, hu, hv⟩; cases h; exact ⟨hu, hv, fun _ _ => rfl⟩
  · rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, cnt3']
    unfold xorClassical
    split_ifs <;> simp_all [map_ofNat]; norm_num

lemma mono5 (a b c : Finset (Fin 5)) (h1 : Disjoint a b) (h2 : Disjoint a c) (h3 : Disjoint b c) :
    tripartiteInformation copiedFiveDensity a b c ≤ 0 := by
  simp only [tripartiteInformation, Sval]
  have h := tN a b c h1 h2 h3
  have h' := (Nat.cast_le (α := ℝ)).mpr h
  push_cast at h'
  linarith

end X4P46

-- ===== P46Sol2 =====

noncomputable section

open scoped BigOperators ComplexConjugate

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P46

open QAlgorithms.Papers.Independent.Gap48.P20 (subsystemEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

theorem solution :
    IsState copiedFiveVector ∧ IsDensityMatrix copiedFiveDensity ∧
    threeMarginal copiedFiveDensity ![0, 2, 4] = xorClassical ∧
    ∀ a b c : Finset (Fin 5),
      Disjoint a b → Disjoint a c → Disjoint b c →
      tripartiteInformation copiedFiveDensity a b c ≤ 0 := by
  refine ⟨X4P46.state5, X4P46.dens5, ?_, ?_⟩
  · convert X4P46.three5
  · intro a b c h1 h2 h3
    convert X4P46.mono5 a b c h1 h2 h3

end
