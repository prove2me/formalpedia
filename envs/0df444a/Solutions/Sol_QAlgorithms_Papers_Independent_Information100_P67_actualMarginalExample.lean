-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P67.actualMarginalExample
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T07:43:37.982176+00:00
-- url     : https://prove2.me/submissions/06e2f4ac-d4e1-41f0-90a6-c6baf6593354

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory Filter

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P67

namespace G55AM

lemma sum_fin1 {X : Type*} [Fintype X] (g : (Fin 1 → X) → ℂ) : ∑ b, g b = ∑ x, g (fun _ => x) :=
  Fintype.sum_equiv (Equiv.funUnique (Fin 1) X) g (fun x => g (fun _ => x))
    (fun b => by congr 1; funext i; fin_cases i; rfl)

lemma fun1_eq {X : Type*} (b c : Fin 1 → X) : b = c ↔ b 0 = c 0 := by
  constructor
  · rintro rfl; rfl
  · intro h; funext i; fin_cases i; exact h

/-- decoded value of the flagged code -/
def dec (M : ℕ) (b : Fin M × Bool) : ℕ := if b.2 then (b.1.val + 1) % M else b.1.val

lemma rho_apply (M : ℕ) (p : ℝ) (m : Fin M) (x y : (Fin 1 → Fin M × Bool) × (Fin 1 → Bool)) :
    (dilationPower (flaggedIdentityDilation M p) 1 * (flaggedIdentityCode M).messages m *
      (dilationPower (flaggedIdentityDilation M p) 1)ᴴ) x y =
      flaggedIdentityDilation M p (x.1 0, x.2 0) m * conj (flaggedIdentityDilation M p (y.1 0, y.2 0) m) := by
  have hmsg : (flaggedIdentityCode M).messages m =
      Matrix.of (fun a b : Fin 1 → Fin M => if a 0 = m ∧ b 0 = m then (1 : ℂ) else 0) := rfl
  rw [hmsg]
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply, dilationPower, Fin.prod_univ_one]
  simp only [sum_fin1 (X := Fin M)]
  rw [Finset.sum_eq_single m]
  · rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  · intro b _ hb
    simp [hb]
  · simp

lemma meas_apply (M : ℕ) (j : Fin M) (c b : Fin 1 → Fin M × Bool) :
    (flaggedIdentityCode M).measurement j c b = if c = b ∧ dec M (c 0) = j.val then 1 else 0 := rfl

lemma meas_apply' (M : ℕ) (j : Fin (flaggedIdentityCode M).M) (c b : Fin 1 → Fin M × Bool) :
    (flaggedIdentityCode M).measurement j c b = if c = b ∧ dec M (c 0) = j.val then 1 else 0 := rfl

lemma U_apply (M : ℕ) (p : ℝ) (b : Fin M × Bool) (e : Bool) (m : Fin M) :
    flaggedIdentityDilation M p (b, e) m =
      if b.1 = m ∧ b.2 = e then (if e then (Real.sqrt (1 - p) : ℂ) else (Real.sqrt p : ℂ)) else 0 := rfl

lemma mo (M : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : Fin M) (je kf : Fin M × (Fin 1 → Bool)) :
    messageOutput (flaggedIdentityDilation M p) (flaggedIdentityCode M) m je kf =
      if je = kf ∧ dec M (m, je.2 0) = je.1.val then
        (((if je.2 0 then 1 - p else p : ℝ)) : ℂ) else 0 := by
  unfold messageOutput
  simp only [rho_apply, meas_apply]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [sum_fin1]
  simp only [U_apply]
  rw [Finset.sum_eq_single (m, je.2 0)]
  · obtain ⟨j, e⟩ := je
    obtain ⟨k, f⟩ := kf
    simp only [Prod.mk.injEq, fun1_eq e f, U_apply]
    have h1 : ((Real.sqrt p : ℂ) * conj (Real.sqrt p : ℂ)) = (p : ℂ) := by
      rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hp0]
    have h2 : ((Real.sqrt (1 - p) : ℂ) * conj (Real.sqrt (1 - p) : ℂ)) = ((1 - p : ℝ) : ℂ) := by
      rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (sub_nonneg.mpr hp1)]
    by_cases hjk : j = k
    · subst hjk
      rcases Bool.eq_false_or_eq_true (e 0) with h | h <;>
        rcases Bool.eq_false_or_eq_true (f 0) with h' | h' <;> simp [h, h', h1, h2] <;>
        split_ifs with H1 H2 <;> first
          | (exfalso; exact H1 rfl)
          | simp_all [← Complex.ofReal_mul, Real.mul_self_sqrt hp0, Real.mul_self_sqrt (sub_nonneg.mpr hp1)]
    · simp only [hjk]; simp; intro h; exact absurd h hjk
  · rintro ⟨k, g⟩ _ hne
    by_cases h1 : k = m
    · subst h1
      have : g ≠ je.2 0 := fun h => hne (by rw [h])
      simp [this, U_apply]
    · simp [h1, U_apply]
  · simp


lemma jo_pt (M : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (a b : Fin M × Fin M × (Fin 1 → Bool)) :
    jointOutput (flaggedIdentityDilation M p) (flaggedIdentityCode M) a b = flaggedExampleOutput M p a b := by
  show (if a.1 = b.1 then ((M : ℕ) : ℂ)⁻¹ *
    messageOutput (flaggedIdentityDilation M p) (flaggedIdentityCode M) a.1 a.2 b.2 else 0) = _
  rw [mo M p hp0 hp1]
  unfold flaggedExampleOutput
  obtain ⟨m, j, e⟩ := a
  obtain ⟨m', k, f⟩ := b
  simp only [Prod.mk.injEq]
  by_cases hm : m = m'
  · subst hm
    by_cases hjk : j = k
    · subst hjk
      by_cases hef : e = f
      · subst hef
        simp only [and_self, if_true, true_and]
        rcases Bool.eq_false_or_eq_true (e 0) with h | h
        · simp only [h, dec, if_true]
          by_cases h2 : (m.val + 1) % M = j.val
          · simp [h2, eq_comm]
          · simp [h2, Ne.symm h2]
        · simp only [h, dec]
          by_cases h2 : m.val = j.val
          · simp [h2, Fin.ext_iff]
          · simp [h2, Fin.ext_iff]
      · simp [hef]
    · simp [hjk]
  · simp [hm]

lemma cfc_diag {X : Type*} [Fintype X] [DecidableEq X] (d : X → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) = Matrix.diagonal (fun i => (f (d i) : ℂ)) := by
  set A := Matrix.diagonal (fun i => (d i : ℂ)) with hA
  have hsa : IsSelfAdjoint A := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, hA, Matrix.diagonal_conjTranspose]
    congr 1; funext i; simp
  set S : Finset ℝ := Finset.univ.image d
  let p : Polynomial ℝ := Lagrange.interpolate S id f
  have hp : ∀ i, p.eval (d i) = f (d i) := by
    intro i
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) (r := f) (i := d i)
      (Set.injOn_id _) (Finset.mem_image_of_mem d (Finset.mem_univ i))
    exact this
  have hspec : ∀ x ∈ spectrum ℝ A, ∃ i, d i = x := by
    intro x hx
    rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage, hA, spectrum_diagonal,
      Set.mem_range] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, by rw [Complex.coe_algebraMap] at hi; exact_mod_cast hi⟩
  have h1 : cfc f A = cfc p.eval A := by
    apply cfc_congr
    intro x hx
    obtain ⟨i, rfl⟩ := hspec x hx
    exact (hp i).symm
  rw [h1, cfc_polynomial p A]
  rw [hA, show Matrix.diagonal (fun i => (d i : ℂ)) =
    Matrix.diagonalAlgHom ℝ (fun i => (d i : ℂ)) from rfl, Polynomial.aeval_algHom_apply]
  rw [show Matrix.diagonal (fun i => (f (d i) : ℂ)) =
    Matrix.diagonalAlgHom ℝ (fun i => (f (d i) : ℂ)) from rfl]
  congr 1
  funext i
  rw [Polynomial.aeval_pi_apply₂]
  rw [show ((d i : ℝ) : ℂ) = algebraMap ℝ ℂ (d i) from rfl, Polynomial.aeval_algebraMap_apply,
    Polynomial.aeval_def, Algebra.algebraMap_self, ← Polynomial.eval, hp]
  rfl

lemma fid_diag {I : Type*} [Fintype I] [DecidableEq I] (r : I → ℝ) (X : Matrix I I ℂ) (D : I → ℝ)
    (hX : ∀ i j, (Real.sqrt (r i) : ℂ) * X i j * Real.sqrt (r j) = if i = j then (D i : ℂ) else 0) :
    rootFidelity (Matrix.diagonal fun i => (r i : ℂ)) X = ∑ i, Real.sqrt (D i) := by
  unfold rootFidelity
  rw [cfc_diag]
  have : Matrix.diagonal (fun i => ((Real.sqrt (r i) : ℝ) : ℂ)) * X *
      Matrix.diagonal (fun i => ((Real.sqrt (r i) : ℝ) : ℂ)) = Matrix.diagonal (fun i => (D i : ℂ)) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hX, Matrix.diagonal_apply]
  rw [this, cfc_diag, Matrix.trace_diagonal, Complex.re_sum]
  simp

lemma sum_fin1' {X β : Type*} [Fintype X] [AddCommMonoid β] (g : (Fin 1 → X) → β) :
    ∑ b, g b = ∑ x, g (fun _ => x) :=
  Fintype.sum_equiv (Equiv.funUnique (Fin 1) X) g (fun x => g (fun _ => x))
    (fun b => by congr 1; funext i; fin_cases i; rfl)


def rr (M : ℕ) (p : ℝ) (a : Fin M × Fin M × (Fin 1 → Bool)) : ℝ :=
  (M : ℝ)⁻¹ * ((if a.1 = a.2.1 ∧ a.2.2 0 = false then p else 0) +
    (if a.2.1.val = (a.1.val + 1) % M ∧ a.2.2 0 = true then 1 - p else 0))

lemma feo_diag (M : ℕ) (p : ℝ) :
    flaggedExampleOutput M p = Matrix.diagonal (fun a => (rr M p a : ℂ)) := by
  ext a b
  unfold flaggedExampleOutput rr
  rw [Matrix.diagonal_apply]
  split_ifs <;> push_cast <;> simp_all

lemma succ_ne (M : ℕ) (hM : 2 ≤ M) (m : Fin M) : (m.val + 1) % M ≠ m.val := by
  have hm := m.2
  by_cases h : m.val + 1 < M
  · rw [Nat.mod_eq_of_lt h]; omega
  · have : m.val + 1 = M := by omega
    rw [this, Nat.mod_self]; omega

lemma fid_ideal (M : ℕ) (hM : 2 ≤ M) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ)
    (hs0' : 0 ≤ (σ (fun _ => false) (fun _ => false)).re)
    (hsim' : σ (fun _ => false) (fun _ => false) = ((σ (fun _ => false) (fun _ => false)).re : ℂ)) :
    squaredFidelity (flaggedExampleOutput M p) (idealJoint M σ) = p * (σ (fun _ => false) (fun _ => false)).re := by
  set s := (σ (fun _ => false) (fun _ => false)).re with hs
  have hs0 : 0 ≤ s := hs0'
  have hsim : (σ (fun _ => false) (fun _ => false)) = (s : ℂ) := hsim'
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  set D : Fin M × Fin M × (Fin 1 → Bool) → ℝ := fun a =>
    if a.1 = a.2.1 ∧ a.2.2 0 = false then p * s / (M : ℝ) ^ 2 else 0 with hD
  have hX : ∀ a b, (Real.sqrt (rr M p a) : ℂ) * idealJoint M σ a b * Real.sqrt (rr M p b) =
      if a = b then (D a : ℂ) else 0 := by
    rintro ⟨m, j, e⟩ ⟨m', k, f⟩
    simp only [idealJoint, rr, hD]
    by_cases hc : m = j ∧ m' = k ∧ m = m'
    · obtain ⟨rfl, rfl, rfl⟩ := hc
      have hsucc : ¬ (m.val = (m.val + 1) % M) := fun h => succ_ne M hM m h.symm
      simp only [true_and, and_self, if_true, hsucc, false_and, if_false, add_zero]
      rcases Bool.eq_false_or_eq_true (e 0) with h | h <;>
        rcases Bool.eq_false_or_eq_true (f 0) with h' | h'
      all_goals first
        | (simp [h, h']; done)
        | (simp only [h, h']; simp; intro hef; rw [hef] at h; rw [h] at h'; exact absurd h' (by decide))
        | (have hef : e = f := (fun1_eq e f).mpr (h.trans h'.symm)
           subst hef
           have he : e = fun _ => false := by funext i; fin_cases i; exact h
           subst he
           simp only [if_true]
           rw [hsim]
           have : (Real.sqrt ((M : ℝ)⁻¹ * p) : ℂ) * (((M : ℂ))⁻¹ * (s : ℂ)) * (Real.sqrt ((M : ℝ)⁻¹ * p) : ℂ) =
               (((M : ℝ)⁻¹ * p) * ((M : ℝ)⁻¹ * s) : ℝ) := by
             rw [mul_comm, ← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
             push_cast; ring
           rw [this]
           congr 1
           field_simp)
    · have hX0 : ¬ (m = j ∧ m' = k ∧ m = m') := hc
      simp only [hX0, if_false, mul_zero, zero_mul, Prod.mk.injEq]
      split_ifs with h1 h2
      · obtain ⟨rfl, rfl, rfl⟩ := h1
        exact absurd ⟨h2.1, h2.1, rfl⟩ hX0
      · rfl
      · rfl
  unfold squaredFidelity
  rw [feo_diag, fid_diag (rr M p) (idealJoint M σ) D hX]
  have hsum : ∑ a, Real.sqrt (D a) = Real.sqrt (p * s) := by
    simp only [hD, Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl fun m _ => (?_ : _ = Real.sqrt (p * s) / M)]
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
    · rw [Finset.sum_eq_single m]
      · rw [sum_fin1']
        simp only [true_and]
        rw [Fintype.sum_bool]
        simp only [Bool.true_eq_false, if_false, if_true, Real.sqrt_zero, zero_add]
        rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hMpos.le]
      · intro j _ hj
        rw [sum_fin1']
        simp [Ne.symm hj]
      · simp
  rw [hsum, Real.sq_sqrt (mul_nonneg hp0 hs0)]

lemma dens_ff (σ : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ) (hσ : IsDensityMatrix σ) (e : Bool) :
    0 ≤ (σ (fun _ => e) (fun _ => e)).re ∧
      σ (fun _ => e) (fun _ => e) = ((σ (fun _ => e) (fun _ => e)).re : ℂ) := by
  have h := Complex.nonneg_iff.mp (hσ.1.diag_nonneg (i := fun _ => e))
  refine ⟨h.1, Complex.ext (by simp) (by simp [← h.2])⟩

lemma dens_sum (σ : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ) (hσ : IsDensityMatrix σ) :
    (σ (fun _ => false) (fun _ => false)).re + (σ (fun _ => true) (fun _ => true)).re = 1 := by
  have h := congrArg Complex.re hσ.2
  rw [Matrix.trace, Complex.re_sum, sum_fin1', Fintype.sum_bool] at h
  simpa [add_comm] using h


lemma env_ff (M : ℕ) (hM : 2 ≤ M) (p : ℝ) :
    traceLeft (traceLeft (flaggedExampleOutput M p)) (fun _ => false) (fun _ => false) = (p : ℂ) := by
  simp only [traceLeft, Matrix.of_apply, flaggedExampleOutput, if_true]
  have hMpos : (M : ℂ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  rw [Finset.sum_congr rfl fun m _ => (?_ : _ = (M : ℂ)⁻¹ * p)]
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  · rw [Finset.sum_eq_single m]
    · simp
    · intro j _ hj; simp; intro h; exact absurd h hj
    · simp

lemma jo' (M : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    jointOutput (flaggedIdentityDilation M p) (flaggedIdentityCode M) = flaggedExampleOutput M p := by
  ext a b; exact jo_pt M p hp0 hp1 a b

lemma dens0 : IsDensityMatrix (Matrix.diagonal (fun e : Fin 1 → Bool => if e 0 = false then (1 : ℂ) else 0)) := by
  refine ⟨?_, ?_⟩
  · apply Matrix.PosSemidef.diagonal
    intro e; simp only [Pi.zero_apply]; split_ifs <;> simp
  · rw [Matrix.trace_diagonal, sum_fin1', Fintype.sum_bool]; simp


lemma fid_sigma (M : ℕ) (hM : 2 ≤ M) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ) (hσ : IsDensityMatrix σ) :
    squaredFidelity (jointOutput (flaggedIdentityDilation M p) (flaggedIdentityCode M)) (idealJoint M σ) =
      p * (σ (fun _ => false) (fun _ => false)).re := by
  rw [jo' M p hp0 hp1]
  exact fid_ideal M hM p hp0 hp1 σ (dens_ff σ hσ false).1 (dens_ff σ hσ false).2

lemma opt (M : ℕ) (hM : 2 ≤ M) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    optimizedFidelity (flaggedIdentityDilation M p) (flaggedIdentityCode M) = p := by
  unfold optimizedFidelity
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨_, dens0, ?_⟩
    have h := fid_sigma M hM p hp0 hp1 _ dens0
    exact (h.trans (by simp)).symm
  · rintro r ⟨σ, hσ, rfl⟩
    have h := fid_sigma M hM p hp0 hp1 σ hσ
    have h1 := dens_sum σ hσ
    have h2 := (dens_ff σ hσ true).1
    calc _ = p * (σ (fun _ => false) (fun _ => false)).re := h
      _ ≤ p := by nlinarith

lemma marg (M : ℕ) (hM : 2 ≤ M) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    marginalFidelity (flaggedIdentityDilation M p) (flaggedIdentityCode M) = p ^ 2 := by
  let F : Matrix (Fin M × Fin M × (Fin 1 → Bool)) (Fin M × Fin M × (Fin 1 → Bool)) ℂ → ℝ :=
    fun X => squaredFidelity X (idealJoint M (traceLeft (traceLeft X)))
  show F (jointOutput (flaggedIdentityDilation M p) (flaggedIdentityCode M)) = _
  rw [jo' M p hp0 hp1]
  show squaredFidelity (flaggedExampleOutput M p)
    (idealJoint M (traceLeft (traceLeft (flaggedExampleOutput M p)))) = _
  rw [fid_ideal M hM p hp0 hp1 _ (by rw [env_ff M hM p]; simpa using hp0) (by rw [env_ff M hM p]; simp)]
  rw [env_ff M hM p]; simp; ring


lemma dec_lt (M : ℕ) (hM : 0 < M) (b : Fin M × Bool) : dec M b < M := by
  unfold dec; split_ifs
  · exact Nat.mod_lt _ hM
  · exact b.1.2

lemma valid (M : ℕ) (hM : 2 ≤ M) : (flaggedIdentityCode M).Valid := by
  have hM0 : 0 < M := by omega
  refine ⟨hM0, ?_, ?_, ?_⟩
  · show ∀ m : Fin M, IsDensityMatrix ((flaggedIdentityCode M).messages m)
    intro m
    have e : (flaggedIdentityCode M).messages m = Matrix.vecMulVec
        (fun a : Fin 1 → Fin M => if a 0 = m then (1 : ℂ) else 0)
        (star (fun a : Fin 1 → Fin M => if a 0 = m then (1 : ℂ) else 0)) := by
      ext a b
      simp only [flaggedIdentityCode, Matrix.vecMulVec_apply, Pi.star_apply]
      by_cases ha : a 0 = m <;> by_cases hb : b 0 = m <;> simp [ha, hb]
    refine ⟨e ▸ Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
    rw [e, Matrix.trace_vecMulVec, dotProduct, sum_fin1']
    simp
  · show ∀ j : Fin M, ((flaggedIdentityCode M).measurement j).PosSemidef
    intro j
    have e : (flaggedIdentityCode M).measurement j =
        Matrix.diagonal (fun c : Fin 1 → Fin M × Bool => if dec M (c 0) = j.val then (1 : ℂ) else 0) := by
      ext c b
      rw [meas_apply, Matrix.diagonal_apply]
      by_cases h : c = b
      · subst h; simp
      · simp [h]
    rw [e]
    apply Matrix.PosSemidef.diagonal
    intro c; simp only [Pi.zero_apply]; split_ifs <;> simp
  · ext c b
    simp only [Matrix.sum_apply, meas_apply', Matrix.one_apply]
    by_cases h : c = b
    · subst h
      simp only [true_and, if_true]
      rw [Finset.sum_eq_single (⟨dec M (c 0), (dec_lt M hM0 (c 0) : dec M (c 0) < (flaggedIdentityCode M).M)⟩ : Fin (flaggedIdentityCode M).M)]
      · simp
      · intro j _ hj
        rw [if_neg]; intro h'; apply hj; ext; exact h'.symm
      · simp
    · simp [h]


def cc (p : ℝ) (e : Bool) : ℂ := if e then (Real.sqrt (1 - p) : ℂ) else (Real.sqrt p : ℂ)

lemma U_apply' (M : ℕ) (p : ℝ) (b : Fin M × Bool) (e : Bool) (m : Fin M) :
    flaggedIdentityDilation M p (b, e) m = if b.1 = m ∧ b.2 = e then cc p e else 0 := rfl

lemma cc_sq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (e : Bool) :
    cc p e * conj (cc p e) = ((if e then 1 - p else p : ℝ) : ℂ) := by
  cases e <;> simp [cc, ← Complex.ofReal_mul, Real.mul_self_sqrt hp0, Real.mul_self_sqrt (sub_nonneg.mpr hp1)]

lemma iso (M : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : IsIsometry (flaggedIdentityDilation M p) := by
  unfold IsIsometry
  ext m m'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, U_apply', Fintype.sum_prod_type, Matrix.one_apply]
  rw [Finset.sum_eq_single m]
  · by_cases hm : m = m'
    · subst hm
      simp only [true_and, if_true, Fintype.sum_bool]
      simp only [if_true, Bool.false_eq_true, if_false, Bool.true_eq_false, star_zero, zero_mul, add_zero, zero_add]
      rw [mul_comm (star (cc p true)), mul_comm (star (cc p false))]
      have h1 := cc_sq p hp0 hp1 true
      have h2 := cc_sq p hp0 hp1 false
      simp only [RCLike.star_def] at *
      rw [h1, h2]; push_cast; simp
    · simp [hm]
  · intro k _ hk; simp [hk]
  · simp

def Kd (M : ℕ) (m : Fin M) : Matrix Bool (Fin M × Bool) ℂ := fun e b => if b.1 = m ∧ b.2 = e then 1 else 0

lemma kd_family (M : ℕ) : IsKrausFamily (Kd M) := by
  unfold IsKrausFamily
  ext b b'
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Kd, Matrix.one_apply, Fintype.sum_bool]
  obtain ⟨k, g⟩ := b
  obtain ⟨k', g'⟩ := b'
  rw [Finset.sum_eq_single k]
  · by_cases hk : k = k' <;> cases g <;> cases g' <;> simp [hk, eq_comm]
  · intro m _ hm; simp [Ne.symm hm]
  · simp


lemma URU (M : ℕ) (p : ℝ) (ρ : Matrix (Fin M) (Fin M) ℂ) (k k' : Fin M) (g e g' e' : Bool) :
    (flaggedIdentityDilation M p * ρ * (flaggedIdentityDilation M p)ᴴ) ((k, g), e) ((k', g'), e') =
      if g = e ∧ g' = e' then cc p e * conj (cc p e') * ρ k k' else 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, U_apply']
  by_cases h1 : g = e <;> by_cases h2 : g' = e' <;>
    simp [h1, h2, RCLike.star_def, apply_ite (starRingEnd ℂ), ite_and, mul_ite, Finset.sum_ite_eq] <;> ring

lemma kd_conj (M : ℕ) (m : Fin M) (R : Matrix (Fin M × Bool) (Fin M × Bool) ℂ) (e e' : Bool) :
    (Kd M m * R * (Kd M m)ᴴ) e e' = R (m, e) (m, e') := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Kd, Fintype.sum_prod_type]
  simp [ite_and, apply_ite (starRingEnd ℂ), Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma degr (M : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsDegradable (flaggedIdentityDilation M p) := by
  refine ⟨iso M p hp0 hp1, krausApply (Kd M), ⟨M, Kd M, kd_family M, fun _ => rfl⟩, fun ρ => ?_⟩
  ext e e'
  have hL : complementaryChannel (flaggedIdentityDilation M p) ρ e e' = ∑ k, ∑ g,
      (flaggedIdentityDilation M p * ρ * (flaggedIdentityDilation M p)ᴴ) ((k, g), e) ((k, g), e') := by
    simp only [complementaryChannel, traceLeft, Matrix.of_apply, Fintype.sum_prod_type]
  have hR : krausApply (Kd M) (receiverChannel (flaggedIdentityDilation M p) ρ) e e' = ∑ k, ∑ f,
      (flaggedIdentityDilation M p * ρ * (flaggedIdentityDilation M p)ᴴ) ((k, e), f) ((k, e'), f) := by
    simp only [krausApply, Matrix.sum_apply, kd_conj, receiverChannel, traceRight, Matrix.of_apply]
  rw [hL, hR]
  simp only [URU]
  refine Finset.sum_congr rfl fun k _ => ?_
  cases e <;> cases e' <;> simp [Fintype.sum_bool]

end G55AM

variable {A B E R S T X C Y G1 G2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype R] [DecidableEq R]

variable [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

variable [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]

variable [Fintype Y] [DecidableEq Y] [Fintype G1] [DecidableEq G1]

variable [Fintype G2] [DecidableEq G2]

open G55AM in
/-- Explicit degradable-channel counterexample (D.6)–(D.9), PDF p.48. -/
theorem solution (M : ℕ) (hM : 2 ≤ M)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    let U := flaggedIdentityDilation M p
    let code := flaggedIdentityCode M
    IsDegradable U ∧ code.Valid ∧ jointOutput U code = flaggedExampleOutput M p ∧
    (∀ sigma : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ, IsDensityMatrix sigma →
      squaredFidelity (jointOutput U code) (idealJoint M sigma) =
        p * (sigma (fun _ => false) (fun _ => false)).re) ∧
    optimizedFidelity U code = p ∧ marginalFidelity U code = p ^ 2 ∧
    marginalFidelity U code < optimizedFidelity U code := by
  intro U code
  refine ⟨degr M p hp0.le hp1.le, valid M hM, jo' M p hp0.le hp1.le,
    fun σ hσ => fid_sigma M hM p hp0.le hp1.le σ hσ, opt M hM p hp0.le hp1.le, marg M hM p hp0.le hp1.le, ?_⟩
  rw [marg M hM p hp0.le hp1.le, opt M hM p hp0.le hp1.le]
  nlinarith
