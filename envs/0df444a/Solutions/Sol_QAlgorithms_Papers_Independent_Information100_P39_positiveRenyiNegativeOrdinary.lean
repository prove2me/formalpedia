-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P39.positiveRenyiNegativeOrdinary
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:23:43.833615+00:00
-- url     : https://prove2.me/submissions/20cf7915-14e4-4154-8ed4-68223f16f67c

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P39

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P39

section F
attribute [local instance] Classical.propDecidable

namespace X6P39F

theorem cases4 (e : PauliLabel 1) : e = 0 ∨ e = labelX ∨ e = labelY ∨ e = labelZ := by
  obtain ⟨a, b⟩ := e
  have ha : a = ![a 0] := by ext i; fin_cases i; rfl
  have hb : b = ![b 0] := by ext i; fin_cases i; rfl
  rw [ha, hb]
  generalize a 0 = x
  generalize b 0 = y
  fin_cases x <;> fin_cases y
  · left; ext i <;> fin_cases i <;> rfl
  · right; right; right; rfl
  · right; left; rfl
  · right; right; left; rfl

theorem sum4 (f : PauliLabel 1 → ℝ) : ∑ x, f x = f 0 + f labelX + f labelY + f labelZ := by
  let e : PauliLabel 1 ≃ ZMod 2 × ZMod 2 :=
    (Equiv.funUnique (Fin 1) (ZMod 2)).prodCongr (Equiv.funUnique (Fin 1) (ZMod 2))
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  change ∑ x : Fin 2, ∑ y : Fin 2, f (e.symm (x, y)) = _
  simp only [Fin.sum_univ_two]
  have h00 : e.symm (0, 0) = 0 := by ext i <;> fin_cases i <;> rfl
  have h10 : e.symm (1, 0) = labelX := by ext i <;> fin_cases i <;> rfl
  have h11 : e.symm (1, 1) = labelY := by ext i <;> fin_cases i <;> rfl
  have h01 : e.symm (0, 1) = labelZ := by ext i <;> fin_cases i <;> rfl
  change f (e.symm (0, 0)) + f (e.symm (0, 1)) + (f (e.symm (1, 0)) + f (e.symm (1, 1))) = _
  rw [h00, h10, h11, h01]; ring

theorem X_ne0 : labelX ≠ 0 := by
  intro h; have := congrArg (fun x : PauliLabel 1 => x.1 0) h; simp [labelX] at this
theorem Y_ne0 : labelY ≠ 0 := by
  intro h; have := congrArg (fun x : PauliLabel 1 => x.1 0) h; simp [labelY] at this
theorem Z_ne0 : labelZ ≠ 0 := by
  intro h; have := congrArg (fun x : PauliLabel 1 => x.2 0) h; simp [labelZ] at this
theorem Y_neX : labelY ≠ labelX := by
  intro h; have := congrArg (fun x : PauliLabel 1 => x.2 0) h; simp [labelX, labelY] at this
theorem Z_neX : labelZ ≠ labelX := by
  intro h; have := congrArg (fun x : PauliLabel 1 => x.1 0) h; simp [labelX, labelZ] at this
theorem Z_neY : labelZ ≠ labelY := by
  intro h; have := congrArg (fun x : PauliLabel 1 => x.1 0) h; simp [labelY, labelZ] at this

theorem pv0 (v : Fin 4 → ℝ) : pauliVector v 0 = v 0 := by simp [pauliVector]
theorem pvX (v : Fin 4 → ℝ) : pauliVector v labelX = v 1 := by
  simp [pauliVector, X_ne0]
theorem pvY (v : Fin 4 → ℝ) : pauliVector v labelY = v 2 := by
  simp [pauliVector, Y_ne0, Y_neX]
theorem pvZ (v : Fin 4 → ℝ) : pauliVector v labelZ = v 3 := by
  simp [pauliVector, Z_ne0, Z_neX, Z_neY]

end X6P39F
end F

section R



namespace X6P39R

open Matrix

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in

lemma two_selfAdjoint (P : Matrix ι ι ℂ) (hPh : Pᴴ = P) (a b : ℝ) :
    IsSelfAdjoint ((a : ℂ) • P + (b : ℂ) • (1 - P)) := by
  show ((a : ℂ) • P + (b : ℂ) • (1 - P))ᴴ = _
  rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_sub,
    conjTranspose_one, hPh]
  simp

lemma spectrum_two (P : Matrix ι ι ℂ) (hP : P * P = P) (a b : ℝ) (r : ℝ)
    (hr : r ∈ spectrum ℝ ((a : ℂ) • P + (b : ℂ) • (1 - P))) : r = a ∨ r = b := by
  by_contra h
  push Not at h
  obtain ⟨ha, hb⟩ := h
  apply (spectrum.mem_iff.1 hr)
  have ha' : ((r : ℂ) - a) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast ha
  have hb' : ((r : ℂ) - b) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hb
  set Y : Matrix ι ι ℂ := ((r : ℂ) - a)⁻¹ • P + ((r : ℂ) - b)⁻¹ • (1 - P)
  have hX : algebraMap ℝ (Matrix ι ι ℂ) r - ((a : ℂ) • P + (b : ℂ) • (1 - P)) =
      ((r : ℂ) - a) • P + ((r : ℂ) - b) • (1 - P) := by
    rw [Algebra.algebraMap_eq_smul_one]
    rw [show (r • (1 : Matrix ι ι ℂ)) = (r : ℂ) • (1 : Matrix ι ι ℂ) by
      rw [← Complex.coe_smul]]
    simp only [sub_smul, smul_sub]
    abel
  rw [hX]
  have hP1 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  have hP2 : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have hP3 : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, one_mul, hP1, sub_zero]
  refine isUnit_iff_exists.2 ⟨Y, ?_, ?_⟩
  · simp only [Y, add_mul, mul_add, smul_mul_smul, hP, hP1, hP2, hP3, smul_zero, add_zero,
      zero_add, mul_inv_cancel₀ ha', mul_inv_cancel₀ hb', one_smul]
    abel
  · simp only [Y, add_mul, mul_add, smul_mul_smul, hP, hP1, hP2, hP3, smul_zero, add_zero,
      zero_add, inv_mul_cancel₀ ha', inv_mul_cancel₀ hb', one_smul]
    abel

lemma cfc_two (P : Matrix ι ι ℂ) (hP : P * P = P) (hPh : Pᴴ = P) (a b : ℝ) (f : ℝ → ℝ) :
    cfc f ((a : ℂ) • P + (b : ℂ) • (1 - P)) = (f a : ℂ) • P + (f b : ℂ) • (1 - P) := by
  have hsa := two_selfAdjoint P hPh a b
  rcases eq_or_ne a b with hab | hab
  · subst hab
    have : (a : ℂ) • P + (a : ℂ) • (1 - P) = algebraMap ℝ (Matrix ι ι ℂ) a := by
      rw [← smul_add, add_sub_cancel, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
    rw [this, cfc_algebraMap, Algebra.algebraMap_eq_smul_one, ← smul_add, add_sub_cancel,
      ← Complex.coe_smul]
  · set α : ℝ := (f a - f b) / (a - b)
    set β : ℝ := (a * f b - b * f a) / (a - b)
    have hab' : a - b ≠ 0 := sub_ne_zero.2 hab
    have hcongr : cfc f ((a : ℂ) • P + (b : ℂ) • (1 - P)) =
        cfc (fun x => α * x + β) ((a : ℂ) • P + (b : ℂ) • (1 - P)) := by
      apply cfc_congr
      intro r hr
      rcases spectrum_two P hP a b r hr with h | h
      · subst h; simp only [α, β]; field_simp; ring
      · subst h; simp only [α, β]; field_simp; ring
    rw [hcongr, cfc_add (a := (a : ℂ) • P + (b : ℂ) • (1 - P)) (fun x => α * x) (fun _ => β),
      cfc_const_mul α (fun x => x) ((a : ℂ) • P + (b : ℂ) • (1 - P)),
      cfc_id' (R := ℝ) (a := (a : ℂ) • P + (b : ℂ) • (1 - P)),
      cfc_const β ((a : ℂ) • P + (b : ℂ) • (1 - P))]
    rw [Algebra.algebraMap_eq_smul_one]
    rw [show (β • (1 : Matrix ι ι ℂ)) = (β : ℂ) • (1 : Matrix ι ι ℂ) by
      rw [← Complex.coe_smul]]
    rw [show (α • ((a : ℂ) • P + (b : ℂ) • (1 - P))) =
        (α : ℂ) • ((a : ℂ) • P + (b : ℂ) • (1 - P)) by rw [← Complex.coe_smul]]
    have hab'' : (a : ℂ) - b ≠ 0 := by rw [sub_ne_zero]; exact_mod_cast hab
    have e1 : (f a : ℂ) = α * a + β := by
      simp only [α, β]; push_cast; field_simp; ring
    have e2 : (f b : ℂ) = α * b + β := by
      simp only [α, β]; push_cast; field_simp; ring
    rw [e1, e2]
    simp only [smul_add, smul_sub, smul_smul, add_smul, sub_smul]
    abel



theorem qe1 (P : Matrix ι ι ℂ) (hP : P * P = P) (hPh : Pᴴ = P) (a b t1 t2 : ℝ)
    (h1 : P.trace = t1) (h2 : (1 - P).trace = t2) :
    quantumEntropy 1 ((a : ℂ) • P + (b : ℂ) • (1 - P)) =
      -(t1 * (a * Real.log a) + t2 * (b * Real.log b)) := by
  unfold quantumEntropy
  rw [if_neg (by decide), if_pos (by rfl), cfc_two P hP hPh a b, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul, h1, h2]
  simp [Complex.mul_re]
  ring

theorem qe2 (P : Matrix ι ι ℂ) (hP : P * P = P) (a b t1 t2 : ℝ)
    (h1 : P.trace = t1) (h2 : (1 - P).trace = t2) :
    quantumEntropy 2 ((a : ℂ) • P + (b : ℂ) • (1 - P)) =
      -Real.log (t1 * a ^ 2 + t2 * b ^ 2) := by
  unfold quantumEntropy
  rw [if_neg (by decide), if_neg (by decide)]
  have hP1 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  have hP2 : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have hP3 : (1 - P) * (1 - P) = 1 - P := by rw [sub_mul, one_mul, hP1, sub_zero]
  have : ((a : ℂ) • P + (b : ℂ) • (1 - P)) ^ (2 : WithTop ℕ).untopD 0 =
      ((a ^ 2 : ℝ) : ℂ) • P + ((b ^ 2 : ℝ) : ℂ) • (1 - P) := by
    show _ ^ 2 = _
    rw [sq]
    simp only [add_mul, mul_add, smul_mul_smul, hP, hP1, hP2, hP3, smul_zero, add_zero, zero_add]
    push_cast; ring_nf
  rw [this, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, h1, h2]
  have e : (((2 : WithTop ℕ).untopD 0 : ℕ) : ℝ) = 2 := by
    have : (2 : WithTop ℕ).untopD 0 = 2 := rfl
    rw [this]; norm_num
  rw [e]
  simp only [smul_eq_mul, Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re]
  norm_num
  ring_nf

end

end X6P39R

end R

section S
attribute [local instance] Classical.propDecidable




namespace X6P39S

open X6P39F X6P39R

theorem lo0 (y z : Qubits 1) :
    SparsePauliNoise.labelOperator (0 : PauliLabel 1) y z = if y 0 = z 0 then 1 else 0 := by
  simp [SparsePauliNoise.labelOperator, canonicalPauli, Stabilizer.PauliString.toMatrix,
    Stabilizer.Pauli.mat, Matrix.one_apply]

theorem loX (y z : Qubits 1) :
    SparsePauliNoise.labelOperator labelX y z = pauliX (y 0) (z 0) := by
  simp [SparsePauliNoise.labelOperator, canonicalPauli, Stabilizer.PauliString.toMatrix,
    Stabilizer.Pauli.mat, labelX]

theorem loY (y z : Qubits 1) :
    SparsePauliNoise.labelOperator labelY y z = pauliY (y 0) (z 0) := by
  simp [SparsePauliNoise.labelOperator, canonicalPauli, Stabilizer.PauliString.toMatrix,
    Stabilizer.Pauli.mat, labelY]

theorem loZ (y z : Qubits 1) :
    SparsePauliNoise.labelOperator labelZ y z = pauliZ (y 0) (z 0) := by
  simp [SparsePauliNoise.labelOperator, canonicalPauli, Stabilizer.PauliString.toMatrix,
    Stabilizer.Pauli.mat, labelZ]

theorem hnu : Learning.IsDistribution (depolarizingLaw (3/10)) := by
  refine ⟨fun e => ?_, ?_⟩
  · rcases cases4 e with h | h | h | h <;> subst h <;>
      simp [depolarizingLaw, pv0, pvX, pvY, pvZ] <;> norm_num
  · rw [sum4]; simp [depolarizingLaw, pv0, pvX, pvY, pvZ]; norm_num

theorem J_apply (r q r' q' : Qubits 1) :
    noisyChoi (1 : Matrix (Qubits 1) (Qubits 1) ℂ) (depolarizingLaw (3/10)) hnu (r, q) (r', q') =
      (1/2 : ℂ) * ∑ a, (depolarizingLaw (3/10) a : ℂ) *
        (SparsePauliNoise.labelOperator a q r * conj (SparsePauliNoise.labelOperator a q' r')) := by
  simp only [noisyChoi, idTensorSuperop, SparsePauliNoise.channelFromRates, conjSuperop,
    pureDensity, maxEntangled, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.mul_apply, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one, smul_eq_mul,
    Matrix.conjTranspose_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * conj (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = 1 / 2 := by
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]
    norm_num
  simp only [pow_one]
  rw [Finset.sum_eq_single r']
  · rw [Finset.sum_eq_single r]
    · simp only [if_true, RCLike.star_def]
      rw [← hs]; ring
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem sum4c (f : PauliLabel 1 → ℂ) : ∑ x, f x = f 0 + f labelX + f labelY + f labelZ := by
  let e : PauliLabel 1 ≃ ZMod 2 × ZMod 2 :=
    (Equiv.funUnique (Fin 1) (ZMod 2)).prodCongr (Equiv.funUnique (Fin 1) (ZMod 2))
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  change ∑ x : Fin 2, ∑ y : Fin 2, f (e.symm (x, y)) = _
  simp only [Fin.sum_univ_two]
  have h00 : e.symm (0, 0) = 0 := by ext i <;> fin_cases i <;> rfl
  have h10 : e.symm (1, 0) = labelX := by ext i <;> fin_cases i <;> rfl
  have h11 : e.symm (1, 1) = labelY := by ext i <;> fin_cases i <;> rfl
  have h01 : e.symm (0, 1) = labelZ := by ext i <;> fin_cases i <;> rfl
  change f (e.symm (0, 0)) + f (e.symm (0, 1)) + (f (e.symm (1, 0)) + f (e.symm (1, 1))) = _
  rw [h00, h10, h11, h01]; ring

theorem q1 (r : Qubits 1) : r = fun _ => r 0 := by
  funext i; rw [Subsingleton.elim i 0]

theorem const_eq (x y : Bool) : ((fun _ : Fin 1 => x) = fun _ => y) ↔ x = y :=
  ⟨fun h => congrFun h 0, fun h => h ▸ rfl⟩

def Phi : Matrix (Qubits 1 × Qubits 1) (Qubits 1 × Qubits 1) ℂ := pureDensity (maxEntangled 1)

theorem Phi_apply (r q r' q' : Qubits 1) :
    Phi (r, q) (r', q') = if r = q ∧ r' = q' then 1 / 2 else 0 := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * conj (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = 1 / 2 := by
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]
    norm_num
  simp only [Phi, pureDensity, maxEntangled, Matrix.of_apply, pow_one]
  split_ifs <;> simp_all

theorem J_eq : noisyChoi (1 : Matrix (Qubits 1) (Qubits 1) ℂ) (depolarizingLaw (3/10)) hnu =
    ((7/10 : ℝ) : ℂ) • Phi + ((1/10 : ℝ) : ℂ) • (1 - Phi) := by
  ext ⟨r, q⟩ ⟨r', q'⟩
  rw [J_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.sub_apply,
    Phi_apply, Matrix.one_apply, sum4c]
  simp only [depolarizingLaw, pv0, pvX, pvY, pvZ, lo0, loX, loY, loZ]
  rw [q1 r, q1 q, q1 r', q1 q']
  generalize r 0 = b1
  generalize q 0 = b2
  generalize r' 0 = b3
  generalize q' 0 = b4
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    simp [const_eq, pauliX, pauliY, pauliZ, Prod.ext_iff] <;> norm_num

end X6P39S

end S

section T
attribute [local instance] Classical.propDecidable




namespace X6P39T

open X6P39F X6P39R X6P39S

theorem sumQ (f : Qubits 1 → ℂ) : ∑ r, f r = f (fun _ => true) + f (fun _ => false) := by
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
  rfl

theorem Phi_herm : Phiᴴ = Phi := by
  ext ⟨r, q⟩ ⟨r', q'⟩
  rw [Matrix.conjTranspose_apply, Phi_apply, Phi_apply]
  split_ifs with h1 h2 h2 <;> simp_all

theorem Phi_idem : Phi * Phi = Phi := by
  ext ⟨r, q⟩ ⟨r', q'⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type, sumQ]
  simp only [sumQ, Phi_apply]
  rw [q1 r, q1 q, q1 r', q1 q']
  generalize r 0 = b1
  generalize q 0 = b2
  generalize r' 0 = b3
  generalize q' 0 = b4
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> simp [const_eq] <;> norm_num

theorem Phi_tr : Phi.trace = ((1 : ℝ) : ℂ) := by
  rw [Matrix.trace, Fintype.sum_prod_type]
  simp only [Matrix.diag, sumQ, Phi_apply]
  simp [const_eq]; norm_num

theorem card4 : Fintype.card (Qubits 1 × Qubits 1) = 4 := by
  simp [Fintype.card_prod, Fintype.card_fun]

theorem Phi_tr' : (1 - Phi).trace = ((3 : ℝ) : ℂ) := by
  rw [Matrix.trace_sub, Phi_tr, Matrix.trace_one, card4]; norm_num

def J : Matrix (Qubits 1 × Qubits 1) (Qubits 1 × Qubits 1) ℂ :=
  noisyChoi (1 : Matrix (Qubits 1) (Qubits 1) ℂ) (depolarizingLaw (3/10)) hnu

theorem tl_J : traceLeft J = ((1/2 : ℝ) : ℂ) • (1 : Matrix (Qubits 1) (Qubits 1) ℂ) +
    ((1/2 : ℝ) : ℂ) • (1 - 1) := by
  rw [J, J_eq]
  ext q q'
  simp only [traceLeft, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    sumQ, Phi_apply, Matrix.one_apply, Prod.mk.injEq]
  rw [q1 q, q1 q']
  generalize q 0 = b2
  generalize q' 0 = b4
  cases b2 <;> cases b4 <;> simp [const_eq] <;> norm_num

theorem one_tr : (1 : Matrix (Qubits 1) (Qubits 1) ℂ).trace = ((2 : ℝ) : ℂ) := by
  rw [Matrix.trace_one]; simp [Fintype.card_fun]

theorem zero_tr : (1 - 1 : Matrix (Qubits 1) (Qubits 1) ℂ).trace = ((0 : ℝ) : ℂ) := by simp

theorem H1J : quantumEntropy 1 J = -(1 * ((7/10) * Real.log (7/10)) + 3 * ((1/10) * Real.log (1/10))) := by
  rw [J, J_eq, qe1 Phi Phi_idem Phi_herm _ _ 1 3 Phi_tr Phi_tr']

theorem H2J : quantumEntropy 2 J = -Real.log (1 * (7/10) ^ 2 + 3 * (1/10) ^ 2) := by
  rw [J, J_eq, qe2 Phi Phi_idem _ _ 1 3 Phi_tr Phi_tr']

theorem H1L : quantumEntropy 1 (traceLeft J) = -(2 * ((1/2) * Real.log (1/2)) + 0 * ((1/2) * Real.log (1/2))) := by
  rw [tl_J, qe1 1 (by simp) (by simp) _ _ 2 0 one_tr zero_tr]

theorem H2L : quantumEntropy 2 (traceLeft J) = -Real.log (2 * (1/2) ^ 2 + 0 * (1/2) ^ 2) := by
  rw [tl_J, qe2 1 (by simp) _ _ 2 0 one_tr zero_tr]

def eq : Qubits 1 × (Unit × Qubits 1) ≃ Qubits 1 × Qubits 1 :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.punitProd _)

theorem ss_eq (M : Matrix (Qubits 1 × Qubits 1) (Qubits 1 × Qubits 1) ℂ) :
    singleSyndromeState M = M.submatrix eq eq := by
  ext ⟨r, u, q⟩ ⟨r', u', q'⟩; rfl

theorem tr_sub {α β : Type*} [Fintype α] [Fintype β] (M : Matrix β β ℂ) (e : α ≃ β) :
    (M.submatrix e e).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact e.sum_comp (fun j => M j j)

def Phi' := Phi.submatrix eq eq

theorem SS_J : singleSyndromeState J = ((7/10 : ℝ) : ℂ) • Phi' + ((1/10 : ℝ) : ℂ) • (1 - Phi') := by
  rw [ss_eq, J, J_eq]
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.one_apply, Phi', eq.injective.eq_iff]

theorem Phi'_idem : Phi' * Phi' = Phi' := by
  rw [Phi', Matrix.submatrix_mul_equiv, Phi_idem]

theorem Phi'_herm : Phi'ᴴ = Phi' := by
  rw [Phi', Matrix.conjTranspose_submatrix, Phi_herm]

theorem Phi'_tr : Phi'.trace = ((1 : ℝ) : ℂ) := by rw [Phi', tr_sub, Phi_tr]

theorem Phi'_tr' : (1 - Phi').trace = ((3 : ℝ) : ℂ) := by
  rw [Matrix.trace_sub, Phi'_tr, Matrix.trace_one]
  simp [Fintype.card_prod, Fintype.card_fun]; norm_num

theorem tl_SS : traceLeft (singleSyndromeState J) =
    ((1/2 : ℝ) : ℂ) • (1 : Matrix (Unit × Qubits 1) (Unit × Qubits 1) ℂ) + ((1/2 : ℝ) : ℂ) • (1 - 1) := by
  have h : traceLeft (singleSyndromeState J) =
      (traceLeft J).submatrix (Equiv.punitProd _) (Equiv.punitProd _) := by
    ext ⟨u, q⟩ ⟨u', q'⟩; rfl
  rw [h, tl_J]
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.one_apply, (Equiv.punitProd (Qubits 1)).injective.eq_iff]

theorem H1S : quantumEntropy 1 (singleSyndromeState J) =
    -(1 * ((7/10) * Real.log (7/10)) + 3 * ((1/10) * Real.log (1/10))) := by
  rw [SS_J, qe1 Phi' Phi'_idem Phi'_herm _ _ 1 3 Phi'_tr Phi'_tr']

theorem H1LS : quantumEntropy 1 (traceLeft (singleSyndromeState J)) =
    -(2 * ((1/2) * Real.log (1/2)) + 0 * ((1/2) * Real.log (1/2))) := by
  rw [tl_SS, qe1 1 (by simp) (by simp) _ _ 2 0 (by rw [Matrix.trace_one]; simp) (by simp)]

theorem final :
    coherentInformation 1 (singleSyndromeState J) = coherentInformation 1 J ∧
      coherentInformation 2 J = Real.log (26/25) ∧
      coherentInformation 1 J = Real.log 2 + (7/10)*Real.log (7/10) +
        (3/10)*Real.log (1/10) ∧
      0 < coherentInformation 2 J ∧ coherentInformation 1 J < 0 := by
  have c1 : coherentInformation 1 J = Real.log 2 + (7/10)*Real.log (7/10) +
      (3/10)*Real.log (1/10) := by
    unfold coherentInformation
    rw [H1L, H1J]
    have : Real.log (1/2) = - Real.log 2 := by rw [one_div, Real.log_inv]
    rw [this]; ring
  have c2 : coherentInformation 2 J = Real.log (26/25) := by
    unfold coherentInformation
    rw [H2L, H2J]
    rw [show (2 * (1/2 : ℝ) ^ 2 + 0 * (1/2) ^ 2) = 1/2 by norm_num,
      show (1 * (7/10 : ℝ) ^ 2 + 3 * (1/10) ^ 2) = 13/25 by norm_num]
    have : Real.log (26/25) = Real.log (13/25) - Real.log (1/2) := by
      rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
    rw [this]; ring
  refine ⟨?_, c2, c1, ?_, ?_⟩
  · unfold coherentInformation
    rw [H1S, H1LS, H1L, H1J]
  · rw [c2]; exact Real.log_pos (by norm_num)
  · rw [c1]
    have h7 : Real.log (7/10) ≤ 7/10 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h10 : Real.log (1/10) = - Real.log 10 := by rw [one_div, Real.log_inv]
    have h2 := Real.log_two_lt_d9
    have hl10 : 2 < Real.log 10 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have he := Real.exp_one_lt_d9
      have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      have h0 : 0 < Real.exp 1 := Real.exp_pos 1
      nlinarith
    rw [h10]
    nlinarith

end X6P39T

end T

section Sol
attribute [local instance] Classical.propDecidable

theorem solution :
    ∃ hnu : Learning.IsDistribution (depolarizingLaw (3/10)),
      let J := noisyChoi (1 : Matrix (Qubits 1) (Qubits 1) ℂ)
        (depolarizingLaw (3/10)) hnu
      coherentInformation 1 (singleSyndromeState J) = coherentInformation 1 J ∧
      coherentInformation 2 J = Real.log (26/25) ∧
      coherentInformation 1 J = Real.log 2 + (7/10)*Real.log (7/10) +
        (3/10)*Real.log (1/10) ∧
      0 < coherentInformation 2 J ∧ coherentInformation 1 J < 0 :=
  ⟨X6P39S.hnu, X6P39T.final⟩

end Sol

end
