-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P40.relativeEntropy_pinch_le
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-29T00:36:20.087129+00:00
-- url     : https://prove2.me/submissions/ef536fe2-bca3-43b8-aac9-a83fa431743e

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40
import Theorems.Thm_TroppMatrixConcentration_ch8_entropy_joint_convex

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40

section PinHelpers

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Double-sum formula for the trace of a product of two unitarily diagonalized matrices. -/
theorem pin_trace_conj_mul (U V : Matrix.unitaryGroup n ℂ) (F G : n → ℝ) :
    ((V : Matrix n n ℂ) * Matrix.diagonal (fun i => (F i : ℂ)) * star (V : Matrix n n ℂ) *
      ((U : Matrix n n ℂ) * Matrix.diagonal (fun j => (G j : ℂ)) * star (U : Matrix n n ℂ))).trace
      = ∑ i, ∑ j, ((F i * G j * Complex.normSq ((star (V : Matrix n n ℂ) * U) i j) : ℝ) : ℂ) := by
  set W : Matrix n n ℂ := star (V : Matrix n n ℂ) * U with hW
  have hstar : star W = star (U : Matrix n n ℂ) * V := by
    simp [hW, StarMul.star_mul]
  have key : ((V : Matrix n n ℂ) * Matrix.diagonal (fun i => (F i : ℂ)) * star (V : Matrix n n ℂ) *
      ((U : Matrix n n ℂ) * Matrix.diagonal (fun j => (G j : ℂ)) * star (U : Matrix n n ℂ))).trace
      = (Matrix.diagonal (fun i => (F i : ℂ)) * W * Matrix.diagonal (fun j => (G j : ℂ)) *
          star W).trace := by
    rw [hstar, hW]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [key, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
    ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

/-- Rows of the overlap probabilities of two unitaries sum to one. -/
theorem pin_row_sum (U V : Matrix.unitaryGroup n ℂ) (i : n) :
    ∑ j, Complex.normSq ((star (V : Matrix n n ℂ) * U) i j) = 1 := by
  set W : Matrix n n ℂ := star (V : Matrix n n ℂ) * U with hW
  have hWu : W ∈ Matrix.unitaryGroup n ℂ := by
    rw [hW]
    exact (star V * U).2
  have h1 : (W * star W) i i = 1 := by
    rw [Matrix.mem_unitaryGroup_iff.mp hWu]; simp
  have h2 : (W * star W) i i = ((∑ j, Complex.normSq (W i j) : ℝ) : ℂ) := by
    simp only [Matrix.mul_apply, Matrix.star_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.mul_conj]; rfl
  exact_mod_cast h2.symm.trans h1

/-- Scalar estimate for `h(b,a) = b log b - b log a - b + a`. -/
theorem pin_scalar {a b c : ℝ} (hc : 0 < c) (ha : c ≤ a) (hb : 0 ≤ b) :
    0 ≤ b * Real.log b - b * Real.log a - b + a ∧
      b * Real.log b - b * Real.log a - b + a ≤ (b - a) ^ 2 / c := by
  have ha0 : 0 < a := lt_of_lt_of_le hc ha
  rcases hb.lt_or_eq with hb | hb
  · constructor
    · have := Real.log_le_sub_one_of_pos (div_pos ha0 hb)
      rw [Real.log_div ha0.ne' hb.ne'] at this
      have h2 := mul_le_mul_of_nonneg_left this hb.le
      have h3 : b * (a / b - 1) = a - b := by field_simp
      nlinarith
    · have := Real.log_le_sub_one_of_pos (div_pos hb ha0)
      rw [Real.log_div hb.ne' ha0.ne'] at this
      have h2 := mul_le_mul_of_nonneg_left this hb.le
      have h3 : b * (b / a - 1) - b + a = (b - a) ^ 2 / a := by field_simp; ring
      have h4 : (b - a) ^ 2 / a ≤ (b - a) ^ 2 / c :=
        div_le_div_of_nonneg_left (sq_nonneg _) hc ha
      nlinarith
  · subst hb
    simp only [Real.log_zero, mul_zero, zero_mul, sub_zero, zero_sub, zero_add]
    refine ⟨ha0.le, ?_⟩
    rw [neg_sq, le_div_iff₀ hc]
    nlinarith

/-- Overlap probabilities between the eigenbases of two Hermitian matrices. -/
noncomputable def pin_P {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (i j : n) : ℝ :=
  Complex.normSq ((star (hB.eigenvectorUnitary : Matrix n n ℂ) * hA.eigenvectorUnitary) i j)

theorem pin_P_nonneg {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (i j : n) :
    0 ≤ pin_P hA hB i j := Complex.normSq_nonneg _

theorem pin_P_row {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (i : n) :
    ∑ j, pin_P hA hB i j = 1 := pin_row_sum _ _ i

theorem pin_trace_cfc {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f g : ℝ → ℝ) :
    (cfc f B * cfc g A).trace = ((∑ i, ∑ j, f (hB.eigenvalues i) * g (hA.eigenvalues j) *
      pin_P hA hB i j : ℝ) : ℂ) := by
  rw [hB.cfc_eq, hA.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  have := pin_trace_conj_mul hA.eigenvectorUnitary hB.eigenvectorUnitary
    (f ∘ hB.eigenvalues) (g ∘ hA.eigenvalues)
  push_cast at this ⊢
  convert this using 1 <;> rfl

end PinHelpers
namespace PinAux

/-- The finite Umegaki expression. -/
def Dfin {d : ℕ} (rho sigma : Mat d) : ℝ :=
  (cfc (fun x : ℝ => x * Real.log x) rho - rho * cfc Real.log sigma).trace.re

theorem relEnt_of_supp {d : ℕ} {rho sigma : Mat d}
    (h : QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported rho sigma) :
    relativeEntropy rho sigma = (Dfin rho sigma : EReal) := by
  simp only [relativeEntropy, if_pos h, Dfin]

theorem supp_of_posDef {d : ℕ} (rho : Mat d) {sigma : Mat d} (hs : sigma.PosDef) :
    QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported rho sigma := by
  intro v hv
  have hv' : sigma *ᵥ v = 0 := hv
  by_contra hne
  have h0 : v ≠ 0 := by
    rintro rfl; exact hne (by simp)
  have := hs.dotProduct_mulVec_pos h0
  rw [hv'] at this
  simp at this

theorem ch8_eq {d : ℕ} {rho sigma : Mat d} (hr : rho.PosDef) (hs : sigma.PosDef)
    (htr : rho.trace = sigma.trace) :
    TroppMatrixConcentration.ch8_relativeEntropy rho sigma = Dfin rho sigma := by
  have hfin := Matrix.finite_real_spectrum (A := rho)
  have hsa : IsSelfAdjoint rho := hr.isHermitian
  have hk : cfc (fun x : ℝ => x * Real.log x) rho = rho * cfc Real.log rho := by
    rw [cfc_mul (fun x : ℝ => x) Real.log rho (hfin.continuousOn _) (hfin.continuousOn _),
      cfc_id' ℝ rho (ha := hsa)]
  simp only [TroppMatrixConcentration.ch8_relativeEntropy, TroppMatrixConcentration.matrixLog,
    Dfin, hk, Matrix.mul_sub, Matrix.trace_sub, htr, sub_self, sub_zero]

theorem Dfin_conj {d : ℕ} (W : Matrix.unitaryGroup (Fin d) ℂ) (rho sigma : Mat d)
    (hr : rho.IsHermitian) (hs : sigma.IsHermitian) :
    Dfin ((W : Mat d) * rho * (W : Mat d)ᴴ) ((W : Mat d) * sigma * (W : Mat d)ᴴ) =
      Dfin rho sigma := by
  let φ := Unitary.conjStarAlgAut ℂ (Mat d) W
  have hφ : ∀ X : Mat d, φ X = (W : Mat d) * X * (W : Mat d)ᴴ := fun X => by
    simp [φ, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  have hc : Continuous φ :=
    LinearMap.continuous_of_finiteDimensional (φ.toAlgEquiv.toLinearEquiv.toLinearMap)
  have hm : ∀ (f : ℝ → ℝ) (X : Mat d), X.IsHermitian → cfc f (φ X) = φ (cfc f X) := by
    intro f X hX
    have hfin := Matrix.finite_real_spectrum (A := X)
    have hX' : IsSelfAdjoint X := hX
    have hφX : IsSelfAdjoint (φ X) := hX'.map φ
    exact (StarAlgHomClass.map_cfc (S := ℂ) φ f X (hfin.continuousOn _) hc hX' hφX).symm
  rw [← hφ, ← hφ, Dfin, Dfin, hm _ _ hr, hm _ _ hs, ← map_mul, ← map_sub, hφ,
    Matrix.trace_mul_cycle]
  have hUU : (W : Mat d)ᴴ * (W : Mat d) = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 W.2
  rw [hUU, Matrix.one_mul]

end PinAux
namespace PinAux

/-- Pinching in the basis given by the columns of `U`. -/
def pinch {d : ℕ} (U : Mat d) (X : Mat d) : Mat d :=
  U * Matrix.diagonal (fun i => (Uᴴ * X * U) i i) * Uᴴ

/-- Clock phases. -/
def clockPhase (d : ℕ) (k j : Fin d) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (j : ℂ) / d)

theorem clockPhase_mul_conj (d : ℕ) (k j : Fin d) :
    clockPhase d k j * star (clockPhase d k j) = 1 := by
  rw [clockPhase, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  simp [map_div₀, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

theorem clock_sum (d : ℕ) (i j : Fin d) :
    ∑ k : Fin d, clockPhase d k i * star (clockPhase d k j) = if i = j then (d : ℂ) else 0 := by
  have hd : (d : ℂ) ≠ 0 := by
    have := i.pos; exact_mod_cast this.ne'
  set ζ := Complex.exp (2 * Real.pi * Complex.I * ((i : ℂ) - (j : ℂ)) / d) with hζ
  have hterm : ∀ k : Fin d, clockPhase d k i * star (clockPhase d k j) = ζ ^ (k : ℕ) := by
    intro k
    rw [clockPhase, clockPhase, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, hζ,
      ← Complex.exp_nat_mul]
    congr 1
    simp [map_div₀, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun k => ζ ^ k)]
  split_ifs with h
  · subst h; simp [hζ]
  · have hζ1 : ζ ≠ 1 := by
      rw [hζ]
      intro he
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 he
      have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      have : ((i : ℂ) - (j : ℂ)) = n * d := by
        field_simp at hn
        linear_combination hn
      have hr : ((i : ℤ) - (j : ℤ)) = n * d := by exact_mod_cast this
      have hi := i.2; have hj := j.2
      have hne : (i : ℤ) ≠ j := fun h' => h (Fin.ext (by exact_mod_cast h'))
      rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
      · nlinarith
      · subst hn0; simp at hr; exact hne (by linarith)
      · nlinarith
    have hζd : ζ ^ d = 1 := by
      rw [hζ, ← Complex.exp_nat_mul]
      rw [Complex.exp_eq_one_iff]
      refine ⟨(i : ℤ) - j, ?_⟩
      push_cast
      field_simp
    rw [geom_sum_eq hζ1, hζd, sub_self, zero_div]

/-- Clock unitary. -/
def clockU (d : ℕ) (k : Fin d) : Matrix.unitaryGroup (Fin d) ℂ :=
  ⟨Matrix.diagonal (clockPhase d k), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one with j
    exact clockPhase_mul_conj d k j⟩

theorem clock_average {d : ℕ} (Y : Mat d) :
    ∑ k : Fin d, ((1 / d : ℝ) • ((clockU d k : Mat d) * Y * (clockU d k : Mat d)ᴴ)) =
      Matrix.diagonal (fun i => Y i i) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, clockU, Matrix.diagonal_conjTranspose,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply]
  have : ∀ k : Fin d, (1 / d : ℝ) • (clockPhase d k i * Y i j * star (clockPhase d k j)) =
      ((1 / d : ℝ) : ℂ) * Y i j * (clockPhase d k i * star (clockPhase d k j)) := by
    intro k; rw [Complex.real_smul]; ring
  simp only [Pi.star_apply] at *
  simp_rw [this]
  rw [← Finset.mul_sum, clock_sum]
  split_ifs with h
  · subst h
    have hd : (d : ℂ) ≠ 0 := by have := i.pos; exact_mod_cast this.ne'
    push_cast; field_simp
  · simp

end PinAux
namespace PinAux

theorem uU {d : ℕ} (W : Matrix.unitaryGroup (Fin d) ℂ) : (W : Mat d)ᴴ * (W : Mat d) = 1 := by
  rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 W.2

theorem Uu {d : ℕ} (W : Matrix.unitaryGroup (Fin d) ℂ) : (W : Mat d) * (W : Mat d)ᴴ = 1 := by
  rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.1 W.2

theorem vecMul_inj {d : ℕ} (W : Matrix.unitaryGroup (Fin d) ℂ) :
    Function.Injective (fun v => v ᵥ* (W : Mat d)) := by
  intro v w h
  have := congrArg (fun x => x ᵥ* (W : Mat d)ᴴ) h
  simpa [Matrix.vecMul_vecMul, Uu] using this

theorem mulVec_inj {d : ℕ} (W : Matrix.unitaryGroup (Fin d) ℂ) :
    Function.Injective (W : Mat d).mulVec := by
  intro v w h
  have := congrArg (fun x => (W : Mat d)ᴴ *ᵥ x) h
  simpa [Matrix.mulVec_mulVec, uU] using this

theorem conj_posDef {d : ℕ} (W : Matrix.unitaryGroup (Fin d) ℂ) {X : Mat d} (hX : X.PosDef) :
    ((W : Mat d) * X * (W : Mat d)ᴴ).PosDef :=
  hX.mul_mul_conjTranspose_same (vecMul_inj W)

theorem conj_trace {d : ℕ} (W : Matrix.unitaryGroup (Fin d) ℂ) (X : Mat d) :
    ((W : Mat d) * X * (W : Mat d)ᴴ).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, uU, Matrix.one_mul]

theorem pinch_posDef {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) {X : Mat d} (hX : X.PosDef) :
    (pinch (U : Mat d) X).PosDef := by
  have hY := hX.conjTranspose_mul_mul_same (mulVec_inj U)
  exact (Matrix.PosDef.diagonal fun i => hY.diag_pos).mul_mul_conjTranspose_same (vecMul_inj U)

theorem pinch_trace {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (X : Mat d) :
    (pinch (U : Mat d) X).trace = X.trace := by
  rw [pinch, conj_trace U, Matrix.trace_diagonal]
  change ((U : Mat d)ᴴ * X * (U : Mat d)).trace = X.trace
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Uu, Matrix.one_mul]

/-- Conjugated clock unitaries. -/
def clockW {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (k : Fin d) :
    Matrix.unitaryGroup (Fin d) ℂ := U * clockU d k * star U

theorem clockW_coe {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (k : Fin d) :
    (clockW U k : Mat d) = (U : Mat d) * (clockU d k : Mat d) * (U : Mat d)ᴴ := by
  simp [clockW, Matrix.star_eq_conjTranspose]

theorem pinch_avg {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (X : Mat d) :
    ∑ k : Fin d, ((1 / d : ℝ) • ((clockW U k : Mat d) * X * (clockW U k : Mat d)ᴴ)) =
      pinch (U : Mat d) X := by
  have h : ∀ k : Fin d, (clockW U k : Mat d) * X * (clockW U k : Mat d)ᴴ =
      (U : Mat d) * ((clockU d k : Mat d) * ((U : Mat d)ᴴ * X * (U : Mat d)) *
        (clockU d k : Mat d)ᴴ) * (U : Mat d)ᴴ := by
    intro k
    rw [clockW_coe]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  simp_rw [h]
  have e : ∀ (M : Mat d), (1 / d : ℝ) • ((U : Mat d) * M * (U : Mat d)ᴴ) =
      (U : Mat d) * ((1 / d : ℝ) • M) * (U : Mat d)ᴴ := fun M => by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  simp_rw [e, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [clock_average, pinch]

theorem posDef_case {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) {rho sigma : Mat d}
    (hr : rho.PosDef) (hs : sigma.PosDef) (htr : rho.trace = sigma.trace) :
    Dfin (pinch (U : Mat d) rho) (pinch (U : Mat d) sigma) ≤ Dfin rho sigma := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [Subsingleton.elim (pinch _ rho) rho, Subsingleton.elim (pinch _ sigma) sigma]
  haveI : NeZero d := ⟨hd.ne'⟩
  have key := (TroppMatrixConcentration.ch8_entropy_joint_convex (d := d)).map_sum_le
    (t := Finset.univ) (w := fun _ => (1 / d : ℝ))
    (p := fun k => ((clockW U k : Mat d) * rho * (clockW U k : Mat d)ᴴ,
      (clockW U k : Mat d) * sigma * (clockW U k : Mat d)ᴴ))
    (fun _ _ => by positivity)
    (by simp)
    (fun k _ => ⟨conj_posDef _ hr, conj_posDef _ hs⟩)
  simp only [Prod.smul_mk] at key
  rw [Prod.fst_sum, Prod.snd_sum] at key
  simp only [pinch_avg] at key
  rw [ch8_eq (pinch_posDef U hr) (pinch_posDef U hs) (by rw [pinch_trace, pinch_trace, htr])]
    at key
  refine key.trans (le_of_eq ?_)
  have : ∀ k : Fin d, TroppMatrixConcentration.ch8_relativeEntropy
      ((clockW U k : Mat d) * rho * (clockW U k : Mat d)ᴴ)
      ((clockW U k : Mat d) * sigma * (clockW U k : Mat d)ᴴ) = Dfin rho sigma := by
    intro k
    rw [ch8_eq (conj_posDef _ hr) (conj_posDef _ hs) (by rw [conj_trace, conj_trace, htr]),
      Dfin_conj _ _ _ hr.isHermitian hs.isHermitian]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, nsmul_eq_mul]
  field_simp

end PinAux
namespace PinAux

/-- Regularization towards the maximally mixed state. -/
def reg (d : ℕ) (ε : ℝ) (X : Mat d) : Mat d := (1 - ε) • X + (ε / d) • (1 : Mat d)

theorem reg_zero {d : ℕ} (X : Mat d) : reg d 0 X = X := by simp [reg]

theorem reg_cfc {d : ℕ} (ε : ℝ) {X : Mat d} (hX : X.IsHermitian) :
    reg d ε X = cfc (fun x : ℝ => (1 - ε) * x + ε / d) X := by
  have hsa : IsSelfAdjoint X := hX
  rw [cfc_add X (fun x : ℝ => (1 - ε) * x) (fun _ => ε / d), cfc_const_mul _ _ X,
    cfc_id' ℝ X, cfc_const _ X, Algebra.algebraMap_eq_smul_one, reg]

theorem reg_posDef {d : ℕ} (hd : 0 < d) {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) {X : Mat d}
    (hX : X.PosSemidef) : (reg d ε X).PosDef := by
  rw [reg, add_comm]
  exact (Matrix.PosDef.one.smul (by positivity : (0 : ℝ) < ε / d)).add_posSemidef
    (hX.smul (by linarith : (0 : ℝ) ≤ 1 - ε))

theorem reg_trace {d : ℕ} (hd : 0 < d) (ε : ℝ) {X : Mat d} (hX : X.trace = 1) :
    (reg d ε X).trace = 1 := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [reg, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hX, Matrix.trace_one,
    Fintype.card_fin]
  simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div,
    Complex.ofReal_natCast, mul_one]
  field_simp
  ring

theorem pinch_reg {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (ε : ℝ) (X : Mat d) :
    pinch (U : Mat d) (reg d ε X) = reg d ε (pinch (U : Mat d) X) := by
  have hd : ∀ i, ((U : Mat d)ᴴ * reg d ε X * (U : Mat d)) i i =
      (1 - ε) • ((U : Mat d)ᴴ * X * (U : Mat d)) i i + (ε / d) • (1 : ℂ) := by
    intro i
    rw [reg, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, uU]
    simp
  have hdiag : Matrix.diagonal (fun i => ((U : Mat d)ᴴ * reg d ε X * (U : Mat d)) i i) =
      (1 - ε) • Matrix.diagonal (fun i => ((U : Mat d)ᴴ * X * (U : Mat d)) i i) +
        (ε / d) • (1 : Mat d) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [hd]
    · simp [Matrix.diagonal_apply, h, Matrix.one_apply]
  rw [pinch, hdiag, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Uu, reg, pinch]

theorem pinch_supp {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) {rho sigma : Mat d}
    (hr : rho.PosSemidef) (hs : sigma.PosSemidef)
    (h : QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported rho sigma) :
    QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported
      (pinch (U : Mat d) rho) (pinch (U : Mat d) sigma) := by
  set V := (U : Mat d)
  have hVV : V * Vᴴ = 1 := Uu U
  have hVV' : Vᴴ * V = 1 := uU U
  set a := Vᴴ * sigma * V
  set b := Vᴴ * rho * V
  have ha : a.PosSemidef := hs.conjTranspose_mul_mul_same V
  have hb : b.PosSemidef := hr.conjTranspose_mul_mul_same V
  -- a zero diagonal entry of `a` forces the same entry of `b` to vanish
  have key : ∀ i, a i i = 0 → b i i = 0 := by
    intro i hai
    have e : star (Pi.single i (1 : ℂ)) ⬝ᵥ a *ᵥ Pi.single i 1 = a i i := by
      simp [Matrix.mulVec_single_one, dotProduct, Pi.single_apply]
    have hav : a *ᵥ Pi.single i 1 = 0 := (ha.dotProduct_mulVec_zero_iff _).1 (by rw [e, hai])
    have hsv : sigma *ᵥ (V *ᵥ Pi.single i 1) = 0 := by
      have : sigma *ᵥ (V *ᵥ Pi.single i 1) = V *ᵥ (a *ᵥ Pi.single i 1) := by
        simp only [a, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hVV, Matrix.one_mul]
      rw [this, hav, Matrix.mulVec_zero]
    have hrv : rho *ᵥ (V *ᵥ Pi.single i 1) = 0 := h hsv
    have hbv : b *ᵥ Pi.single i 1 = 0 := by
      simp only [b, ← Matrix.mulVec_mulVec, hrv, Matrix.mulVec_zero]
    have := congrFun hbv i
    simpa [Matrix.mulVec_single_one] using this
  intro v hv
  have hv' : pinch V sigma *ᵥ v = 0 := hv
  change pinch V rho *ᵥ v = 0
  set w := Vᴴ *ᵥ v
  have hw : ∀ i, a i i * w i = 0 := by
    have : Matrix.diagonal (fun i => a i i) *ᵥ w = 0 := by
      have := congrArg (fun x => Vᴴ *ᵥ x) hv'
      simpa [pinch, a, w, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hVV'] using this
    intro i
    simpa [Matrix.mulVec_diagonal] using congrFun this i
  have hbw : Matrix.diagonal (fun i => b i i) *ᵥ w = 0 := by
    funext i
    rw [Matrix.mulVec_diagonal]
    rcases mul_eq_zero.1 (hw i) with h0 | h0
    · rw [key i h0, zero_mul]; rfl
    · rw [h0, mul_zero]; rfl
  simp only [pinch, ← Matrix.mulVec_mulVec]
  change V *ᵥ (Matrix.diagonal (fun i => b i i) *ᵥ w) = 0
  rw [hbw, Matrix.mulVec_zero]

end PinAux
namespace PinAux

theorem pinch_psd {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) {X : Mat d} (hX : X.PosSemidef) :
    (pinch (U : Mat d) X).PosSemidef := by
  have hY := hX.conjTranspose_mul_mul_same (U : Mat d)
  exact (Matrix.PosSemidef.diagonal fun i => hY.diag_nonneg).mul_mul_conjTranspose_same _

/-- Eigenvalue weights of `rho` vanish on the kernel of `sigma` under support containment. -/
theorem supp_weight {d : ℕ} {rho sigma : Mat d} (hr : rho.PosSemidef) (hs : sigma.PosSemidef)
    (h : QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported rho sigma) (i j : Fin d)
    (hj : hs.isHermitian.eigenvalues j = 0) :
    hr.isHermitian.eigenvalues i * pin_P hs.isHermitian hr.isHermitian i j = 0 := by
  set g : ℝ → ℝ := fun x => if x = 0 then 1 else 0
  have hfin := Matrix.finite_real_spectrum (A := sigma)
  have hsa : IsSelfAdjoint sigma := hs.isHermitian
  have hrsa : IsSelfAdjoint rho := hr.isHermitian
  have hsP : sigma * cfc g sigma = 0 := by
    have : cfc (fun x => x * g x) sigma = 0 := by
      rw [show (fun x => x * g x) = fun _ => (0 : ℝ) by
        funext x; by_cases hx : x = 0 <;> simp [g, hx]]
      exact cfc_const_zero ℝ sigma
    rw [cfc_mul (fun x : ℝ => x) g sigma (hfin.continuousOn _) (hfin.continuousOn _),
      cfc_id' ℝ sigma hsa] at this
    exact this
  have hrP : rho * cfc g sigma = 0 := by
    ext a b
    have hcol : sigma *ᵥ (cfc g sigma *ᵥ Pi.single b 1) = 0 := by
      rw [Matrix.mulVec_mulVec, hsP, Matrix.zero_mulVec]
    have hv : rho *ᵥ (cfc g sigma *ᵥ Pi.single b 1) = 0 := h hcol
    have := congrFun hv a
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at this
    simpa using this
  have htr := pin_trace_cfc hs.isHermitian hr.isHermitian (fun x => x) g
  rw [cfc_id' ℝ rho hrsa, hrP, Matrix.trace_zero] at htr
  have hsum : (∑ i, ∑ j, hr.isHermitian.eigenvalues i * g (hs.isHermitian.eigenvalues j) *
      pin_P hs.isHermitian hr.isHermitian i j) = 0 := by exact_mod_cast htr.symm
  have hnn : ∀ i j, 0 ≤ hr.isHermitian.eigenvalues i * g (hs.isHermitian.eigenvalues j) *
      pin_P hs.isHermitian hr.isHermitian i j := fun i j =>
    mul_nonneg (mul_nonneg (hr.eigenvalues_nonneg i) (by simp only [g]; split_ifs <;> norm_num))
      (pin_P_nonneg _ _ _ _)
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg
    (fun j _ => hnn i j))).1 hsum i (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn i j)).1 h1 j (Finset.mem_univ _)
  simpa [g, hj] using h2

/-- Affine regularization of eigenvalues. -/
def aff (d : ℕ) (ε x : ℝ) : ℝ := (1 - ε) * x + ε / d

theorem trace_formula {d : ℕ} {rho sigma : Mat d} (hr : rho.IsHermitian) (hs : sigma.IsHermitian)
    (ε : ℝ) :
    Dfin (reg d ε rho) (reg d ε sigma) = ∑ i, ∑ j,
      (aff d ε (hr.eigenvalues i) * Real.log (aff d ε (hr.eigenvalues i)) -
        aff d ε (hr.eigenvalues i) * Real.log (aff d ε (hs.eigenvalues j))) * pin_P hs hr i j := by
  have hfr := Matrix.finite_real_spectrum (A := rho)
  have hfs := Matrix.finite_real_spectrum (A := sigma)
  have hrsa : IsSelfAdjoint rho := hr
  have hssa : IsSelfAdjoint sigma := hs
  rw [reg_cfc ε hr, reg_cfc ε hs, Dfin,
    ← cfc_comp (fun x : ℝ => x * Real.log x) _ rho hrsa ((hfr.image _).continuousOn _)
      (hfr.continuousOn _),
    ← cfc_comp Real.log _ sigma hssa ((hfs.image _).continuousOn _) (hfs.continuousOn _),
    ← Matrix.mul_one (cfc ((fun x : ℝ => x * Real.log x) ∘ _) rho),
    ← cfc_const_one ℝ sigma hssa, Matrix.trace_sub, pin_trace_cfc hs hr, pin_trace_cfc hs hr,
    ← Complex.ofReal_sub, Complex.ofReal_re, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Function.comp, aff]
  ring

theorem tendsto_reg {d : ℕ} {rho sigma : Mat d} (hr : rho.PosSemidef) (hs : sigma.PosSemidef)
    (h : QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported rho sigma) :
    Tendsto (fun ε => Dfin (reg d ε rho) (reg d ε sigma)) (𝓝[>] 0) (𝓝 (Dfin rho sigma)) := by
  have h0 := trace_formula hr.isHermitian hs.isHermitian 0
  rw [reg_zero, reg_zero] at h0
  simp_rw [trace_formula hr.isHermitian hs.isHermitian, h0]
  apply tendsto_nhdsWithin_of_tendsto_nhds
  refine tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => ?_
  set r := hr.isHermitian.eigenvalues i
  set s := hs.isHermitian.eigenvalues j
  set P := pin_P hs.isHermitian hr.isHermitian i j
  have haff : ∀ x, Continuous fun ε : ℝ => aff d ε x := fun x => by
    unfold aff; fun_prop
  have hk : ∀ x, Continuous fun ε : ℝ => aff d ε x * Real.log (aff d ε x) := fun x =>
    Real.continuous_mul_log.comp (haff x)
  apply ContinuousAt.tendsto
  by_cases hs0 : s = 0
  · have hw : r * P = 0 := supp_weight hr hs h i j hs0
    rcases mul_eq_zero.1 hw with hr0 | hP0
    · have e : (fun ε => (aff d ε r * Real.log (aff d ε r) -
          aff d ε r * Real.log (aff d ε s)) * P) = fun _ => (0 : ℝ) := by
        funext ε; rw [hr0, hs0]; ring
      rw [e]; exact continuousAt_const
    · have e : (fun ε => (aff d ε r * Real.log (aff d ε r) -
          aff d ε r * Real.log (aff d ε s)) * P) = fun _ => (0 : ℝ) := by
        funext ε; rw [hP0, mul_zero]
      rw [e]; exact continuousAt_const
  · have hlog : ContinuousAt (fun ε => Real.log (aff d ε s)) 0 :=
      ContinuousAt.log (haff s).continuousAt (by simpa [aff] using hs0)
    exact (((hk r).continuousAt).sub ((haff r).continuousAt.mul hlog)).mul continuousAt_const

theorem pinch_le {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) {rho sigma : Mat d}
    (hr : IsDensityMatrix rho) (hs : IsDensityMatrix sigma) :
    relativeEntropy (pinch (U : Mat d) rho) (pinch (U : Mat d) sigma) ≤
      relativeEntropy rho sigma := by
  by_cases h : QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported rho sigma
  · have hd : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · have := hr.2; simp [Matrix.trace] at this
      · exact hd
    rw [relEnt_of_supp (pinch_supp U hr.1 hs.1 h), relEnt_of_supp h, EReal.coe_le_coe_iff]
    refine le_of_tendsto_of_tendsto (tendsto_reg (pinch_psd U hr.1) (pinch_psd U hs.1)
      (pinch_supp U hr.1 hs.1 h)) (tendsto_reg hr.1 hs.1 h) ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε
    rw [← pinch_reg, ← pinch_reg]
    exact posDef_case U (reg_posDef hd hε.1 hε.2.le hr.1) (reg_posDef hd hε.1 hε.2.le hs.1)
      (by rw [reg_trace hd ε hr.2, reg_trace hd ε hs.2])
  · simp only [relativeEntropy, if_neg h, le_top]

end PinAux

theorem rpl_main {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (rho sigma : Mat d) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    relativeEntropy
        ((U : Mat d) * Matrix.diagonal (fun i => ((U : Mat d)ᴴ * rho * (U : Mat d)) i i) *
          (U : Mat d)ᴴ)
        ((U : Mat d) * Matrix.diagonal (fun i => ((U : Mat d)ᴴ * sigma * (U : Mat d)) i i) *
          (U : Mat d)ᴴ) ≤
      relativeEntropy rho sigma :=
  PinAux.pinch_le U hrho hsigma

end QAlgorithms.Papers.Independent.Gap48.P40

open QAlgorithms.Papers.Independent.Gap48.P40 in
theorem solution {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (rho sigma : Mat d) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    relativeEntropy
        ((U : Mat d) * Matrix.diagonal (fun i => ((U : Mat d)ᴴ * rho * (U : Mat d)) i i) *
          (U : Mat d)ᴴ)
        ((U : Mat d) * Matrix.diagonal (fun i => ((U : Mat d)ᴴ * sigma * (U : Mat d)) i i) *
          (U : Mat d)ᴴ) ≤
      relativeEntropy rho sigma :=
  rpl_main U rho sigma hrho hsigma

end
