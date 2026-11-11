-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P36.lhs_invariant
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T15:32:13.175592+00:00
-- url     : https://prove2.me/submissions/564e4e7a-454d-40bd-b935-3a17b0f262ca

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P36
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Module.BigOperators

set_option autoImplicit false

noncomputable section




open scoped BigOperators ComplexOrder MatrixOrder
open QAlgorithms.Papers.Independent.Intakethird100.P36

namespace Prove2Me.S12.Steering

variable {d r s df rf sf m : ℕ}

/-- Averaging a family of equal input sums returns any one of those sums. -/
lemma asm_bobTotal_eq_sum (rho : AssemblageBlocks d r s) (hs : 0 < s)
    (hns : ∀ x y, ∑ a, rho a x = ∑ a, rho a y) (x : Fin s) :
    bobTotal rho = ∑ a, rho a x := by
  classical
  have hsc : (s : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs)
  unfold bobTotal
  simp_rw [hns _ x]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ s, smul_smul, inv_mul_cancel₀ hsc, one_smul]

/-- The reduced matrix of an assemblage is positive semidefinite. -/
lemma asm_bobTotal_posSemidef (rho : AssemblageBlocks d r s)
    (hrho : IsAssemblage rho) : (bobTotal rho).PosSemidef := by
  classical
  rcases hrho with ⟨_, _, hs, hpos, hns, _, _⟩
  rw [asm_bobTotal_eq_sum rho hs hns ⟨0, hs⟩]
  exact Matrix.posSemidef_sum _ (fun a _ => hpos a ⟨0, hs⟩)

/-- Positivity of the complex trace also implies positivity of its real part. -/
lemma asm_trace_re_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) : 0 ≤ A.trace.re :=
  (RCLike.nonneg_iff.mp hA.trace_nonneg).1

/-- Cyclic trace converts a product of positive matrices to a positive congruence. -/
lemma asm_trace_mul_re_nonneg {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [hC, Matrix.star_eq_conjTranspose, ← Matrix.mul_assoc,
    Matrix.trace_mul_cycle A C.conjTranspose C]
  exact asm_trace_re_nonneg (hA.mul_mul_conjTranspose_same C)

/-- A classical output law leaves the corresponding branch total unchanged. -/
lemma asm_branch_sum (P : SteeringProtocol d r s df rf sf m)
    (rho : AssemblageBlocks d r s) (hrho : IsAssemblage rho)
    (w : Fin m) (xf : Fin sf) :
    ∑ af, protocolBranch P rho w af xf =
      P.kraus w * bobTotal rho * (P.kraus w).conjTranspose := by
  classical
  rcases hrho with ⟨_, _, hs, _, hns, _, _⟩
  have hout (a : Fin r) (x : Fin s) :
      (∑ af, (P.output w af a x xf : ℂ)) = 1 := by
    exact_mod_cast (P.output_law w a x xf).2
  have hin : (∑ x, (P.input w xf x : ℂ)) = 1 := by
    exact_mod_cast (P.input_law w xf).2
  have hcollapse (a : Fin r) (x : Fin s) :
      (∑ af, (P.output w af a x xf : ℂ) •
        ((P.input w xf x : ℂ) • bobStep P rho w a x)) =
      (P.input w xf x : ℂ) • bobStep P rho w a x := by
    rw [← Finset.sum_smul, hout, one_smul]
  have hsum (x : Fin s) :
      (∑ a, bobStep P rho w a x) =
      P.kraus w * bobTotal rho * (P.kraus w).conjTranspose := by
    simp only [bobStep, ← Matrix.sum_mul, ← Matrix.mul_sum]
    rw [← asm_bobTotal_eq_sum rho hs hns x]
  calc
    ∑ af, protocolBranch P rho w af xf =
        ∑ x, ∑ a, ∑ af, (P.output w af a x xf : ℂ) •
          ((P.input w xf x : ℂ) • bobStep P rho w a x) := by
      unfold protocolBranch
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = ∑ x, (P.input w xf x : ℂ) • (∑ a, bobStep P rho w a x) := by
      simp_rw [hcollapse, Finset.smul_sum]
    _ = ∑ x, (P.input w xf x : ℂ) •
        (P.kraus w * bobTotal rho * (P.kraus w).conjTranspose) := by
      simp_rw [hsum]
    _ = P.kraus w * bobTotal rho * (P.kraus w).conjTranspose := by
      rw [← Finset.sum_smul, hin, one_smul]

/-- Every output input has the same sum of Kraus-transformed reduced matrices. -/
lemma asm_action_sum (P : SteeringProtocol d r s df rf sf m)
    (rho : AssemblageBlocks d r s) (hrho : IsAssemblage rho) (xf : Fin sf) :
    ∑ af, protocolAction P rho af xf =
      ∑ w, P.kraus w * bobTotal rho * (P.kraus w).conjTranspose := by
  classical
  unfold protocolAction
  rw [Finset.sum_comm]
  simp_rw [asm_branch_sum P rho hrho]

/-- The total output matrix is the Kraus map of the input total matrix. -/
lemma asm_action_bobTotal (P : SteeringProtocol d r s df rf sf m)
    (rho : AssemblageBlocks d r s) (hrho : IsAssemblage rho) :
    bobTotal (protocolAction P rho) =
      ∑ w, P.kraus w * bobTotal rho * (P.kraus w).conjTranspose := by
  have hsf : 0 < sf := P.dimensions.2.2.2.2.2
  have hns : ∀ x y, ∑ a, protocolAction P rho a x =
      ∑ a, protocolAction P rho a y := by
    intro x y
    rw [asm_action_sum P rho hrho x, asm_action_sum P rho hrho y]
  rw [asm_bobTotal_eq_sum (protocolAction P rho) hsf hns ⟨0, hsf⟩,
    asm_action_sum P rho hrho]

/-- Trace-decreasing Kraus maps cannot increase an assemblage's mass. -/
lemma asm_action_mass_le (P : SteeringProtocol d r s df rf sf m)
    (rho : AssemblageBlocks d r s) (hrho : IsAssemblage rho) :
    assemblageMass (protocolAction P rho) ≤ assemblageMass rho := by
  classical
  have htrace : assemblageMass (protocolAction P rho) =
      (bobTotal rho * (∑ w, (P.kraus w).conjTranspose * P.kraus w)).trace.re := by
    unfold assemblageMass
    rw [asm_action_bobTotal P rho hrho, Matrix.mul_sum]
    simp only [Matrix.trace_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro w _
    apply congrArg Complex.re
    calc
      (P.kraus w * bobTotal rho * (P.kraus w).conjTranspose).trace =
          ((P.kraus w).conjTranspose * P.kraus w * bobTotal rho).trace :=
        Matrix.trace_mul_cycle _ _ _
      _ = (bobTotal rho * ((P.kraus w).conjTranspose * P.kraus w)).trace :=
        Matrix.trace_mul_comm _ _
  have hslack := asm_trace_mul_re_nonneg
    (asm_bobTotal_posSemidef rho hrho) P.trace_decreasing
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re] at hslack
  change 0 ≤ assemblageMass rho -
    (bobTotal rho * (∑ w, (P.kraus w).conjTranspose * P.kraus w)).trace.re at hslack
  rw [← htrace] at hslack
  exact sub_nonneg.mp hslack

/-- A steering protocol preserves all assemblage conditions, including mass bounds. -/
theorem action_isAssemblage (P : SteeringProtocol d r s df rf sf m)
    (rho : AssemblageBlocks d r s) (hrho : IsAssemblage rho) :
    IsAssemblage (protocolAction P rho) := by
  classical
  have hmass := asm_action_mass_le P rho hrho
  have htotal := asm_action_bobTotal P rho hrho
  have hsums := asm_action_sum P rho hrho
  have hR := asm_bobTotal_posSemidef rho hrho
  rcases hrho with ⟨_, _, _, hblocks, _, _, hmass_one⟩
  refine ⟨P.dimensions.2.2.2.1, P.dimensions.2.2.2.2.1,
    P.dimensions.2.2.2.2.2, ?_, ?_, ?_, hmass.trans hmass_one⟩
  · intro af xf
    unfold protocolAction protocolBranch
    apply Matrix.posSemidef_sum
    intro w _
    apply Matrix.posSemidef_sum
    intro x _
    apply Matrix.posSemidef_sum
    intro a _
    exact (((hblocks a x).mul_mul_conjTranspose_same (P.kraus w)).smul
      (RCLike.ofReal_nonneg.mpr ((P.input_law w xf).1 x))).smul
      (RCLike.ofReal_nonneg.mpr ((P.output_law w a x xf).1 af))
  · intro x y
    rw [hsums x, hsums y]
  · unfold assemblageMass
    rw [htotal]
    apply asm_trace_re_nonneg
    exact Matrix.posSemidef_sum _
      (fun w _ => hR.mul_mul_conjTranspose_same (P.kraus w))

end Prove2Me.S12.Steering



open scoped BigOperators ComplexConjugate ComplexOrder Matrix

namespace Prove2Me.S12.Steering

open QAlgorithms.Papers.Independent.Intakethird100.P36
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable

variable {d r s : ℕ}

theorem raw_trace_re_nonneg {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) :
    0 ≤ A.trace.re :=
  (RCLike.nonneg_iff.mp hA.trace_nonneg).1

theorem raw_trace_eq_re {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) :
    A.trace = (A.trace.re : ℂ) := by
  have him : A.trace.im = 0 := (RCLike.nonneg_iff.mp hA.trace_nonneg).2
  apply Complex.ext <;> simp [him]

theorem raw_eq_zero_of_trace_re_eq_zero {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosSemidef) (hz : A.trace.re = 0) : A = 0 := by
  apply hA.trace_eq_zero_iff.mp
  rw [raw_trace_eq_re hA, hz, Complex.ofReal_zero]

def raw_defaultDensity (hd : 0 < d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun i => if i = (⟨0, hd⟩ : Fin d) then 1 else 0)

theorem raw_defaultDensity_isDensity (hd : 0 < d) :
    QAlgorithms.IsDensityMatrix (raw_defaultDensity hd) := by
  refine ⟨Matrix.PosSemidef.diagonal ?_, ?_⟩
  · intro i
    dsimp
    by_cases hi : i = (⟨0, hd⟩ : Fin d) <;> simp [hi]
  · simp [raw_defaultDensity, Matrix.trace_diagonal]

def raw_defaultLaw (hr : 0 < r) : Fin r → ℝ :=
  fun a => if a = (⟨0, hr⟩ : Fin r) then 1 else 0

theorem raw_defaultLaw_isLaw (hr : 0 < r) : IsLaw (raw_defaultLaw hr) := by
  constructor
  · intro a
    by_cases ha : a = (⟨0, hr⟩ : Fin r) <;> simp [raw_defaultLaw, ha]
  · simp [raw_defaultLaw]

/-- A zero-trace PSD branch receives a fixed density matrix and zero weight. -/
def raw_normalizedState (hd : 0 < d) (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  if A.trace.re = 0 then raw_defaultDensity hd else (((A.trace.re)⁻¹ : ℝ) : ℂ) • A

theorem raw_normalizedState_isDensity (hd : 0 < d)
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) :
    QAlgorithms.IsDensityMatrix (raw_normalizedState hd A) := by
  by_cases hz : A.trace.re = 0
  · rw [raw_normalizedState, if_pos hz]
    exact raw_defaultDensity_isDensity hd
  · rw [raw_normalizedState, if_neg hz]
    refine ⟨hA.smul ?_, ?_⟩
    · exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr (raw_trace_re_nonneg hA))
    · rw [Matrix.trace_smul, raw_trace_eq_re hA]
      change (((A.trace.re)⁻¹ : ℝ) : ℂ) * (A.trace.re : ℂ) = 1
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ hz, Complex.ofReal_one]

theorem raw_rescale_normalizedState (hd : 0 < d)
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) :
    (A.trace.re : ℂ) • raw_normalizedState hd A = A := by
  by_cases hz : A.trace.re = 0
  · rw [raw_normalizedState, if_pos hz]
    simp [hz, raw_eq_zero_of_trace_re_eq_zero hA hz]
  · rw [raw_normalizedState, if_neg hz, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hz,
      Complex.ofReal_one, one_smul]

/-- The total matrix of a raw hidden-state decomposition is its sum of hidden matrices. -/
theorem raw_bobTotal_eq_sum {H : Type*} [Fintype H]
    (rho : AssemblageBlocks d r s) (hs : 0 < s)
    (A : H → Matrix (Fin d) (Fin d) ℂ)
    (q : H → Fin s → Fin r → ℝ)
    (hq : ∀ h x, IsLaw (q h x))
    (heq : ∀ a x, rho a x = ∑ h, (q h x a : ℂ) • A h) :
    bobTotal rho = ∑ h, A h := by
  classical
  have hqsum (h : H) (x : Fin s) : ∑ a, (q h x a : ℂ) = 1 := by
    exact_mod_cast (hq h x).2
  have hsum (x : Fin s) : ∑ a, rho a x = ∑ h, A h := by
    simp_rw [heq]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    rw [← Finset.sum_smul, hqsum, one_smul]
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  unfold bobTotal
  simp_rw [hsum]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hs0, one_smul]

theorem raw_mass_eq_sum_trace {H : Type*} [Fintype H]
    (rho : AssemblageBlocks d r s) (hs : 0 < s)
    (A : H → Matrix (Fin d) (Fin d) ℂ)
    (q : H → Fin s → Fin r → ℝ)
    (hq : ∀ h x, IsLaw (q h x))
    (heq : ∀ a x, rho a x = ∑ h, (q h x a : ℂ) • A h) :
    assemblageMass rho = ∑ h, (A h).trace.re := by
  unfold assemblageMass
  rw [raw_bobTotal_eq_sum rho hs A q hq heq]
  simp only [Matrix.trace_sum, Complex.re_sum]

/-- Convert finitely many PSD hidden matrices into the platform's normalized-law model.
The supplied assemblage validity gives the physical dimensions and mass bound.
Both an empty hidden alphabet and zero output mass are covered. -/
theorem finiteLHS_of_psd_decomposition
    (rho : AssemblageBlocks d r s) (hrho : IsAssemblage rho)
    {H : Type*} [Fintype H]
    (A : H → Matrix (Fin d) (Fin d) ℂ)
    (q : H → Fin s → Fin r → ℝ)
    (hA : ∀ h, (A h).PosSemidef)
    (hq : ∀ h x, IsLaw (q h x))
    (heq : ∀ a x, rho a x = ∑ h, (q h x a : ℂ) • A h) :
    HasFiniteLHSModel rho := by
  classical
  refine ⟨hrho, ?_⟩
  rcases hrho with ⟨hd, hr, hs, hblocks, hsignal, hmass_nonneg, hmass_le⟩
  have hmass := raw_mass_eq_sum_trace rho hs A q hq heq
  have hnonneg (h : H) : 0 ≤ (A h).trace.re := raw_trace_re_nonneg (hA h)
  by_cases hz : assemblageMass rho = 0
  · have hsumzero : (∑ h, (A h).trace.re) = 0 := hmass.symm.trans hz
    have hAz (h : H) : A h = 0 := by
      apply raw_eq_zero_of_trace_re_eq_zero (hA h)
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun h _ => hnonneg h)).mp hsumzero h
        (Finset.mem_univ h)
    have hrhoz (a : Fin r) (x : Fin s) : rho a x = 0 := by
      rw [heq]
      simp [hAz]
    refine ⟨1, (fun _ => 1), (fun _ => raw_defaultDensity hd),
      (fun _ _ => raw_defaultLaw hr), ?_, ?_, ?_, ?_⟩
    · constructor <;> simp
    · intro l
      exact raw_defaultDensity_isDensity hd
    · intro l x
      exact raw_defaultLaw_isLaw hr
    · intro a x
      rw [hrhoz]
      simp [hz]
  · let e := Fintype.equivFin H
    refine ⟨Fintype.card H,
      (fun l => (A (e.symm l)).trace.re / assemblageMass rho),
      (fun l => raw_normalizedState hd (A (e.symm l))),
      (fun l => q (e.symm l)), ?_, ?_, ?_, ?_⟩
    · constructor
      · intro l
        exact div_nonneg (hnonneg _) hmass_nonneg
      · calc
          (∑ l, (A (e.symm l)).trace.re / assemblageMass rho) =
              ∑ h, (A h).trace.re / assemblageMass rho :=
            e.symm.sum_comp (fun h => (A h).trace.re / assemblageMass rho)
          _ = (∑ h, (A h).trace.re) / assemblageMass rho :=
            (Finset.sum_div _ _ _).symm
          _ = 1 := by rw [← hmass, div_self hz]
    · intro l
      exact raw_normalizedState_isDensity hd (hA _)
    · intro l x
      exact hq _ x
    · intro a x
      calc
        rho a x = ∑ h, (q h x a : ℂ) • A h := heq a x
        _ = ∑ l, (q (e.symm l) x a : ℂ) • A (e.symm l) :=
          (e.symm.sum_comp (fun h => (q h x a : ℂ) • A h)).symm
        _ = ∑ l, ((assemblageMass rho *
              ((A (e.symm l)).trace.re / assemblageMass rho) * q (e.symm l) x a : ℝ) : ℂ) •
            raw_normalizedState hd (A (e.symm l)) := by
          apply Finset.sum_congr rfl
          intro l _
          have hcoef : assemblageMass rho *
                ((A (e.symm l)).trace.re / assemblageMass rho) * q (e.symm l) x a =
              q (e.symm l) x a * (A (e.symm l)).trace.re := by
            rw [mul_div_cancel₀ _ hz, mul_comm]
          rw [hcoef, Complex.ofReal_mul, mul_smul,
            raw_rescale_normalizedState hd (hA _)]

end Prove2Me.S12.Steering



namespace Prove2Me.S12.Steering

open QAlgorithms.Papers.Independent.Intakethird100.P36
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open scoped BigOperators ComplexConjugate ComplexOrder Matrix

variable {d r s df rf sf m n : ℕ}

/-- The response of a fixed hidden state after both classical wirings. -/
def wiredResponse (P : SteeringProtocol d r s df rf sf m)
    (q : Fin n → Fin s → Fin r → ℝ)
    (j : Fin m × Fin n) (xf : Fin sf) (af : Fin rf) : ℝ :=
  ∑ x, ∑ a, (P.input j.1 xf x * q j.2 x a) * P.output j.1 af a x xf

theorem wiredResponse_law (P : SteeringProtocol d r s df rf sf m)
    (q : Fin n → Fin s → Fin r → ℝ) (hq : ∀ l x, IsLaw (q l x))
    (j : Fin m × Fin n) (xf : Fin sf) : IsLaw (wiredResponse P q j xf) := by
  constructor
  · intro af
    apply Finset.sum_nonneg
    intro x hx
    apply Finset.sum_nonneg
    intro a ha
    exact mul_nonneg (mul_nonneg ((P.input_law j.1 xf).1 x) ((hq j.2 x).1 a))
      ((P.output_law j.1 a x xf).1 af)
  · change (∑ af, ∑ x, ∑ a,
      (P.input j.1 xf x * q j.2 x a) * P.output j.1 af a x xf) = 1
    calc
      _ = ∑ x, ∑ a, (P.input j.1 xf x * q j.2 x a) *
          ∑ af, P.output j.1 af a x xf := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ = ∑ x, P.input j.1 xf x := by
        apply Finset.sum_congr rfl
        intro x hx
        have hout : ∀ a, ∑ af, P.output j.1 af a x xf = 1 :=
          fun a => (P.output_law j.1 a x xf).2
        simp only [hout, mul_one]
        rw [← Finset.mul_sum, (hq j.2 x).2, mul_one]
      _ = 1 := (P.input_law j.1 xf).2

/-- Expand a finite hidden-state model through the exact protocol action. -/
theorem protocol_raw_decomposition (P : SteeringProtocol d r s df rf sf m)
    (rho : AssemblageBlocks d r s) (t : ℝ) (p : Fin n → ℝ)
    (xi : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (q : Fin n → Fin s → Fin r → ℝ)
    (heq : ∀ a x, rho a x = ∑ l, ((t * p l * q l x a : ℝ) : ℂ) • xi l)
    (af : Fin rf) (xf : Fin sf) :
    protocolAction P rho af xf =
      ∑ j : Fin m × Fin n, (wiredResponse P q j xf af : ℂ) •
        (((t * p j.2 : ℝ) : ℂ) •
          (P.kraus j.1 * xi j.2 * (P.kraus j.1)ᴴ)) := by
  simp only [protocolAction, protocolBranch, bobStep, heq,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Finset.smul_sum, smul_smul, ← mul_assoc]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro w hw
  calc
    _ = ∑ l, ∑ x, ∑ a,
        ((P.output w af a x xf : ℂ) * (P.input w xf x : ℂ) *
          ((t * p l * q l x a : ℝ) : ℂ)) •
            (P.kraus w * xi l * (P.kraus w)ᴴ) := by
      calc
        _ = ∑ x, ∑ l, ∑ a,
          ((P.output w af a x xf : ℂ) * (P.input w xf x : ℂ) *
            ((t * p l * q l x a : ℝ) : ℂ)) •
              (P.kraus w * xi l * (P.kraus w)ᴴ) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l hl
      simp only [wiredResponse, Complex.ofReal_sum, Finset.sum_smul,
        smul_smul, Complex.ofReal_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro a ha
      congr 1
      ac_rfl

end Prove2Me.S12.Steering



namespace Prove2Me.S12.Steering

open QAlgorithms.Papers.Independent.Intakethird100.P36
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open scoped BigOperators ComplexConjugate ComplexOrder

variable {d r s : ℕ}

theorem normalize_bobTotal_smul (rho : AssemblageBlocks d r s) (c : ℂ) :
    bobTotal (fun a x => c • rho a x) = c • bobTotal rho := by
  simp only [bobTotal, ← Finset.smul_sum, smul_smul]
  congr 1
  exact mul_comm _ _

theorem normalize_mass_smul (rho : AssemblageBlocks d r s) (c : ℝ) :
    assemblageMass (fun a x => (c : ℂ) • rho a x) = c * assemblageMass rho := by
  unfold assemblageMass
  rw [normalize_bobTotal_smul, Matrix.trace_smul]
  simp [smul_eq_mul, Complex.mul_re]

theorem normalize_mass_one (rho : AssemblageBlocks d r s)
    (ht : 0 < assemblageMass rho) : assemblageMass (normalizeAssemblage rho) = 1 := by
  have heq : normalizeAssemblage rho =
      fun a x => (((assemblageMass rho)⁻¹ : ℝ) : ℂ) • rho a x := by
    funext a x
    simp only [normalizeAssemblage, Complex.ofReal_inv]
  rw [heq, normalize_mass_smul, inv_mul_cancel₀ ht.ne']

theorem normalize_isAssemblage (rho : AssemblageBlocks d r s)
    (hrho : IsAssemblage rho) (ht : 0 < assemblageMass rho) :
    IsAssemblage (normalizeAssemblage rho) := by
  rcases hrho with ⟨hd, hr, hs, hpsd, hns, ht0, ht1⟩
  have hc : 0 ≤ (assemblageMass rho : ℂ)⁻¹ := by
    exact_mod_cast (inv_nonneg.mpr ht.le)
  refine ⟨hd, hr, hs, ?_, ?_, ?_, ?_⟩
  · intro a x
    exact (hpsd a x).smul hc
  · intro x y
    simpa only [normalizeAssemblage, ← Finset.smul_sum] using
      congrArg (fun M => (assemblageMass rho : ℂ)⁻¹ • M) (hns x y)
  · simpa only [normalize_mass_one rho ht] using (zero_le_one : (0 : ℝ) ≤ 1)
  · simpa only [normalize_mass_one rho ht] using (le_refl (1 : ℝ))

theorem normalize_finiteLHS (rho : AssemblageBlocks d r s)
    (hrho : HasFiniteLHSModel rho) (ht : 0 < assemblageMass rho) :
    IsNormalized (normalizeAssemblage rho) ∧ HasFiniteLHSModel (normalizeAssemblage rho) := by
  have hasm := normalize_isAssemblage rho hrho.1 ht
  have hmass := normalize_mass_one rho ht
  refine ⟨⟨hasm, hmass⟩, hasm, ?_⟩
  rcases hrho.2 with ⟨n, p, xi, q, hp, hxi, hq, heq⟩
  refine ⟨n, p, xi, q, hp, hxi, hq, ?_⟩
  intro a x
  change (assemblageMass rho : ℂ)⁻¹ • rho a x = _
  rw [heq a x, Finset.smul_sum, hmass]
  have htc : (assemblageMass rho : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  apply Finset.sum_congr rfl
  intro l hl
  simp only [smul_smul, Complex.ofReal_mul, Complex.ofReal_one,
    ← mul_assoc, inv_mul_cancel₀ htc, one_mul]

end Prove2Me.S12.Steering

open QAlgorithms.Papers.Independent.Intakethird100.P36
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open Prove2Me.S12.Steering
open scoped BigOperators ComplexConjugate ComplexOrder Matrix

variable {d r s df rf sf m : ℕ}

theorem solution (P : SteeringProtocol d r s df rf sf m)
    (rho : AssemblageBlocks d r s) (hrho : HasFiniteLHSModel rho) :
    HasFiniteLHSModel (protocolAction P rho) ∧
    (0 < assemblageMass (protocolAction P rho) →
      IsNormalized (normalizeAssemblage (protocolAction P rho)) ∧
      HasFiniteLHSModel (normalizeAssemblage (protocolAction P rho))) := by
  have hout : HasFiniteLHSModel (protocolAction P rho) := by
    have hasm := action_isAssemblage P rho hrho.1
    have ht : 0 ≤ assemblageMass rho := hrho.1.2.2.2.2.2.1
    rcases hrho.2 with ⟨n, p, xi, q, hp, hxi, hq, heq⟩
    let A : Fin m × Fin n → Matrix (Fin df) (Fin df) ℂ :=
      fun j => ((assemblageMass rho * p j.2 : ℝ) : ℂ) •
        (P.kraus j.1 * xi j.2 * (P.kraus j.1)ᴴ)
    refine finiteLHS_of_psd_decomposition (protocolAction P rho) hasm A
      (wiredResponse P q) ?_ ?_ ?_
    · intro j
      apply ((hxi j.2).1.mul_mul_conjTranspose_same (P.kraus j.1)).smul
      exact_mod_cast mul_nonneg ht (hp.1 j.2)
    · exact wiredResponse_law P q hq
    · intro af xf
      exact protocol_raw_decomposition P rho (assemblageMass rho) p xi q heq af xf
  exact ⟨hout, fun hmass => normalize_finiteLHS (protocolAction P rho) hout hmass⟩

#print axioms solution
