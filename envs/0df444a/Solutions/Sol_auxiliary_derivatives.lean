-- Prove2me | solution 1 for auxiliary_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T17:06:17.149584+00:00
-- url     : https://prove2.me/submissions/988563ae-96c1-4d41-a76b-70438c5cf5b3

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_HasseDerivatives
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_hasse_formulas




theorem solution (F : Type*) [Field F]
    (f : Polynomial F) (m d ℓ c : ℕ)
    (hfdeg : f.natDegree = m)
    (rj sj : Polynomial F) (hr : rj.natDegree ≤ d) (hs : sj.natDegree ≤ d)
    (k : ℕ) (hk : k ≤ ℓ) :
  ∃ rjk sjk : Polynomial F,
    hasseDerivOp F k (f^ℓ * rj) = rjk * f^(ℓ - k) ∧
    hasseDerivOp F k (f^(ℓ + c) * sj) = sjk * f^(ℓ + c - k) ∧
    rjk.natDegree ≤ d + k * (m - 1) ∧ sjk.natDegree ≤ d + k * (m - 1) :=
by
  by_cases hf0 : f = 0
  · subst hf0
    have hm0 : m = 0 := by
      simpa [Polynomial.natDegree_zero] using hfdeg.symm
    by_cases hk0 : k = 0
    · subst hk0
      refine ⟨rj, sj, ?_, ?_, ?_, ?_⟩
      · simp [hasseDerivOp, mul_comm]
      · simp [hasseDerivOp, mul_comm]
      · simpa [hm0]
      · simpa [hm0]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hℓpos : 0 < ℓ := lt_of_lt_of_le hkpos hk
      refine ⟨0, 0, ?_, ?_, ?_, ?_⟩
      · have hpow : (0 : Polynomial F) ^ ℓ = 0 := by
          have hne : ℓ ≠ 0 := ne_of_gt hℓpos
          simp [hne]
        simp [hasseDerivOp, hpow]
      · have hℓcpos : 0 < ℓ + c := lt_of_lt_of_le hℓpos (Nat.le_add_right _ _)
        have hpow : (0 : Polynomial F) ^ (ℓ + c) = 0 := by
          have hne : ℓ + c ≠ 0 := ne_of_gt hℓcpos
          simpa [hne] using (zero_pow (M₀ := Polynomial F) (n := ℓ + c) hne)
        simp [hasseDerivOp, hpow]
      · simp [hm0]
      · simp [hm0]
  · have hdeg_f_eq : Polynomial.degree f = (m : WithBot ℕ) := by
      simpa [hfdeg] using Polynomial.degree_eq_natDegree hf0
    obtain ⟨_, hℓ⟩ := hasse_formulas F k ℓ hk
    rcases hℓ rj f with ⟨hdiv_rj_core, hdeg_rj_core⟩
    have hdiv_rj : f ^ (ℓ - k) ∣ hasseDerivOp F k (f ^ ℓ * rj) := by
      simpa [mul_comm] using hdiv_rj_core
    have hkℓc : k ≤ ℓ + c := le_trans hk (Nat.le_add_right _ _)
    obtain ⟨_, hℓc⟩ := hasse_formulas F k (ℓ + c) hkℓc
    rcases hℓc sj f with ⟨hdiv_sj_core, hdeg_sj_core⟩
    have hdiv_sj : f ^ (ℓ + c - k) ∣ hasseDerivOp F k (f ^ (ℓ + c) * sj) := by
      simpa [mul_comm] using hdiv_sj_core
    set rjk : Polynomial F :=
      hasseDerivOp F k (f ^ ℓ * rj) / f ^ (ℓ - k) with hrjk_def
    set sjk : Polynomial F :=
      hasseDerivOp F k (f ^ (ℓ + c) * sj) / f ^ (ℓ + c - k) with hsjk_def
    have hr_eq : hasseDerivOp F k (f ^ ℓ * rj) = rjk * f ^ (ℓ - k) := by
      simpa [hrjk_def, mul_comm] using
        (EuclideanDomain.mul_div_cancel'
          (R := Polynomial F)
          (a := hasseDerivOp F k (f ^ ℓ * rj))
          (b := f ^ (ℓ - k)) (pow_ne_zero _ hf0) hdiv_rj).symm
    have hs_eq : hasseDerivOp F k (f ^ (ℓ + c) * sj) = sjk * f ^ (ℓ + c - k) := by
      simpa [hsjk_def, mul_comm] using
        (EuclideanDomain.mul_div_cancel'
          (R := Polynomial F)
          (a := hasseDerivOp F k (f ^ (ℓ + c) * sj))
          (b := f ^ (ℓ + c - k)) (pow_ne_zero _ hf0) hdiv_sj).symm
    have hdeg_rjk_match :
        Polynomial.degree rjk ≤
          (match
              Polynomial.degree rj + (k : WithBot ℕ) * Polynomial.degree f with
            | ⊥ => ⊥
            | some n => ((n - k : ℕ) : WithBot ℕ)) := by
      dsimp [rjk]
      rw [mul_comm (f ^ ℓ) rj]
      exact hdeg_rj_core
    have hdeg_sjk_match :
        Polynomial.degree sjk ≤
          (match
              Polynomial.degree sj + (k : WithBot ℕ) * Polynomial.degree f with
            | ⊥ => ⊥
            | some n => ((n - k : ℕ) : WithBot ℕ)) := by
      dsimp [sjk]
      rw [mul_comm (f ^ (ℓ + c)) sj]
      exact hdeg_sj_core
    have hdeg_rj_le_d : Polynomial.degree rj ≤ (d : WithBot ℕ) :=
      (Polynomial.natDegree_le_iff_degree_le).1 hr
    have hdeg_sj_le_d : Polynomial.degree sj ≤ (d : WithBot ℕ) :=
      (Polynomial.natDegree_le_iff_degree_le).1 hs
    let Ftrunc : WithBot ℕ → WithBot ℕ :=
      fun x => match x with | ⊥ => ⊥ | some n => ((n - k : ℕ) : WithBot ℕ)
    have hF_mono :
        ∀ {x y : WithBot ℕ}, x ≤ y → Ftrunc x ≤ Ftrunc y := by
      intro x y hxy
      cases x using WithBot.recBotCoe with
      | bot =>
          cases y using WithBot.recBotCoe with
          | bot => simp [Ftrunc]
          | coe _ => simp [Ftrunc]
      | coe a =>
          cases y using WithBot.recBotCoe with
          | bot =>
              have hxbot : ((a : ℕ) : WithBot ℕ) = (⊥ : WithBot ℕ) :=
                (le_bot_iff).1 hxy
              exact (WithBot.natCast_ne_bot (α := ℕ) a) hxbot |> False.elim
          | coe b =>
              have hab : a ≤ b := (WithBot.coe_le_coe).1 hxy
              have hsub : a - k ≤ b - k := Nat.sub_le_sub_right hab k
              exact (WithBot.coe_le_coe).2 hsub
    let x_rj : WithBot ℕ :=
      Polynomial.degree rj + (k : WithBot ℕ) * Polynomial.degree f
    let x_sj : WithBot ℕ :=
      Polynomial.degree sj + (k : WithBot ℕ) * Polynomial.degree f
    let y : WithBot ℕ :=
      (d : WithBot ℕ) + (k : WithBot ℕ) * Polynomial.degree f
    have hx_rj_le_y : x_rj ≤ y := by
      have :=
        add_le_add_left hdeg_rj_le_d ((k : WithBot ℕ) * Polynomial.degree f)
      exact this
    have hx_sj_le_y : x_sj ≤ y := by
      have :=
        add_le_add_left hdeg_sj_le_d ((k : WithBot ℕ) * Polynomial.degree f)
      exact this
    have hF_xrj_le_y : Ftrunc x_rj ≤ Ftrunc y := hF_mono hx_rj_le_y
    have hF_xsj_le_y : Ftrunc x_sj ≤ Ftrunc y := hF_mono hx_sj_le_y
    have hF_y_eq :
        Ftrunc y = ((d + k * m - k : ℕ) : WithBot ℕ) := by
      have hy : y = ((d + k * m : ℕ) : WithBot ℕ) := by
        simp [y, hdeg_f_eq, mul_comm]
      have hyF : Ftrunc y = Ftrunc ((d + k * m : ℕ) : WithBot ℕ) :=
        congrArg Ftrunc hy
      exact hyF
    have hdeg_rjk_le :
        Polynomial.degree rjk ≤ ((d + k * m - k : ℕ) : WithBot ℕ) := by
      rw [hF_y_eq] at hF_xrj_le_y
      exact le_trans hdeg_rjk_match hF_xrj_le_y
    have hdeg_sjk_le :
        Polynomial.degree sjk ≤ ((d + k * m - k : ℕ) : WithBot ℕ) := by
      rw [hF_y_eq] at hF_xsj_le_y
      exact le_trans hdeg_sjk_match hF_xsj_le_y
    have hnat_rjk_le : rjk.natDegree ≤ d + k * m - k :=
      (Polynomial.natDegree_le_iff_degree_le).2 hdeg_rjk_le
    have hnat_sjk_le : sjk.natDegree ≤ d + k * m - k :=
      (Polynomial.natDegree_le_iff_degree_le).2 hdeg_sjk_le
    have h_nat_ineq : d + k * m - k ≤ d + k * (m - 1) := by
      cases m with
      | zero => simp
      | succ m' =>
          have : d + k * Nat.succ m' - k = d + k * m' := by
            simpa [Nat.mul_succ, Nat.add_assoc] using
              (Nat.add_sub_cancel (d + k * m') k)
          simp [this]
    refine ⟨rjk, sjk, hr_eq, hs_eq, ?_, ?_⟩
    · exact le_trans hnat_rjk_le h_nat_ineq
    · exact le_trans hnat_sjk_le h_nat_ineq
