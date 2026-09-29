-- Prove2me | solution 1 for PowerSeries.exists_bijective_residue_reduction_dualNumber_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/838a8c83-aaaf-54e8-923a-63460300c787

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_exists_bijective_residue_reduction_dualNumber_of_isDiscreteValuationRing

set_option autoImplicit false

open IsLocalRing PowerSeries

namespace PSRingFacts

variable (O : Type) [CommRing O] [IsLocalRing O]

theorem mem_maximalIdeal_iff (f : PowerSeries O) : f ∈ maximalIdeal (PowerSeries O) ↔ constantCoeff f ∈ maximalIdeal O := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_iff_constantCoeff]

theorem coeff_one_mul' (f g : PowerSeries O) : coeff 1 (f * g) = coeff 0 f * coeff 1 g + coeff 1 f * coeff 0 g := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]

noncomputable def tauTilde : PowerSeries O →+* DualNumber (ResidueField O) where
  toFun f := TrivSqZeroExt.inl (residue O (coeff 0 f)) + TrivSqZeroExt.inr (residue O (coeff 1 f))
  map_one' := by
    apply TrivSqZeroExt.ext
    · simp [coeff_zero_eq_constantCoeff_apply]
    · simp [coeff_one, TrivSqZeroExt.snd_one]
  map_mul' f g := by
    apply TrivSqZeroExt.ext
    · simp [coeff_zero_eq_constantCoeff_apply, TrivSqZeroExt.fst_mul]
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, TrivSqZeroExt.snd_mul,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, smul_eq_mul, op_smul_eq_mul,
        coeff_one_mul', map_add, map_mul]
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_add' f g := by
    apply TrivSqZeroExt.ext
    · simp [add_comm, add_left_comm]
    · simp [add_comm, add_left_comm]

theorem tauTilde_apply (f : PowerSeries O) :
    tauTilde O f = TrivSqZeroExt.inl (residue O (coeff 0 f)) + TrivSqZeroExt.inr (residue O (coeff 1 f)) := rfl

@[scoped simp] theorem fst_tauTilde (f : PowerSeries O) : (tauTilde O f).fst = residue O (coeff 0 f) := by
  simp [tauTilde_apply]

@[scoped simp] theorem snd_tauTilde (f : PowerSeries O) : (tauTilde O f).snd = residue O (coeff 1 f) := by
  simp [tauTilde_apply]

theorem tauTilde_C (a : O) : tauTilde O (C a) = algebraMap (ResidueField O) (DualNumber (ResidueField O)) (residue O a) := by
  apply TrivSqZeroExt.ext
  · simp [TrivSqZeroExt.algebraMap_eq_inl, coeff_zero_C]
  · simp [TrivSqZeroExt.algebraMap_eq_inl, coeff_C]

theorem tauTilde_X : tauTilde O X = DualNumber.eps := by
  apply TrivSqZeroExt.ext
  · simp [coeff_zero_X, DualNumber.fst_eps]
  · simp [coeff_one_X, DualNumber.snd_eps]

theorem fst_tauTilde_eq_zero {f : PowerSeries O} (hf : f ∈ maximalIdeal (PowerSeries O)) : (tauTilde O f).fst = 0 := by
  rw [fst_tauTilde, IsLocalRing.residue_eq_zero_iff, coeff_zero_eq_constantCoeff_apply]
  exact (mem_maximalIdeal_iff O f).mp hf

theorem tauTilde_eq_zero_of_mem_sq {f : PowerSeries O} (hf : f ∈ maximalIdeal (PowerSeries O) ^ (1 + 1)) : tauTilde O f = 0 := by
  rw [show (1 + 1 : ℕ) = 2 from rfl, pow_two] at hf
  refine Submodule.mul_induction_on hf (fun x hx y hy => ?_) (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
  rw [map_mul]
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, fst_tauTilde_eq_zero O hx, zero_mul, TrivSqZeroExt.fst_zero]
  · rw [TrivSqZeroExt.snd_mul, fst_tauTilde_eq_zero O hx, fst_tauTilde_eq_zero O hy, TrivSqZeroExt.snd_zero]
    simp

theorem decomp (f : PowerSeries O) : f = C (coeff 0 f) + X * C (coeff 1 f) + X * (X * mk fun p => coeff (p + 2) f) := by
  ext n
  rcases n with _ | _ | n
  · simp
  · simp [coeff_succ_X_mul, coeff_C]
  · simp only [map_add, map_mul, coeff_C, coeff_succ_X_mul, coeff_mk]
    simp

theorem mul_mem_sq {f g : PowerSeries O} (h0 : coeff 0 f ∈ maximalIdeal O) (h1 : coeff 1 f ∈ maximalIdeal O)
    (hg : g ∈ maximalIdeal (PowerSeries O)) : f * g ∈ maximalIdeal (PowerSeries O) ^ (1 + 1) := by
  have hC0 : C (coeff 0 f) ∈ maximalIdeal (PowerSeries O) := (mem_maximalIdeal_iff O _).mpr (by rwa [constantCoeff_C])
  have hC1 : C (coeff 1 f) ∈ maximalIdeal (PowerSeries O) := (mem_maximalIdeal_iff O _).mpr (by rwa [constantCoeff_C])
  have hXm : (X : PowerSeries O) ∈ maximalIdeal (PowerSeries O) := (mem_maximalIdeal_iff O _).mpr (by rw [constantCoeff_X]; exact (maximalIdeal O).zero_mem)
  rw [show (1 + 1 : ℕ) = 2 from rfl, pow_two, decomp O f, add_mul, add_mul]
  refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_mul hC0 hg) ?_) ?_
  · exact Ideal.mul_mem_mul (Ideal.mul_mem_right _ _ hXm) hg
  · rw [mul_assoc]
    exact Ideal.mul_mem_mul hXm (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hXm))

end PSRingFacts
p2m_reactivate "P2MW.S_PowerSeries_exists_bijective_residue_reduction_dualNumber_of_isDiscreteValuationRing.PSRingFacts"

open PSRingFacts

theorem solution
    (O : Type) [CommRing O] [IsLocalRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    ∃ (ι₀ : (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (0 + 1)) →+* ResidueField O) (hι₀ : Function.Bijective ι₀)
      (hι₀O : ι₀.comp ((Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (0 + 1))).comp (algebraMap O (PowerSeries O))) = residue O)
      (π : ∀ n : ℕ, (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (n + 1 + 1)) →+* (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (n + 1)))
      (hπ : ∀ n, (π n).comp (Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (n + 1 + 1))) = Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (n + 1)))
      (τ : (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (1 + 1)) →+* DualNumber (ResidueField O)),
      τ.comp ((Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1))).comp (algebraMap O (PowerSeries O))) =
          (algebraMap (ResidueField O) (DualNumber (ResidueField O))).comp (residue O) ∧
      τ (Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1)) PowerSeries.X) = DualNumber.eps ∧
      Function.Surjective τ ∧
      RingHom.ker τ * (maximalIdeal (PowerSeries O)).map (Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1))) = ⊥ ∧
      (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)).toRingHom.comp τ = ι₀.comp (π 0) ∧
      ∀ τ' : (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (1 + 1)) →+* DualNumber (ResidueField O),
        τ'.comp ((Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1))).comp (algebraMap O (PowerSeries O))) =
            (algebraMap (ResidueField O) (DualNumber (ResidueField O))).comp (residue O) →
        τ' (Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1)) PowerSeries.X) = DualNumber.eps →
        τ' = τ := by
  classical

  have hker0 : ∀ f ∈ maximalIdeal (PowerSeries O) ^ (0 + 1), (residue O).comp (constantCoeff (R := O)) f = 0 := by
    intro f hf
    rw [zero_add, pow_one] at hf
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
    exact (mem_maximalIdeal_iff O f).mp hf
  let ι₀ : (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (0 + 1)) →+* ResidueField O := Ideal.Quotient.lift _ ((residue O).comp (constantCoeff (R := O))) hker0
  have hι₀mk : ∀ f, ι₀ (Ideal.Quotient.mk _ f) = residue O (constantCoeff f) := fun f => Ideal.Quotient.lift_mk _ _ _
  have hι₀ : Function.Bijective ι₀ := by
    constructor
    · rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
      intro x hx
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [hι₀mk, IsLocalRing.residue_eq_zero_iff] at hx
      rw [Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one]
      exact (mem_maximalIdeal_iff O f).mpr hx
    · intro y
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      exact ⟨Ideal.Quotient.mk _ (C a), by rw [hι₀mk, constantCoeff_C]⟩
  have hι₀O : ι₀.comp ((Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (0 + 1))).comp (algebraMap O (PowerSeries O))) = residue O := by
    ext a
    rw [RingHom.comp_apply, RingHom.comp_apply, hι₀mk, show algebraMap O (PowerSeries O) a = C a from rfl, constantCoeff_C]

  have hle : ∀ n : ℕ, maximalIdeal (PowerSeries O) ^ (n + 1 + 1) ≤ maximalIdeal (PowerSeries O) ^ (n + 1) := fun n => Ideal.pow_le_pow_right (Nat.le_succ _)
  let π : ∀ n : ℕ, (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (n + 1 + 1)) →+* (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (n + 1)) := fun n => Ideal.Quotient.factor (hle n)
  have hπ : ∀ n, (π n).comp (Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (n + 1 + 1))) = Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (n + 1)) :=
    fun n => RingHom.ext fun x => rfl

  let τ : (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (1 + 1)) →+* DualNumber (ResidueField O) :=
    Ideal.Quotient.lift _ (tauTilde O) (fun f hf => tauTilde_eq_zero_of_mem_sq O hf)
  have hτmk : ∀ f, τ (Ideal.Quotient.mk _ f) = tauTilde O f := fun f => Ideal.Quotient.lift_mk _ _ _
  have hτO : τ.comp ((Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1))).comp (algebraMap O (PowerSeries O))) =
      (algebraMap (ResidueField O) (DualNumber (ResidueField O))).comp (residue O) := by
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, hτmk, show algebraMap O (PowerSeries O) a = C a from rfl, tauTilde_C, RingHom.comp_apply]
  have hτX : τ (Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1)) PowerSeries.X) = DualNumber.eps := by rw [hτmk, tauTilde_X]
  have hτsurj : Function.Surjective τ := by
    intro z
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective z.fst
    obtain ⟨b, hb⟩ := IsLocalRing.residue_surjective z.snd
    refine ⟨Ideal.Quotient.mk _ (C a + C b * X), ?_⟩
    rw [hτmk, map_add, map_mul, tauTilde_C, tauTilde_C, tauTilde_X, ha, hb]
    apply TrivSqZeroExt.ext
    · simp [TrivSqZeroExt.algebraMap_eq_inl, DualNumber.fst_eps, TrivSqZeroExt.fst_mul]
    · simp [TrivSqZeroExt.algebraMap_eq_inl, DualNumber.snd_eps, DualNumber.fst_eps, TrivSqZeroExt.snd_mul]
  have hτsmall : RingHom.ker τ * (maximalIdeal (PowerSeries O)).map (Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1))) = ⊥ := by
    rw [← le_bot_iff, Ideal.mul_le]
    intro x hx y hy
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hy
    obtain ⟨g, hg, rfl⟩ := hy
    rw [RingHom.mem_ker, hτmk] at hx
    have h0 : coeff 0 f ∈ maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff, ← fst_tauTilde O f, hx, TrivSqZeroExt.fst_zero]
    have h1 : coeff 1 f ∈ maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff, ← snd_tauTilde O f, hx, TrivSqZeroExt.snd_zero]
    rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact mul_mem_sq O h0 h1 hg
  have hτfst : (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)).toRingHom.comp τ = ι₀.comp (π 0) := by
    apply Ideal.Quotient.ringHom_ext
    ext f
    rw [RingHom.comp_apply, RingHom.comp_apply, hτmk, RingHom.comp_apply, RingHom.comp_apply]
    change (tauTilde O f).fst = ι₀ (π 0 (Ideal.Quotient.mk _ f))
    rw [fst_tauTilde, show π 0 (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ f from rfl, hι₀mk, coeff_zero_eq_constantCoeff_apply]
  have hτuniq : ∀ τ' : (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (1 + 1)) →+* DualNumber (ResidueField O),
      τ'.comp ((Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1))).comp (algebraMap O (PowerSeries O))) =
          (algebraMap (ResidueField O) (DualNumber (ResidueField O))).comp (residue O) →
      τ' (Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1)) PowerSeries.X) = DualNumber.eps → τ' = τ := by
    intro τ' h1 h2
    apply Ideal.Quotient.ringHom_ext
    refine RingHom.ext fun f => ?_
    have hC : ∀ a : O, τ' (Ideal.Quotient.mk _ (C a)) = τ (Ideal.Quotient.mk _ (C a)) := by
      intro a
      have e1 := congrArg (fun φ : O →+* DualNumber (ResidueField O) => φ a) h1
      have e2 := congrArg (fun φ : O →+* DualNumber (ResidueField O) => φ a) hτO
      simp only [RingHom.comp_apply] at e1 e2
      rw [show algebraMap O (PowerSeries O) a = C a from rfl] at e1 e2
      rw [e1, e2]
    have hXX : Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1)) (X * (X * mk fun p => coeff (p + 2) f)) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, ← mul_assoc, show (1 + 1 : ℕ) = 2 from rfl, pow_two]
      have hXm : (X : PowerSeries O) ∈ maximalIdeal (PowerSeries O) := (mem_maximalIdeal_iff O _).mpr (by rw [constantCoeff_X]; exact (maximalIdeal O).zero_mem)
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hXm hXm)
    rw [RingHom.comp_apply, RingHom.comp_apply]
    conv_lhs => rw [decomp O f]
    conv_rhs => rw [decomp O f]
    simp only [map_add, map_mul, hXX, mul_zero, add_zero]
    rw [hC, hC, h2, hτX]
  exact ⟨ι₀, hι₀, hι₀O, π, hπ, τ, hτO, hτX, hτsurj, hτsmall, hτfst, hτuniq⟩

end S_PowerSeries_exists_bijective_residue_reduction_dualNumber_of_isDiscreteValuationRing
end P2MW
export P2MW.S_PowerSeries_exists_bijective_residue_reduction_dualNumber_of_isDiscreteValuationRing (solution)
