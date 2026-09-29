-- Prove2me | solution 1 for PowerSeries.exists_ringEquiv_adicCompletion_quotient_span_X_sub_C
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/2640656d-a661-5dc9-a261-ecb9de4efde8

import Mathlib
import Theorems.Thm_PowerSeries_isAdicComplete_quotient_span_X_sub_C_of_irreducible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_exists_ringEquiv_adicCompletion_quotient_span_X_sub_C
set_option autoImplicit false

namespace FltWs21
namespace ComplId

open PowerSeries IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

local notation "𝔪" => IsLocalRing.maximalIdeal O
local notation "Ô" => AdicCompletion (IsLocalRing.maximalIdeal O) O

noncomputable def psum (ϖ : O) (n : ℕ) (F : PowerSeries O) : O :=
  ∑ i ∈ Finset.range n, coeff i F * ϖ ^ i

theorem psum_eq_eval_trunc (ϖ : O) (n : ℕ) (F : PowerSeries O) :
    psum ϖ n F = Polynomial.eval₂ (RingHom.id O) ϖ (trunc n F) := by
  rw [eval₂_trunc_eq_sum_range]; rfl

theorem psum_add (ϖ : O) (n : ℕ) (F G : PowerSeries O) : psum ϖ n (F + G) = psum ϖ n F + psum ϖ n G := by
  simp only [psum, map_add, add_mul, Finset.sum_add_distrib]

theorem psum_zero_left (ϖ : O) (F : PowerSeries O) : psum ϖ 0 F = 0 := by simp [psum]

theorem psum_succ (ϖ : O) (n : ℕ) (F : PowerSeries O) : psum ϖ (n + 1) F = psum ϖ n F + coeff n F * ϖ ^ n := by
  simp [psum, Finset.sum_range_succ]

theorem psum_sub_psum_mem (ϖ : O) {m n : ℕ} (h : n ≤ m) (F : PowerSeries O) :
    psum ϖ m F - psum ϖ n F ∈ Ideal.span {ϖ ^ n} := by
  induction m, h using Nat.le_induction with
  | base => rw [sub_self]; exact zero_mem _
  | succ m hnm ih =>
      rw [psum_succ, add_sub_right_comm]
      refine add_mem ih (Ideal.mem_span_singleton.mpr ⟨coeff m F * ϖ ^ (m - n), ?_⟩)
      rw [mul_comm (ϖ ^ n), mul_assoc, ← pow_add, Nat.sub_add_cancel hnm]

theorem mk_pow_zero_eq (x y : O) :
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ 0) x = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ 0) y := by
  rw [Ideal.Quotient.eq, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top

theorem psum_C (ϖ : O) {n : ℕ} (hn : 1 ≤ n) (o : O) : psum ϖ n (C o) = o := by
  induction n, hn using Nat.le_induction with
  | base => simp [psum, coeff_C]
  | succ m hm ih => rw [psum_succ, ih, coeff_C, if_neg (by omega), zero_mul, add_zero]

theorem psum_X (ϖ : O) {n : ℕ} (hn : 2 ≤ n) : psum ϖ n (X : PowerSeries O) = ϖ := by
  induction n, hn using Nat.le_induction with
  | base => simp [psum, Finset.sum_range_succ, coeff_X]
  | succ m hm ih => rw [psum_succ, ih, coeff_X, if_neg (by omega), zero_mul, add_zero]

theorem psum_mul_sub_mem (ϖ : O) (n : ℕ) (F G : PowerSeries O) :
    psum ϖ n (F * G) - psum ϖ n F * psum ϖ n G ∈ Ideal.span {ϖ ^ n} := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, Ideal.span_singleton_one]; exact Submodule.mem_top
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩

  set p : Polynomial O := trunc (k + 1) F * trunc (k + 1) G with hp
  have h1 : psum ϖ (k + 1) (F * G) = psum ϖ (k + 1) (p : PowerSeries O) := by
    rw [psum_eq_eval_trunc, psum_eq_eval_trunc, ← trunc_trunc_mul_trunc, hp, Polynomial.coe_mul]
  have h2 : psum ϖ (k + 1) F * psum ϖ (k + 1) G = Polynomial.eval₂ (RingHom.id O) ϖ p := by
    rw [psum_eq_eval_trunc, psum_eq_eval_trunc, hp, Polynomial.eval₂_mul]

  have hdeg : p.natDegree < (k + 1) + (k + 1) :=
    calc p.natDegree ≤ (trunc (k + 1) F).natDegree + (trunc (k + 1) G).natDegree := Polynomial.natDegree_mul_le
      _ < (k + 1) + (k + 1) := add_lt_add (natDegree_trunc_lt F k) (natDegree_trunc_lt G k)
  have h3 : Polynomial.eval₂ (RingHom.id O) ϖ p = psum ϖ ((k + 1) + (k + 1)) (p : PowerSeries O) := by
    rw [psum_eq_eval_trunc, trunc_coe_eq_self hdeg]
  rw [h1, h2, h3, ← neg_sub]
  exact neg_mem (psum_sub_psum_mem ϖ (by omega) _)

noncomputable def psi (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) : PowerSeries O →+* O ⧸ (IsLocalRing.maximalIdeal O) ^ n where
  toFun F := Ideal.Quotient.mk _ (psum ϖ n F)
  map_one' := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [← map_one (Ideal.Quotient.mk _)]; exact mk_pow_zero_eq _ _
    · rw [show (1 : PowerSeries O) = C 1 from (map_one C).symm, psum_C ϖ hn, map_one]
  map_mul' F G := by
    rw [← map_mul, Ideal.Quotient.eq, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.span_singleton_pow]
    exact psum_mul_sub_mem ϖ n F G
  map_zero' := by simp [psum]
  map_add' F G := by rw [psum_add, map_add]

theorem psi_apply (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) (F : PowerSeries O) :
    psi ϖ hϖ n F = Ideal.Quotient.mk _ (psum ϖ n F) := rfl

theorem psi_compat (ϖ : O) (hϖ : Irreducible ϖ) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal O) hle).comp (psi ϖ hϖ n) = psi ϖ hϖ m := by
  ext F
  simp only [RingHom.comp_apply, psi_apply, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.span_singleton_pow]
  exact psum_sub_psum_mem ϖ hle F

noncomputable def Phi (ϖ : O) (hϖ : Irreducible ϖ) : PowerSeries O →+* Ô :=
  AdicCompletion.liftRingHom (IsLocalRing.maximalIdeal O) (psi ϖ hϖ) (psi_compat ϖ hϖ)

theorem evalₐ_Phi (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) (F : PowerSeries O) :
    AdicCompletion.evalₐ (IsLocalRing.maximalIdeal O) n (Phi ϖ hϖ F) = Ideal.Quotient.mk _ (psum ϖ n F) :=
  AdicCompletion.evalₐ_liftRingHom _ _ _ n F

theorem Phi_C (ϖ : O) (hϖ : Irreducible ϖ) (o : O) : Phi ϖ hϖ (C o) = algebraMap O Ô o := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_Phi, AdicCompletion.algebraMap_apply]
  change _ = AdicCompletion.evalₐ _ n (AdicCompletion.of _ O o)
  rw [AdicCompletion.evalₐ_of]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact mk_pow_zero_eq _ _
  · rw [psum_C ϖ hn]

theorem Phi_X (ϖ : O) (hϖ : Irreducible ϖ) : Phi ϖ hϖ X = algebraMap O Ô ϖ := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_Phi, AdicCompletion.algebraMap_apply]
  change _ = AdicCompletion.evalₐ _ n (AdicCompletion.of _ O ϖ)
  rw [AdicCompletion.evalₐ_of]
  rcases lt_or_ge n 2 with hn | hn
  ·
    interval_cases n
    · exact mk_pow_zero_eq _ _
    · rw [Ideal.Quotient.eq, pow_one]
      have : psum ϖ 1 (X : PowerSeries O) = 0 := by simp [psum, coeff_X]
      rw [this, zero_sub]
      exact neg_mem ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ ▸ Ideal.mem_span_singleton_self ϖ)
  · rw [psum_X ϖ hn]

theorem Phi_X_sub_C (ϖ : O) (hϖ : Irreducible ϖ) : Phi ϖ hϖ (X - C ϖ) = 0 := by
  rw [map_sub, Phi_X, Phi_C, sub_self]

noncomputable def Phibar (ϖ : O) (hϖ : Irreducible ϖ) :
    (PowerSeries O ⧸ Ideal.span {(X : PowerSeries O) - C ϖ}) →+* Ô :=
  Ideal.Quotient.lift _ (Phi ϖ hϖ) fun F hF => by
    obtain ⟨G, rfl⟩ := Ideal.mem_span_singleton'.mp hF
    rw [map_mul, Phi_X_sub_C, mul_zero]

theorem Phibar_mk (ϖ : O) (hϖ : Irreducible ϖ) (F : PowerSeries O) :
    Phibar ϖ hϖ (Ideal.Quotient.mk _ F) = Phi ϖ hϖ F := rfl

theorem Phibar_mk_C (ϖ : O) (hϖ : Irreducible ϖ) (o : O) :
    Phibar ϖ hϖ (Ideal.Quotient.mk _ (C o)) = algebraMap O Ô o := by
  rw [Phibar_mk, Phi_C]

theorem Phi_surjective (ϖ : O) (hϖ : Irreducible ϖ) : Function.Surjective (Phi ϖ hϖ) := by
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  intro x
  induction x using AdicCompletion.induction_on with
  | h b =>

    have hd : ∀ n : ℕ, ∃ d : O, (b : ℕ → O) (n + 1) - (b : ℕ → O) n = ϖ ^ n * d := by
      intro n
      have h := (AdicCompletion.AdicCauchySequence.mk_eq_mk (Nat.le_succ n) b)

      rw [Submodule.Quotient.eq] at h
      have h' : (b : ℕ → O) (n + 1) - (b : ℕ → O) n ∈ (IsLocalRing.maximalIdeal O) ^ n := by
        simpa [smul_eq_mul, Ideal.mul_top] using h
      have h'' : (b : ℕ → O) (n + 1) - (b : ℕ → O) n ∈ Ideal.span {ϖ ^ n} := by
        rw [← Ideal.span_singleton_pow, ← hmax]; exact h'
      exact Ideal.mem_span_singleton'.mp h'' |>.imp fun d hd => by rw [← hd, mul_comm]
    choose d hd using hd
    refine ⟨C ((b : ℕ → O) 0) + PowerSeries.mk d, ?_⟩

    have htel : ∀ n, psum ϖ n (C ((b : ℕ → O) 0) + PowerSeries.mk d) = if n = 0 then 0 else (b : ℕ → O) n := by
      intro n
      induction n with
      | zero => simp [psum]
      | succ n ih =>
          rw [psum_succ, ih, map_add, coeff_mk, coeff_C]
          simp only [Nat.succ_ne_zero, if_false]
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · simp only [if_true, zero_add]
            linear_combination -(hd 0)
          · simp only [hn.ne', if_false, zero_add]
            linear_combination -(hd n)
    refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [evalₐ_Phi, AdicCompletion.evalₐ_mk, htel]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact mk_pow_zero_eq _ _
    · rw [if_neg hn.ne']

theorem Phibar_surjective (ϖ : O) (hϖ : Irreducible ϖ) : Function.Surjective (Phibar ϖ hϖ) := by
  intro x
  obtain ⟨F, hF⟩ := Phi_surjective ϖ hϖ x
  exact ⟨Ideal.Quotient.mk _ F, hF⟩

end FltWs21.ComplId

namespace FltWs21
namespace ComplId

open IsLocalRing

theorem algebraMap_adicCompletion_injective {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    Function.Injective (algebraMap O (AdicCompletion (maximalIdeal O) O)) := by
  haveI : IsHausdorff (maximalIdeal O) O :=
    IsHausdorff.of_isLocalRing _ _ (maximalIdeal.isMaximal O).ne_top
  exact AdicCompletion.of_injective (maximalIdeal O) O

theorem injective_of_apply_mk_C {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ϖ : O) (hϖ : Irreducible ϖ)
    (Φbar : (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}) →+*
      AdicCompletion (IsLocalRing.maximalIdeal O) O)
    (h : ∀ o : O, Φbar (Ideal.Quotient.mk _ (PowerSeries.C o)) = algebraMap O _ o) :
    Function.Injective Φbar := by
  obtain ⟨hdom, hdvr, -, hirr⟩ := PowerSeries.isAdicComplete_quotient_span_X_sub_C_of_irreducible ϖ hϖ
  rw [injective_iff_map_eq_zero]
  intro z hz
  by_contra hz0

  obtain ⟨kk, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz0 hirr
  have hpow : Φbar ((Ideal.Quotient.mk _ (PowerSeries.C ϖ)) ^ kk) = 0 := by
    have hu : IsUnit (Φbar (u : PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ})) :=
      (Units.isUnit u).map Φbar
    rw [map_mul] at hz
    exact (hu.mul_right_eq_zero).mp hz
  rw [map_pow, h ϖ, ← map_pow] at hpow
  have : (ϖ ^ kk : O) = 0 := by
    apply algebraMap_adicCompletion_injective
    rw [hpow, map_zero]
  exact hϖ.ne_zero (pow_eq_zero_iff'.mp this).1

end FltWs21.ComplId

open FltWs21.ComplId in
theorem solution
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal O) O ≃+*
        (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}),
      ∀ o : O, e (algebraMap O (AdicCompletion (IsLocalRing.maximalIdeal O) O) o) =
        Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}) (PowerSeries.C o) := by
  set e₀ := RingEquiv.ofBijective (Phibar ϖ hϖ)
    ⟨injective_of_apply_mk_C ϖ hϖ (Phibar ϖ hϖ) (Phibar_mk_C ϖ hϖ), Phibar_surjective ϖ hϖ⟩ with he₀
  refine ⟨e₀.symm, fun o => ?_⟩
  rw [RingEquiv.symm_apply_eq]
  exact (Phibar_mk_C ϖ hϖ o).symm

end S_PowerSeries_exists_ringEquiv_adicCompletion_quotient_span_X_sub_C
end P2MW
export P2MW.S_PowerSeries_exists_ringEquiv_adicCompletion_quotient_span_X_sub_C (solution)
