-- Prove2me | solution 1 for QuaternionAlgebra.exists_nrd_eq_of_pos_of_isDefiniteRamifiedExactlyAt_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/572912fb-cdc2-5c98-b78d-63adf8c06d13

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_forall_isUnit_iff_forall_normForm_eq_zero
import Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_normForm_eq_zero
import Theorems.Thm_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero
import Theorems.Thm_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split
import Theorems.Thm_QuadraticForm_exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_nrd_eq_of_pos_of_isDefiniteRamifiedExactlyAt_two
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

noncomputable section

namespace HSCC2

section Places

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem intCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℤ) :
    (z : 𝓞 ℚ) ∈ w.asIdeal ↔ (Rat.HeightOneSpectrum.natGenerator w : ℤ) ∣ z := by
  rw [Int.natCast_dvd, ← natCast_mem_asIdeal_iff]
  rcases Int.natAbs_eq z with h | h
  · conv_lhs => rw [h]
    simp
  · conv_lhs => rw [h]
    simp

theorem asIdeal_eq_span_natGenerator (w : HeightOneSpectrum (𝓞 ℚ)) :
    w.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.natGenerator w : ℕ) : 𝓞 ℚ)} := by
  set e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  have h := Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) w
  have h1 : w.asIdeal = (w.asIdeal.map e).comap e := (Ideal.comap_map_of_bijective e e.bijective).symm
  rw [h1, ← h, ← Ideal.map_symm, Ideal.map_span, Set.image_singleton]
  congr 2
  simp [e]

theorem valuation_natGenerator_self (w : HeightOneSpectrum (𝓞 ℚ)) :
    w.valuation ℚ ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : ℚ) = WithZero.exp (-1 : ℤ) := by
  rw [show ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : ℚ) =
      algebraMap (𝓞 ℚ) ℚ ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : 𝓞 ℚ) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  refine HeightOneSpectrum.intValuation_singleton w ?_ (asIdeal_eq_span_natGenerator w)
  exact_mod_cast (Rat.HeightOneSpectrum.prime_natGenerator w).ne_zero

theorem valuation_intCast_eq_one_of_not_dvd (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℤ)
    (hz : ¬ (Rat.HeightOneSpectrum.natGenerator w : ℤ) ∣ z) : w.valuation ℚ (z : ℚ) = 1 := by
  rw [show (z : ℚ) = algebraMap (𝓞 ℚ) ℚ z from (map_intCast _ _).symm]
  refine (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w) (r := (z : 𝓞 ℚ))).2 ?_
  rwa [intCast_mem_asIdeal_iff]

theorem valuation_natCast_eq_one_of_not_dvd (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ)
    (hn : ¬ Rat.HeightOneSpectrum.natGenerator w ∣ n) : w.valuation ℚ (n : ℚ) = 1 := by
  have := valuation_intCast_eq_one_of_not_dvd w n (by rwa [Int.natCast_dvd_natCast])
  simpa using this

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) = w.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w r

def place (q : ℕ) (hq : q.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨q, hq⟩

theorem natGenerator_place (q : ℕ) (hq : q.Prime) : Rat.HeightOneSpectrum.natGenerator (place q hq) = q := by
  have := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨q, hq⟩
  exact congrArg Subtype.val this

theorem natCast_mem_asIdeal_place (q : ℕ) (hq : q.Prime) : (q : 𝓞 ℚ) ∈ (place q hq).asIdeal := by
  rw [natCast_mem_asIdeal_iff, natGenerator_place]

theorem eq_place_of_mem {q : ℕ} (hq : q.Prime) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : (q : 𝓞 ℚ) ∈ w.asIdeal) :
    w = place q hq := by
  rw [natCast_mem_asIdeal_iff] at hw
  have := (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) hq).mp hw
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  rw [place, Equiv.apply_symm_apply]
  exact Subtype.ext this

end Places

section NonSquare

theorem not_isSquare_of_valuation_odd (w : HeightOneSpectrum (𝓞 ℚ)) (x : w.adicCompletion ℚ) (n : ℤ)
    (hn : Odd n) (hx : Valued.v x = WithZero.exp n) : ¬ IsSquare x := by
  rintro ⟨s, rfl⟩
  have hs0 : Valued.v s ≠ 0 := by
    intro h0
    rw [map_mul, h0, mul_zero] at hx
    exact WithZero.exp_ne_zero hx.symm
  have hs : WithZero.exp (WithZero.log (Valued.v s)) = Valued.v s := WithZero.exp_log hs0
  rw [map_mul, ← hs, ← WithZero.exp_add, WithZero.exp_inj] at hx
  obtain ⟨k, hk⟩ := hn
  omega

theorem padic_isSquare_zmod_of_isSquare {p : ℕ} [Fact p.Prime] (u : ℤ) (hu : ¬ (p : ℤ) ∣ u)
    (h : IsSquare ((u : ℚ) : ℚ_[p])) : IsSquare ((u : ℤ) : ZMod p) := by
  obtain ⟨s, hs⟩ := h
  have hcast : ((u : ℚ) : ℚ_[p]) = ((u : ℤ) : ℚ_[p]) := by push_cast; rfl
  rw [hcast] at hs
  have hu1 : ‖((u : ℤ) : ℚ_[p])‖ = 1 := by
    have h1 : ‖((u : ℤ) : ℚ_[p])‖ ≤ 1 := Padic.norm_int_le_one u
    have h2 : ¬ ‖((u : ℤ) : ℚ_[p])‖ < 1 := by rwa [Padic.norm_intCast_lt_one_iff]
    push Not at h2
    exact le_antisymm h1 h2
  have hs1 : ‖s‖ = 1 := by
    have hmul : ‖s‖ * ‖s‖ = 1 := by rw [← norm_mul, ← hs, hu1]
    rcases mul_self_eq_one_iff.1 hmul with h | h
    · exact h
    · linarith [norm_nonneg s]
  let S : ℤ_[p] := ⟨s, hs1.le⟩
  have hS : ((u : ℤ) : ℤ_[p]) = S * S := by
    apply Subtype.ext
    rw [PadicInt.coe_intCast, PadicInt.coe_mul, hs]
  have := congrArg (PadicInt.toZMod (p := p)) hS
  rw [map_intCast, map_mul] at this
  exact ⟨_, this⟩

theorem isSquare_zmod_of_isSquare_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (u : ℤ)
    (hu : ¬ (Rat.HeightOneSpectrum.natGenerator w : ℤ) ∣ u)
    (h : IsSquare (algebraMap ℚ (w.adicCompletion ℚ) (u : ℚ))) :
    IsSquare ((u : ℤ) : ZMod (Rat.HeightOneSpectrum.natGenerator w)) := by
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.natGenerator w)) :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator w⟩
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w : ℕ)) :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator w⟩
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv (R := 𝓞 ℚ) w
  have h' : IsSquare (e (algebraMap ℚ (w.adicCompletion ℚ) (u : ℚ))) := h.map e
  have he : e (algebraMap ℚ (w.adicCompletion ℚ) (u : ℚ)) =
      ((u : ℚ) : ℚ_[(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w : ℕ)]) := by
    rw [AlgHomClass.commutes]
    simp
  rw [he] at h'
  exact padic_isSquare_zmod_of_isSquare u hu h'

theorem isSquare_of_isSquare_sq_mul {K : Type*} [Field K] {s r : K} (hs : s ≠ 0)
    (h : IsSquare (s ^ 2 * r)) : IsSquare r := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t / s, ?_⟩
  field_simp
  linear_combination ht

end NonSquare

section Local

variable {a b : ℚ}

theorem not_nonempty_algEquiv_matrix_of_forall_isUnit (v : HeightOneSpectrum (𝓞 ℚ))
    (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) :
    ¬ Nonempty (ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]
        ≃ₐ[v.adicCompletion ℚ] Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
  rintro ⟨ψ⟩
  set K := v.adicCompletion ℚ
  obtain ⟨φ₀, -, -⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := K) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ K a) (d₂ := (0 : K)) (d₃ := algebraMap ℚ K b) rfl (map_zero _) rfl AlgEquiv.refl
  let E : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, 0]
  let F : Matrix (Fin 2) (Fin 2) K := !![0, 0; 0, 1]
  have hEF : E * F = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [E, F]
  have hF : F ≠ 0 := fun h => by simpa [F] using congrFun (congrFun h 1) 1
  have hE : E ≠ 0 := fun h => by simpa [E] using congrFun (congrFun h 0) 0
  have hEu : ¬ IsUnit E := fun hu => hF ((hu.mul_right_eq_zero).1 hEF)
  have hx0 : φ₀.symm (ψ.symm E) ≠ 0 := by
    intro h0
    apply hE
    have := congrArg ψ (congrArg φ₀ h0)
    simpa using this
  have hxu := hdiv _ hx0
  have : IsUnit E := by simpa using (hxu.map φ₀).map ψ
  exact hEu this

theorem exists_pureNrd_eq_of_not_forall_isUnit (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ))
    (hndiv : ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) :
    ∀ c : v.adicCompletion ℚ, ∃ x y z : v.adicCompletion ℚ,
      -(algebraMap ℚ (v.adicCompletion ℚ) a) * x ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) b) * y ^ 2
        + (algebraMap ℚ (v.adicCompletion ℚ) a) * (algebraMap ℚ (v.adicCompletion ℚ) b) * z ^ 2 = c := by
  set K := v.adicCompletion ℚ
  intro c
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  set A := algebraMap ℚ K a
  set B := algebraMap ℚ K b
  obtain ⟨φ₀, -, -⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := K) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := A) (d₂ := (0 : K)) (d₃ := B) rfl (map_zero _) rfl AlgEquiv.refl
  have hK : ¬ ∀ x : ℍ[K, A, B], x ≠ 0 → IsUnit x := by
    intro hall
    apply hndiv
    intro x hx
    have hx' : φ₀ x ≠ 0 := by
      intro h0; apply hx; simpa using congrArg φ₀.symm h0
    have hu := hall (φ₀ x) hx'
    simpa using hu.map φ₀.symm
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hAK : A ≠ 0 := by simpa [A] using (algebraMap ℚ K).injective.ne ha
  have hBK : B ≠ 0 := by simpa [B] using (algebraMap ℚ K).injective.ne hb
  have hiso : ∃ x₀ x₁ x₂ x₃ : K, ¬ (x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ∧
      x₀ ^ 2 - A * x₁ ^ 2 - B * x₂ ^ 2 + A * B * x₃ ^ 2 = 0 := by
    by_contra hno
    apply hK
    refine (QuaternionAlgebra.forall_isUnit_iff_forall_normForm_eq_zero K A B).2 fun x₀ x₁ x₂ x₃ h0 => ?_
    by_contra hne
    exact hno ⟨x₀, x₁, x₂, x₃, hne, h0⟩
  obtain ⟨x₀, x₁, x₂, x₃, hx, h0⟩ := hiso
  obtain ⟨ψ⟩ := QuaternionAlgebra.nonempty_algEquiv_matrix_of_normForm_eq_zero K h2 A B hAK hBK x₀ x₁ x₂ x₃ hx h0

  let Nm : Matrix (Fin 2) (Fin 2) K := !![0, 1; 0, 0]
  have hNm : Nm * Nm = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Nm]
  have hNm0 : Nm ≠ 0 := fun h => by simpa [Nm] using congrFun (congrFun h 0) 1
  obtain ⟨n₀, n₁, n₂, n₃, hn⟩ : ∃ n₀ n₁ n₂ n₃ : K, ψ.symm Nm = ⟨n₀, n₁, n₂, n₃⟩ :=
    ⟨(ψ.symm Nm).re, (ψ.symm Nm).imI, (ψ.symm Nm).imJ, (ψ.symm Nm).imK, by ext <;> rfl⟩
  have hnn : (⟨n₀, n₁, n₂, n₃⟩ : ℍ[K, A, B]) * ⟨n₀, n₁, n₂, n₃⟩ = 0 := by
    rw [← hn, ← map_mul, hNm, map_zero]
  have hn0 : (⟨n₀, n₁, n₂, n₃⟩ : ℍ[K, A, B]) ≠ 0 := by
    rw [← hn]
    intro h0
    apply hNm0
    simpa using congrArg ψ h0
  rw [QuaternionAlgebra.mk_mul_mk] at hnn
  have hre := congrArg QuaternionAlgebra.re hnn
  have hI := congrArg QuaternionAlgebra.imI hnn
  have hJ := congrArg QuaternionAlgebra.imJ hnn
  have hKk := congrArg QuaternionAlgebra.imK hnn
  change _ = (0 : K) at hre hI hJ hKk
  have hn₀ : n₀ = 0 := by
    by_contra h
    have h1 : n₁ = 0 := by
      have : (2 * n₀) * n₁ = 0 := by linear_combination hI
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' (mul_ne_zero h2 h)
      · exact h'
    have h2' : n₂ = 0 := by
      have : (2 * n₀) * n₂ = 0 := by linear_combination hJ
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' (mul_ne_zero h2 h)
      · exact h'
    have h3 : n₃ = 0 := by
      have : (2 * n₀) * n₃ = 0 := by linear_combination hKk
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' (mul_ne_zero h2 h)
      · exact h'
    subst h1 h2' h3
    have : n₀ * n₀ = 0 := by linear_combination hre
    exact h (mul_self_eq_zero.1 this)
  subst hn₀
  have hiso3 : ∃ x y z : K, ¬ (x = 0 ∧ y = 0 ∧ z = 0) ∧ -A * x ^ 2 - B * y ^ 2 + A * B * z ^ 2 = 0 := by
    refine ⟨n₁, n₂, n₃, ?_, by linear_combination (-1 : K) * hre⟩
    rintro ⟨rfl, rfl, rfl⟩
    exact hn0 (by ext <;> rfl)
  exact QuadraticForm.forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero K A B hAK hBK hiso3 c

end Local

section Two

theorem zmod_eight_sq (σ : ZMod (2 ^ 3)) : σ * σ = 0 ∨ σ * σ = 1 ∨ σ * σ = 4 := by
  revert σ; decide

theorem padicTwo_zmod_eq_one_of_isSquare {p : ℕ} [Fact p.Prime] (hp : p = 2) (u : ℤ) (hu : ¬ (2 : ℤ) ∣ u)
    (h : IsSquare ((u : ℚ) : ℚ_[p])) : ((u : ℤ) : ZMod (2 ^ 3)) = 1 := by
  subst hp
  obtain ⟨s, hs⟩ := h
  have hcast : ((u : ℚ) : ℚ_[2]) = ((u : ℤ) : ℚ_[2]) := by push_cast; rfl
  rw [hcast] at hs
  have hu1 : ‖((u : ℤ) : ℚ_[2])‖ = 1 := by
    have h1 : ‖((u : ℤ) : ℚ_[2])‖ ≤ 1 := Padic.norm_int_le_one u
    have h2 : ¬ ‖((u : ℤ) : ℚ_[2])‖ < 1 := by
      rw [Padic.norm_intCast_lt_one_iff]; exact_mod_cast hu
    push Not at h2
    exact le_antisymm h1 h2
  have hs1 : ‖s‖ = 1 := by
    have hmul : ‖s‖ * ‖s‖ = 1 := by rw [← norm_mul, ← hs, hu1]
    rcases mul_self_eq_one_iff.1 hmul with h | h
    · exact h
    · linarith [norm_nonneg s]
  let S : ℤ_[2] := ⟨s, hs1.le⟩
  have hS : ((u : ℤ) : ℤ_[2]) = S * S := by
    apply Subtype.ext
    rw [PadicInt.coe_intCast, PadicInt.coe_mul, hs]
  have h8 := congrArg (PadicInt.toZModPow (p := 2) 3) hS
  rw [map_intCast, map_mul] at h8
  rcases zmod_eight_sq (PadicInt.toZModPow (p := 2) 3 S) with h0 | h1 | h4
  · exfalso
    rw [h0, ZMod.intCast_zmod_eq_zero_iff_dvd] at h8
    exact hu (dvd_trans (by norm_num) h8)
  · rw [h8, h1]
  · exfalso
    rw [h4] at h8
    have : ((u - 4 : ℤ) : ZMod (2 ^ 3)) = 0 := by push_cast; rw [h8]; ring
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    have h2 : (2 : ℤ) ∣ u - 4 := dvd_trans (by norm_num) this
    have h3 := dvd_add h2 (by norm_num : (2 : ℤ) ∣ 4)
    rw [sub_add_cancel] at h3
    exact hu h3

theorem zmod_eq_one_of_isSquare_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (hw : Rat.HeightOneSpectrum.natGenerator w = 2)
    (u : ℤ) (hu : ¬ (2 : ℤ) ∣ u)
    (h : IsSquare (algebraMap ℚ (w.adicCompletion ℚ) (u : ℚ))) : ((u : ℤ) : ZMod (2 ^ 3)) = 1 := by
  have hp : (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w : ℕ) = 2 := hw
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w : ℕ)) :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator w⟩
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv (R := 𝓞 ℚ) w
  have h' : IsSquare (e (algebraMap ℚ (w.adicCompletion ℚ) (u : ℚ))) := h.map e
  have he : e (algebraMap ℚ (w.adicCompletion ℚ) (u : ℚ)) =
      ((u : ℚ) : ℚ_[(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w : ℕ)]) := by
    rw [AlgHomClass.commutes]
    simp
  rw [he] at h'
  exact padicTwo_zmod_eq_one_of_isSquare hp u hu h'

theorem exists_sq_add_two (e t₁ : ℕ) (ht₁ : ¬ 2 ∣ t₁) :
    ∃ x₀ c : ℚ, ((2 : ℚ) ^ e * t₁ = x₀ ^ 2 + c) ∧ 0 < c ∧
      ¬ IsSquare (algebraMap ℚ ((place 2 Nat.prime_two).adicCompletion ℚ) (-c)) := by
  set w := place 2 Nat.prime_two with hw
  have hgen : Rat.HeightOneSpectrum.natGenerator w = 2 := natGenerator_place 2 Nat.prime_two
  have ht₁0 : 0 < t₁ := Nat.pos_of_ne_zero fun h => ht₁ (h ▸ dvd_zero 2)
  have ht₁0' : (0 : ℚ) < t₁ := by exact_mod_cast ht₁0
  have hvq : w.valuation ℚ (2 : ℚ) = WithZero.exp (-1 : ℤ) := by
    have := valuation_natGenerator_self w; rw [hgen] at this; exact_mod_cast this
  have hv1n : ∀ n : ℕ, ¬ 2 ∣ n → w.valuation ℚ (n : ℚ) = 1 := fun n hn =>
    valuation_natCast_eq_one_of_not_dvd w n (by rwa [hgen])
  have ht₁Z : ¬ (2 : ℤ) ∣ (t₁ : ℤ) := by exact_mod_cast ht₁
  rcases Nat.even_or_odd e with ⟨m, hm⟩ | hodd
  ·
    by_cases h7 : ((t₁ : ℤ) : ZMod (2 ^ 3)) = 7
    ·
      set D : ℤ := 9 * t₁ - 4 with hD
      have hDpos : (0 : ℤ) < D := by rw [hD]; omega
      have hDodd : ¬ (2 : ℤ) ∣ D := by
        rw [hD]; intro h; apply ht₁Z
        have : (2 : ℤ) ∣ 9 * t₁ := by
          have := dvd_add h (by norm_num : (2 : ℤ) ∣ 4)
          rwa [sub_add_cancel] at this
        rcases (Int.prime_two).dvd_or_dvd this with h9 | h9
        · norm_num at h9
        · exact h9
      refine ⟨(2 : ℚ) ^ m * 2 / 3, (2 : ℚ) ^ (m + m) * (D : ℚ) / 9, ?_, by positivity, ?_⟩
      · rw [hm, hD]; push_cast; field_simp; ring
      · intro hsq
        have h1 : IsSquare (algebraMap ℚ (w.adicCompletion ℚ) ((-D : ℤ) : ℚ)) := by
          have : algebraMap ℚ (w.adicCompletion ℚ) (-((2 : ℚ) ^ (m + m) * (D : ℚ) / 9)) =
              (algebraMap ℚ (w.adicCompletion ℚ) ((2 : ℚ) ^ m / 3)) ^ 2 *
                algebraMap ℚ (w.adicCompletion ℚ) ((-D : ℤ) : ℚ) := by
            rw [← map_pow, ← map_mul]; congr 1; push_cast; field_simp; ring
          rw [this] at hsq
          refine isSquare_of_isSquare_sq_mul ?_ hsq
          rw [map_ne_zero_iff _ (algebraMap ℚ (w.adicCompletion ℚ)).injective]
          positivity
        have hDq' : ¬ (2 : ℤ) ∣ -D := fun h => hDodd (dvd_neg.1 h)
        have h8 := zmod_eq_one_of_isSquare_algebraMap w hgen (-D) hDq' h1
        rw [hD] at h8
        push_cast at h8 h7
        rw [h7] at h8
        revert h8
        decide
    ·
      refine ⟨0, (2 : ℚ) ^ e * t₁, by ring, by positivity, ?_⟩
      intro hsq
      apply h7
      have h1 : IsSquare (algebraMap ℚ (w.adicCompletion ℚ) ((-(t₁ : ℤ) : ℤ) : ℚ)) := by
        have : algebraMap ℚ (w.adicCompletion ℚ) (-((2 : ℚ) ^ e * t₁)) =
            (algebraMap ℚ (w.adicCompletion ℚ) ((2 : ℚ) ^ m)) ^ 2 *
              algebraMap ℚ (w.adicCompletion ℚ) ((-(t₁ : ℤ) : ℤ) : ℚ) := by
          rw [← map_pow, ← map_mul]; congr 1; rw [hm]; push_cast; ring
        rw [this] at hsq
        refine isSquare_of_isSquare_sq_mul ?_ hsq
        rw [map_ne_zero_iff _ (algebraMap ℚ (w.adicCompletion ℚ)).injective]
        positivity
      have h8 := zmod_eq_one_of_isSquare_algebraMap w hgen (-(t₁ : ℤ)) (by rwa [dvd_neg]) h1
      rw [Int.cast_neg] at h8
      rw [neg_eq_iff_eq_neg.1 h8]
      decide
  ·
    refine ⟨0, (2 : ℚ) ^ e * t₁, by ring, by positivity, ?_⟩
    refine not_isSquare_of_valuation_odd w _ (-(e : ℤ)) (by
      obtain ⟨k, hk⟩ := hodd; exact ⟨-(k : ℤ) - 1, by omega⟩) ?_
    rw [valued_algebraMap, Valuation.map_neg, map_mul, map_pow, hvq, hv1n t₁ ht₁, mul_one,
      ← WithZero.exp_nsmul]
    congr 1
    simp

end Two

section Main

variable {a b : ℚ}

theorem nrd_smul' (r : ℚ) (γ : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.nrd (r • γ) = r ^ 2 * QuaternionAlgebra.nrd γ := by
  obtain ⟨g0, g1, g2, g3⟩ := γ
  simp only [QuaternionAlgebra.nrd]
  change (r * g0) ^ 2 - a * (r * g1) ^ 2 - b * (r * g2) ^ 2 + a * b * (r * g3) ^ 2 = _
  ring

theorem exists_nrd_eq_natCast
    (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b 2) (T : ℕ) (hT : 0 < T) :
    ∃ γ : ℍ[ℚ, a, b], QuaternionAlgebra.nrd γ = T := by
  have ha : a < 0 := hdef.1
  have hb : b < 0 := hdef.2.1
  have ha0 : a ≠ 0 := ha.ne
  have hb0 : b ≠ 0 := hb.ne
  obtain ⟨e, t₁, ht₁, hTe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hT.ne' 2 (by norm_num)
  obtain ⟨x₀, c, hxc, hc, hnsq⟩ := exists_sq_add_two e t₁ ht₁
  have hc0 : c ≠ 0 := hc.ne'

  have hv : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ x y z : v.adicCompletion ℚ,
      -(algebraMap ℚ (v.adicCompletion ℚ) a) * x ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) b) * y ^ 2
        + (algebraMap ℚ (v.adicCompletion ℚ) a) * (algebraMap ℚ (v.adicCompletion ℚ) b) * z ^ 2
        = algebraMap ℚ (v.adicCompletion ℚ) c := by
    intro v
    by_cases hvq : ((2 : ℕ) : 𝓞 ℚ) ∈ v.asIdeal
    · have hveq := eq_place_of_mem Nat.prime_two hvq
      subst hveq
      have hdiv := (hdef.2.2 (place 2 Nat.prime_two)).2 (natCast_mem_asIdeal_place 2 Nat.prime_two)
      refine QuadraticForm.exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split a b ha0 hb0
        (place 2 Nat.prime_two) (not_nonempty_algEquiv_matrix_of_forall_isUnit (place 2 Nat.prime_two) hdiv) _ ?_
      rwa [← map_neg]
    · have hndiv : ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x :=
        fun h => hvq ((hdef.2.2 v).1 h)
      exact exists_pureNrd_eq_of_not_forall_isUnit ha0 hb0 v hndiv _

  have hR : ∃ x y z : ℝ, -(algebraMap ℚ ℝ a) * x ^ 2 - (algebraMap ℚ ℝ b) * y ^ 2
      + (algebraMap ℚ ℝ a) * (algebraMap ℚ ℝ b) * z ^ 2 = algebraMap ℚ ℝ c := by
    refine ⟨Real.sqrt ((c : ℝ) / (-(a : ℝ))), 0, 0, ?_⟩
    have ha' : (0 : ℝ) < -(a : ℝ) := by
      have : (a : ℝ) < 0 := by exact_mod_cast ha
      linarith
    have hc' : (0 : ℝ) ≤ (c : ℝ) / (-(a : ℝ)) := div_nonneg (by exact_mod_cast hc.le) ha'.le
    simp only [eq_ratCast]
    rw [Real.sq_sqrt hc']
    field_simp
    ring
  obtain ⟨x, y, z, hxyz⟩ :=
    QuadraticForm.exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real a b ha0 hb0 c hc0 hv hR
  refine ⟨⟨x₀, x, y, z⟩, ?_⟩
  rw [QuaternionAlgebra.nrd_mk, hTe]
  push_cast
  linear_combination hxyz - hxc

theorem main
    (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b 2)
    (t : ℚ) (ht : 0 < t) :
    ∃ γ : ℍ[ℚ, a, b], QuaternionAlgebra.nrd γ = t := by
  have hnum : 0 < t.num := Rat.num_pos.2 ht
  set T : ℕ := t.num.toNat * t.den with hT
  have hTpos : 0 < T := Nat.mul_pos (by omega) t.den_pos
  have hTq : (T : ℚ) = t * (t.den : ℚ) ^ 2 := by
    rw [hT]
    push_cast
    have h1 : ((t.num.toNat : ℕ) : ℚ) = (t.num : ℚ) := by
      have h2 : ((t.num.toNat : ℕ) : ℤ) = t.num := Int.toNat_of_nonneg hnum.le
      exact_mod_cast h2
    rw [h1, ← Rat.mul_den_eq_num t]
    ring
  obtain ⟨γ, hγ⟩ := exists_nrd_eq_natCast hdef T hTpos
  refine ⟨((t.den : ℚ))⁻¹ • γ, ?_⟩
  rw [nrd_smul', hγ, hTq]
  have hd : (t.den : ℚ) ≠ 0 := by exact_mod_cast t.den_ne_zero
  field_simp

end Main

end HSCC2

end

theorem solution
    {a b : ℚ} (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b 2)
    (t : ℚ) (ht : 0 < t) :
    ∃ γ : ℍ[ℚ, a, b], QuaternionAlgebra.nrd γ = t :=
  HSCC2.main hdef t ht

end S_QuaternionAlgebra_exists_nrd_eq_of_pos_of_isDefiniteRamifiedExactlyAt_two
end P2MW
export P2MW.S_QuaternionAlgebra_exists_nrd_eq_of_pos_of_isDefiniteRamifiedExactlyAt_two (solution)
