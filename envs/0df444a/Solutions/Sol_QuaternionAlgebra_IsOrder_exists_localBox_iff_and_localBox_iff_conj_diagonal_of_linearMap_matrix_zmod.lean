-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.exists_localBox_iff_and_localBox_iff_conj_diagonal_of_linearMap_matrix_zmod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/81ae5b17-1107-5e8a-a597-37af58580bec

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_basis_span_eq
import Theorems.Thm_Submodule_mem_localBox_iff_exists_eq_sum_basis_tmul
import Theorems.Thm_Matrix_exists_generalLinearGroup_forall_algHom_apply_eq_conj
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_QuaternionAlgebra_IsOrder_exists_localBox_iff_and_localBox_iff_conj_diagonal_of_linearMap_matrix_zmod

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

namespace S4Local

local notation "Kv" v => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "Ov" v => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v

section A

variable (w : HeightOneSpectrum (𝓞 ℚ))

noncomputable abbrev ℓ : ℕ := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w : ℕ)

scoped instance fact_prime_ℓ : Fact (Nat.Prime (ℓ w)) := ⟨(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w).2⟩

theorem ℓ_eq_natGenerator : ℓ w = Rat.HeightOneSpectrum.natGenerator w := rfl

theorem natCast_mem_asIdeal_iff (n : ℕ) : (n : 𝓞 ℚ) ∈ w.asIdeal ↔ ℓ w ∣ n := by
  rw [ℓ_eq_natGenerator, Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem ℓ_eq_of_prime_mem {p : ℕ} (hp : p.Prime) (hpw : (p : 𝓞 ℚ) ∈ w.asIdeal) : ℓ w = p :=
  (Nat.prime_dvd_prime_iff_eq (fact_prime_ℓ w).out hp).mp ((natCast_mem_asIdeal_iff w p).mp hpw)

noncomputable def red : (Ov w) →+* ZMod (ℓ w) :=
  (PadicInt.toZMod (p := ℓ w)).comp
    ((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv (R := 𝓞 ℚ) w).toAlgEquiv.toRingEquiv.toRingHom)

theorem red_surjective : Function.Surjective (red w) := ZMod.ringHom_surjective _

theorem red_eq_zero_iff (c : (Ov w)) : red w c = 0 ↔ ∃ t : (Ov w), c = (ℓ w : (Ov w)) * t := by
  set e := (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv (R := 𝓞 ℚ) w).toAlgEquiv.toRingEquiv with he
  have h1 : red w c = 0 ↔ e c ∈ RingHom.ker (PadicInt.toZMod (p := ℓ w)) := by
    rw [RingHom.mem_ker]; rfl
  rw [h1, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨e.symm a, ?_⟩
    apply e.injective
    rw [map_mul, map_natCast, RingEquiv.apply_symm_apply, ← ha, mul_comm]
  · rintro ⟨t, rfl⟩
    exact ⟨e t, by rw [map_mul, map_natCast, mul_comm]⟩

theorem red_natCast_ℓ : red w (ℓ w : (Ov w)) = 0 := by
  rw [map_natCast, ZMod.natCast_self]

theorem exists_int_add_mul (c : (Ov w)) : ∃ (n : ℤ) (t : (Ov w)), c = (n : (Ov w)) + (ℓ w : (Ov w)) * t := by
  obtain ⟨t, ht⟩ := (red_eq_zero_iff w (c - (((red w c).val : ℕ) : ℤ))).mp (by
    rw [map_sub, map_intCast, Int.cast_natCast, ZMod.natCast_zmod_val, sub_self])
  exact ⟨(red w c).val, t, by rw [← ht]; ring⟩

theorem natCast_ℓ_ne_zero : ((ℓ w : ℕ) : (Kv w)) ≠ 0 := by
  have := (map_ne_zero (algebraMap ℚ ((Kv w)))).mpr (Nat.cast_ne_zero.mpr (fact_prime_ℓ w).out.ne_zero : ((ℓ w : ℕ) : ℚ) ≠ 0)
  rwa [map_natCast] at this

theorem valued_algebraMap (r : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) = w.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w r

theorem natCast_inv_mem (n : ℕ) (hn : ((n : ℕ) : 𝓞 ℚ) ∉ w.asIdeal) : ((n : (Kv w)))⁻¹ ∈ (Ov w) := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀]
  have h1 : Valued.v ((n : (Kv w))) = 1 := by
    rw [show (n : (Kv w)) = algebraMap ℚ ((Kv w)) (n : ℚ) from (map_natCast _ _).symm, valued_algebraMap,
      show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w) (r := (n : 𝓞 ℚ))).2 hn
  rw [h1, inv_one]

theorem dvd_of_intCast_eq_mul (n : ℤ) (t : (Ov w)) (h : (n : (Ov w)) = (ℓ w : (Ov w)) * t) : (ℓ w : ℤ) ∣ n := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← map_intCast (red w), h, map_mul, red_natCast_ℓ, zero_mul]

end A

section B

variable (w : HeightOneSpectrum (𝓞 ℚ))

def IsInt (A : Matrix (Fin 2) (Fin 2) ((Kv w))) : Prop := ∀ i j, A i j ∈ (Ov w)

def lift (A : Matrix (Fin 2) (Fin 2) ((Kv w))) (hA : IsInt w A) : Matrix (Fin 2) (Fin 2) ((Ov w)) :=
  Matrix.of fun i j => ⟨A i j, hA i j⟩

theorem map_lift (A : Matrix (Fin 2) (Fin 2) ((Kv w))) (hA : IsInt w A) :
    (lift w A hA).map (algebraMap ((Ov w)) ((Kv w))) = A := by
  ext i j; rfl

theorem isInt_map (M : Matrix (Fin 2) (Fin 2) ((Ov w))) : IsInt w (M.map (algebraMap ((Ov w)) ((Kv w)))) :=
  fun i j => (M i j).2

theorem lift_map (M : Matrix (Fin 2) (Fin 2) ((Ov w))) (hM : IsInt w (M.map (algebraMap ((Ov w)) ((Kv w))))) :
    lift w (M.map (algebraMap ((Ov w)) ((Kv w)))) hM = M := by
  ext i j; rfl

theorem map_injective : Function.Injective
    (fun M : Matrix (Fin 2) (Fin 2) ((Ov w)) => M.map (algebraMap ((Ov w)) ((Kv w)))) := by
  intro M M' h
  ext i j : 1
  have := congrFun (congrFun h i) j
  simpa [Matrix.map_apply] using this

theorem IsInt.add {A B : Matrix (Fin 2) (Fin 2) ((Kv w))} (hA : IsInt w A) (hB : IsInt w B) : IsInt w (A + B) :=
  fun i j => by rw [Matrix.add_apply]; exact add_mem (hA i j) (hB i j)

theorem IsInt.neg {A : Matrix (Fin 2) (Fin 2) ((Kv w))} (hA : IsInt w A) : IsInt w (-A) :=
  fun i j => by rw [Matrix.neg_apply]; exact neg_mem (hA i j)

theorem IsInt.sub {A B : Matrix (Fin 2) (Fin 2) ((Kv w))} (hA : IsInt w A) (hB : IsInt w B) : IsInt w (A - B) :=
  fun i j => by rw [Matrix.sub_apply]; exact sub_mem (hA i j) (hB i j)

theorem IsInt.zero : IsInt w (0 : Matrix (Fin 2) (Fin 2) ((Kv w))) := fun i j => by
  rw [Matrix.zero_apply]; exact zero_mem _

theorem IsInt.one : IsInt w (1 : Matrix (Fin 2) (Fin 2) ((Kv w))) := by
  have : (1 : Matrix (Fin 2) (Fin 2) ((Kv w))) = (1 : Matrix (Fin 2) (Fin 2) ((Ov w))).map (algebraMap ((Ov w)) ((Kv w))) := by
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
  rw [this]; exact isInt_map w _

theorem IsInt.mul {A B : Matrix (Fin 2) (Fin 2) ((Kv w))} (hA : IsInt w A) (hB : IsInt w B) : IsInt w (A * B) := by
  rw [← map_lift w A hA, ← map_lift w B hB, ← Matrix.map_mul]
  exact isInt_map w _

theorem IsInt.smul {A : Matrix (Fin 2) (Fin 2) ((Kv w))} (hA : IsInt w A) {c : (Kv w)} (hc : c ∈ (Ov w)) :
    IsInt w (c • A) :=
  fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hA i j)

theorem lift_mul {A B : Matrix (Fin 2) (Fin 2) ((Kv w))} (hA : IsInt w A) (hB : IsInt w B) :
    lift w (A * B) (hA.mul w hB) = lift w A hA * lift w B hB := by
  apply map_injective w
  simp only [Matrix.map_mul, map_lift]

theorem lift_add {A B : Matrix (Fin 2) (Fin 2) ((Kv w))} (hA : IsInt w A) (hB : IsInt w B) :
    lift w (A + B) (hA.add w hB) = lift w A hA + lift w B hB := by
  ext i j; rfl

theorem lift_one : lift w (1 : Matrix (Fin 2) (Fin 2) ((Kv w))) (IsInt.one w) = 1 := by
  apply map_injective w
  simp only [map_lift, Matrix.map_one _ (map_zero _) (map_one _)]

noncomputable def redM (A : Matrix (Fin 2) (Fin 2) ((Kv w))) (hA : IsInt w A) : Matrix (Fin 2) (Fin 2) (ZMod (ℓ w)) :=
  (lift w A hA).map (red w)

theorem redM_congr {A B : Matrix (Fin 2) (Fin 2) ((Kv w))} (hA : IsInt w A) (hB : IsInt w B) (h : A = B) :
    redM w A hA = redM w B hB := by
  subst h; rfl

theorem redM_apply (A : Matrix (Fin 2) (Fin 2) ((Kv w))) (hA : IsInt w A) (i j : Fin 2) :
    redM w A hA i j = red w ⟨A i j, hA i j⟩ := rfl

theorem redM_mul {A B : Matrix (Fin 2) (Fin 2) ((Kv w))} (hA : IsInt w A) (hB : IsInt w B) :
    redM w (A * B) (hA.mul w hB) = redM w A hA * redM w B hB := by
  rw [redM, lift_mul, Matrix.map_mul]; rfl

theorem redM_add {A B : Matrix (Fin 2) (Fin 2) ((Kv w))} (hA : IsInt w A) (hB : IsInt w B) :
    redM w (A + B) (hA.add w hB) = redM w A hA + redM w B hB := by
  rw [redM, lift_add]; exact Matrix.map_add (red w) (map_add (red w)) _ _

theorem redM_one : redM w 1 (IsInt.one w) = 1 := by
  rw [redM, lift_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem redM_ℓ_smul {A : Matrix (Fin 2) (Fin 2) ((Kv w))} (hA : IsInt w A)
    (h : IsInt w (((ℓ w : ℕ) : (Kv w)) • A)) : redM w (((ℓ w : ℕ) : (Kv w)) • A) h = 0 := by
  ext i j
  rw [redM_apply, Matrix.zero_apply]
  have : (⟨(((ℓ w : ℕ) : (Kv w)) • A) i j, h i j⟩ : (Ov w)) = (ℓ w : (Ov w)) * ⟨A i j, hA i j⟩ := by
    apply Subtype.ext
    simp [Matrix.smul_apply]
  rw [this, map_mul, red_natCast_ℓ, zero_mul]

theorem redM_smul {A : Matrix (Fin 2) (Fin 2) ((Kv w))} (hA : IsInt w A) {c : (Kv w)} (hc : c ∈ (Ov w)) :
    redM w (c • A) (hA.smul w hc) = red w ⟨c, hc⟩ • redM w A hA := by
  ext i j
  simp only [redM_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← map_mul]
  congr 1

theorem exists_eq_ℓ_smul_of_redM_eq_zero {A : Matrix (Fin 2) (Fin 2) ((Kv w))} (hA : IsInt w A)
    (h : redM w A hA = 0) : ∃ B : Matrix (Fin 2) (Fin 2) ((Kv w)), IsInt w B ∧ A = ((ℓ w : ℕ) : (Kv w)) • B := by
  have key : ∀ i j, ∃ t : (Ov w), (⟨A i j, hA i j⟩ : (Ov w)) = (ℓ w : (Ov w)) * t := fun i j =>
    (red_eq_zero_iff w _).mp (by rw [← redM_apply, h, Matrix.zero_apply])
  choose t ht using key
  refine ⟨fun i j => (t i j : (Kv w)), fun i j => (t i j).2, ?_⟩
  ext i j : 1
  have := congrArg (fun z : (Ov w) => (z : (Kv w))) (ht i j)
  simpa [Matrix.smul_apply] using this

end B

section A2

variable (w : HeightOneSpectrum (𝓞 ℚ))

theorem isUnit_of_red_ne_zero (c : (Ov w)) (h : red w c ≠ 0) : IsUnit c := by
  set e := (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv (R := 𝓞 ℚ) w).toAlgEquiv.toRingEquiv with he
  have h1 : e c ∉ RingHom.ker (PadicInt.toZMod (p := ℓ w)) := by
    rw [RingHom.mem_ker]; exact h
  rw [PadicInt.ker_toZMod] at h1
  have h2 : IsUnit (e c) := by
    by_contra hc
    exact h1 ((IsLocalRing.mem_maximalIdeal _).mpr hc)
  simpa using h2.map e.symm

theorem exists_eq_mul_of_castHom_eq_zero {N : ℕ} [NeZero N] (hℓN : ℓ w ∣ N) (x : ZMod N)
    (h : ZMod.castHom hℓN (ZMod (ℓ w)) x = 0) : ∃ m : ZMod N, x = (ℓ w : ZMod N) * m := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨(k : ZMod N), ?_⟩
  rw [← ZMod.natCast_zmod_val x, hk, Nat.cast_mul]

end A2

section B2

variable (w : HeightOneSpectrum (𝓞 ℚ))

theorem lift_sub {A B : Matrix (Fin 2) (Fin 2) (Kv w)} (hA : IsInt w A) (hB : IsInt w B) :
    lift w (A - B) (hA.sub w hB) = lift w A hA - lift w B hB := by
  ext i j; rfl

theorem redM_sub {A B : Matrix (Fin 2) (Fin 2) (Kv w)} (hA : IsInt w A) (hB : IsInt w B) :
    redM w (A - B) (hA.sub w hB) = redM w A hA - redM w B hB := by
  rw [redM, lift_sub]; exact Matrix.map_sub (red w) (map_sub (red w)) _ _

theorem redM_map (M : Matrix (Fin 2) (Fin 2) (Ov w)) :
    redM w (M.map (algebraMap (Ov w) (Kv w))) (isInt_map w M) = M.map (red w) := by
  rw [redM, lift_map]

theorem exists_units_redM_eq (u : GL (Fin 2) (ZMod (ℓ w))) :
    ∃ G : GL (Fin 2) (Kv w), ∃ (hG : IsInt w (G : Matrix (Fin 2) (Fin 2) (Kv w)))
      (hG' : IsInt w ((G⁻¹ : GL (Fin 2) (Kv w)) : Matrix (Fin 2) (Fin 2) (Kv w))),
      redM w (G : Matrix (Fin 2) (Fin 2) (Kv w)) hG = (u : Matrix (Fin 2) (Fin 2) (ZMod (ℓ w))) ∧
      redM w ((G⁻¹ : GL (Fin 2) (Kv w)) : Matrix (Fin 2) (Fin 2) (Kv w)) hG' =
        ((u⁻¹ : GL (Fin 2) (ZMod (ℓ w))) : Matrix (Fin 2) (Fin 2) (ZMod (ℓ w))) := by
  classical

  have hlift : ∀ i j, ∃ c : (Ov w), red w c = (u : Matrix (Fin 2) (Fin 2) (ZMod (ℓ w))) i j :=
    fun i j => red_surjective w _
  choose M hM using hlift
  set MO : Matrix (Fin 2) (Fin 2) (Ov w) := Matrix.of fun i j => M i j with hMO
  have hMOred : MO.map (red w) = (u : Matrix (Fin 2) (Fin 2) (ZMod (ℓ w))) := by
    ext i j; simp [hMO, hM]

  have hdet : IsUnit MO.det := by
    apply isUnit_of_red_ne_zero w
    rw [RingHom.map_det, show (red w).mapMatrix MO = MO.map (red w) from rfl, hMOred]
    exact (Matrix.isUnits_det_units u).ne_zero
  obtain ⟨MU, hMU⟩ := (Matrix.isUnit_iff_isUnit_det MO).mpr hdet

  let G : GL (Fin 2) (Kv w) := Units.map ((algebraMap (Ov w) (Kv w)).mapMatrix : Matrix (Fin 2) (Fin 2) (Ov w) →+*
      Matrix (Fin 2) (Fin 2) (Kv w)).toMonoidHom MU
  have hGval : (G : Matrix (Fin 2) (Fin 2) (Kv w)) = MO.map (algebraMap (Ov w) (Kv w)) := by
    simp only [G, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, hMU]; rfl
  have hGinv : ((G⁻¹ : GL (Fin 2) (Kv w)) : Matrix (Fin 2) (Fin 2) (Kv w)) =
      ((MU⁻¹ : (Matrix (Fin 2) (Fin 2) (Ov w))ˣ) : Matrix (Fin 2) (Fin 2) (Ov w)).map (algebraMap (Ov w) (Kv w)) := by
    simp only [G, Units.coe_map_inv]; rfl
  have hG : IsInt w (G : Matrix (Fin 2) (Fin 2) (Kv w)) := by rw [hGval]; exact isInt_map w _
  have hG' : IsInt w ((G⁻¹ : GL (Fin 2) (Kv w)) : Matrix (Fin 2) (Fin 2) (Kv w)) := by rw [hGinv]; exact isInt_map w _
  refine ⟨G, hG, hG', ?_, ?_⟩
  · rw [redM_congr w hG (isInt_map w MO) hGval, redM_map, hMOred]
  · rw [redM_congr w hG' (isInt_map w _) hGinv, redM_map]

    have h1 : ((MU⁻¹ : (Matrix (Fin 2) (Fin 2) (Ov w))ˣ) : Matrix (Fin 2) (Fin 2) (Ov w)).map (red w) *
        (u : Matrix (Fin 2) (Fin 2) (ZMod (ℓ w))) = 1 := by
      rw [← hMOred, ← hMU]
      change (red w).mapMatrix _ * (red w).mapMatrix _ = 1
      rw [← map_mul, Units.inv_mul, map_one]
    calc ((MU⁻¹ : (Matrix (Fin 2) (Fin 2) (Ov w))ˣ) : Matrix (Fin 2) (Fin 2) (Ov w)).map (red w)
        = ((MU⁻¹ : (Matrix (Fin 2) (Fin 2) (Ov w))ˣ) : Matrix (Fin 2) (Fin 2) (Ov w)).map (red w) *
            ((u : Matrix (Fin 2) (Fin 2) (ZMod (ℓ w))) * ((u⁻¹ : GL (Fin 2) (ZMod (ℓ w))) : Matrix _ _ _)) := by
          rw [Units.mul_inv, mul_one]
      _ = ((u⁻¹ : GL (Fin 2) (ZMod (ℓ w))) : Matrix _ _ _) := by rw [← mul_assoc, h1, one_mul]

end B2

section C

variable {a b : ℚ} (w : HeightOneSpectrum (𝓞 ℚ))
variable (φw : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w) ≃+* Matrix (Fin 2) (Fin 2) (Kv w))

def frame (G : GL (Fin 2) (Kv w)) (x : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w)) : Matrix (Fin 2) (Fin 2) (Kv w) :=
  ((G⁻¹ : GL (Fin 2) (Kv w)) : Matrix (Fin 2) (Fin 2) (Kv w)) * φw x * (G : Matrix (Fin 2) (Fin 2) (Kv w))

variable (G : GL (Fin 2) (Kv w))

theorem frame_mul (x y : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w)) :
    frame w φw G (x * y) = frame w φw G x * frame w φw G y := by
  simp only [frame, φw.map_mul, mul_assoc, Units.mul_inv_cancel_left]

theorem frame_add (x y : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w)) :
    frame w φw G (x + y) = frame w φw G x + frame w φw G y := by
  simp only [frame, φw.map_add, mul_add, add_mul]

theorem frame_sub (x y : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w)) :
    frame w φw G (x - y) = frame w φw G x - frame w φw G y := by
  simp only [frame, φw.map_sub, mul_sub, sub_mul]

theorem frame_zero : frame w φw G 0 = 0 := by
  simp only [frame, φw.map_zero, mul_zero, zero_mul]

theorem frame_one : frame w φw G 1 = 1 := by
  simp only [frame, φw.map_one, mul_one, Units.inv_mul]

theorem frame_mul_right (G₀ : GL (Fin 2) (Kv w)) (x : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w)) :
    frame w φw (G * G₀) x = ((G₀⁻¹ : GL (Fin 2) (Kv w)) : Matrix (Fin 2) (Fin 2) (Kv w)) * frame w φw G x *
      (G₀ : Matrix (Fin 2) (Fin 2) (Kv w)) := by
  simp only [frame, mul_inv_rev, Units.val_mul, mul_assoc]

theorem frame_tmul (hφw : ∀ c : (Kv w), φw ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) = c • (1 : Matrix (Fin 2) (Fin 2) (Kv w)))
    (z : ℍ[ℚ, a, b]) (c : (Kv w)) :
    frame w φw G (z ⊗ₜ[ℚ] c) = c • frame w φw G (z ⊗ₜ[ℚ] (1 : (Kv w))) := by
  have : z ⊗ₜ[ℚ] c = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * (z ⊗ₜ[ℚ] (1 : (Kv w))) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [this, frame_mul, show frame w φw G ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) = c • 1 from by
    simp only [frame, hφw, Matrix.mul_smul, Matrix.smul_mul, mul_one, Units.inv_mul], smul_one_mul]

theorem frame_one_tmul_mul (hφw : ∀ c : (Kv w), φw ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) = c • (1 : Matrix (Fin 2) (Fin 2) (Kv w)))
    (c : (Kv w)) (x : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w)) :
    frame w φw G (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x) = c • frame w φw G x := by
  rw [frame_mul, show frame w φw G ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) = c • 1 from by
    simp only [frame, hφw, Matrix.mul_smul, Matrix.smul_mul, mul_one, Units.inv_mul], smul_one_mul]

theorem isInt_frame_mul_iff {G₀ : GL (Fin 2) (Kv w)} (hG₀ : IsInt w (G₀ : Matrix (Fin 2) (Fin 2) (Kv w)))
    (hG₀' : IsInt w ((G₀⁻¹ : GL (Fin 2) (Kv w)) : Matrix (Fin 2) (Fin 2) (Kv w))) (x : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w)) :
    IsInt w (frame w φw (G * G₀) x) ↔ IsInt w (frame w φw G x) := by
  rw [frame_mul_right]
  constructor
  · intro h
    have : frame w φw G x = (G₀ : Matrix (Fin 2) (Fin 2) (Kv w)) *
        (((G₀⁻¹ : GL (Fin 2) (Kv w)) : Matrix (Fin 2) (Fin 2) (Kv w)) * frame w φw G x * (G₀ : Matrix (Fin 2) (Fin 2) (Kv w))) *
        ((G₀⁻¹ : GL (Fin 2) (Kv w)) : Matrix (Fin 2) (Fin 2) (Kv w)) := by
      simp only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one]
    rw [this]
    exact (hG₀.mul w h).mul w hG₀'
  · intro h
    exact (hG₀'.mul w h).mul w hG₀

theorem smul_tmul_one (q : ℚ) (z : ℍ[ℚ, a, b]) :
    (q • z) ⊗ₜ[ℚ] (1 : (Kv w)) = z ⊗ₜ[ℚ] (algebraMap ℚ (Kv w) q) := by
  rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

end C

section Coords

variable {a b : ℚ} (w : HeightOneSpectrum (𝓞 ℚ))

theorem coords_unique (B : Module.Basis (Fin 4) ℚ ℍ[ℚ, a, b]) (c d : Fin 4 → (Kv w))
    (h : ∑ i, B i ⊗ₜ[ℚ] c i = ∑ i, B i ⊗ₜ[ℚ] d i) : c = d := by
  classical
  have key : ∀ e : Fin 4 → (Kv w), ∀ j,
      (Algebra.TensorProduct.basis (Kv w) B).repr
        (Algebra.TensorProduct.comm ℚ ℍ[ℚ, a, b] (Kv w) (∑ i, B i ⊗ₜ[ℚ] e i)) j = e j := by
    intro e j
    rw [map_sum (Algebra.TensorProduct.comm ℚ ℍ[ℚ, a, b] (Kv w)), map_sum (Algebra.TensorProduct.basis (Kv w) B).repr,
      Finsupp.finset_sum_apply]
    simp only [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.basis_repr_tmul,
      Module.Basis.repr_self, Finsupp.mapRange_single, map_one, Finsupp.smul_single, smul_eq_mul, mul_one,
      Finsupp.single_apply]
    simp [Finset.sum_ite_eq']
  funext j
  rw [← key c j, ← key d j, h]

end Coords

structure Setup (a b : ℚ) where
  w : HeightOneSpectrum (𝓞 ℚ)
  R : Submodule ℤ ℍ[ℚ, a, b]
  hR : QuaternionAlgebra.IsOrder R
  φw : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w) ≃+* Matrix (Fin 2) (Fin 2) (Kv w)
  hφw : ∀ c : (Kv w), φw ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) = c • (1 : Matrix (Fin 2) (Fin 2) (Kv w))
  h : GL (Fin 2) (Kv w)
  hRw : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w), x ∈ Submodule.localBox R w ↔ IsInt w (frame w φw h x)
  N : ℕ
  hN : NeZero N
  hℓN : ℓ w ∣ N
  hℓℓN : ¬ ℓ w ^ 2 ∣ N
  φ : ↥R →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod N)
  hφ1 : ∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ R, φ ⟨1, h1⟩ = 1
  hφmul : ∀ (x y : ↥R) (hxy : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ R),
    φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ = φ x * φ y
  hφsurj : Function.Surjective φ
  hφker : ∀ x : ↥R, φ x = 0 ↔ ∃ y : ↥R, (x : ℍ[ℚ, a, b]) = (N : ℚ) • (y : ℍ[ℚ, a, b])
  R₀ : Submodule ℤ ℍ[ℚ, a, b]
  hR₀ : ∀ x : ↥R, (x : ℍ[ℚ, a, b]) ∈ R₀ ↔ φ x 1 0 = 0
  hR₀R : R₀ ≤ R

namespace Setup

variable {a b : ℚ} (S : Setup a b)

scoped instance : NeZero S.N := S.hN

theorem tmul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) {c : Kv S.w} (hc : c ∈ Ov S.w) :
    z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ S.w :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

def θK (x : ↥S.R) : Matrix (Fin 2) (Fin 2) (Kv S.w) :=
  frame S.w S.φw S.h ((x : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : Kv S.w))

theorem isInt_θK (x : ↥S.R) : IsInt S.w (S.θK x) :=
  (S.hRw _).1 (S.tmul_mem_localBox x.2 (one_mem _))

def θbar (x : ↥S.R) : Matrix (Fin 2) (Fin 2) (ZMod (ℓ S.w)) :=
  redM S.w (S.θK x) (S.isInt_θK x)

def φbar (x : ↥S.R) : Matrix (Fin 2) (Fin 2) (ZMod (ℓ S.w)) :=
  (S.φ x).map (ZMod.castHom S.hℓN (ZMod (ℓ S.w)))

def oneR : ↥S.R := ⟨1, S.hR.one_mem⟩

def mulR (x y : ↥S.R) : ↥S.R := ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), S.hR.mul_mem x.2 y.2⟩

theorem θK_one : S.θK S.oneR = 1 := by
  rw [θK, show ((S.oneR : ↥S.R) : ℍ[ℚ, a, b]) = 1 from rfl, show ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : Kv S.w)) =
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] (Kv S.w)) from rfl, frame_one]

theorem θK_mul (x y : ↥S.R) : S.θK (S.mulR x y) = S.θK x * S.θK y := by
  rw [θK, θK, θK, ← frame_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]; rfl

theorem θK_add (x y : ↥S.R) : S.θK (x + y) = S.θK x + S.θK y := by
  rw [θK, θK, θK, ← frame_add, Submodule.coe_add, TensorProduct.add_tmul]

theorem θK_sub (x y : ↥S.R) : S.θK (x - y) = S.θK x - S.θK y := by
  rw [θK, θK, θK, ← frame_sub, Submodule.coe_sub, TensorProduct.sub_tmul]

theorem θbar_one : S.θbar S.oneR = 1 := by
  rw [θbar, redM_congr S.w (S.isInt_θK _) (IsInt.one S.w) S.θK_one, redM_one]

theorem θbar_mul (x y : ↥S.R) : S.θbar (S.mulR x y) = S.θbar x * S.θbar y := by
  rw [θbar, redM_congr S.w (S.isInt_θK _) ((S.isInt_θK x).mul S.w (S.isInt_θK y)) (S.θK_mul x y), redM_mul]; rfl

theorem θbar_add (x y : ↥S.R) : S.θbar (x + y) = S.θbar x + S.θbar y := by
  rw [θbar, redM_congr S.w (S.isInt_θK _) ((S.isInt_θK x).add S.w (S.isInt_θK y)) (S.θK_add x y), redM_add]; rfl

theorem θbar_sub (x y : ↥S.R) : S.θbar (x - y) = S.θbar x - S.θbar y := by
  rw [θbar, redM_congr S.w (S.isInt_θK _) ((S.isInt_θK x).sub S.w (S.isInt_θK y)) (S.θK_sub x y), redM_sub]; rfl

theorem φbar_one : S.φbar S.oneR = 1 := by
  rw [φbar, show S.φ S.oneR = 1 from S.hφ1 S.hR.one_mem, Matrix.map_one _ (map_zero _) (map_one _)]

theorem φbar_mul (x y : ↥S.R) : S.φbar (S.mulR x y) = S.φbar x * S.φbar y := by
  rw [φbar, show S.φ (S.mulR x y) = S.φ x * S.φ y from S.hφmul x y _, Matrix.map_mul]; rfl

theorem φbar_add (x y : ↥S.R) : S.φbar (x + y) = S.φbar x + S.φbar y := by
  rw [φbar, map_add]; exact Matrix.map_add _ (map_add _) _ _

theorem φbar_sub (x y : ↥S.R) : S.φbar (x - y) = S.φbar x - S.φbar y := by
  rw [φbar, map_sub]; exact Matrix.map_sub _ (map_sub _) _ _

theorem φbar_nsmul (n : ℕ) (x : ↥S.R) : S.φbar (n • x) = n • S.φbar x := by
  rw [φbar, map_nsmul]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, map_nsmul]
  rfl

theorem coe_zsmul (n : ℤ) (x : ↥S.R) : (((n • x : ↥S.R)) : ℍ[ℚ, a, b]) = (n : ℚ) • (x : ℍ[ℚ, a, b]) := by
  rw [Submodule.coe_smul_of_tower, Int.cast_smul_eq_zsmul]

end Setup
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsOrder_exists_localBox_iff_and_localBox_iff_conj_diagonal_of_linearMap_matrix_zmod.S4Local.Setup"

namespace Setup

variable {a b : ℚ} (S : Setup a b)

theorem ℓK_ne_zero : ((ℓ S.w : ℕ) : Kv S.w) ≠ 0 := natCast_ℓ_ne_zero S.w

theorem ℓK_mem : ((ℓ S.w : ℕ) : Kv S.w) ∈ Ov S.w := natCast_mem _ _

theorem θbar_zero : S.θbar 0 = 0 := by simpa using S.θbar_sub 0 0

theorem φbar_zero : S.φbar 0 = 0 := by simpa using S.φbar_sub 0 0

theorem θbar_nsmul (n : ℕ) (x : ↥S.R) : S.θbar (n • x) = n • S.θbar x := by
  induction n with
  | zero => rw [zero_smul, zero_smul, S.θbar_zero]
  | succ n ih => rw [add_smul, add_smul, one_smul, one_smul, S.θbar_add, ih]

theorem exists_basis : ∃ B : Module.Basis (Fin 4) ℚ ℍ[ℚ, a, b], (∀ i, B i ∈ S.R) ∧
    Submodule.span ℤ (Set.range B) = S.R :=
  QuaternionAlgebra.IsOrder.exists_basis_span_eq S.hR

theorem exists_eq_smul_of_tmul_inv_mem (z : ↥S.R)
    (hz : (z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (((ℓ S.w : ℕ) : Kv S.w))⁻¹ ∈ Submodule.localBox S.R S.w) :
    ∃ y : ↥S.R, (z : ℍ[ℚ, a, b]) = ((ℓ S.w : ℕ) : ℚ) • (y : ℍ[ℚ, a, b]) := by
  classical
  have hL0 := S.ℓK_ne_zero
  obtain ⟨B, hBR, hspan⟩ := S.exists_basis
  obtain ⟨c, hc, hzc⟩ := (Submodule.mem_localBox_iff_exists_eq_sum_basis_tmul B S.R hspan S.w _).1 hz
  have hzspan : (z : ℍ[ℚ, a, b]) ∈ Submodule.span ℤ (Set.range B) := by rw [hspan]; exact z.2
  obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hzspan
  have key : ∀ i, c i = algebraMap ℚ (Kv S.w) (n i : ℚ) * (((ℓ S.w : ℕ) : Kv S.w))⁻¹ := by
    have hsum : (z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (((ℓ S.w : ℕ) : Kv S.w))⁻¹ =
        ∑ i, B i ⊗ₜ[ℚ] (algebraMap ℚ (Kv S.w) (n i : ℚ) * (((ℓ S.w : ℕ) : Kv S.w))⁻¹) := by
      rw [← hn, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℚ, TensorProduct.smul_tmul, Algebra.smul_def]
    have := coords_unique S.w B c _ (hzc.symm.trans hsum)
    exact fun i => congrFun this i
  have hdvd : ∀ i, ((ℓ S.w : ℕ) : ℤ) ∣ n i := by
    intro i
    have e : ((n i : ℤ) : Kv S.w) = ((ℓ S.w : ℕ) : Kv S.w) * c i := by
      rw [key i, map_intCast, mul_left_comm, mul_inv_cancel₀ hL0, mul_one]
    apply dvd_of_intCast_eq_mul S.w (n i) ⟨c i, hc i⟩
    apply Subtype.ext
    simpa using e
  choose k hk using hdvd
  refine ⟨⟨∑ i, k i • B i, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hBR i)⟩, ?_⟩
  show (z : ℍ[ℚ, a, b]) = ((ℓ S.w : ℕ) : ℚ) • ∑ i, k i • B i
  rw [← hn, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hk i, ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ (k i), smul_smul, Int.cast_mul, Int.cast_natCast]

theorem φbar_eq_zero_iff (x : ↥S.R) :
    S.φbar x = 0 ↔ ∃ y : ↥S.R, (x : ℍ[ℚ, a, b]) = ((ℓ S.w : ℕ) : ℚ) • (y : ℍ[ℚ, a, b]) := by
  constructor
  · intro hx
    have hent : ∀ i j, ∃ m : ZMod S.N, S.φ x i j = (ℓ S.w : ZMod S.N) * m := fun i j =>
      exists_eq_mul_of_castHom_eq_zero S.w S.hℓN _ (by
        have := congrFun (congrFun hx i) j
        simpa [φbar, Matrix.map_apply] using this)
    choose m hm using hent
    obtain ⟨t, ht⟩ := S.hφsurj (Matrix.of fun i j => m i j)
    have h0 : S.φ (x - ((ℓ S.w : ℕ) : ℤ) • t) = 0 := by
      rw [map_sub, map_zsmul, ht]
      ext i j
      rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, hm, zsmul_eq_mul, Int.cast_natCast,
        Matrix.zero_apply, sub_self]
    obtain ⟨y', hy'⟩ := (S.hφker _).1 h0
    refine ⟨t + ((S.N / ℓ S.w : ℕ) : ℤ) • y', ?_⟩
    have hN : ((ℓ S.w : ℕ) : ℚ) * ((S.N / ℓ S.w : ℕ) : ℚ) = (S.N : ℚ) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' S.hℓN]
    have e1 : (((x - ((ℓ S.w : ℕ) : ℤ) • t : ↥S.R)) : ℍ[ℚ, a, b]) =
        (x : ℍ[ℚ, a, b]) - ((ℓ S.w : ℕ) : ℚ) • (t : ℍ[ℚ, a, b]) := by
      rw [Submodule.coe_sub, coe_zsmul, Int.cast_natCast]
    rw [e1] at hy'
    rw [Submodule.coe_add, coe_zsmul, Int.cast_natCast, smul_add, smul_smul, hN, ← hy']
    abel
  · rintro ⟨y, hy⟩
    have : x = ((ℓ S.w : ℕ) : ℤ) • y := by
      apply Subtype.ext
      rw [hy, coe_zsmul, Int.cast_natCast]
    rw [this, φbar, map_zsmul]
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, zsmul_eq_mul, Int.cast_natCast, map_mul, map_natCast,
      ZMod.natCast_self, zero_mul, Matrix.zero_apply]

theorem θbar_eq_zero_iff (x : ↥S.R) :
    S.θbar x = 0 ↔ ∃ y : ↥S.R, (x : ℍ[ℚ, a, b]) = ((ℓ S.w : ℕ) : ℚ) • (y : ℍ[ℚ, a, b]) := by
  have hL0 := S.ℓK_ne_zero
  constructor
  · intro hx
    obtain ⟨Bm, hBm, hθ⟩ := exists_eq_ℓ_smul_of_redM_eq_zero S.w (S.isInt_θK x) hx
    apply S.exists_eq_smul_of_tmul_inv_mem
    rw [S.hRw]
    have : frame S.w S.φw S.h ((x : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (((ℓ S.w : ℕ) : Kv S.w))⁻¹) = Bm := by
      rw [frame_tmul S.w S.φw S.h S.hφw, show frame S.w S.φw S.h ((x : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : Kv S.w)) = S.θK x
        from rfl, hθ, smul_smul, inv_mul_cancel₀ hL0, one_smul]
    rw [this]; exact hBm
  · rintro ⟨y, hy⟩
    have e : S.θK x = ((ℓ S.w : ℕ) : Kv S.w) • S.θK y := by
      rw [θK, θK, hy, smul_tmul_one, map_natCast, frame_tmul S.w S.φw S.h S.hφw]
    rw [θbar, redM_congr S.w (S.isInt_θK x) ((S.isInt_θK y).smul S.w S.ℓK_mem) e]
    exact redM_ℓ_smul S.w (S.isInt_θK y) _

theorem exists_tmul_add_mul (u : ℍ[ℚ, a, b] ⊗[ℚ] (Kv S.w)) (hu : u ∈ Submodule.localBox S.R S.w) :
    ∃ z : ↥S.R, ∃ t ∈ Submodule.localBox S.R S.w,
      u = (z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : Kv S.w) + ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((ℓ S.w : ℕ) : Kv S.w)) * t := by
  refine AddSubgroup.closure_induction (p := fun u _ => ∃ z : ↥S.R, ∃ t ∈ Submodule.localBox S.R S.w,
      u = (z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : Kv S.w) + ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((ℓ S.w : ℕ) : Kv S.w)) * t)
    ?_ ?_ ?_ ?_ hu
  · rintro x ⟨z, hz, c, hc, rfl⟩
    obtain ⟨n, t, hct⟩ := exists_int_add_mul S.w ⟨c, hc⟩
    have hc' : c = ((n : ℤ) : Kv S.w) + ((ℓ S.w : ℕ) : Kv S.w) * (t : Kv S.w) := by
      have := congrArg (fun z : Ov S.w => (z : Kv S.w)) hct
      simpa using this
    refine ⟨n • ⟨z, hz⟩, z ⊗ₜ[ℚ] (t : Kv S.w), S.tmul_mem_localBox hz t.2, ?_⟩
    rw [hc', TensorProduct.tmul_add, coe_zsmul, show ((⟨z, hz⟩ : ↥S.R) : ℍ[ℚ, a, b]) = z from rfl, smul_tmul_one,
      map_intCast, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  · exact ⟨0, 0, zero_mem _, by rw [Submodule.coe_zero, TensorProduct.zero_tmul, mul_zero, add_zero]⟩
  · rintro x y _ _ ⟨z₁, t₁, ht₁, rfl⟩ ⟨z₂, t₂, ht₂, rfl⟩
    refine ⟨z₁ + z₂, t₁ + t₂, add_mem ht₁ ht₂, ?_⟩
    rw [Submodule.coe_add, TensorProduct.add_tmul, mul_add]
    abel
  · rintro x _ ⟨z, t, ht, rfl⟩
    refine ⟨-z, -t, neg_mem ht, ?_⟩
    have h1 : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((ℓ S.w : ℕ) : Kv S.w)) * (-t) +
        ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((ℓ S.w : ℕ) : Kv S.w)) * t = 0 := by
      rw [← mul_add, neg_add_cancel, mul_zero]
    rw [Submodule.coe_neg, TensorProduct.neg_tmul, eq_neg_of_add_eq_zero_left h1, neg_add]

theorem θbar_surjective : Function.Surjective S.θbar := by
  classical
  intro X
  have hl : ∀ i j, ∃ c : Ov S.w, red S.w c = X i j := fun i j => red_surjective S.w _
  choose M hM using hl
  let MO : Matrix (Fin 2) (Fin 2) (Ov S.w) := Matrix.of fun i j => M i j
  let A : Matrix (Fin 2) (Fin 2) (Kv S.w) := MO.map (algebraMap (Ov S.w) (Kv S.w))
  have hAint : IsInt S.w A := isInt_map S.w MO
  have hAred : redM S.w A hAint = X := by
    rw [show redM S.w A hAint = MO.map (red S.w) from redM_map S.w MO]
    ext i j; simp [MO, hM]
  let u : ℍ[ℚ, a, b] ⊗[ℚ] (Kv S.w) := S.φw.symm ((S.h : Matrix (Fin 2) (Fin 2) (Kv S.w)) * A *
    ((S.h⁻¹ : GL (Fin 2) (Kv S.w)) : Matrix (Fin 2) (Fin 2) (Kv S.w)))
  have hframe : frame S.w S.φw S.h u = A := by
    simp only [frame, u, RingEquiv.apply_symm_apply, mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]
  have hu : u ∈ Submodule.localBox S.R S.w := by rw [S.hRw, hframe]; exact hAint
  obtain ⟨z, t, ht, hzt⟩ := S.exists_tmul_add_mul u hu
  refine ⟨z, ?_⟩
  have htint : IsInt S.w (frame S.w S.φw S.h t) := (S.hRw t).1 ht
  have htint' : IsInt S.w (((ℓ S.w : ℕ) : Kv S.w) • frame S.w S.φw S.h t) := htint.smul S.w S.ℓK_mem
  have hB : IsInt S.w (S.θK z + ((ℓ S.w : ℕ) : Kv S.w) • frame S.w S.φw S.h t) := (S.isInt_θK z).add S.w htint'
  have e : A = S.θK z + ((ℓ S.w : ℕ) : Kv S.w) • frame S.w S.φw S.h t := by
    rw [← hframe, hzt, frame_add, frame_one_tmul_mul S.w S.φw S.h S.hφw]; rfl
  have h1 : redM S.w A hAint = redM S.w _ hB := redM_congr S.w hAint hB e
  have h2 : redM S.w _ hB = redM S.w (S.θK z) (S.isInt_θK z) + redM S.w _ htint' := redM_add S.w _ _
  have h3 : redM S.w _ htint' = 0 := redM_ℓ_smul S.w htint htint'
  rw [← hAred, h1, h2, h3, add_zero]
  rfl

theorem φbar_surjective : Function.Surjective S.φbar := by
  classical
  intro Y
  have hl : ∀ i j, ∃ m : ZMod S.N, ZMod.castHom S.hℓN (ZMod (ℓ S.w)) m = Y i j := fun i j =>
    ZMod.ringHom_surjective _ _
  choose m hm using hl
  obtain ⟨x, hx⟩ := S.hφsurj (Matrix.of fun i j => m i j)
  exact ⟨x, by ext i j; simp [φbar, hx, hm]⟩

theorem exists_conj : ∃ u : GL (Fin 2) (ZMod (ℓ S.w)), ∀ x : ↥S.R,
    S.θbar x = (u : Matrix (Fin 2) (Fin 2) (ZMod (ℓ S.w))) * S.φbar x *
      ((u⁻¹ : GL (Fin 2) (ZMod (ℓ S.w))) : Matrix (Fin 2) (Fin 2) (ZMod (ℓ S.w))) := by
  classical
  have hwd : ∀ x y : ↥S.R, S.φbar x = S.φbar y → S.θbar x = S.θbar y := by
    intro x y hxy
    have h0 : S.φbar (x - y) = 0 := by rw [S.φbar_sub, hxy, sub_self]
    obtain ⟨t, ht⟩ := (S.φbar_eq_zero_iff _).1 h0
    have h1 : S.θbar (x - y) = 0 := (S.θbar_eq_zero_iff _).2 ⟨t, ht⟩
    rwa [S.θbar_sub, sub_eq_zero] at h1
  choose pre hpre using S.φbar_surjective
  let f₀ : Matrix (Fin 2) (Fin 2) (ZMod (ℓ S.w)) → Matrix (Fin 2) (Fin 2) (ZMod (ℓ S.w)) := fun Y => S.θbar (pre Y)
  have hf₀ : ∀ x, f₀ (S.φbar x) = S.θbar x := fun x => hwd _ _ (hpre _)
  have hf₀_mul : ∀ X Y, f₀ (X * Y) = f₀ X * f₀ Y := by
    intro X Y
    conv_lhs => rw [← hpre X, ← hpre Y, ← S.φbar_mul, hf₀]
    rw [S.θbar_mul]
  have hf₀_add : ∀ X Y, f₀ (X + Y) = f₀ X + f₀ Y := by
    intro X Y
    conv_lhs => rw [← hpre X, ← hpre Y, ← S.φbar_add, hf₀]
    rw [S.θbar_add]
  have hf₀_one : f₀ 1 = 1 := by
    conv_lhs => rw [← S.φbar_one]
    rw [hf₀, S.θbar_one]
  have hf₀_zero : f₀ 0 = 0 := by
    conv_lhs => rw [← S.φbar_zero]
    rw [hf₀, S.θbar_zero]
  have hf₀_smul : ∀ (r : ZMod (ℓ S.w)) (X : Matrix (Fin 2) (Fin 2) (ZMod (ℓ S.w))), f₀ (r • X) = r • f₀ X := by
    intro r X
    conv_lhs => rw [← ZMod.natCast_zmod_val r, Nat.cast_smul_eq_nsmul, ← hpre X, ← S.φbar_nsmul, hf₀]
    rw [S.θbar_nsmul, ← ZMod.natCast_zmod_val r, Nat.cast_smul_eq_nsmul, ZMod.natCast_zmod_val]
  let f : Matrix (Fin 2) (Fin 2) (ZMod (ℓ S.w)) →ₐ[ZMod (ℓ S.w)] Matrix (Fin 2) (Fin 2) (ZMod (ℓ S.w)) :=
    { toFun := f₀, map_one' := hf₀_one, map_mul' := hf₀_mul, map_zero' := hf₀_zero, map_add' := hf₀_add,
      commutes' := fun r => by
        rw [Algebra.algebraMap_eq_smul_one, hf₀_smul, hf₀_one] }
  obtain ⟨u, hu⟩ := Matrix.exists_generalLinearGroup_forall_algHom_apply_eq_conj (ZMod (ℓ S.w)) (Fin 2) f
  refine ⟨u, fun x => ?_⟩
  rw [← hu (S.φbar x)]
  exact (hf₀ x).symm

end Setup
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsOrder_exists_localBox_iff_and_localBox_iff_conj_diagonal_of_linearMap_matrix_zmod.S4Local.Setup"

section C2

variable {a b : ℚ} (w : HeightOneSpectrum (𝓞 ℚ))
variable (φw : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w) ≃+* Matrix (Fin 2) (Fin 2) (Kv w)) (G : GL (Fin 2) (Kv w))

theorem frame_neg (x : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w)) : frame w φw G (-x) = -frame w φw G x := by
  rw [eq_neg_iff_add_eq_zero, ← frame_add, neg_add_cancel, frame_zero]

theorem isInt_diag_conj_iff (x : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w)) (hX : IsInt w (frame w φw G x)) :
    (∀ i j, (Matrix.diagonal ![(1 : Kv w), (((ℓ w : ℕ) : Kv w))⁻¹] *
        ((G⁻¹ : GL (Fin 2) (Kv w)) : Matrix (Fin 2) (Fin 2) (Kv w)) * φw x *
        (G : Matrix (Fin 2) (Fin 2) (Kv w)) *
        Matrix.diagonal ![(1 : Kv w), ((ℓ w : ℕ) : Kv w)]) i j ∈ (Ov w)) ↔
      (((ℓ w : ℕ) : Kv w))⁻¹ * frame w φw G x 1 0 ∈ (Ov w) := by
  have hL0 := natCast_ℓ_ne_zero w
  have e : Matrix.diagonal ![(1 : Kv w), (((ℓ w : ℕ) : Kv w))⁻¹] *
        ((G⁻¹ : GL (Fin 2) (Kv w)) : Matrix (Fin 2) (Fin 2) (Kv w)) * φw x *
        (G : Matrix (Fin 2) (Fin 2) (Kv w)) *
        Matrix.diagonal ![(1 : Kv w), ((ℓ w : ℕ) : Kv w)] =
      Matrix.diagonal ![(1 : Kv w), (((ℓ w : ℕ) : Kv w))⁻¹] * frame w φw G x *
        Matrix.diagonal ![(1 : Kv w), ((ℓ w : ℕ) : Kv w)] := by
    simp only [frame, mul_assoc]
  rw [e]
  have hent : ∀ i j, (Matrix.diagonal ![(1 : Kv w), (((ℓ w : ℕ) : Kv w))⁻¹] * frame w φw G x *
        Matrix.diagonal ![(1 : Kv w), ((ℓ w : ℕ) : Kv w)]) i j =
      ![(1 : Kv w), (((ℓ w : ℕ) : Kv w))⁻¹] i * frame w φw G x i j * ![(1 : Kv w), ((ℓ w : ℕ) : Kv w)] j := by
    intro i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  constructor
  · intro h
    have := h 1 0
    rw [hent] at this
    simpa using this
  · intro h i j
    rw [hent]
    fin_cases i <;> fin_cases j
    · simpa using hX 0 0
    · simpa using mul_mem (hX 0 1) (natCast_mem (Ov w) (ℓ w))
    · simpa using h
    · have : (((ℓ w : ℕ) : Kv w))⁻¹ * frame w φw G x 1 1 * ((ℓ w : ℕ) : Kv w) = frame w φw G x 1 1 := by
        rw [mul_assoc, mul_comm (frame w φw G x 1 1), ← mul_assoc, inv_mul_cancel₀ hL0, one_mul]
      simpa [this] using hX 1 1

end C2
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsOrder_exists_localBox_iff_and_localBox_iff_conj_diagonal_of_linearMap_matrix_zmod.S4Local.Setup"

namespace Setup

variable {a b : ℚ} (S : Setup a b)

theorem natCast_smul_mem_R₀ (z : ℍ[ℚ, a, b]) (hz : z ∈ S.R) : ((S.N : ℕ) : ℤ) • z ∈ S.R₀ := by
  have hmem : ((S.N : ℕ) : ℤ) • z ∈ S.R := S.R.smul_mem _ hz
  have h0 : S.φ ⟨((S.N : ℕ) : ℤ) • z, hmem⟩ = 0 := by
    have : (⟨((S.N : ℕ) : ℤ) • z, hmem⟩ : ↥S.R) = ((S.N : ℕ) : ℤ) • (⟨z, hz⟩ : ↥S.R) := rfl
    rw [this, map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod S.N), Int.cast_natCast, ZMod.natCast_self, zero_smul]
  exact (S.hR₀ ⟨_, hmem⟩).2 (by rw [h0]; rfl)

theorem natCast_div_not_mem : (((S.N / ℓ S.w : ℕ)) : 𝓞 ℚ) ∉ S.w.asIdeal := by
  intro h
  rw [natCast_mem_asIdeal_iff] at h
  apply S.hℓℓN
  rw [pow_two, ← Nat.mul_div_cancel' S.hℓN]
  exact Nat.mul_dvd_mul_left _ h

theorem mul_mem_localBox_R₀ (y : ℍ[ℚ, a, b] ⊗[ℚ] (Kv S.w)) (hy : y ∈ Submodule.localBox S.R S.w) :
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((ℓ S.w : ℕ) : Kv S.w)) * y ∈ Submodule.localBox S.R₀ S.w := by
  refine AddSubgroup.closure_induction
    (p := fun y _ => ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((ℓ S.w : ℕ) : Kv S.w)) * y ∈ Submodule.localBox S.R₀ S.w) ?_ ?_ ?_ ?_ hy
  · rintro x ⟨z, hz, c, hc, rfl⟩
    have hNm : S.N = ℓ S.w * (S.N / ℓ S.w) := (Nat.mul_div_cancel' S.hℓN).symm
    have hm0 : ((S.N / ℓ S.w : ℕ) : Kv S.w) ≠ 0 := by
      have hne : (S.N / ℓ S.w : ℕ) ≠ 0 := fun h0 => by
        have := NeZero.ne S.N
        rw [hNm, h0, mul_zero] at this
        exact this rfl
      have := (map_ne_zero (algebraMap ℚ (Kv S.w))).mpr (Nat.cast_ne_zero.mpr hne : ((S.N / ℓ S.w : ℕ) : ℚ) ≠ 0)
      rwa [map_natCast] at this
    have e : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((ℓ S.w : ℕ) : Kv S.w)) * (z ⊗ₜ[ℚ] c) =
        ((((S.N : ℕ) : ℤ) • z) ⊗ₜ[ℚ] ((((S.N / ℓ S.w : ℕ) : Kv S.w))⁻¹ * c)) := by
      have hNK : ((S.N : ℕ) : Kv S.w) = ((ℓ S.w : ℕ) : Kv S.w) * ((S.N / ℓ S.w : ℕ) : Kv S.w) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' S.hℓN]
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast,
        TensorProduct.smul_tmul, Algebra.smul_def, map_natCast, hNK, mul_assoc,
        ← mul_assoc ((S.N / ℓ S.w : ℕ) : Kv S.w), mul_inv_cancel₀ hm0, one_mul]
    beta_reduce
    rw [e]
    exact S.tmul_mem_localBox (S.natCast_smul_mem_R₀ z hz)
      (mul_mem (natCast_inv_mem S.w _ S.natCast_div_not_mem) hc)
  · beta_reduce; rw [mul_zero]; exact zero_mem _
  · intro x y _ _ hx hy; beta_reduce; rw [mul_add]; exact add_mem hx hy
  · intro x _ hx
    beta_reduce
    have h1 : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((ℓ S.w : ℕ) : Kv S.w)) * (-x) +
        ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((ℓ S.w : ℕ) : Kv S.w)) * x = 0 := by
      rw [← mul_add, neg_add_cancel, mul_zero]
    rw [eq_neg_of_add_eq_zero_left h1]; exact neg_mem hx

end Setup
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsOrder_exists_localBox_iff_and_localBox_iff_conj_diagonal_of_linearMap_matrix_zmod.S4Local.Setup"

namespace Setup

variable {a b : ℚ} (S : Setup a b)

set_option maxHeartbeats 3200000 in

theorem final : ∃ G₀ : GL (Fin 2) (Kv S.w), IsInt S.w (G₀ : Matrix (Fin 2) (Fin 2) (Kv S.w)) ∧
    IsInt S.w ((G₀⁻¹ : GL (Fin 2) (Kv S.w)) : Matrix (Fin 2) (Fin 2) (Kv S.w)) ∧
    ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] (Kv S.w), x ∈ Submodule.localBox S.R₀ S.w ↔
      IsInt S.w (frame S.w S.φw (S.h * G₀) x) ∧
        (((ℓ S.w : ℕ) : Kv S.w))⁻¹ * frame S.w S.φw (S.h * G₀) x 1 0 ∈ Ov S.w := by
  classical
  have hL0 := S.ℓK_ne_zero
  obtain ⟨u, hu⟩ := S.exists_conj
  obtain ⟨G₀, hG, hG', hGred, hG'red⟩ := exists_units_redM_eq S.w u
  refine ⟨G₀, hG, hG', ?_⟩

  have hE1 : ∀ x, IsInt S.w (frame S.w S.φw (S.h * G₀) x) ↔ x ∈ Submodule.localBox S.R S.w := fun x => by
    rw [S.hRw]; exact isInt_frame_mul_iff S.w S.φw S.h hG hG' x
  have hint : ∀ z : ↥S.R, IsInt S.w (frame S.w S.φw (S.h * G₀) ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : Kv S.w))) :=
    fun z => (hE1 _).2 (S.tmul_mem_localBox z.2 (one_mem _))

  have hE2 : ∀ z : ↥S.R, redM S.w _ (hint z) = S.φbar z := by
    intro z
    rw [redM_congr S.w (hint z) ((hG'.mul S.w (S.isInt_θK z)).mul S.w hG) (frame_mul_right S.w S.φw S.h G₀ _),
      redM_mul S.w (hG'.mul S.w (S.isInt_θK z)) hG, redM_mul S.w hG' (S.isInt_θK z), hG'red, hGred,
      show redM S.w (S.θK z) (S.isInt_θK z) = S.θbar z from rfl, hu z]
    simp only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]

  have hE3 : ∀ z : ↥S.R, (z : ℍ[ℚ, a, b]) ∈ S.R₀ →
      (((ℓ S.w : ℕ) : Kv S.w))⁻¹ * frame S.w S.φw (S.h * G₀) ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : Kv S.w)) 1 0 ∈ Ov S.w := by
    intro z hz
    have h1 : S.φbar z 1 0 = 0 := by
      rw [φbar, Matrix.map_apply, (S.hR₀ z).1 hz, map_zero]
    rw [← hE2 z, redM_apply] at h1
    obtain ⟨t, ht⟩ := (red_eq_zero_iff S.w _).1 h1
    have ht' := congrArg (fun z : Ov S.w => (z : Kv S.w)) ht
    simp only [Subring.coe_mul, SubringClass.coe_natCast] at ht'
    have : frame S.w S.φw (S.h * G₀) ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : Kv S.w)) 1 0 = ((ℓ S.w : ℕ) : Kv S.w) * (t : Kv S.w) := by
      simpa using ht'
    rw [this, ← mul_assoc, inv_mul_cancel₀ hL0, one_mul]
    exact t.2

  let T : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] (Kv S.w)) :=
    { carrier := {x | IsInt S.w (frame S.w S.φw (S.h * G₀) x) ∧
        (((ℓ S.w : ℕ) : Kv S.w))⁻¹ * frame S.w S.φw (S.h * G₀) x 1 0 ∈ Ov S.w}
      add_mem' := by
        rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
        refine ⟨?_, ?_⟩
        · rw [frame_add]; exact hx1.add S.w hy1
        · rw [frame_add, Matrix.add_apply, mul_add]; exact add_mem hx2 hy2
      zero_mem' := by
        refine ⟨?_, ?_⟩
        · rw [frame_zero]; exact IsInt.zero S.w
        · rw [frame_zero, Matrix.zero_apply, mul_zero]; exact zero_mem _
      neg_mem' := by
        rintro x ⟨hx1, hx2⟩
        refine ⟨?_, ?_⟩
        · rw [frame_neg]; exact hx1.neg S.w
        · rw [frame_neg, Matrix.neg_apply, mul_neg]; exact neg_mem hx2 }

  have hsub : Submodule.localBox S.R₀ S.w ≤ T := by
    refine (AddSubgroup.closure_le T).2 ?_
    rintro x ⟨z, hz, c, hc, rfl⟩
    have hzR : z ∈ S.R := S.hR₀R hz
    refine ⟨?_, ?_⟩
    · rw [frame_tmul S.w S.φw _ S.hφw]; exact (hint ⟨z, hzR⟩).smul S.w hc
    · rw [frame_tmul S.w S.φw _ S.hφw, Matrix.smul_apply, smul_eq_mul, mul_left_comm]
      exact mul_mem hc (hE3 ⟨z, hzR⟩ hz)

  have hsup : ∀ x, x ∈ T → x ∈ Submodule.localBox S.R₀ S.w := by
    rintro x ⟨hx1, hx2⟩
    have hxR : x ∈ Submodule.localBox S.R S.w := (hE1 x).1 hx1
    obtain ⟨z, t, ht, hzt⟩ := S.exists_tmul_add_mul x hxR
    have htint : IsInt S.w (frame S.w S.φw (S.h * G₀) t) := (hE1 t).2 ht
    have e10 : frame S.w S.φw (S.h * G₀) x 1 0 =
        frame S.w S.φw (S.h * G₀) ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : Kv S.w)) 1 0 +
          ((ℓ S.w : ℕ) : Kv S.w) * frame S.w S.φw (S.h * G₀) t 1 0 := by
      rw [hzt, frame_add, frame_one_tmul_mul S.w S.φw _ S.hφw, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have hz10 : (((ℓ S.w : ℕ) : Kv S.w))⁻¹ *
        frame S.w S.φw (S.h * G₀) ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : Kv S.w)) 1 0 ∈ Ov S.w := by
      have : (((ℓ S.w : ℕ) : Kv S.w))⁻¹ * frame S.w S.φw (S.h * G₀) ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : Kv S.w)) 1 0 =
          (((ℓ S.w : ℕ) : Kv S.w))⁻¹ * frame S.w S.φw (S.h * G₀) x 1 0 - frame S.w S.φw (S.h * G₀) t 1 0 := by
        rw [e10, mul_add, ← mul_assoc, inv_mul_cancel₀ hL0, one_mul, add_sub_cancel_right]
      rw [this]; exact sub_mem hx2 (htint 1 0)
    have hred0 : red S.w ⟨frame S.w S.φw (S.h * G₀) ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : Kv S.w)) 1 0, hint z 1 0⟩ = 0 :=
      (red_eq_zero_iff S.w _).2 ⟨⟨_, hz10⟩, Subtype.ext (by simp [mul_inv_cancel_left₀ hL0])⟩
    have h2 : S.φbar z 1 0 = 0 := by rw [← hE2 z, redM_apply]; exact hred0
    have hφz : ZMod.castHom S.hℓN (ZMod (ℓ S.w)) (S.φ z 1 0) = 0 := by
      simpa [φbar, Matrix.map_apply] using h2
    obtain ⟨m, hm⟩ := exists_eq_mul_of_castHom_eq_zero S.w S.hℓN _ hφz
    obtain ⟨s, hs⟩ := S.hφsurj (Matrix.of fun i j => if i = 1 ∧ j = 0 then m else 0)
    have hz'R₀ : (((z - ((ℓ S.w : ℕ) : ℤ) • s : ↥S.R)) : ℍ[ℚ, a, b]) ∈ S.R₀ := by
      rw [S.hR₀, map_sub, map_zsmul, hs, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, hm, zsmul_eq_mul,
        Int.cast_natCast]
      simp
    have hxeq : x = (((z - ((ℓ S.w : ℕ) : ℤ) • s : ↥S.R)) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : Kv S.w) +
        ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((ℓ S.w : ℕ) : Kv S.w)) * ((s : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : Kv S.w) + t) := by
      rw [hzt, Submodule.coe_sub, TensorProduct.sub_tmul, coe_zsmul, Int.cast_natCast, smul_tmul_one, map_natCast,
        mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      abel
    rw [hxeq]
    exact add_mem (S.tmul_mem_localBox hz'R₀ (one_mem _))
      (S.mul_mem_localBox_R₀ _ (add_mem (S.tmul_mem_localBox s.2 (one_mem _)) ht))
  intro x
  exact ⟨fun hx => hsub hx, fun hx => hsup x hx⟩

end Setup
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsOrder_exists_localBox_iff_and_localBox_iff_conj_diagonal_of_linearMap_matrix_zmod.S4Local.Setup"

end S4Local
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsOrder_exists_localBox_iff_and_localBox_iff_conj_diagonal_of_linearMap_matrix_zmod.S4Local.Setup P2MW.S_QuaternionAlgebra_IsOrder_exists_localBox_iff_and_localBox_iff_conj_diagonal_of_linearMap_matrix_zmod.S4Local"

end
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsOrder_exists_localBox_iff_and_localBox_iff_conj_diagonal_of_linearMap_matrix_zmod.S4Local.Setup P2MW.S_QuaternionAlgebra_IsOrder_exists_localBox_iff_and_localBox_iff_conj_diagonal_of_linearMap_matrix_zmod.S4Local"

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain NumberField QuaternionAlgebra

theorem solution
    {a b : ℚ} (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R)
    (w : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) (hp : p.Prime) (hpw : ((p : ℕ) : 𝓞 ℚ) ∈ w.asIdeal)
    (φw : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))
    (hφw : ∀ c : w.adicCompletion ℚ,
      φw ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) = c • (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)))
    (h : GL (Fin 2) (w.adicCompletion ℚ))
    (hRw : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ,
      x ∈ Submodule.localBox R w ↔
        ∀ i j, (((h⁻¹ : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) *
          φw x * (h : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))) i j ∈ w.adicCompletionIntegers ℚ)
    {N : ℕ} [NeZero N] (hpN : p ∣ N) (hppN : ¬ p ^ 2 ∣ N)
    (φ : ↥R →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod N))
    (hφ1 : ∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ R, φ ⟨1, h1⟩ = 1)
    (hφmul : ∀ (x y : ↥R) (hxy : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ R),
      φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ = φ x * φ y)
    (hφsurj : Function.Surjective φ)
    (hφker : ∀ x : ↥R, φ x = 0 ↔ ∃ y : ↥R, (x : ℍ[ℚ, a, b]) = (N : ℚ) • (y : ℍ[ℚ, a, b]))
    (R₀ : Submodule ℤ ℍ[ℚ, a, b]) (hR₀ : ∀ x : ↥R, (x : ℍ[ℚ, a, b]) ∈ R₀ ↔ φ x 1 0 = 0) (hR₀R : R₀ ≤ R) :
    ∃ g : GL (Fin 2) (w.adicCompletion ℚ),
      (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ,
        x ∈ Submodule.localBox R w ↔
          ∀ i j, (((g⁻¹ : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) *
            φw x * (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))) i j ∈ w.adicCompletionIntegers ℚ) ∧
      (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ,
        x ∈ Submodule.localBox R₀ w ↔
          (∀ i j, (((g⁻¹ : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) *
            φw x * (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))) i j ∈ w.adicCompletionIntegers ℚ) ∧
          (∀ i j, (Matrix.diagonal ![(1 : w.adicCompletion ℚ), ((p : w.adicCompletion ℚ))⁻¹] *
            ((g⁻¹ : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) *
            φw x * (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) *
            Matrix.diagonal ![(1 : w.adicCompletion ℚ), (p : w.adicCompletion ℚ)]) i j
              ∈ w.adicCompletionIntegers ℚ)) := by
  classical
  obtain rfl : p = S4Local.ℓ w := (S4Local.ℓ_eq_of_prime_mem w hp hpw).symm
  let S : S4Local.Setup a b :=
    { w := w, R := R, hR := hR, φw := φw, hφw := hφw, h := h, hRw := fun x => hRw x, N := N, hN := inferInstance,
      hℓN := hpN, hℓℓN := hppN, φ := φ, hφ1 := hφ1, hφmul := hφmul, hφsurj := hφsurj, hφker := hφker, R₀ := R₀,
      hR₀ := hR₀, hR₀R := hR₀R }
  obtain ⟨G₀, hG, hG', hbox⟩ := S.final
  refine ⟨h * G₀, fun x => ?_, fun x => ?_⟩
  · change x ∈ Submodule.localBox R w ↔ S4Local.IsInt w (S4Local.frame w φw (h * G₀) x)
    rw [S4Local.isInt_frame_mul_iff w φw h hG hG' x]
    exact hRw x
  · refine (hbox x).trans ⟨fun hx => ⟨hx.1, ?_⟩, fun hx => ⟨hx.1, ?_⟩⟩
    · exact (S4Local.isInt_diag_conj_iff w φw (h * G₀) x hx.1).2 hx.2
    · exact (S4Local.isInt_diag_conj_iff w φw (h * G₀) x hx.1).1 hx.2

end S_QuaternionAlgebra_IsOrder_exists_localBox_iff_and_localBox_iff_conj_diagonal_of_linearMap_matrix_zmod
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_exists_localBox_iff_and_localBox_iff_conj_diagonal_of_linearMap_matrix_zmod (solution)
