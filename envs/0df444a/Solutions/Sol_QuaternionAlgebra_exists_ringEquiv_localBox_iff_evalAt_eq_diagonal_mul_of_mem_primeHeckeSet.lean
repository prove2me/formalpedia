-- Prove2me | solution 1 for QuaternionAlgebra.exists_ringEquiv_localBox_iff_evalAt_eq_diagonal_mul_of_mem_primeHeckeSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e4f8f47a-375c-5863-ada5-10cbcf79707e

import Mathlib
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_ringEquiv_mem_localBox_iff_of_notMem
import Theorems.Thm_Matrix_exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_ringEquiv_localBox_iff_evalAt_eq_diagonal_mul_of_mem_primeHeckeSet
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField Matrix

noncomputable section

namespace HeckeIdeleNormalForm

section Places

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v

def pr : ℕ := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v : ℕ)

theorem pr_prime : (pr v).Prime := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v).2

scoped instance factPr : Fact (pr v).Prime := ⟨pr_prime v⟩

theorem pr_ne_zero : pr v ≠ 0 := (pr_prime v).ne_zero

theorem natGenerator_eq_pr : Rat.HeightOneSpectrum.natGenerator v = pr v := rfl

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem natCast_mem_asIdeal_iff_pr_dvd (n : ℕ) : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ pr v ∣ n := by
  rw [natCast_mem_asIdeal_iff, natGenerator_eq_pr]

theorem pr_mem_asIdeal : (pr v : 𝓞 ℚ) ∈ v.asIdeal := by
  rw [natCast_mem_asIdeal_iff, natGenerator_eq_pr]

theorem pr_notMem_asIdeal_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ v) :
    (pr v : 𝓞 ℚ) ∉ w.asIdeal := by
  rw [natCast_mem_asIdeal_iff]
  intro h
  have : Rat.HeightOneSpectrum.natGenerator w = pr v :=
    (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) (pr_prime v)).mp h
  apply hw
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  exact Subtype.ext this

theorem asIdeal_eq_span_pr : v.asIdeal = Ideal.span {(pr v : 𝓞 ℚ)} := by
  have h := Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) v
  rw [natGenerator_eq_pr] at h
  have h2 : v.asIdeal = Ideal.map ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm : ℤ →+* 𝓞 ℚ)
      (Ideal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) : 𝓞 ℚ →+* ℤ) v.asIdeal) := by
    rw [Ideal.map_map]
    have : ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm : ℤ →+* 𝓞 ℚ).comp
        (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) : 𝓞 ℚ →+* ℤ) = RingHom.id _ := by
      ext x; simp
    rw [this, Ideal.map_id]
  rw [h2]
  erw [← h]
  rw [Ideal.map_span, Set.image_singleton]
  congr 2
  simp

theorem valuation_pr : v.valuation ℚ (pr v : ℚ) = WithZero.exp (-1) := by
  rw [show (pr v : ℚ) = algebraMap (𝓞 ℚ) ℚ (pr v) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton v (by exact_mod_cast pr_ne_zero v)
    (asIdeal_eq_span_pr v)

theorem valued_algebraMap (r : ℚ) : Valued.v (algebraMap ℚ 𝕂 r) = v.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v r

theorem algebraMap_natCast (n : ℕ) : algebraMap ℚ 𝕂 (n : ℚ) = (n : 𝕂) := map_natCast _ n

theorem valued_pr : Valued.v ((pr v : ℕ) : 𝕂) = WithZero.exp (-1) := by
  rw [← algebraMap_natCast, valued_algebraMap, valuation_pr]

theorem pr_ne_zero' : ((pr v : ℕ) : 𝕂) ≠ 0 := by
  intro h
  have := valued_pr v
  rw [h, map_zero] at this
  exact WithZero.zero_ne_coe this

theorem natCast_mem_integers (n : ℕ) : ((n : ℕ) : 𝕂) ∈ 𝓞v := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← algebraMap_natCast, valued_algebraMap,
    show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  exact HeightOneSpectrum.valuation_le_one v _

theorem pr_mem_integers : ((pr v : ℕ) : 𝕂) ∈ 𝓞v := natCast_mem_integers v _

theorem valued_natCast_eq_one {n : ℕ} (w : HeightOneSpectrum (𝓞 ℚ)) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    Valued.v (n : w.adicCompletion ℚ) = 1 := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) w (n : 𝓞 ℚ)
  rw [(HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w)).mpr hn] at h
  change Valued.v (algebraMap (𝓞 ℚ) (w.adicCompletion ℚ) n) = 1 at h
  rwa [map_natCast] at h

theorem natCast_ne_zero_of_notMem {n : ℕ} (w : HeightOneSpectrum (𝓞 ℚ)) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    (n : w.adicCompletion ℚ) ≠ 0 := by
  intro h
  have := valued_natCast_eq_one w hn
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem natCast_inv_mem_integers {n : ℕ} (w : HeightOneSpectrum (𝓞 ℚ)) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    (n : w.adicCompletion ℚ)⁻¹ ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, valued_natCast_eq_one w hn, inv_one]

end Places

section Box

variable {D : Type*} [Ring D] [Algebra ℚ D] (Λ : Submodule ℤ D) (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v

theorem tmul_mem_localBox {z : D} (hz : z ∈ Λ) {c : 𝕂} (hc : c ∈ 𝓞v) :
    z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ v :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem tmul_one_mem_localBox {z : D} (hz : z ∈ Λ) :
    z ⊗ₜ[ℚ] (1 : 𝕂) ∈ Submodule.localBox Λ v :=
  tmul_mem_localBox Λ v hz (one_mem _)

omit Λ in
theorem localBox_mono {Λ Λ' : Submodule ℤ D} (h : Λ ≤ Λ') :
    Submodule.localBox Λ v ≤ Submodule.localBox Λ' v :=
  AddSubgroup.closure_mono fun _ ⟨z, hz, c, hc, hx⟩ => ⟨z, h hz, c, hc, hx⟩

theorem one_tmul_mul_mem_localBox {x : D ⊗[ℚ] 𝕂} (hx : x ∈ Submodule.localBox Λ v) {c : 𝕂}
    (hc : c ∈ 𝓞v) : ((1 : D) ⊗ₜ[ℚ] c) * x ∈ Submodule.localBox Λ v := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hy
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact tmul_mem_localBox Λ v hz (mul_mem hc hc')
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => exact (mul_neg _ x).symm ▸ neg_mem hx

theorem mul_mem_localBox (hmul : ∀ x y : D, x ∈ Λ → y ∈ Λ → x * y ∈ Λ)
    {x y : D ⊗[ℚ] 𝕂} (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox Λ v := by
  induction hy using AddSubgroup.closure_induction with
  | mem y' hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using AddSubgroup.closure_induction with
    | mem x' hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_localBox Λ v (hmul _ _ hz' hz) (mul_mem hc' hc)
    | zero => rw [zero_mul]; exact zero_mem _
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | neg x _ hx => exact (neg_mul x _).symm ▸ neg_mem hx
  | zero => rw [mul_zero]; exact zero_mem _
  | add x' y' _ _ hx' hy' => rw [mul_add]; exact add_mem hx' hy'
  | neg x' _ hx' => exact (mul_neg _ x').symm ▸ neg_mem hx'

omit Λ in
theorem ratCast_smul_eq_one_tmul_mul (r : ℚ) (x : D ⊗[ℚ] 𝕂) :
    r • x = ((1 : D) ⊗ₜ[ℚ] (algebraMap ℚ 𝕂 r)) * x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, mul_zero]
  | tmul z c =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul', TensorProduct.smul_tmul,
      Algebra.smul_def]
  | add x y hx hy => rw [smul_add, mul_add, hx, hy]

theorem localBox_le_of_nsmul_mem {Λ Λ' : Submodule ℤ D} {m : ℕ} (hm : (m : 𝓞 ℚ) ∉ v.asIdeal)
    (h : ∀ z ∈ Λ', (m : ℤ) • z ∈ Λ) :
    Submodule.localBox Λ' v ≤ Submodule.localBox Λ v := by
  unfold Submodule.localBox
  rw [AddSubgroup.closure_le]
  rintro _ ⟨z, hz, c, hc, rfl⟩
  have hm0 := natCast_ne_zero_of_notMem v hm
  have : z ⊗ₜ[ℚ] c = ((m : ℤ) • z) ⊗ₜ[ℚ] ((m : 𝕂)⁻¹ * c) := by
    rw [← Int.cast_smul_eq_zsmul ℚ, TensorProduct.smul_tmul, Int.cast_natCast, Algebra.smul_def,
      map_natCast, ← mul_assoc, mul_inv_cancel₀ hm0, one_mul]
  rw [this]
  exact AddSubgroup.subset_closure ⟨(m : ℤ) • z, h z hz, _, mul_mem (natCast_inv_mem_integers v hm) hc, rfl⟩

end Box

section LocalMatrix

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))

def intMat : Subring M₂ where
  carrier := {M | ∀ i j, M i j ∈ 𝓞v}
  mul_mem' {A B} hA hB i j := by
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => mul_mem (hA i k) (hB k j)
  one_mem' i j := by
    rw [Matrix.one_apply]; split_ifs
    exacts [one_mem _, zero_mem _]
  add_mem' {A B} hA hB i j := by rw [Matrix.add_apply]; exact add_mem (hA i j) (hB i j)
  zero_mem' i j := by rw [Matrix.zero_apply]; exact zero_mem _
  neg_mem' {A} hA i j := by rw [Matrix.neg_apply]; exact neg_mem (hA i j)

theorem mem_intMat_iff (M : M₂) : M ∈ intMat v ↔ ∀ i j, M i j ∈ 𝓞v := Iff.rfl

theorem smul_mem_intMat {c : 𝕂} (hc : c ∈ 𝓞v) {M : M₂} (hM : M ∈ intMat v) : c • M ∈ intMat v :=
  fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hM i j)

def tM : M₂ := !![1, 0; 0, ϖ]

def tMi : M₂ := !![1, 0; 0, ϖ⁻¹]
theorem tM_mul_tMi : tM v * tMi v = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [tM, tMi, Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ (pr_ne_zero' v)]

theorem tMi_mul_tM : tMi v * tM v = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [tM, tMi, Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ (pr_ne_zero' v)]

theorem exists_eq_mul_tM_mul {Y Yi : M₂} (h1 : Y * Yi = 1) (h2 : Yi * Y = 1) (hY : Y ∈ intMat v)
    (hpYi : ϖ • Yi ∈ intMat v) (hYi : Yi ∉ intMat v) (hpY : ϖ⁻¹ • Y ∉ intMat v) :
    ∃ K1 K1i K2 K2i : M₂, K1 ∈ intMat v ∧ K1i ∈ intMat v ∧ K2 ∈ intMat v ∧ K2i ∈ intMat v ∧
      K1 * K1i = 1 ∧ K1i * K1 = 1 ∧ K2 * K2i = 1 ∧ K2i * K2 = 1 ∧ Y = K1 * tM v * K2 :=
  Matrix.exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers (pr v) (pr_prime v) v
    (pr_mem_asIdeal v) Y Yi h1 h2 hY hpYi hYi hpY

theorem conj_mem_intMat {P Pi Y : M₂} (hP : P ∈ intMat v) (hPi : Pi ∈ intMat v) (hY : Y ∈ intMat v) :
    Pi * Y * P ∈ intMat v :=
  (intMat v).mul_mem ((intMat v).mul_mem hPi hY) hP

theorem conj_mem_intMat_iff {P Pi Y : M₂} (hP : P ∈ intMat v) (hPi : Pi ∈ intMat v)
    (h1 : P * Pi = 1) (h2 : Pi * P = 1) : Pi * Y * P ∈ intMat v ↔ Y ∈ intMat v := by
  refine ⟨fun h => ?_, conj_mem_intMat v hP hPi⟩
  have := conj_mem_intMat v hPi hP h
  have e : P * (Pi * Y * P) * Pi = (P * Pi) * Y * (P * Pi) := by noncomm_ring
  rwa [e, h1, one_mul, mul_one] at this

def conjRingEquiv (P Pi : M₂) (h1 : P * Pi = 1) (h2 : Pi * P = 1) : M₂ ≃+* M₂ where
  toFun x := Pi * x * P
  invFun x := P * x * Pi
  left_inv x := by
    show P * (Pi * x * P) * Pi = x
    calc _ = (P * Pi) * x * (P * Pi) := by noncomm_ring
      _ = x := by rw [h1, one_mul, mul_one]
  right_inv x := by
    show Pi * (P * x * Pi) * P = x
    calc _ = (Pi * P) * x * (Pi * P) := by noncomm_ring
      _ = x := by rw [h2, one_mul, mul_one]
  map_mul' x y := by
    show Pi * (x * y) * P = Pi * x * P * (Pi * y * P)
    calc _ = Pi * x * (P * Pi) * y * P := by rw [h1]; noncomm_ring
      _ = _ := by noncomm_ring
  map_add' x y := by
    show Pi * (x + y) * P = _
    rw [mul_add, add_mul]

theorem conjRingEquiv_apply (P Pi : M₂) (h1 : P * Pi = 1) (h2 : Pi * P = 1) (x : M₂) :
    conjRingEquiv v P Pi h1 h2 x = Pi * x * P := rfl

end LocalMatrix

section Frame

variable {a b : ℚ}

set_option quotPrecheck false in
local notation "𝔹" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b]

open QuaternionAlgebra

theorem mem_box_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (x : 𝔹) :
    x ∈ Submodule.finiteAdeleBox Λ ↔ ∀ w, ev w x ∈ Submodule.localBox Λ w :=
  Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hΛ.fg hΛ.spanTop x

theorem ev_ratCast_smul (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) (x : 𝔹) :
    ev w (r • x) = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (algebraMap ℚ _ r)) * ev w x := by
  rw [map_smul, ratCast_smul_eq_one_tmul_mul]

theorem ev_units_mul_inv (w : HeightOneSpectrum (𝓞 ℚ)) (g : (𝔹)ˣ) :
    ev w (g : 𝔹) * ev w ((g⁻¹ : (𝔹)ˣ) : 𝔹) = 1 := by rw [← map_mul, Units.mul_inv, map_one]

theorem ev_units_inv_mul (w : HeightOneSpectrum (𝓞 ℚ)) (g : (𝔹)ˣ) :
    ev w ((g⁻¹ : (𝔹)ˣ) : 𝔹) * ev w (g : 𝔹) = 1 := by rw [← map_mul, Units.inv_mul, map_one]

variable (R : Submodule ℤ ℍ[ℚ, a, b]) (hRo : IsOrder R) (v : HeightOneSpectrum (𝓞 ℚ))
  (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
  (hφ1 : ∀ r : v.adicCompletion ℚ,
    φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
  (hφR : ∀ x, x ∈ Submodule.localBox R v ↔ φ x ∈ intMat v)

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))
local notation "ℍv" => ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v

include hφ1 in
theorem map_one_tmul_mul (c : 𝕂) (x : ℍv) : φ (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x) = c • φ x := by
  rw [map_mul, hφ1, smul_mul_assoc, one_mul]

omit φ in
theorem one_tmul_natCast_inv_mul_cancel (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ v)
    (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((pr v : ℕ) : w.adicCompletion ℚ)⁻¹) *
      (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((pr v : ℕ) : w.adicCompletion ℚ)) * x) = x := by
  rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    inv_mul_cancel₀ (natCast_ne_zero_of_notMem w (pr_notMem_asIdeal_of_ne v w hw))]
  change (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) * x = x
  rw [one_mul]

include hRo hφ1 hφR in

theorem local_of_mem_primeHeckeSet {g : (𝔹)ˣ} (hg : g ∈ primeHeckeSet R (pr v)) :
    (∀ w, w ≠ v → ev w (g : 𝔹) ∈ Submodule.localBox R w ∧
      ev w ((g⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w) ∧
    φ (ev v (g : 𝔹)) ∈ intMat v ∧ ϖ • φ (ev v ((g⁻¹ : (𝔹)ˣ) : 𝔹)) ∈ intMat v ∧
    φ (ev v ((g⁻¹ : (𝔹)ˣ) : 𝔹)) ∉ intMat v ∧ ϖ⁻¹ • φ (ev v (g : 𝔹)) ∉ intMat v := by
  obtain ⟨h1, h2, h3, h4⟩ := hg
  have hw1 : ∀ w, ev w (g : 𝔹) ∈ Submodule.localBox R w := (mem_box_iff hRo _).1 h1
  have hw2' : ∀ w, ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((pr v : ℕ) : w.adicCompletion ℚ)) *
      ev w ((g⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w := by
    intro w
    have := (mem_box_iff hRo _).1 h2 w
    rwa [ev_ratCast_smul, map_natCast] at this
  have hw2 : ∀ w, w ≠ v → ev w ((g⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w := fun w hw => by
    have := one_tmul_mul_mem_localBox R w (hw2' w)
      (natCast_inv_mem_integers w (pr_notMem_asIdeal_of_ne v w hw))
    rwa [one_tmul_natCast_inv_mul_cancel v w hw] at this
  refine ⟨fun w hw => ⟨hw1 w, hw2 w hw⟩, (hφR _).1 (hw1 v), ?_, ?_, ?_⟩
  · rw [← map_one_tmul_mul v φ hφ1]; exact (hφR _).1 (hw2' v)
  · intro H
    apply h3
    rw [mem_box_iff hRo]
    intro w
    by_cases hw : w = v
    · obtain rfl : v = w := (‹w = v›).symm; exact (hφR _).2 H
    · exact hw2 w hw
  · intro H
    apply h4
    rw [mem_box_iff hRo]
    intro w
    rw [ev_ratCast_smul, map_inv₀, map_natCast]
    by_cases hw : w = v
    · obtain rfl : v = w := (‹w = v›).symm; rw [hφR, map_one_tmul_mul _ φ hφ1]; exact H
    · exact one_tmul_mul_mem_localBox R w (hw1 w) (natCast_inv_mem_integers w (pr_notMem_asIdeal_of_ne v w hw))

omit φ in

theorem main_at {q' : ℕ} (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (hq'v : (q' : 𝓞 ℚ) ∉ v.asIdeal) {N : ℕ} (hR : IsEichlerOrder R N)
    (hNv : (N : 𝓞 ℚ) ∉ v.asIdeal) (n : (𝔹)ˣ) (hnH : n ∈ primeHeckeSet R (pr v)) :
    (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → ev w (n : 𝔹) ∈ Submodule.localBox R w ∧
      ev w ((n⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w) ∧
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ r : v.adicCompletion ℚ,
        φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) ∧
      (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
        x ∈ Submodule.localBox R v ↔ ∀ i j, φ x i j ∈ v.adicCompletionIntegers ℚ) ∧
      ∃ k₀ k₀i : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
        (∀ i j, k₀ i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, k₀i i j ∈ v.adicCompletionIntegers ℚ) ∧
        k₀ * k₀i = 1 ∧ k₀i * k₀ = 1 ∧
        φ (ev v (n : 𝔹)) = tM v * k₀ ∧ φ (ev v ((n⁻¹ : (𝔹)ˣ) : 𝔹)) = k₀i * tMi v := by
  have hRo : IsOrder R := hR.isOrder

  obtain ⟨φ₀, hφ₀1, hφ₀R'⟩ :=
    QuaternionAlgebra.IsEichlerOrder.exists_ringEquiv_mem_localBox_iff_of_notMem hdef hR v hq'v hNv
  have hφ₀R : ∀ x, x ∈ Submodule.localBox R v ↔ φ₀ x ∈ intMat v := hφ₀R'

  obtain ⟨hnw, hN, hpNi, hNi, hpN⟩ := local_of_mem_primeHeckeSet R hRo v φ₀ hφ₀1 hφ₀R hnH
  set N₀ := φ₀ (ev v (n : 𝔹)) with hN₀
  set N₀i := φ₀ (ev v ((n⁻¹ : (𝔹)ˣ) : 𝔹)) with hN₀i
  have h1 : N₀ * N₀i = 1 := by rw [hN₀, hN₀i, ← map_mul, ev_units_mul_inv, map_one]
  have h2 : N₀i * N₀ = 1 := by rw [hN₀, hN₀i, ← map_mul, ev_units_inv_mul, map_one]
  obtain ⟨K1, K1i, K2, K2i, hK1, hK1i, hK2, hK2i, h11, h11', h22, h22', hNeq⟩ :=
    exists_eq_mul_tM_mul v h1 h2 hN hpNi hNi hpN
  have hNieq : N₀i = K2i * tMi v * K1i := by
    refine left_inv_eq_right_inv h2 ?_
    rw [hNeq]
    calc K1 * tM v * K2 * (K2i * tMi v * K1i) = K1 * (tM v * (K2 * K2i) * tMi v) * K1i := by noncomm_ring
      _ = 1 := by rw [h22, mul_one, tM_mul_tMi, mul_one, h11]

  let φ := φ₀.trans (conjRingEquiv v K1 K1i h11 h11')
  have hφ1 : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := fun r => by
    show conjRingEquiv v K1 K1i h11 h11' (φ₀ _) = _
    rw [conjRingEquiv_apply, hφ₀1, Matrix.mul_smul, Matrix.smul_mul, mul_one, h11']
  have hφR : ∀ x, x ∈ Submodule.localBox R v ↔ φ x ∈ intMat v := fun x => by
    show _ ↔ conjRingEquiv v K1 K1i h11 h11' (φ₀ x) ∈ intMat v
    rw [conjRingEquiv_apply, conj_mem_intMat_iff v hK1 hK1i h11 h11', hφ₀R]
  have hn : φ (ev v (n : 𝔹)) = tM v * (K2 * K1) := by
    show conjRingEquiv v K1 K1i h11 h11' (φ₀ _) = _
    rw [conjRingEquiv_apply, ← hN₀, hNeq]
    calc K1i * (K1 * tM v * K2) * K1 = (K1i * K1) * tM v * (K2 * K1) := by noncomm_ring
      _ = _ := by rw [h11', one_mul]
  have hni : φ (ev v ((n⁻¹ : (𝔹)ˣ) : 𝔹)) = (K1i * K2i) * tMi v := by
    show conjRingEquiv v K1 K1i h11 h11' (φ₀ _) = _
    rw [conjRingEquiv_apply, ← hN₀i, hNieq]
    calc K1i * (K2i * tMi v * K1i) * K1 = (K1i * K2i) * tMi v * (K1i * K1) := by noncomm_ring
      _ = _ := by rw [h11', mul_one]
  have hA : K2 * K1 * (K1i * K2i) = 1 := by
    calc K2 * K1 * (K1i * K2i) = K2 * (K1 * K1i) * K2i := by noncomm_ring
      _ = 1 := by rw [h11, mul_one, h22]
  have hB : K1i * K2i * (K2 * K1) = 1 := by
    calc K1i * K2i * (K2 * K1) = K1i * (K2i * K2) * K1 := by noncomm_ring
      _ = 1 := by rw [h22', mul_one, h11']
  exact ⟨hnw, φ, hφ1, hφR, K2 * K1, K1i * K2i, (intMat v).mul_mem hK2 hK1, (intMat v).mul_mem hK1i hK2i,
    hA, hB, hn, hni⟩

end Frame

end HeckeIdeleNormalForm
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_ringEquiv_localBox_iff_evalAt_eq_diagonal_mul_of_mem_primeHeckeSet.HeckeIdeleNormalForm"

theorem solution
    {a b : ℚ} {q' : ℕ} (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (hq'v : (q' : 𝓞 ℚ) ∉ v.asIdeal) (hNv : (N : 𝓞 ℚ) ∉ v.asIdeal)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ QuaternionAlgebra.primeHeckeSet R p) :
    (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
          ((n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
        Submodule.localBox R w ∧
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
          ((n⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
        Submodule.localBox R w) ∧
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ r : v.adicCompletion ℚ,
        φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) ∧
      (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
        x ∈ Submodule.localBox R v ↔ ∀ i j, φ x i j ∈ v.adicCompletionIntegers ℚ) ∧
      ∃ k₀ k₀i : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
        (∀ i j, k₀ i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, k₀i i j ∈ v.adicCompletionIntegers ℚ) ∧
        k₀ * k₀i = 1 ∧ k₀i * k₀ = 1 ∧
        φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v
          ((n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) =
          !![1, 0; 0, (p : v.adicCompletion ℚ)] * k₀ ∧
        φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v
          ((n⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) =
          k₀i * !![1, 0; 0, (p : v.adicCompletion ℚ)⁻¹] := by
  have hpr : HeckeIdeleNormalForm.pr v = p :=
    (Nat.prime_dvd_prime_iff_eq (HeckeIdeleNormalForm.pr_prime v) hp).1
      ((HeckeIdeleNormalForm.natCast_mem_asIdeal_iff_pr_dvd v p).1 hpv)
  have hn' : n ∈ QuaternionAlgebra.primeHeckeSet R (HeckeIdeleNormalForm.pr v) := by rw [hpr]; exact hn
  have := HeckeIdeleNormalForm.main_at R v hdef hq'v hR hNv n hn'
  simp only [HeckeIdeleNormalForm.tM, HeckeIdeleNormalForm.tMi, hpr] at this
  exact this

end
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_ringEquiv_localBox_iff_evalAt_eq_diagonal_mul_of_mem_primeHeckeSet.HeckeIdeleNormalForm"

end S_QuaternionAlgebra_exists_ringEquiv_localBox_iff_evalAt_eq_diagonal_mul_of_mem_primeHeckeSet
end P2MW
export P2MW.S_QuaternionAlgebra_exists_ringEquiv_localBox_iff_evalAt_eq_diagonal_mul_of_mem_primeHeckeSet (solution)
