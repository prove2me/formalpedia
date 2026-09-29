-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.exists_isMaximalOrder_and_eq_inf_and_relIndex_eq_of_squarefree_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/eccf1b40-b9f4-57eb-8a43-e95cb0ac0fde

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_relIndex_eq_of_isMaximalOrder_of_le_of_ne_zero
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_ne_zero_and_ne_zero
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_localBox_eq_localBox_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_ne_zero_of_not_isUnit
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_pair_localBox_iff_conj_diagonal_pow_mem_adicCompletionIntegers
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_localBox_iff_generalLinearGroup_conj_mem_adicCompletionIntegers
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_exists_forall_finiteAdeleEvalAt_eq
import Theorems.Thm_Submodule_eq_of_forall_finiteAdeleEvalAt_eq
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_conjByFiniteIdele
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_isMaximalOrder_and_eq_inf_and_relIndex_eq_of_squarefree_of_le
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "LocalGL2.swapUnit_val QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField Matrix

noncomputable section

namespace EndVertex

section Places

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v

abbrev gen : ℕ := Rat.HeightOneSpectrum.natGenerator v

theorem gen_prime : (gen v).Prime := Rat.HeightOneSpectrum.prime_natGenerator v

theorem natCast_mem_asIdeal_iff (n : ℕ) : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ gen v ∣ n := by
  rw [gen, Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem gen_mem_asIdeal : ((gen v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := (natCast_mem_asIdeal_iff v _).2 dvd_rfl

theorem asIdeal_eq_span : v.asIdeal = Ideal.span {((gen v : ℕ) : 𝓞 ℚ)} := by
  have h := Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) v
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

theorem valuation_gen : v.valuation ℚ ((gen v : ℕ) : ℚ) = WithZero.exp (-1) := by
  rw [show ((gen v : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ (gen v : ℕ) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _ (by exact_mod_cast (gen_prime v).ne_zero)
    (asIdeal_eq_span v)

theorem valued_algebraMap (r : ℚ) : Valued.v (algebraMap ℚ 𝕂 r) = v.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v r

theorem algebraMap_natCast (n : ℕ) : algebraMap ℚ 𝕂 (n : ℚ) = (n : 𝕂) := map_natCast _ n

theorem valued_natCast (n : ℕ) : Valued.v ((n : ℕ) : 𝕂) = v.valuation ℚ (n : ℚ) := by
  rw [← algebraMap_natCast, valued_algebraMap]

theorem valued_gen : Valued.v ((gen v : ℕ) : 𝕂) = WithZero.exp (-1) := by
  rw [valued_natCast, valuation_gen]

theorem gen_ne_zero' : ((gen v : ℕ) : 𝕂) ≠ 0 := by
  intro h
  have := valued_gen v
  rw [h, map_zero] at this
  exact WithZero.zero_ne_coe this

theorem valuation_natCast_le_one (n : ℕ) : v.valuation ℚ (n : ℚ) ≤ 1 := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  exact HeightOneSpectrum.valuation_le_one v _

theorem natCast_mem_integers (n : ℕ) : ((n : ℕ) : 𝕂) ∈ 𝓞v := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_natCast]
  exact valuation_natCast_le_one v n

theorem valuation_natCast_eq_one_of_not_dvd (n : ℕ) (hn : ¬ gen v ∣ n) : v.valuation ℚ (n : ℚ) = 1 := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := v) (r := (n : 𝓞 ℚ))).2
    (mt (natCast_mem_asIdeal_iff v n).1 hn)

theorem valuation_natCast_eq (n : ℕ) (hn : n ≠ 0) :
    v.valuation ℚ (n : ℚ) = WithZero.exp (-(n.factorization (gen v) : ℤ)) := by
  have hp := gen_prime v
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n (gen v)]
  rw [Nat.cast_mul, map_mul, Nat.cast_pow, map_pow, valuation_gen,
    valuation_natCast_eq_one_of_not_dvd v _ (Nat.not_dvd_ordCompl hp hn), mul_one, ← WithZero.exp_nsmul]
  congr 1
  simp

theorem exp_neg_one_le_valuation_of_squarefree (n : ℕ) (hn : Squarefree n) :
    WithZero.exp (-1) ≤ v.valuation ℚ (n : ℚ) := by
  rw [valuation_natCast_eq v n hn.ne_zero, WithZero.exp_le_exp]
  have := hn.natFactorization_le_one (gen v)
  omega

theorem valued_le_exp_neg_one_of_lt_one (x : 𝕂) (hx : Valued.v x < 1) : Valued.v x ≤ WithZero.exp (-1) := by
  by_cases h0 : Valued.v x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

end Places

section Box

variable {D : Type*} [Ring D] [Algebra ℚ D] (Λ : Submodule ℤ D) (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem tmul_mem_localBox {z : D} (hz : z ∈ Λ) {c : 𝕂} (hc : c ∈ 𝓞v) :
    z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ v :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem tmul_one_mem_localBox {z : D} (hz : z ∈ Λ) :
    z ⊗ₜ[ℚ] (1 : 𝕂) ∈ Submodule.localBox Λ v :=
  tmul_mem_localBox Λ v hz (one_mem _)

theorem localBox_mono {Λ Λ' : Submodule ℤ D} (h : Λ ≤ Λ') :
    Submodule.localBox Λ v ≤ Submodule.localBox Λ' v :=
  AddSubgroup.closure_mono fun _ ⟨z, hz, c, hc, hx⟩ => ⟨z, h hz, c, hc, hx⟩

omit Λ in
theorem ratCast_smul_eq_one_tmul_mul (r : ℚ) (x : D ⊗[ℚ] 𝕂) :
    r • x = ((1 : D) ⊗ₜ[ℚ] (algebraMap ℚ 𝕂 r)) * x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, mul_zero]
  | tmul z c =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul', TensorProduct.smul_tmul,
      Algebra.smul_def]
  | add x y hx hy => rw [smul_add, mul_add, hx, hy]

theorem ratCast_smul_mem_localBox_of_forall {Λ' : Submodule ℤ D} (r : ℚ) (h : ∀ z ∈ Λ', r • z ∈ Λ)
    {x : D ⊗[ℚ] 𝕂} (hx : x ∈ Submodule.localBox Λ' v) : r • x ∈ Submodule.localBox Λ v := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy
    rw [TensorProduct.smul_tmul']
    exact tmul_mem_localBox Λ v (h z hz) hc
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem mem_iff_forall_tmul_one_mem_localBox (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤)
    (z : D) :
    z ∈ Λ ↔ ∀ w : HeightOneSpectrum (𝓞 ℚ),
      z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w := by
  constructor
  · intro hz w; exact tmul_one_mem_localBox Λ w hz
  · intro h
    have hbox : z ⊗ₜ[ℚ] (1 : 𝔸f) ∈ Submodule.finiteAdeleBox Λ := by
      rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hfg hspan]
      intro w
      rw [Submodule.finiteAdeleEvalAt_tmul]
      exact h w
    have : z ∈ Submodule.ofFiniteIdele Λ 1 := by
      rw [Submodule.mem_ofFiniteIdele_iff]
      exact ⟨_, hbox, by simp⟩
    rwa [Submodule.ofFiniteIdele_one Λ hfg hspan] at this

abbrev unitAt (w : HeightOneSpectrum (𝓞 ℚ)) (g : (D ⊗[ℚ] 𝔸f)ˣ) : (D ⊗[ℚ] w.adicCompletion ℚ)ˣ :=
  Units.map (Submodule.finiteAdeleEvalAt D w).toRingHom.toMonoidHom g

omit Λ in
theorem coe_unitAt (w : HeightOneSpectrum (𝓞 ℚ)) (g : (D ⊗[ℚ] 𝔸f)ˣ) :
    ((unitAt w g : (D ⊗[ℚ] w.adicCompletion ℚ)ˣ) : D ⊗[ℚ] w.adicCompletion ℚ) =
      Submodule.finiteAdeleEvalAt D w (g : D ⊗[ℚ] 𝔸f) := rfl

omit Λ in
theorem coe_inv_unitAt (w : HeightOneSpectrum (𝓞 ℚ)) (g : (D ⊗[ℚ] 𝔸f)ˣ) :
    ((unitAt w g)⁻¹ : (D ⊗[ℚ] w.adicCompletion ℚ)ˣ) =
      Submodule.finiteAdeleEvalAt D w ((g⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) : D ⊗[ℚ] 𝔸f) := by
  rw [← map_inv]; rfl

theorem mem_conjByFiniteIdele_iff_forall (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤)
    (g : (D ⊗[ℚ] 𝔸f)ˣ) (z : D) :
    z ∈ Submodule.conjByFiniteIdele Λ g ↔ ∀ w : HeightOneSpectrum (𝓞 ℚ),
      ((unitAt w g)⁻¹ : (D ⊗[ℚ] w.adicCompletion ℚ)ˣ) * (z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) *
        (unitAt w g : (D ⊗[ℚ] w.adicCompletion ℚ)ˣ) ∈ Submodule.localBox Λ w := by
  rw [Submodule.mem_conjByFiniteIdele_iff]
  have key : z ⊗ₜ[ℚ] (1 : 𝔸f) ∈ (Submodule.finiteAdeleBox Λ).map
      ((AddMonoidHom.mulRight ((g⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) : D ⊗[ℚ] 𝔸f)).comp
        (AddMonoidHom.mulLeft (g : D ⊗[ℚ] 𝔸f))) ↔
      ((g⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) : D ⊗[ℚ] 𝔸f) * (z ⊗ₜ[ℚ] (1 : 𝔸f)) * (g : D ⊗[ℚ] 𝔸f) ∈
        Submodule.finiteAdeleBox Λ := by
    constructor
    · rintro ⟨y, hy, hyz⟩
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft,
        AddMonoidHom.coe_mulRight] at hyz
      rw [← hyz]
      have : ((g⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) : D ⊗[ℚ] 𝔸f) * ((g : D ⊗[ℚ] 𝔸f) * y * ((g⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) : D ⊗[ℚ] 𝔸f)) *
          (g : D ⊗[ℚ] 𝔸f) = y := by
        rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
      rw [this]; exact hy
    · intro h
      refine ⟨_, h, ?_⟩
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft,
        AddMonoidHom.coe_mulRight]
      rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
  rw [key, Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hfg hspan]
  refine forall_congr' fun w => ?_
  rw [map_mul, map_mul, Submodule.finiteAdeleEvalAt_tmul, coe_inv_unitAt, coe_unitAt]
  rfl

end Box

section Mat

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)

def intMat : Subring M₂ where
  carrier := {X | ∀ i j, X i j ∈ 𝓞v}
  mul_mem' {A B} hA hB i j := by
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => mul_mem (hA i k) (hB k j)
  one_mem' i j := by
    rw [Matrix.one_apply]; split_ifs
    exacts [one_mem _, zero_mem _]
  add_mem' {A B} hA hB i j := by rw [Matrix.add_apply]; exact add_mem (hA i j) (hB i j)
  zero_mem' i j := by rw [Matrix.zero_apply]; exact zero_mem _
  neg_mem' {A} hA i j := by rw [Matrix.neg_apply]; exact neg_mem (hA i j)

theorem mem_intMat_iff (X : M₂) : X ∈ intMat v ↔ ∀ i j, X i j ∈ 𝓞v := Iff.rfl

theorem mem_intMat_iff' (X : M₂) :
    X ∈ intMat v ↔ X 0 0 ∈ 𝓞v ∧ X 0 1 ∈ 𝓞v ∧ X 1 0 ∈ 𝓞v ∧ X 1 1 ∈ 𝓞v := by
  rw [mem_intMat_iff]
  constructor
  · intro h; exact ⟨h 0 0, h 0 1, h 1 0, h 1 1⟩
  · rintro ⟨h00, h01, h10, h11⟩ i j
    fin_cases i <;> fin_cases j
    exacts [h00, h01, h10, h11]

theorem smul_mem_intMat {c : 𝕂} (hc : c ∈ 𝓞v) {X : M₂} (hX : X ∈ intMat v) : c • X ∈ intMat v :=
  fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hX i j)

theorem trace_mem_of_mem_intMat {X : M₂} (hX : X ∈ intMat v) : Matrix.trace X ∈ 𝓞v := by
  rw [Matrix.trace_fin_two]; exact add_mem (hX 0 0) (hX 1 1)

variable (k : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

def conjHom : M₂ →+* M₂ where
  toFun X := ((k⁻¹ : GL (Fin 2) 𝕂) : M₂) * X * (k : M₂)
  map_one' := by rw [mul_one]; exact Units.inv_mul k
  map_mul' X Y := by
    have e : (k : M₂) * ((k⁻¹ : GL (Fin 2) 𝕂) : M₂) = 1 := Units.mul_inv k
    calc ((k⁻¹ : GL (Fin 2) 𝕂) : M₂) * (X * Y) * (k : M₂)
        = ((k⁻¹ : GL (Fin 2) 𝕂) : M₂) * X * ((k : M₂) * ((k⁻¹ : GL (Fin 2) 𝕂) : M₂)) * Y * (k : M₂) := by
          rw [e]; noncomm_ring
      _ = _ := by noncomm_ring
  map_zero' := by rw [mul_zero, zero_mul]
  map_add' X Y := by rw [mul_add, add_mul]

theorem conjHom_apply (X : M₂) : conjHom v k X = ((k⁻¹ : GL (Fin 2) 𝕂) : M₂) * X * (k : M₂) := rfl

def conjInt : Subring M₂ := (intMat v).comap (conjHom v k)

theorem mem_conjInt_iff (X : M₂) :
    X ∈ conjInt v k ↔ ((k⁻¹ : GL (Fin 2) 𝕂) : M₂) * X * (k : M₂) ∈ intMat v := Iff.rfl

theorem smul_mem_conjInt {c : 𝕂} (hc : c ∈ 𝓞v) {X : M₂} (hX : X ∈ conjInt v k) : c • X ∈ conjInt v k := by
  rw [mem_conjInt_iff] at hX ⊢
  rw [Matrix.mul_smul, Matrix.smul_mul]
  exact smul_mem_intMat v hc hX

theorem mem_integers_of_diag_mem {c : 𝕂} (i : Fin 2)
    (h : Matrix.single i i c ∈ conjInt v k) : c ∈ 𝓞v := by
  rw [mem_conjInt_iff] at h
  have ht := trace_mem_of_mem_intMat v h
  rw [Matrix.trace_mul_cycle, Units.mul_inv, one_mul] at ht
  have : Matrix.trace (Matrix.single i i c) = c := by
    fin_cases i <;> simp [Matrix.trace_fin_two, Matrix.single_apply]
  rwa [this] at ht

theorem single_mul_mul_single (X : M₂) (i j : Fin 2) :
    Matrix.single i i (1 : 𝕂) * X * Matrix.single j j 1 = Matrix.single i j (X i j) := by
  ext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]

theorem single_entry_mem {S : Subring M₂} {X : M₂} (hX : X ∈ S) (i j : Fin 2)
    (hi : Matrix.single i i (1 : 𝕂) ∈ S) (hj : Matrix.single j j (1 : 𝕂) ∈ S) :
    Matrix.single i j (X i j) ∈ S := by
  rw [← single_mul_mul_single v X i j]
  exact S.mul_mem (S.mul_mem hi hX) hj

theorem single_mul_single_swap (i j : Fin 2) (c c' : 𝕂) :
    Matrix.single i j c * Matrix.single j i c' = Matrix.single i i (c * c') :=
  Matrix.single_mul_single_same _ _ _ _ _

theorem single_one_mem_intMat (i j : Fin 2) : Matrix.single i j (1 : 𝕂) ∈ intMat v := by
  intro a b
  rw [Matrix.single_apply]
  split_ifs
  exacts [one_mem _, zero_mem _]

theorem single_mem_intMat_iff (i j : Fin 2) (c : 𝕂) : Matrix.single i j c ∈ intMat v ↔ c ∈ 𝓞v := by
  constructor
  · intro h; simpa [Matrix.single_apply] using h i j
  · intro h a b
    rw [Matrix.single_apply]
    split_ifs
    exacts [h, zero_mem _]

theorem conjInt_le_of_le (h : ∀ X ∈ intMat v, X ∈ conjInt v k) : ∀ X ∈ conjInt v k, X ∈ intMat v := by
  intro X hX
  have hE : ∀ i j : Fin 2, Matrix.single i j (1 : 𝕂) ∈ conjInt v k :=
    fun i j => h _ (single_one_mem_intMat v i j)
  have hent : ∀ i j : Fin 2, Matrix.single i j (X i j) ∈ conjInt v k :=
    fun i j => single_entry_mem v hX i j (hE i i) (hE j j)
  intro i j
  by_cases hij : i = j
  · subst hij
    exact mem_integers_of_diag_mem v k i (hent i i)
  · have h1 : Matrix.single i j (X i j) * Matrix.single j i 1 ∈ conjInt v k :=
      (conjInt v k).mul_mem (hent i j) (hE j i)
    rw [single_mul_single_swap, mul_one] at h1
    exact mem_integers_of_diag_mem v k i h1

theorem le_conjInt_of_le (h : ∀ X ∈ conjInt v k, X ∈ intMat v) : ∀ X ∈ intMat v, X ∈ conjInt v k := by
  have h' : ∀ X ∈ intMat v, X ∈ conjInt v k⁻¹ := by
    intro X hX
    rw [mem_conjInt_iff, inv_inv]
    apply h
    rw [mem_conjInt_iff]
    have : ((k⁻¹ : GL (Fin 2) 𝕂) : M₂) * ((k : M₂) * X * ((k⁻¹ : GL (Fin 2) 𝕂) : M₂)) * (k : M₂) = X := by
      calc _ = (((k⁻¹ : GL (Fin 2) 𝕂) : M₂) * (k : M₂)) * X * (((k⁻¹ : GL (Fin 2) 𝕂) : M₂) * (k : M₂)) := by
            noncomm_ring
        _ = X := by rw [Units.inv_mul, one_mul, mul_one]
    rw [this]; exact hX
  have h'' := conjInt_le_of_le v k⁻¹ h'
  intro X hX
  rw [mem_conjInt_iff]
  apply h''
  rw [mem_conjInt_iff, inv_inv]
  have : (k : M₂) * (((k⁻¹ : GL (Fin 2) 𝕂) : M₂) * X * (k : M₂)) * ((k⁻¹ : GL (Fin 2) 𝕂) : M₂) = X := by
    calc _ = ((k : M₂) * ((k⁻¹ : GL (Fin 2) 𝕂) : M₂)) * X * ((k : M₂) * ((k⁻¹ : GL (Fin 2) 𝕂) : M₂)) := by
          noncomm_ring
      _ = X := by rw [Units.mul_inv, one_mul, mul_one]
  rw [this]; exact hX

variable (π : HeightOneSpectrum.adicCompletion ℚ v)

def dmat : M₂ := Matrix.diagonal ![(1 : 𝕂), π]

def dinv : M₂ := Matrix.diagonal ![(1 : 𝕂), π⁻¹]

def nmat : M₂ := !![0, 1; π, 0]

def ninv : M₂ := !![0, π⁻¹; 1, 0]

variable {π} (hπ : π ≠ 0)
include hπ

omit k in
theorem dmat_mul_dinv : dmat v π * dinv v π = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dmat, dinv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, mul_inv_cancel₀ hπ]

omit k in
theorem dinv_mul_dmat : dinv v π * dmat v π = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dmat, dinv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, inv_mul_cancel₀ hπ]

omit k in
theorem nmat_mul_ninv : nmat v π * ninv v π = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [nmat, ninv, Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ hπ]

omit k in
theorem ninv_mul_nmat : ninv v π * nmat v π = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [nmat, ninv, Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ hπ]

omit k in

theorem dinv_mul_mul_dmat (X : M₂) :
    dinv v π * X * dmat v π = !![X 0 0, X 0 1 * π; π⁻¹ * X 1 0, X 1 1] := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;>
    simp [dmat, dinv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]
  rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hπ, one_mul]

omit k in

theorem ninv_mul_mul_nmat (X : M₂) :
    ninv v π * X * nmat v π = !![X 1 1, π⁻¹ * X 1 0; π * X 0 1, X 0 0] := by
  ext i j : 1
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [nmat, ninv]
  · rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hπ, one_mul]
  · ring

omit k in

theorem dinv_ninv_mul_mul_nmat_dmat (X : M₂) :
    dinv v π * (ninv v π * X * nmat v π) * dmat v π = !![X 1 1, X 1 0; X 0 1, X 0 0] := by
  rw [ninv_mul_mul_nmat v hπ, dinv_mul_mul_dmat v hπ]
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp
  · rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hπ, one_mul]
  · rw [← mul_assoc, inv_mul_cancel₀ hπ, one_mul]

def dGL : GL (Fin 2) 𝕂 := ⟨dmat v π, dinv v π, dmat_mul_dinv v hπ, dinv_mul_dmat v hπ⟩

omit k in
theorem coe_dGL : ((dGL v hπ : GL (Fin 2) 𝕂) : M₂) = dmat v π := rfl

omit k in
theorem coe_dGL_inv : (((dGL v hπ)⁻¹ : GL (Fin 2) 𝕂) : M₂) = dinv v π := rfl

variable (hπO : π ∈ HeightOneSpectrum.adicCompletionIntegers ℚ v)
  (hπ1 : ∀ x : HeightOneSpectrum.adicCompletion ℚ v, Valued.v x < 1 →
    π⁻¹ * x ∈ HeightOneSpectrum.adicCompletionIntegers ℚ v)
include hπO hπ1

theorem endpoint
    (hIw : ∀ X ∈ intMat v, dinv v π * X * dmat v π ∈ intMat v → X ∈ conjInt v k) :
    (∀ X, X ∈ conjInt v k ↔ X ∈ intMat v) ∨
    (∀ X, X ∈ conjInt v k ↔ dinv v π * X * dmat v π ∈ intMat v) := by

  have hdiag : ∀ i : Fin 2, Matrix.single i i (1 : 𝕂) ∈ conjInt v k := by
    intro i
    refine hIw _ (single_one_mem_intMat v i i) ?_
    rw [dinv_mul_mul_dmat v hπ, mem_intMat_iff']
    fin_cases i <;> simp [Matrix.single_apply, one_mem, zero_mem]
  have h01 : Matrix.single 0 1 (1 : 𝕂) ∈ conjInt v k := by
    refine hIw _ (single_one_mem_intMat v 0 1) ?_
    rw [dinv_mul_mul_dmat v hπ, mem_intMat_iff']
    simp [Matrix.single_apply, one_mem, zero_mem, hπO]
  have h10 : Matrix.single 1 0 π ∈ conjInt v k := by
    refine hIw _ ((single_mem_intMat_iff v 1 0 π).2 hπO) ?_
    rw [dinv_mul_mul_dmat v hπ, mem_intMat_iff']
    simp [Matrix.single_apply, one_mem, zero_mem, inv_mul_cancel₀ hπ]

  have hent : ∀ X ∈ conjInt v k, ∀ i j : Fin 2, Matrix.single i j (X i j) ∈ conjInt v k :=
    fun X hX i j => single_entry_mem v hX i j (hdiag i) (hdiag j)
  have hdiag' : ∀ X ∈ conjInt v k, ∀ i : Fin 2, X i i ∈ 𝓞v :=
    fun X hX i => mem_integers_of_diag_mem v k i (hent X hX i i)

  have h01π : ∀ X ∈ conjInt v k, X 0 1 * π ∈ 𝓞v := by
    intro X hX
    have := (conjInt v k).mul_mem (hent X hX 0 1) h10
    rw [single_mul_single_swap] at this
    exact mem_integers_of_diag_mem v k 0 this
  by_cases hc : ∀ X ∈ conjInt v k, X 0 1 ∈ 𝓞v
  ·
    left
    have hle : ∀ X ∈ conjInt v k, X ∈ intMat v := by
      intro X hX
      rw [mem_intMat_iff']
      refine ⟨hdiag' X hX 0, hc X hX, ?_, hdiag' X hX 1⟩
      have := (conjInt v k).mul_mem h01 (hent X hX 1 0)
      rw [single_mul_single_swap, one_mul] at this
      exact mem_integers_of_diag_mem v k 0 this
    exact fun X => ⟨hle X, le_conjInt_of_le v k hle X⟩
  ·
    right
    push Not at hc
    obtain ⟨X₀, hX₀, hc⟩ := hc
    set c := X₀ 0 1 with hcdef
    have hcS : Matrix.single 0 1 c ∈ conjInt v k := hent X₀ hX₀ 0 1
    have hvc : 1 < Valued.v c := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at hc; exact hc
    have hle : ∀ X ∈ conjInt v k, dinv v π * X * dmat v π ∈ intMat v := by
      intro X hX
      rw [dinv_mul_mul_dmat v hπ, mem_intMat_iff']
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      refine ⟨hdiag' X hX 0, h01π X hX, ?_, hdiag' X hX 1⟩

      have h1 : Matrix.single 0 1 c * Matrix.single 1 0 (X 1 0) ∈ conjInt v k :=
        (conjInt v k).mul_mem hcS (hent X hX 1 0)
      rw [single_mul_single_swap] at h1
      have h2 : c * X 1 0 ∈ 𝓞v := mem_integers_of_diag_mem v k 0 h1
      apply hπ1
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul] at h2
      by_contra hlt
      rw [not_lt] at hlt
      have : 1 < Valued.v c * Valued.v (X 1 0) :=
        lt_of_lt_of_le hvc (by simpa using mul_le_mul_right hlt (Valued.v c))
      exact absurd h2 (not_le.2 this)

    intro X
    refine ⟨hle X, fun hX => ?_⟩
    set k' : GL (Fin 2) 𝕂 := (dGL v hπ)⁻¹ * k with hk'
    have hk'S : ∀ Y, Y ∈ conjInt v k' ↔ dmat v π * Y * dinv v π ∈ conjInt v k := by
      intro Y
      rw [mem_conjInt_iff, mem_conjInt_iff, hk', _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul,
        coe_dGL, coe_dGL_inv]
      constructor <;> intro h <;> convert h using 1 <;> noncomm_ring
    have hle' : ∀ Y ∈ conjInt v k', Y ∈ intMat v := by
      intro Y hY
      have hY' := hle _ ((hk'S Y).1 hY)
      have e1 := dinv_mul_dmat v hπ
      have : dinv v π * (dmat v π * Y * dinv v π) * dmat v π = Y := by
        calc _ = (dinv v π * dmat v π) * Y * (dinv v π * dmat v π) := by noncomm_ring
          _ = Y := by rw [e1, one_mul, mul_one]
      rwa [this] at hY'
    have := le_conjInt_of_le v k' hle' _ hX
    rw [hk'S] at this
    have e2 := dmat_mul_dinv v hπ
    have e3 : dmat v π * (dinv v π * X * dmat v π) * dinv v π = X := by
      calc _ = (dmat v π * dinv v π) * X * (dmat v π * dinv v π) := by noncomm_ring
        _ = X := by rw [e2, one_mul, mul_one]
    rwa [e3] at this

end Mat

section LocalPackage

variable {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ℍv" => ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v

variable (φ : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v ≃+*
    Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
  (h : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

def coord : ℍv →+* M₂ := (conjHom v h).comp φ.toRingHom

theorem coord_apply (x : ℍv) : coord v φ h x = ((h⁻¹ : GL (Fin 2) 𝕂) : M₂) * φ x * (h : M₂) := rfl

theorem coord_symm (Y : M₂) : coord v φ h (φ.symm ((h : M₂) * Y * ((h⁻¹ : GL (Fin 2) 𝕂) : M₂))) = Y := by
  rw [coord_apply, RingEquiv.apply_symm_apply]
  calc ((h⁻¹ : GL (Fin 2) 𝕂) : M₂) * ((h : M₂) * Y * ((h⁻¹ : GL (Fin 2) 𝕂) : M₂)) * (h : M₂)
      = (((h⁻¹ : GL (Fin 2) 𝕂) : M₂) * (h : M₂)) * Y * (((h⁻¹ : GL (Fin 2) 𝕂) : M₂) * (h : M₂)) := by noncomm_ring
    _ = Y := by rw [Units.inv_mul, one_mul, mul_one]

theorem coord_one_tmul_mul
    (hφ : ∀ r : 𝕂, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : M₂)) (c : 𝕂) (x : ℍv) :
    coord v φ h (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x) = c • coord v φ h x := by
  rw [coord_apply, coord_apply, map_mul, hφ, smul_mul_assoc, one_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem diag_conj_eq (π : 𝕂) (x : ℍv) :
    Matrix.diagonal ![(1 : 𝕂), π⁻¹] * ((h⁻¹ : GL (Fin 2) 𝕂) : M₂) * φ x * (h : M₂) * Matrix.diagonal ![(1 : 𝕂), π] =
      dinv v π * coord v φ h x * dmat v π := by
  rw [coord_apply, dinv, dmat]; noncomm_ring

variable (Λ Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]) (e : ℕ) (g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

abbrev piPow : HeightOneSpectrum.adicCompletion ℚ v := ((gen v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v) ^ e

theorem piPow_ne_zero : piPow v e ≠ 0 := pow_ne_zero _ (gen_ne_zero' v)

theorem piPow_mem : piPow v e ∈ 𝓞v := pow_mem (natCast_mem_integers v _) e

theorem valued_piPow : Valued.v (piPow v e) = WithZero.exp (-(e : ℤ)) := by
  rw [piPow, map_pow, valued_gen, ← WithZero.exp_nsmul]; congr 1; simp

theorem piPow_inv_mul_mem (he : e ≤ 1) (x : 𝕂) (hx : Valued.v x < 1) : (piPow v e)⁻¹ * x ∈ 𝓞v := by
  have hx' := valued_le_exp_neg_one_of_lt_one v x hx
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, valued_piPow, ← WithZero.exp_neg, neg_neg]
  calc WithZero.exp (e : ℤ) * Valued.v x ≤ WithZero.exp (e : ℤ) * WithZero.exp (-1) := mul_le_mul_right hx' _
    _ = WithZero.exp ((e : ℤ) + (-1)) := (WithZero.exp_add _ _).symm
    _ ≤ WithZero.exp 0 := by rw [WithZero.exp_le_exp]; omega
    _ = 1 := WithZero.exp_zero

structure LocalData : Prop where
  ord₁ : QuaternionAlgebra.IsOrder Λ₁
  ord₂ : QuaternionAlgebra.IsOrder Λ₂
  le : Λ₁ ⊓ Λ₂ ≤ Λ
  h1 : ∀ x : ℍv, x ∈ Submodule.localBox Λ₁ v ↔ coord v φ h x ∈ intMat v
  h2 : ∀ x : ℍv, x ∈ Submodule.localBox Λ₂ v ↔ dinv v (piPow v e) * coord v φ h x * dmat v (piPow v e) ∈ intMat v
  hg : ∀ x : ℍv, x ∈ Submodule.localBox Λ v ↔
    ((g⁻¹ : GL (Fin 2) 𝕂) : M₂) * φ x * (g : M₂) ∈ intMat v

variable {v φ h Λ Λ₁ Λ₂ e g} (H : LocalData v φ h Λ Λ₁ Λ₂ e g)
include H

theorem LocalData.memR_iff (x : ℍv) : x ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) v ↔
    coord v φ h x ∈ intMat v ∧ dinv v (piPow v e) * coord v φ h x * dmat v (piPow v e) ∈ intMat v := by
  rw [Submodule.localBox_inf Λ₁ Λ₂ H.ord₁.fg H.ord₁.spanTop H.ord₂.fg H.ord₂.spanTop v, AddSubgroup.mem_inf,
    H.h1, H.h2]

theorem LocalData.memΛ_iff (x : ℍv) : x ∈ Submodule.localBox Λ v ↔ coord v φ h x ∈ conjInt v (h⁻¹ * g) := by
  rw [H.hg, mem_conjInt_iff, coord_apply, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
  have : ((g⁻¹ : GL (Fin 2) 𝕂) : M₂) * (h : M₂) * (((h⁻¹ : GL (Fin 2) 𝕂) : M₂) * φ x * (h : M₂)) *
      (((h⁻¹ : GL (Fin 2) 𝕂) : M₂) * (g : M₂)) = ((g⁻¹ : GL (Fin 2) 𝕂) : M₂) * φ x * (g : M₂) := by
    calc _ = ((g⁻¹ : GL (Fin 2) 𝕂) : M₂) * ((h : M₂) * ((h⁻¹ : GL (Fin 2) 𝕂) : M₂)) * φ x *
          ((h : M₂) * ((h⁻¹ : GL (Fin 2) 𝕂) : M₂)) * (g : M₂) := by noncomm_ring
      _ = _ := by rw [Units.mul_inv, mul_one, mul_one]
  rw [this]

theorem LocalData.iwahori_le (X : M₂) (hX : X ∈ intMat v)
    (hX' : dinv v (piPow v e) * X * dmat v (piPow v e) ∈ intMat v) : X ∈ conjInt v (h⁻¹ * g) := by
  have hx : φ.symm ((h : M₂) * X * ((h⁻¹ : GL (Fin 2) 𝕂) : M₂)) ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) v := by
    rw [H.memR_iff, coord_symm]; exact ⟨hX, hX'⟩
  have := (H.memΛ_iff _).1 (localBox_mono v H.le hx)
  rwa [coord_symm] at this

theorem LocalData.exponent_le
    (hφ : ∀ r : 𝕂, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : M₂))
    {M : ℕ} (hM : Squarefree M) (hidx : (Λ₁ ⊓ Λ₂).toAddSubgroup.relIndex Λ₁.toAddSubgroup = M) :
    e ≤ 1 ∧ (¬ gen v ∣ M → e = 0) := by

  set x₀ : ℍv := φ.symm ((h : M₂) * Matrix.single 1 0 (1 : 𝕂) * ((h⁻¹ : GL (Fin 2) 𝕂) : M₂)) with hx₀
  have hx₀Λ₁ : x₀ ∈ Submodule.localBox Λ₁ v := by
    rw [H.h1, coord_symm]; exact single_one_mem_intMat v 1 0
  have hsm : ∀ z ∈ Λ₁, ((M : ℕ) : ℚ) • z ∈ Λ₁ ⊓ Λ₂ := by
    intro z hz
    have := AddSubgroup.nsmul_relIndex_mem (Λ₁ ⊓ Λ₂).toAddSubgroup (K := Λ₁.toAddSubgroup) hz
    rw [hidx] at this
    rwa [Nat.cast_smul_eq_nsmul]
  have hMx₀ : ((M : ℕ) : ℚ) • x₀ ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) v :=
    ratCast_smul_mem_localBox_of_forall (Λ₁ ⊓ Λ₂) v _ hsm hx₀Λ₁
  rw [H.memR_iff, ratCast_smul_eq_one_tmul_mul, algebraMap_natCast, coord_one_tmul_mul v φ h hφ, coord_symm,
    Matrix.mul_smul, Matrix.smul_mul, dinv_mul_mul_dmat v (piPow_ne_zero v e)] at hMx₀
  have key : (piPow v e)⁻¹ * ((M : ℕ) : 𝕂) ∈ 𝓞v := by
    have := (mem_intMat_iff' v _).1 hMx₀.2
    rw [mul_comm]
    simpa [Matrix.single_apply] using this.2.2.1

  have hM0 : M ≠ 0 := hM.ne_zero
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, valued_piPow, valued_natCast,
    valuation_natCast_eq v M hM0, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_add, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at key
  have hfac := hM.natFactorization_le_one (gen v)
  refine ⟨by omega, fun hndvd => ?_⟩
  have : M.factorization (gen v) = 0 := Nat.factorization_eq_zero_of_not_dvd hndvd
  omega

theorem LocalData.dichotomy (he : e ≤ 1) :
    (∀ x : ℍv, x ∈ Submodule.localBox Λ v ↔ x ∈ Submodule.localBox Λ₁ v) ∨
    (∀ x : ℍv, x ∈ Submodule.localBox Λ v ↔ x ∈ Submodule.localBox Λ₂ v) := by
  rcases endpoint v (h⁻¹ * g) (piPow_ne_zero v e) (piPow_mem v e) (piPow_inv_mul_mem v e he) H.iwahori_le with
    hcase | hcase
  · left; intro x; rw [H.memΛ_iff, H.h1, hcase]
  · right; intro x; rw [H.memΛ_iff, H.h2, hcase]

def swap (v : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v ≃+*
      Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
    (h : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) (e : ℕ) :
    ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v :=
  φ.symm ((h : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) * nmat v (piPow v e) *
    ((h⁻¹ : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) :
      Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)))

def swapInv (v : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v ≃+*
      Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
    (h : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) (e : ℕ) :
    ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v :=
  φ.symm ((h : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) * ninv v (piPow v e) *
    ((h⁻¹ : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) :
      Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)))

omit H in
theorem coord_swap : coord v φ h (swap v φ h e) = nmat v (piPow v e) := coord_symm v φ h _

omit H in
theorem coord_swapInv : coord v φ h (swapInv v φ h e) = ninv v (piPow v e) := coord_symm v φ h _

omit H in
theorem swap_mul_swapInv : swap v φ h e * swapInv v φ h e = 1 := by
  rw [swap, swapInv, ← map_mul, ← map_one φ.symm]
  congr 1
  calc (h : M₂) * nmat v (piPow v e) * ((h⁻¹ : GL (Fin 2) 𝕂) : M₂) *
        ((h : M₂) * ninv v (piPow v e) * ((h⁻¹ : GL (Fin 2) 𝕂) : M₂))
      = (h : M₂) * (nmat v (piPow v e) * (((h⁻¹ : GL (Fin 2) 𝕂) : M₂) * (h : M₂)) * ninv v (piPow v e)) *
          ((h⁻¹ : GL (Fin 2) 𝕂) : M₂) := by noncomm_ring
    _ = 1 := by rw [Units.inv_mul, mul_one, nmat_mul_ninv v (piPow_ne_zero v e), mul_one, Units.mul_inv]

omit H in
theorem swapInv_mul_swap : swapInv v φ h e * swap v φ h e = 1 := by
  rw [swap, swapInv, ← map_mul, ← map_one φ.symm]
  congr 1
  calc (h : M₂) * ninv v (piPow v e) * ((h⁻¹ : GL (Fin 2) 𝕂) : M₂) *
        ((h : M₂) * nmat v (piPow v e) * ((h⁻¹ : GL (Fin 2) 𝕂) : M₂))
      = (h : M₂) * (ninv v (piPow v e) * (((h⁻¹ : GL (Fin 2) 𝕂) : M₂) * (h : M₂)) * nmat v (piPow v e)) *
          ((h⁻¹ : GL (Fin 2) 𝕂) : M₂) := by noncomm_ring
    _ = 1 := by rw [Units.inv_mul, mul_one, ninv_mul_nmat v (piPow_ne_zero v e), mul_one, Units.mul_inv]

omit H in
theorem coord_conj_swap (x : ℍv) :
    coord v φ h (swapInv v φ h e * x * swap v φ h e) = ninv v (piPow v e) * coord v φ h x * nmat v (piPow v e) := by
  rw [map_mul, map_mul, coord_swap, coord_swapInv]

theorem LocalData.swap_mem : swap v φ h e ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) v := by
  rw [H.memR_iff, coord_swap, dinv_mul_mul_dmat v (piPow_ne_zero v e), mem_intMat_iff', mem_intMat_iff']
  simp [nmat, one_mem, zero_mem, piPow_mem, inv_mul_cancel₀ (piPow_ne_zero v e)]

theorem LocalData.swapInv_mem (he : e = 0) : swapInv v φ h e ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) v := by
  rw [H.memR_iff, coord_swapInv, dinv_mul_mul_dmat v (piPow_ne_zero v e), mem_intMat_iff', mem_intMat_iff']
  subst he
  simp [ninv, piPow, one_mem, zero_mem]

theorem LocalData.conj_mem_of_memR (he : e ≤ 1) (x : ℍv) (hx : x ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) v) :
    swapInv v φ h e * x * swap v φ h e ∈ Submodule.localBox Λ v := by
  have hπ := piPow_ne_zero v e
  rw [H.memR_iff, dinv_mul_mul_dmat v hπ, mem_intMat_iff' v (Matrix.of _)] at hx
  obtain ⟨hX, h00, h01, h10, h11⟩ := hx
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h00 h01 h10 h11
  rw [mem_intMat_iff'] at hX
  rcases H.dichotomy he with hcase | hcase
  · rw [hcase, H.h1, coord_conj_swap, ninv_mul_mul_nmat v hπ, mem_intMat_iff']
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    exact ⟨hX.2.2.2, h10, by rw [mul_comm]; exact h01, hX.1⟩
  · rw [hcase, H.h2, coord_conj_swap, dinv_ninv_mul_mul_nmat_dmat v hπ, mem_intMat_iff']
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    exact ⟨hX.2.2.2, hX.2.2.1, hX.2.1, hX.1⟩

theorem LocalData.memR_of_conj_mem (he : e ≤ 1) (x : ℍv) (hx : x ∈ Submodule.localBox Λ v)
    (hx' : swapInv v φ h e * x * swap v φ h e ∈ Submodule.localBox Λ v) :
    x ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) v := by
  have hπ := piPow_ne_zero v e
  rw [H.memR_iff, dinv_mul_mul_dmat v hπ, mem_intMat_iff' v (Matrix.of _), mem_intMat_iff']
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rcases H.dichotomy he with hcase | hcase
  · rw [hcase, H.h1, mem_intMat_iff'] at hx
    rw [hcase, H.h1, coord_conj_swap, ninv_mul_mul_nmat v hπ, mem_intMat_iff'] at hx'
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at hx'
    exact ⟨hx, hx.1, by rw [mul_comm]; exact hx'.2.2.1, hx'.2.1, hx.2.2.2⟩
  · rw [hcase, H.h2, dinv_mul_mul_dmat v hπ, mem_intMat_iff'] at hx
    rw [hcase, H.h2, coord_conj_swap, dinv_ninv_mul_mul_nmat_dmat v hπ, mem_intMat_iff'] at hx'
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at hx hx'
    exact ⟨⟨hx'.2.2.2, hx'.2.2.1, hx'.2.1, hx'.1⟩, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2⟩

end LocalPackage

section Glue

variable {a b : ℚ}

theorem exists_split (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ))
    (hnd : ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) :
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      ∀ r : v.adicCompletion ℚ,
        φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
  push_neg at hnd
  obtain ⟨x, hx0, hxu⟩ := hnd

  obtain ⟨φ₀, hφ₀1, hφ₀x⟩ :=
    QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
      (R := ℚ) (S := v.adicCompletion ℚ)
      (T := ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, 0, algebraMap ℚ (v.adicCompletion ℚ) b])
      (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b) rfl (map_zero _) rfl AlgEquiv.refl
  have hx0' : φ₀ x ≠ 0 := fun h => hx0 (by simpa using congrArg φ₀.symm h)
  have hxu' : ¬ IsUnit (φ₀ x) := fun h => hxu (by simpa using h.map φ₀.symm)
  haveI : CharZero (v.adicCompletion ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective
  haveI : NeZero (2 : v.adicCompletion ℚ) := ⟨two_ne_zero⟩
  have ha' : algebraMap ℚ (v.adicCompletion ℚ) a ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap ℚ (v.adicCompletion ℚ)).injective]; exact ha
  have hb' : algebraMap ℚ (v.adicCompletion ℚ) b ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap ℚ (v.adicCompletion ℚ)).injective]; exact hb
  obtain ⟨ψ⟩ := QuaternionAlgebra.nonempty_algEquiv_matrix_of_ne_zero_of_not_isUnit ha' hb' (φ₀ x) hx0' hxu'
  obtain ⟨φ, hφ1, -⟩ :=
    QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
      (R := ℚ) (S := v.adicCompletion ℚ) (T := Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
      (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b) rfl (map_zero _) rfl ψ
  exact ⟨φ, hφ1⟩

theorem exists_localData (ha : a ≠ 0) (hb : b ≠ 0)
    {Λ Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    (hΛ₁ : QuaternionAlgebra.IsMaximalOrder Λ₁) (hΛ₂ : QuaternionAlgebra.IsMaximalOrder Λ₂) (hRΛ : Λ₁ ⊓ Λ₂ ≤ Λ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hnd : ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) :
    ∃ (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
      (h : GL (Fin 2) (v.adicCompletion ℚ)) (e : ℕ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      (∀ r : v.adicCompletion ℚ, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) ∧
      LocalData v φ h Λ Λ₁ Λ₂ e g := by
  obtain ⟨φ, hφ⟩ := exists_split ha hb v hnd
  obtain ⟨e, ⟨h, hh1, hh2⟩, -⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_pair_localBox_iff_conj_diagonal_pow_mem_adicCompletionIntegers
      hΛ₁ hΛ₂ v (gen v) (gen_prime v) (gen_mem_asIdeal v) φ hφ
  obtain ⟨g, hg⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_localBox_iff_generalLinearGroup_conj_mem_adicCompletionIntegers hΛ v φ hφ
  refine ⟨φ, h, e, g, hφ, ⟨hΛ₁.isOrder, hΛ₂.isOrder, hRΛ, fun x => hh1 x, fun x => ?_, fun x => hg x⟩⟩
  rw [hh2, ← diag_conj_eq]
  rfl

theorem local_package (ha : a ≠ 0) (hb : b ≠ 0)
    {M : ℕ} (hM : Squarefree M)
    {Λ Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    (hΛ₁ : QuaternionAlgebra.IsMaximalOrder Λ₁) (hΛ₂ : QuaternionAlgebra.IsMaximalOrder Λ₂)
    (hidx : (Λ₁ ⊓ Λ₂).toAddSubgroup.relIndex Λ₁.toAddSubgroup = M) (hRΛ : Λ₁ ⊓ Λ₂ ≤ Λ)
    (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ c ci : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, c * ci = 1 ∧ ci * c = 1 ∧
      c ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) w ∧
      ((M : 𝓞 ℚ) ∉ w.asIdeal → ci ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) w) ∧
      (∀ x, x ∈ Submodule.localBox Λ w → ci * x * c ∈ Submodule.localBox Λ w →
        x ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) w) ∧
      (∀ x, x ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) w → ci * x * c ∈ Submodule.localBox Λ w) := by
  have hR : QuaternionAlgebra.IsOrder (Λ₁ ⊓ Λ₂) := hΛ₁.isOrder.inf hΛ₂.isOrder
  by_cases hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, x ≠ 0 → IsUnit x
  ·
    have e1 := QuaternionAlgebra.IsMaximalOrder.localBox_eq_localBox_of_forall_isUnit w hdiv hΛ hΛ₁
    have e2 := QuaternionAlgebra.IsMaximalOrder.localBox_eq_localBox_of_forall_isUnit w hdiv hΛ hΛ₂
    have hRw : ∀ x, x ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) w ↔ x ∈ Submodule.localBox Λ w := by
      intro x
      rw [Submodule.localBox_inf Λ₁ Λ₂ hΛ₁.isOrder.fg hΛ₁.isOrder.spanTop hΛ₂.isOrder.fg hΛ₂.isOrder.spanTop w,
        AddSubgroup.mem_inf, ← e1, ← e2, and_self]
    refine ⟨1, 1, one_mul 1, one_mul 1, tmul_one_mem_localBox _ w hR.one_mem,
      fun _ => tmul_one_mem_localBox _ w hR.one_mem, fun x hx _ => (hRw x).2 hx, fun x hx => ?_⟩
    rw [one_mul, mul_one]; exact (hRw x).1 hx
  ·
    obtain ⟨φ, h, e, g, hφ, H⟩ := exists_localData ha hb hΛ hΛ₁ hΛ₂ hRΛ w hdiv
    obtain ⟨he, he0⟩ := H.exponent_le hφ hM hidx
    refine ⟨swap w φ h e, swapInv w φ h e, swap_mul_swapInv, swapInv_mul_swap, H.swap_mem, fun hMw => ?_,
      fun x hx hx' => H.memR_of_conj_mem he x hx hx', fun x hx => H.conj_mem_of_memR he x hx⟩
    exact H.swapInv_mem (he0 (mt (natCast_mem_asIdeal_iff w M).2 hMw))

theorem exists_isMaximalOrder_inf_eq (ha : a ≠ 0) (hb : b ≠ 0)
    {M : ℕ} [NeZero M] (hM : Squarefree M)
    (Λ Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    (hΛ₁ : QuaternionAlgebra.IsMaximalOrder Λ₁) (hΛ₂ : QuaternionAlgebra.IsMaximalOrder Λ₂)
    (hidx : (Λ₁ ⊓ Λ₂).toAddSubgroup.relIndex Λ₁.toAddSubgroup = M) (hRΛ : Λ₁ ⊓ Λ₂ ≤ Λ) :
    ∃ Λ' : Submodule ℤ ℍ[ℚ, a, b], QuaternionAlgebra.IsMaximalOrder Λ' ∧ Λ₁ ⊓ Λ₂ = Λ ⊓ Λ' := by
  classical
  have hR : QuaternionAlgebra.IsOrder (Λ₁ ⊓ Λ₂) := hΛ₁.isOrder.inf hΛ₂.isOrder
  choose c ci hcci hcic hcR hciR hP4 hP5 using local_package ha hb hM hΛ hΛ₁ hΛ₂ hidx hRΛ

  obtain ⟨y, hy⟩ := Submodule.exists_forall_finiteAdeleEvalAt_eq (Λ₁ ⊓ Λ₂) hR.fg hR.spanTop c
    (Filter.Eventually.of_forall hcR)
  have hM0 : Ideal.span {(M : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (NeZero.ne M)
  have hev : ∀ᶠ w in Filter.cofinite, ci w ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) w := by
    rw [Filter.eventually_cofinite]
    refine (Ideal.finite_factors hM0).subset fun w hw => ?_
    by_contra hdvd
    refine hw (hciR w ?_)
    rwa [Set.mem_setOf_eq, Ideal.dvd_span_singleton] at hdvd
  obtain ⟨y', hy'⟩ := Submodule.exists_forall_finiteAdeleEvalAt_eq (Λ₁ ⊓ Λ₂) hR.fg hR.spanTop ci hev
  have hyy' : y * y' = 1 := by
    refine Submodule.eq_of_forall_finiteAdeleEvalAt_eq _ _ fun w => ?_
    rw [map_mul, hy, hy', hcci, map_one]
  have hy'y : y' * y = 1 := by
    refine Submodule.eq_of_forall_finiteAdeleEvalAt_eq _ _ fun w => ?_
    rw [map_mul, hy, hy', hcic, map_one]
  set m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := ⟨y, y', hyy', hy'y⟩ with hm
  have hmw : ∀ w, ((unitAt w m : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) = c w :=
    fun w => hy w
  have hmw' : ∀ w, (((unitAt w m)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) = ci w :=
    fun w => by rw [coe_inv_unitAt]; exact hy' w

  refine ⟨Submodule.conjByFiniteIdele Λ m, QuaternionAlgebra.IsMaximalOrder.conjByFiniteIdele hΛ m, ?_⟩
  ext z
  rw [show (z ∈ Λ ⊓ Submodule.conjByFiniteIdele Λ m ↔ z ∈ Λ ∧ z ∈ Submodule.conjByFiniteIdele Λ m) from
      Submodule.mem_inf, mem_conjByFiniteIdele_iff_forall Λ hΛ.isOrder.fg hΛ.isOrder.spanTop m z]
  simp only [hmw, hmw']
  constructor
  · intro hz
    exact ⟨hRΛ hz, fun w => hP5 w _ (tmul_one_mem_localBox _ w hz)⟩
  · rintro ⟨hzΛ, hz'⟩
    rw [mem_iff_forall_tmul_one_mem_localBox (Λ₁ ⊓ Λ₂) hR.fg hR.spanTop]
    exact fun w => hP4 w _ (tmul_one_mem_localBox Λ w hzΛ) (hz' w)

end Glue

end EndVertex

end

open scoped TensorProduct Quaternion NumberField
open QuaternionAlgebra

theorem solution
    {a b : ℚ} {N : ℕ} [NeZero N] (hN : Squarefree N)
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ) :
    ∃ Λ' : Submodule ℤ ℍ[ℚ, a, b], IsMaximalOrder Λ' ∧ R = Λ ⊓ Λ' ∧
      R.toAddSubgroup.relIndex Λ.toAddSubgroup = N := by
  obtain ⟨ha, hb⟩ := QuaternionAlgebra.IsMaximalOrder.ne_zero_and_ne_zero hΛ
  have hidxΛ := QuaternionAlgebra.IsEichlerOrder.relIndex_eq_of_isMaximalOrder_of_le_of_ne_zero ha hb hR hΛ hRΛ
  obtain ⟨Λ₁, Λ₂, hΛ₁, hΛ₂, rfl, hidx⟩ := hR
  obtain ⟨Λ', hΛ', hEq⟩ := EndVertex.exists_isMaximalOrder_inf_eq ha hb hN Λ Λ₁ Λ₂ hΛ hΛ₁ hΛ₂ hidx hRΛ
  exact ⟨Λ', hΛ', hEq, hidxΛ⟩

end S_QuaternionAlgebra_IsEichlerOrder_exists_isMaximalOrder_and_eq_inf_and_relIndex_eq_of_squarefree_of_le
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_isMaximalOrder_and_eq_inf_and_relIndex_eq_of_squarefree_of_le (solution)
