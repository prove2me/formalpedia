-- Prove2me | solution 1 for QuaternionAlgebra.exists_ofFiniteIdele_mul_eq_ofFiniteIdele_mul_mul_iff_relIndex_eq_sq_and_forall_not_le_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ec8f3286-3d9f-551f-ab4c-39a8943bd3a0

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_localBoxUnits_and_exists_eq_mul_diagonal_mul_of_relIndex_inf_conjByFiniteIdele_eq
import Theorems.Thm_QuaternionAlgebra_forall_inv_smul_not_mem_finiteAdeleBox_of_mem_of_smul_inv_mem_of_relIndex_inf_conjByFiniteIdele_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_ofFiniteIdele_mul_le_zsmul_ofFiniteIdele_iff_inv_smul_mem_finiteAdeleBox
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_ne_zero_and_ne_zero
import Theorems.Thm_QuaternionAlgebra_relIndex_map_mulLeft_eq_pow_of_eq_mul_diagonal_pow_mul
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_relIndex_map_mulLeft_localBox_eq_pow
import Theorems.Thm_Matrix_GeneralLinearGroup_exists_eq_mul_diagonal_natCast_pow_mul_of_forall_mem_adicCompletionIntegers
import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_ofFiniteIdele_mul_eq_finprod_relIndex_map_mulLeft_localBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_Submodule_ofFiniteIdele_eq_ofFiniteIdele_iff
import Theorems.Thm_Submodule_exists_units_finiteAdeleEvalAt_eq
import Theorems.Thm_Submodule_exists_ne_zero_natCast_smul_mem_finiteAdeleBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_ofFiniteIdele_mul_eq_ofFiniteIdele_mul_mul_iff_relIndex_eq_sq_and_forall_not_le_zsmul
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra IsDedekindDomain NumberField

namespace QType

variable {a b : ℚ}

section WsTwentyOne

theorem natGenerator_dvd_iff' (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    Rat.HeightOneSpectrum.natGenerator v ∣ n ↔ ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n,
    Ideal.apply_mem_of_equiv_iff]

theorem natGenerator_mem (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal :=
  (natGenerator_dvd_iff' v _).mp dvd_rfl

theorem one_tmul_mul_mem_localBox (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ))
    {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) :
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x ∈ Submodule.localBox Λ v := by
  unfold Submodule.localBox at hx ⊢
  have hle : AddSubgroup.closure {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ |
        ∃ z ∈ Λ, ∃ c : v.adicCompletion ℚ, c ∈ v.adicCompletionIntegers ℚ ∧ x = z ⊗ₜ[ℚ] c} ≤
      (AddSubgroup.closure {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ |
        ∃ z ∈ Λ, ∃ c : v.adicCompletion ℚ, c ∈ v.adicCompletionIntegers ℚ ∧ x = z ⊗ₜ[ℚ] c}).comap
        (AddMonoidHom.mulLeft ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c)) := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨z, hz, d, hd, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, AddMonoidHom.coe_mulLeft]
    refine AddSubgroup.subset_closure ⟨z, hz, c * d, mul_mem hc hd, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact hle hx

theorem inv_natCast_mem_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ)
    (hnv : ((n : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) :
    ((n : v.adicCompletion ℚ))⁻¹ ∈ v.adicCompletionIntegers ℚ := by
  have h1 : ((n : ℕ) : v.adicCompletion ℚ) = algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) ((n : ℕ) : 𝓞 ℚ) := by
    rw [map_natCast]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1]
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v ((n : ℕ) : 𝓞 ℚ)
  erw [h2, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) v).mpr hnv, inv_one]

theorem natCast_eq_one_tmul (v : HeightOneSpectrum (𝓞 ℚ)) (N : ℕ) :
    ((N : ℕ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((N : ℕ) : v.adicCompletion ℚ) := by
  induction N with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, Nat.cast_succ, ih, Algebra.TensorProduct.one_def, TensorProduct.tmul_add]

theorem natCast_rat_smul_eq (v : HeightOneSpectrum (𝓞 ℚ)) (N : ℕ) (y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    ((N : ℕ) : ℚ) • y = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((N : ℕ) : v.adicCompletion ℚ)) * y := by
  rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, natCast_eq_one_tmul]

theorem eq_factorization_of_prod_pow_natGenerator_eq (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (n : HeightOneSpectrum (𝓞 ℚ) → ℕ) (N : ℕ)
    (h : ∏ v ∈ S, (Rat.HeightOneSpectrum.natGenerator v) ^ (n v) = N) (v₀ : HeightOneSpectrum (𝓞 ℚ)) (hv₀ : v₀ ∈ S) :
    n v₀ = N.factorization (Rat.HeightOneSpectrum.natGenerator v₀) := by
  classical
  have hne : ∀ v ∈ S, (Rat.HeightOneSpectrum.natGenerator v) ^ (n v) ≠ 0 :=
    fun v _ => pow_ne_zero _ (Rat.HeightOneSpectrum.prime_natGenerator v).ne_zero
  rw [← h, Nat.factorization_prod hne, Finset.sum_apply']
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have key : ∀ v ∈ S, n v * (Rat.HeightOneSpectrum.natGenerator v).factorization (Rat.HeightOneSpectrum.natGenerator v₀) =
      if v = v₀ then n v₀ else 0 := by
    intro v _
    rw [(Rat.HeightOneSpectrum.prime_natGenerator v).factorization, Finsupp.single_apply]
    by_cases hv : v = v₀
    · subst hv; simp
    · have hne' : Rat.HeightOneSpectrum.natGenerator v ≠ Rat.HeightOneSpectrum.natGenerator v₀ := by
        intro heq
        apply hv
        apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
        exact Subtype.ext heq
      rw [if_neg hne', if_neg hv, mul_zero]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq' S v₀, if_pos hv₀]

end WsTwentyOne

section Boxes

theorem one_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) :
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ :=
  AddSubgroup.subset_closure ⟨1, hΛ.one_mem, 1, fun _ => one_mem _, Algebra.TensorProduct.one_def⟩

theorem mul_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x y : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ}
    (hx : x ∈ Submodule.finiteAdeleBox Λ) (hy : y ∈ Submodule.finiteAdeleBox Λ) :
    x * y ∈ Submodule.finiteAdeleBox Λ := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ Submodule.finiteAdeleBox Λ)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨z, hz, c, hc, rfl⟩ ⟨z', hz', c', hc', rfl⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    exact AddSubgroup.subset_closure ⟨z * z', hΛ.mul_mem hz hz', c * c', fun v => mul_mem (hc v) (hc' v), rfl⟩
  · intro x _
    rw [zero_mul]; exact zero_mem _
  · intro x _
    rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h h'
    rw [add_mul]; exact add_mem h h'
  · intro x y z _ _ _ h h'
    rw [mul_add]; exact add_mem h h'
  · intro x y _ _ h
    convert neg_mem h using 1
    exact neg_mul x y
  · intro x y _ _ h
    convert neg_mem h using 1
    exact mul_neg x y

theorem localBox_one_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v :=
  AddSubgroup.subset_closure ⟨1, hΛ.one_mem, 1, one_mem _, Algebra.TensorProduct.one_def⟩

theorem localBox_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox Λ v := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ Submodule.localBox Λ v)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨z, hz, c, hc, rfl⟩ ⟨z', hz', c', hc', rfl⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    exact AddSubgroup.subset_closure ⟨z * z', hΛ.mul_mem hz hz', c * c', mul_mem hc hc', rfl⟩
  · intro x _
    rw [zero_mul]; exact zero_mem _
  · intro x _
    rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h h'
    rw [add_mul]; exact add_mem h h'
  · intro x y z _ _ _ h h'
    rw [mul_add]; exact add_mem h h'
  · intro x y _ _ h
    convert neg_mem h using 1
    exact neg_mul x y
  · intro x y _ _ h
    convert neg_mem h using 1
    exact mul_neg x y

theorem mem_box_of_mem_stabilizer {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) :
    ((u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ := by
  rw [Submodule.mem_finiteIdeleStabilizer_iff] at hu
  have : ((u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ u • ((Submodule.finiteAdeleBox Λ : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
    ⟨1, one_mem_box hΛ, by dsimp only; rw [smul_eq_mul, mul_one]⟩
  rw [hu] at this
  exact this

theorem localBoxUnits_one {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) ∈ Submodule.localBoxUnits Λ v :=
  ⟨by rw [Units.val_one]; exact localBox_one_mem hΛ v, by rw [inv_one, Units.val_one]; exact localBox_one_mem hΛ v⟩

theorem localBoxUnits_mul {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {x y : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ} (hx : x ∈ Submodule.localBoxUnits Λ v) (hy : y ∈ Submodule.localBoxUnits Λ v) :
    x * y ∈ Submodule.localBoxUnits Λ v :=
  ⟨by rw [Units.val_mul]; exact localBox_mul_mem hΛ v hx.1 hy.1,
   by rw [mul_inv_rev, Units.val_mul]; exact localBox_mul_mem hΛ v hy.2 hx.2⟩

theorem localBoxUnits_inv {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    {x : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ} (hx : x ∈ Submodule.localBoxUnits Λ v) : x⁻¹ ∈ Submodule.localBoxUnits Λ v :=
  ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

theorem map_mulLeft_eq_of_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {x : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ} (hx : x ∈ Submodule.localBoxUnits Λ v) :
    (Submodule.localBox Λ v).map (AddMonoidHom.mulLeft ((x : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) = Submodule.localBox Λ v := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact localBox_mul_mem hΛ v hx.1 hy
  · intro y hy
    refine ⟨((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * y, localBox_mul_mem hΛ v hx.2 hy, ?_⟩
    rw [AddMonoidHom.coe_mulLeft, Units.mul_inv_cancel_left]

theorem relIndex_map_mulLeft_unit_mul {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {x : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ} (hx : x ∈ Submodule.localBoxUnits Λ v) (h : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    ((Submodule.localBox Λ v).map (AddMonoidHom.mulLeft (((x : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * h))).relIndex
        (Submodule.localBox Λ v) =
      ((Submodule.localBox Λ v).map (AddMonoidHom.mulLeft h)).relIndex (Submodule.localBox Λ v) := by
  have e1 : (Submodule.localBox Λ v).map (AddMonoidHom.mulLeft (((x : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * h)) =
      ((Submodule.localBox Λ v).map (AddMonoidHom.mulLeft h)).map (AddMonoidHom.mulLeft ((x : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) := by
    rw [AddSubgroup.map_map]
    congr 1
    ext y
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft, mul_assoc]
  have e2 := map_mulLeft_eq_of_mem_localBoxUnits hΛ v hx
  rw [e1, show ((((Submodule.localBox Λ v).map (AddMonoidHom.mulLeft h)).map
      (AddMonoidHom.mulLeft ((x : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))).relIndex (Submodule.localBox Λ v)) =
      (((Submodule.localBox Λ v).map (AddMonoidHom.mulLeft h)).map
        (AddMonoidHom.mulLeft ((x : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))).relIndex
        ((Submodule.localBox Λ v).map (AddMonoidHom.mulLeft ((x : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))) by rw [e2]]
  have hinj : Function.Injective (AddMonoidHom.mulLeft ((x : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) :=
    (Units.isUnit x).mul_right_injective
  exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj

theorem mem_localBoxUnits_of_relIndex_eq_one {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {x : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ} (hx : ((x : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v)
    (h1 : ((Submodule.localBox Λ v).map (AddMonoidHom.mulLeft ((x : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))).relIndex
      (Submodule.localBox Λ v) = 1) :
    x ∈ Submodule.localBoxUnits Λ v := by
  refine ⟨hx, ?_⟩
  rw [AddSubgroup.relIndex_eq_one] at h1
  obtain ⟨y, hy, hEq⟩ := h1 (localBox_one_mem hΛ v)
  rw [AddMonoidHom.coe_mulLeft] at hEq
  have : ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = y := by
    rw [← mul_one ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ), ← hEq, Units.inv_mul_cancel_left]
  rw [SetLike.mem_coe, this]
  exact hy

end Boxes

section Places

theorem natGenerator_injective : Function.Injective (Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ)) := by
  intro v w h
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  exact Subtype.ext h

noncomputable def placesOver (n : ℕ) : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  n.primeFactors.preimage (Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ)) (natGenerator_injective.injOn)

theorem mem_placesOver_iff {n : ℕ} (hn : n ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) :
    v ∈ placesOver n ↔ Rat.HeightOneSpectrum.natGenerator v ∣ n := by
  rw [placesOver, Finset.mem_preimage, Nat.mem_primeFactors]
  exact ⟨fun h => h.2.1, fun h => ⟨Rat.HeightOneSpectrum.prime_natGenerator v, h, hn⟩⟩

theorem finprod_natGenerator_pow_two_mul_padicValNat (N : ℕ) (hN : N ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
      (Rat.HeightOneSpectrum.natGenerator v) ^ (2 * padicValNat (Rat.HeightOneSpectrum.natGenerator v) N) = N ^ 2 := by
  classical
  have hsupp : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 ℚ) =>
      (Rat.HeightOneSpectrum.natGenerator v) ^ (2 * padicValNat (Rat.HeightOneSpectrum.natGenerator v) N)) ⊆
        (placesOver N : Set (HeightOneSpectrum (𝓞 ℚ))) := by
    intro v hv
    rw [Function.mem_mulSupport] at hv
    rw [Finset.mem_coe, mem_placesOver_iff hN]
    by_contra hnd
    haveI : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
    rw [padicValNat.eq_zero_of_not_dvd hnd, mul_zero, pow_zero] at hv
    exact hv rfl
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp, placesOver,
    Finset.prod_preimage (Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ)) N.primeFactors natGenerator_injective.injOn
      (fun p => p ^ (2 * padicValNat p N))]
  · conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hN, Nat.prod_factorization_eq_prod_primeFactors, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [pow_mul', Nat.factorization_def N (Nat.prime_of_mem_primeFactors hp)]
  · intro p hp hnot
    exfalso
    apply hnot
    refine ⟨(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, Nat.prime_of_mem_primeFactors hp⟩, ?_⟩
    show (((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ))
      ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, Nat.prime_of_mem_primeFactors hp⟩) : Nat.Primes) : ℕ) = p
    rw [Equiv.apply_symm_apply]

end Places

end QType

namespace QType

section LocalM

theorem relIndex_m {a b : ℚ} (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (N : ℕ) [NeZero N]
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hm₁ : ((m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ₁)
    (hmN : ((N : ℕ) : ℚ) • ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ₁)
    (hRN : (Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m).toAddSubgroup.relIndex Λ₁.toAddSubgroup = N) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((Submodule.localBox Λ₁ v).map (AddMonoidHom.mulLeft (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)))).relIndex (Submodule.localBox Λ₁ v) =
      (Rat.HeightOneSpectrum.natGenerator v) ^ (2 * padicValNat (Rat.HeightOneSpectrum.natGenerator v) N) := by
  classical
  obtain ⟨ha, hb⟩ := QuaternionAlgebra.IsMaximalOrder.ne_zero_and_ne_zero hΛ₁
  have hO : IsOrder Λ₁ := hΛ₁.isOrder
  obtain ⟨hunit, htype⟩ :=
    QuaternionAlgebra.IsMaximalOrder.localBoxUnits_and_exists_eq_mul_diagonal_mul_of_relIndex_inf_conjByFiniteIdele_eq
      ⟨ha, hb⟩ hΛ₁ N m hm₁ hmN hRN
  set ℓ := Rat.HeightOneSpectrum.natGenerator v with hℓdef
  have hℓ : ℓ.Prime := Rat.HeightOneSpectrum.prime_natGenerator v
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  by_cases hdvd : ℓ ∣ N
  · obtain ⟨-, φ, hφ, hfr, k₁, k₂, hk₁, hk₁i, hk₂, hk₂i, hm⟩ := htype v ℓ hℓ (natGenerator_mem v) hdvd
    rw [QuaternionAlgebra.relIndex_map_mulLeft_eq_pow_of_eq_mul_diagonal_pow_mul ⟨ha, hb⟩ v hℓ (natGenerator_mem v)
      φ hφ (Submodule.localBox Λ₁ v) hfr k₁ k₂ hk₁ hk₁i hk₂ hk₂i 0 (padicValNat ℓ N) _ (by rw [hm, pow_zero]), zero_add]
  · have hNv : ((N : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hdvd ((natGenerator_dvd_iff' v N).mpr h)
    have hu := hunit v hNv
    rw [padicValNat.eq_zero_of_not_dvd hdvd, mul_zero, pow_zero,
      show Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
        ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom m : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) from rfl,
      map_mulLeft_eq_of_mem_localBoxUnits hO v hu, AddSubgroup.relIndex_self]

end LocalM

section Forward

theorem forward {a b : ℚ} (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (N : ℕ) [NeZero N]
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hm₁ : ((m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ₁)
    (hmN : ((N : ℕ) : ℚ) • ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ₁)
    (hRN : (Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m).toAddSubgroup.relIndex Λ₁.toAddSubgroup = N)
    (x g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hg : ((g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ₁)
    (u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hu : u ∈ Submodule.finiteIdeleStabilizer Λ₁)
    (hJ : Submodule.ofFiniteIdele Λ₁ (x * g) = Submodule.ofFiniteIdele Λ₁ (x * u * m)) :
    (Submodule.ofFiniteIdele Λ₁ (x * g)).toAddSubgroup.relIndex (Submodule.ofFiniteIdele Λ₁ x).toAddSubgroup = N ^ 2 ∧
      ∀ p : ℕ, p.Prime → ¬ (Submodule.ofFiniteIdele Λ₁ (x * g) ≤ ((p : ℕ) : ℤ) • Submodule.ofFiniteIdele Λ₁ x) := by
  classical
  have hO : IsOrder Λ₁ := hΛ₁.isOrder
  have hubox : ((u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ₁ := mem_box_of_mem_stabilizer hO hu
  refine ⟨?_, ?_⟩
  ·
    have hum : (((u * m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ₁ := by
      rw [Units.val_mul]; exact mul_mem_box hO hubox hm₁
    rw [hJ, mul_assoc,
      QuaternionAlgebra.IsOrder.relIndex_ofFiniteIdele_mul_eq_finprod_relIndex_map_mulLeft_localBox hO x (u * m) hum,
      ← finprod_natGenerator_pow_two_mul_padicValNat N (NeZero.ne N)]
    refine finprod_congr fun v => ?_
    have hloc := (QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
      Λ₁ hO u).mp hu v
    rw [Units.val_mul, map_mul,
      show Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
        ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom u : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) from rfl,
      relIndex_map_mulLeft_unit_mul hO v hloc, relIndex_m Λ₁ hΛ₁ N m hm₁ hmN hRN v]
  ·
    intro p hp hle
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hpg := (QuaternionAlgebra.IsOrder.ofFiniteIdele_mul_le_zsmul_ofFiniteIdele_iff_inv_smul_mem_finiteAdeleBox
      hO x g p).mp hle
    have hw := (Submodule.ofFiniteIdele_eq_ofFiniteIdele_iff Λ₁ hO.fg hO.spanTop (x * g) (x * u * m)).mp hJ
    set w : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := (x * g)⁻¹ * (x * u * m) with hwdef
    have hm_eq : m = u⁻¹ * g * w := by rw [hwdef]; group
    have hwbox : ((w : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ₁ := mem_box_of_mem_stabilizer hO hw
    have huibox : ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ₁ := mem_box_of_mem_stabilizer hO (inv_mem hu)
    apply QuaternionAlgebra.forall_inv_smul_not_mem_finiteAdeleBox_of_mem_of_smul_inv_mem_of_relIndex_inf_conjByFiniteIdele_eq
      Λ₁ hΛ₁ N m hm₁ hmN hRN p hp
    rw [hm_eq, Units.val_mul, Units.val_mul, ← smul_mul_assoc, ← mul_smul_comm]
    exact mul_mem_box hO (mul_mem_box hO huibox hpg) hwbox

end Forward

end QType

namespace QTypeConv

open QType

variable {a b : ℚ}

theorem rat_smul_eq_one_tmul_mul (v : HeightOneSpectrum (𝓞 ℚ)) (q : ℚ) (z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    q • z = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (algebraMap ℚ (v.adicCompletion ℚ) q)) * z := by
  have h := Algebra.smul_def q z
  rw [Algebra.TensorProduct.algebraMap_apply'] at h
  exact h

theorem map_rat_smul (v : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (q : ℚ) (z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    φ (q • z) = (algebraMap ℚ (v.adicCompletion ℚ) q) • φ z := by
  rw [rat_smul_eq_one_tmul_mul, map_mul, hφ, smul_mul_assoc, one_mul]

theorem natCast_adicCompletion_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (hn : n ≠ 0) :
    ((n : ℕ) : v.adicCompletion ℚ) ≠ 0 := by
  intro h
  apply hn
  have hinj : Function.Injective (algebraMap ℚ (v.adicCompletion ℚ)) := (algebraMap ℚ _).injective
  have : algebraMap ℚ (v.adicCompletion ℚ) (n : ℚ) = algebraMap ℚ (v.adicCompletion ℚ) 0 := by rw [map_natCast, map_zero]; exact h
  exact_mod_cast hinj this

theorem relIndex_g {Λ₁ : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder Λ₁) (N : ℕ) [NeZero N]
    (x g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hg : ((g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ₁)
    (hidx : (Submodule.ofFiniteIdele Λ₁ (x * g)).toAddSubgroup.relIndex (Submodule.ofFiniteIdele Λ₁ x).toAddSubgroup = N ^ 2)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((Submodule.localBox Λ₁ v).map (AddMonoidHom.mulLeft (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)))).relIndex (Submodule.localBox Λ₁ v) =
      (Rat.HeightOneSpectrum.natGenerator v) ^ (2 * padicValNat (Rat.HeightOneSpectrum.natGenerator v) N) := by
  classical
  have hfg := hO.fg
  have hsp := hO.spanTop

  have hgv : ∀ w : HeightOneSpectrum (𝓞 ℚ), Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
      Submodule.localBox Λ₁ w :=
    (Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ₁ hfg hsp _).mp hg

  have hex : ∀ w : HeightOneSpectrum (𝓞 ℚ), ∃ f : ℕ,
      ((Submodule.localBox Λ₁ w).map (AddMonoidHom.mulLeft
        (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)))).relIndex (Submodule.localBox Λ₁ w) =
        (Rat.HeightOneSpectrum.natGenerator w) ^ f := fun w =>
    QuaternionAlgebra.IsOrder.exists_relIndex_map_mulLeft_localBox_eq_pow hO w (Rat.HeightOneSpectrum.prime_natGenerator w)
      (natGenerator_mem w) _ (hgv w) ((Units.isUnit g).map _)
  choose f hf using hex

  have hprod : ∏ᶠ w : HeightOneSpectrum (𝓞 ℚ), (Rat.HeightOneSpectrum.natGenerator w) ^ f w = N ^ 2 := by
    rw [← hidx, QuaternionAlgebra.IsOrder.relIndex_ofFiniteIdele_mul_eq_finprod_relIndex_map_mulLeft_localBox hO x g hg]
    exact finprod_congr fun w => (hf w).symm

  obtain ⟨M, hM0, hM⟩ := Submodule.exists_ne_zero_natCast_smul_mem_finiteAdeleBox Λ₁ hsp
    ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)
  have hf0 : ∀ w : HeightOneSpectrum (𝓞 ℚ), ¬ Rat.HeightOneSpectrum.natGenerator w ∣ M → f w = 0 := by
    intro w hnd
    set gw : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ :=
      Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom g with hgw
    have hgw_val : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
        ((gw : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) := rfl
    have hMw : ((M : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => hnd ((natGenerator_dvd_iff' w M).mpr h)
    have hMinv := inv_natCast_mem_adicCompletionIntegers w M hMw
    have h1 : ((M : ℕ) : ℚ) • (((gw⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ)) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) ∈
        Submodule.localBox Λ₁ w := by
      have hgw_inv : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          ((gw⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) := rfl
      have := (Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ₁ hfg hsp _).mp hM w
      rwa [map_smul, hgw_inv] at this
    have hunit : gw ∈ Submodule.localBoxUnits Λ₁ w := by
      refine ⟨by rw [← hgw_val]; exact hgv w, ?_⟩
      have h2 : (((gw⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ)) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) =
          ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (((M : ℕ) : w.adicCompletion ℚ))⁻¹) *
            (((M : ℕ) : ℚ) • (((gw⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ)) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) := by
        rw [natCast_rat_smul_eq, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          inv_mul_cancel₀ (natCast_adicCompletion_ne_zero w hM0), ← Algebra.TensorProduct.one_def, one_mul]
      rw [SetLike.mem_coe, h2]
      exact one_tmul_mul_mem_localBox Λ₁ w hMinv h1
    have h := hf w
    rw [hgw_val, map_mulLeft_eq_of_mem_localBoxUnits hO w hunit, AddSubgroup.relIndex_self] at h
    by_contra hne
    exact absurd h.symm (Nat.one_lt_pow hne (Rat.HeightOneSpectrum.prime_natGenerator w).one_lt).ne'

  have hMN : M * N ≠ 0 := mul_ne_zero hM0 (NeZero.ne N)
  have hsupp : (Function.mulSupport fun w : HeightOneSpectrum (𝓞 ℚ) => (Rat.HeightOneSpectrum.natGenerator w) ^ f w) ⊆
      (placesOver (M * N) : Set (HeightOneSpectrum (𝓞 ℚ))) := by
    intro w hw
    rw [Function.mem_mulSupport] at hw
    rw [Finset.mem_coe, mem_placesOver_iff hMN]
    by_contra hnd
    rw [hf0 w (fun h => hnd (h.mul_right N)), pow_zero] at hw
    exact hw rfl
  have hprodS : ∏ w ∈ placesOver (M * N), (Rat.HeightOneSpectrum.natGenerator w) ^ f w = N ^ 2 := by
    rw [← finprod_eq_prod_of_mulSupport_subset _ hsupp, hprod]
  have hfN : f v = 2 * padicValNat (Rat.HeightOneSpectrum.natGenerator v) N := by
    haveI : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
    by_cases hv : v ∈ placesOver (M * N)
    · rw [eq_factorization_of_prod_pow_natGenerator_eq _ f (N ^ 2) hprodS v hv, Nat.factorization_pow, Finsupp.smul_apply,
        smul_eq_mul, Nat.factorization_def N (Rat.HeightOneSpectrum.prime_natGenerator v)]
    · have hnd : ¬ Rat.HeightOneSpectrum.natGenerator v ∣ M * N := fun h => hv ((mem_placesOver_iff hMN v).mpr h)
      rw [hf0 v (fun h => hnd (h.mul_right N)),
        padicValNat.eq_zero_of_not_dvd (fun h => hnd (dvd_mul_of_dvd_right h M)), mul_zero]
  rw [hf v, hfN]

end QTypeConv

namespace QTypeConv

open QType

section IntM
variable {K : Type*} [Field K] {O : ValuationSubring K}

theorem intM_mul {A B : Matrix (Fin 2) (Fin 2) K} (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) :
    ∀ i j, (A * B) i j ∈ O := by
  intro i j
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hA i k) (hB k j)

end IntM

variable {a b : ℚ}

theorem map_symm_mem_localBoxUnits {Λ₁ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hfr : ∀ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, z ∈ Submodule.localBox Λ₁ v ↔ ∀ i j, φ z i j ∈ v.adicCompletionIntegers ℚ)
    (k : GL (Fin 2) (v.adicCompletion ℚ))
    (hk : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ)
    (hki : ∀ i j, ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ) :
    (Units.map φ.symm.toRingHom.toMonoidHom k : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) ∈ Submodule.localBoxUnits Λ₁ v := by
  have hval : ((Units.map φ.symm.toRingHom.toMonoidHom k : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = φ.symm (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := rfl
  have hinv : (((Units.map φ.symm.toRingHom.toMonoidHom k)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) =
      φ.symm ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := rfl
  refine ⟨?_, ?_⟩
  · rw [SetLike.mem_coe, hfr, hval]
    intro i j
    rw [RingEquiv.apply_symm_apply]
    exact hk i j
  · rw [SetLike.mem_coe, hfr, hinv]
    intro i j
    rw [RingEquiv.apply_symm_apply]
    exact hki i j

theorem local_factor {a b : ℚ} (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (N : ℕ) [NeZero N]
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hm₁ : ((m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ₁)
    (hmN : ((N : ℕ) : ℚ) • ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ₁)
    (hRN : (Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m).toAddSubgroup.relIndex Λ₁.toAddSubgroup = N)
    (x g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hg : ((g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ₁)
    (hidx : (Submodule.ofFiniteIdele Λ₁ (x * g)).toAddSubgroup.relIndex (Submodule.ofFiniteIdele Λ₁ x).toAddSubgroup = N ^ 2)
    (hprim : ∀ p : ℕ, p.Prime → ¬ (Submodule.ofFiniteIdele Λ₁ (x * g) ≤ ((p : ℕ) : ℤ) • Submodule.ofFiniteIdele Λ₁ x)) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ U U' : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ, U ∈ Submodule.localBoxUnits Λ₁ v ∧ U' ∈ Submodule.localBoxUnits Λ₁ v ∧
      (¬ Rat.HeightOneSpectrum.natGenerator v ∣ N → U' = 1) ∧
      (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) = U * (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom m : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) * U' := by
  classical
  obtain ⟨ha, hb⟩ := QuaternionAlgebra.IsMaximalOrder.ne_zero_and_ne_zero hΛ₁
  have hO : IsOrder Λ₁ := hΛ₁.isOrder
  have hfg := hO.fg
  have hsp := hO.spanTop
  obtain ⟨hunit, htype⟩ :=
    QuaternionAlgebra.IsMaximalOrder.localBoxUnits_and_exists_eq_mul_diagonal_mul_of_relIndex_inf_conjByFiniteIdele_eq
      ⟨ha, hb⟩ hΛ₁ N m hm₁ hmN hRN
  have hgv : ∀ w : HeightOneSpectrum (𝓞 ℚ), Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
      Submodule.localBox Λ₁ w :=
    (Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ₁ hfg hsp _).mp hg
  have hidxv := relIndex_g hO N x g hg hidx v
  set ℓ := Rat.HeightOneSpectrum.natGenerator v with hℓdef
  have hℓ : ℓ.Prime := Rat.HeightOneSpectrum.prime_natGenerator v
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hgU_val : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) := rfl
  by_cases hdvd : ℓ ∣ N
  ·
    obtain ⟨-, φ, hφ, hfr, k₁, k₂, hk₁, hk₁i, hk₂, hk₂i, hm⟩ := htype v ℓ hℓ (natGenerator_mem v) hdvd
    set Y : GL (Fin 2) (v.adicCompletion ℚ) := Units.map φ.toRingHom.toMonoidHom (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) with hYdef
    have hYval : (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = φ ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) := rfl
    have hYint : ∀ i j, (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ := by
      rw [hYval, ← hgU_val]; exact (hfr _).mp (hgv v)
    obtain ⟨e₁, e₂, k₁', k₂', hle12, hk₁', hk₁'i, hk₂', hk₂'i, hYeq, hprimY⟩ :=
      Matrix.GeneralLinearGroup.exists_eq_mul_diagonal_natCast_pow_mul_of_forall_mem_adicCompletionIntegers v hℓ
        (natGenerator_mem v) Y hYint

    have hidx2 := QuaternionAlgebra.relIndex_map_mulLeft_eq_pow_of_eq_mul_diagonal_pow_mul ⟨ha, hb⟩ v hℓ (natGenerator_mem v)
      φ hφ (Submodule.localBox Λ₁ v) hfr k₁' k₂' hk₁' hk₁'i hk₂' hk₂'i e₁ e₂ ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (by rw [← hYval, hYeq])
    have hsum : e₁ + e₂ = padicValNat ℓ N := by
      have h1 := hidxv
      rw [hgU_val, hidx2] at h1
      have h2 := Nat.pow_right_injective hℓ.two_le h1
      omega

    have he₁ : e₁ = 0 := by
      by_contra hne
      have hint := hprimY.mpr (Nat.one_le_iff_ne_zero.mpr hne)
      apply hprim ℓ hℓ
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      rw [QuaternionAlgebra.IsOrder.ofFiniteIdele_mul_le_zsmul_ofFiniteIdele_iff_inv_smul_mem_finiteAdeleBox hO x g ℓ,
        Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ₁ hfg hsp]
      intro w
      rw [map_smul]
      by_cases hw : v = w
      · subst hw
        rw [hfr, map_rat_smul v φ hφ, map_inv₀, map_natCast, hgU_val, ← hYval]
        exact hint
      · have hℓw : ((ℓ : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
          intro h
          apply hw
          apply natGenerator_injective
          exact ((Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) hℓ).mp
            ((natGenerator_dvd_iff' w ℓ).mpr h)).symm
        rw [rat_smul_eq_one_tmul_mul w, map_inv₀, map_natCast]
        exact one_tmul_mul_mem_localBox Λ₁ w (inv_natCast_mem_adicCompletionIntegers w ℓ hℓw) (hgv w)
    subst he₁
    rw [zero_add] at hsum
    rw [pow_zero, hsum] at hYeq

    refine ⟨Units.map φ.symm.toRingHom.toMonoidHom (k₁' * k₁⁻¹), Units.map φ.symm.toRingHom.toMonoidHom (k₂⁻¹ * k₂'),
      map_symm_mem_localBoxUnits v φ hfr _ (by rw [Units.val_mul]; exact intM_mul hk₁' hk₁i)
        (by rw [mul_inv_rev, inv_inv, Units.val_mul]; exact intM_mul hk₁ hk₁'i),
      map_symm_mem_localBoxUnits v φ hfr _ (by rw [Units.val_mul]; exact intM_mul hk₂i hk₂')
        (by rw [mul_inv_rev, inv_inv, Units.val_mul]; exact intM_mul hk₂'i hk₂),
      fun h => absurd hdvd h, ?_⟩
    apply Units.ext
    apply φ.injective
    have hmU_val : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom m : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) := rfl
    rw [← hYval, hYeq, Units.val_mul, Units.val_mul, map_mul, map_mul, ← hmU_val, hm]
    rw [show ((Units.map φ.symm.toRingHom.toMonoidHom (k₁' * k₁⁻¹) : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) =
        φ.symm ((k₁' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * ((k₁⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) from rfl,
      show ((Units.map φ.symm.toRingHom.toMonoidHom (k₂⁻¹ * k₂') : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) =
        φ.symm (((k₂⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * (k₂' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) from rfl,
      RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
      show ∀ A B C D E F G : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), A * B * (C * D * E) * (F * G) = A * (B * C) * D * (E * F) * G from
        fun _ _ _ _ _ _ _ => by simp only [mul_assoc],
      Units.inv_mul, Units.mul_inv, mul_one, mul_one]
  ·
    have hNv : ((N : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hdvd ((natGenerator_dvd_iff' v N).mpr h)
    have hmu := hunit v hNv
    have hgu : (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) ∈ Submodule.localBoxUnits Λ₁ v := by
      apply mem_localBoxUnits_of_relIndex_eq_one hO v (by rw [← hgU_val]; exact hgv v)
      rw [← hgU_val, hidxv, padicValNat.eq_zero_of_not_dvd hdvd, mul_zero, pow_zero]
    refine ⟨(Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) * ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom m : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ))⁻¹, 1, localBoxUnits_mul hO v hgu (localBoxUnits_inv v hmu), localBoxUnits_one hO v,
      fun _ => rfl, ?_⟩
    rw [mul_one, inv_mul_cancel_right]

end QTypeConv

namespace QTypeConv

open QType

variable {a b : ℚ}

theorem converse {a b : ℚ} (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (N : ℕ) [NeZero N]
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hm₁ : ((m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ₁)
    (hmN : ((N : ℕ) : ℚ) • ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ₁)
    (hRN : (Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m).toAddSubgroup.relIndex Λ₁.toAddSubgroup = N)
    (x g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hg : ((g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ₁)
    (hidx : (Submodule.ofFiniteIdele Λ₁ (x * g)).toAddSubgroup.relIndex (Submodule.ofFiniteIdele Λ₁ x).toAddSubgroup = N ^ 2)
    (hprim : ∀ p : ℕ, p.Prime → ¬ (Submodule.ofFiniteIdele Λ₁ (x * g) ≤ ((p : ℕ) : ℤ) • Submodule.ofFiniteIdele Λ₁ x)) :
    ∃ u ∈ Submodule.finiteIdeleStabilizer Λ₁,
      Submodule.ofFiniteIdele Λ₁ (x * g) = Submodule.ofFiniteIdele Λ₁ (x * u * m) := by
  classical
  have hO : IsOrder Λ₁ := hΛ₁.isOrder
  choose U U' hU hU' hU'1 hfact using local_factor Λ₁ hΛ₁ N m hm₁ hmN hRN x g hg hidx hprim
  obtain ⟨β, hβS, hβoff⟩ := Submodule.exists_units_finiteAdeleEvalAt_eq (D := ℍ[ℚ, a, b]) (placesOver N) U'
  have hβU' : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom β : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) = U' v := by
    intro v
    apply Units.ext
    by_cases hv : v ∈ placesOver N
    · exact hβS v hv
    · have h1 : ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom β : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) =
          Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((β : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) := rfl
      rw [h1, hβoff v hv, hU'1 v (fun h => hv ((mem_placesOver_iff (NeZero.ne N) v).mpr h)), Units.val_one]
  have hβ : β ∈ Submodule.finiteIdeleStabilizer Λ₁ :=
    (QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits Λ₁ hO β).mpr
      fun v => by rw [hβU' v]; exact hU' v
  refine ⟨g * β⁻¹ * m⁻¹, ?_, ?_⟩
  · rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits Λ₁ hO]
    intro v
    rw [map_mul, map_mul, map_inv, map_inv, hfact v, hβU' v,
      show ∀ A B C : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ, A * B * C * C⁻¹ * B⁻¹ = A from fun A B C => by group]
    exact hU v
  · rw [show x * (g * β⁻¹ * m⁻¹) * m = (x * g) * β⁻¹ by group]
    exact (Submodule.ofFiniteIdele_eq_ofFiniteIdele_iff Λ₁ hO.fg hO.spanTop (x * g) ((x * g) * β⁻¹)).mpr
      (by rw [inv_mul_cancel_left]; exact inv_mem hβ)

end QTypeConv

theorem solution
    {a b : ℚ} (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (N : ℕ) [NeZero N]
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hm₁ : ((m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hmN : ((N : ℕ) : ℚ) • ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hRN : (Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m).toAddSubgroup.relIndex Λ₁.toAddSubgroup = N)
    (x g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hg : ((g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁) :
    (∃ u ∈ Submodule.finiteIdeleStabilizer Λ₁,
        Submodule.ofFiniteIdele Λ₁ (x * g) = Submodule.ofFiniteIdele Λ₁ (x * u * m)) ↔
      ((Submodule.ofFiniteIdele Λ₁ (x * g)).toAddSubgroup.relIndex (Submodule.ofFiniteIdele Λ₁ x).toAddSubgroup = N ^ 2 ∧
        ∀ p : ℕ, p.Prime → ¬ (Submodule.ofFiniteIdele Λ₁ (x * g) ≤ ((p : ℕ) : ℤ) • Submodule.ofFiniteIdele Λ₁ x)) :=
  ⟨fun ⟨u, hu, hJ⟩ => QType.forward Λ₁ hΛ₁ N m hm₁ hmN hRN x g hg u hu hJ,
   fun h => QTypeConv.converse Λ₁ hΛ₁ N m hm₁ hmN hRN x g hg h.1 h.2⟩

end S_QuaternionAlgebra_exists_ofFiniteIdele_mul_eq_ofFiniteIdele_mul_mul_iff_relIndex_eq_sq_and_forall_not_le_zsmul
end P2MW
export P2MW.S_QuaternionAlgebra_exists_ofFiniteIdele_mul_eq_ofFiniteIdele_mul_mul_iff_relIndex_eq_sq_and_forall_not_le_zsmul (solution)
