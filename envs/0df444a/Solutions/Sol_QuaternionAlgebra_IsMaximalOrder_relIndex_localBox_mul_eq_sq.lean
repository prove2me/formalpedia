-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.relIndex_localBox_mul_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4503c0bc-217f-540f-9c0d-e72239d8fd15

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_natCard_adicCompletionIntegers_rat_quotient_span_natCast_eq_prime_pow_factorization
import Theorems.Thm_Matrix_relIndex_inf_conj_diagonal_pow_eq
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_pair_localBox_iff_conj_diagonal_pow_mem_adicCompletionIntegers
import Theorems.Thm_QuaternionAlgebra_forall_isUnit_iff_forall_normForm_eq_zero
import Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_normForm_eq_zero
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_localBox_eq_localBox_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_ne_zero_and_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_relIndex_localBox_mul_eq_sq
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "LocalGL2.swapUnit_val QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star"

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

namespace EichlerIndexGen50

variable {a b : ℚ}

theorem exists_prime_natCast_mem_asIdeal (v : HeightOneSpectrum (𝓞 ℚ)) : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 ℚ) ∈ v.asIdeal := by
  classical
  have hI := v.isPrime

  have hm : (Ideal.absNorm v.asIdeal : 𝓞 ℚ) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal
  have hm0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hm1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact hI.ne_top

  suffices key : ∀ m : ℕ, m ≠ 0 → (m : 𝓞 ℚ) ∈ v.asIdeal → m = 1 ∨ ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 ℚ) ∈ v.asIdeal by
    rcases key _ hm0 hm with h | h
    · exact absurd h hm1
    · exact h
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm0 hmem
    by_cases h1 : m = 1
    · exact Or.inl h1
    · right
      have hmf : m.minFac.Prime := Nat.minFac_prime h1
      have hdvd : m.minFac ∣ m := Nat.minFac_dvd m
      obtain ⟨k, hk⟩ := hdvd
      have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hm0 hk
      have hcast : ((m.minFac : 𝓞 ℚ)) * (k : 𝓞 ℚ) ∈ v.asIdeal := by rw [← Nat.cast_mul, ← hk]; exact hmem
      rcases hI.mem_or_mem hcast with h | h
      · exact ⟨m.minFac, hmf, h⟩
      · have hkm : k < m := by
          rw [hk]; exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hk0) hmf.one_lt
        rcases ih k hkm hk0 h with rfl | ⟨ℓ, hℓ, hℓm⟩
        · exact absurd (v.asIdeal.eq_top_of_isUnit_mem h (by simp)) hI.ne_top
        · exact ⟨ℓ, hℓ, hℓm⟩

theorem exists_splitting_of_not_forall_isUnit (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ))
    (hndiv : ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) :
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      ∀ r : v.adicCompletion ℚ, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
  set K := v.adicCompletion ℚ

  obtain ⟨φ₀, -, -⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv (R := ℚ) (S := K) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ K a) (d₂ := (0 : K)) (d₃ := algebraMap ℚ K b) rfl (map_zero _) rfl (AlgEquiv.refl)

  have hK : ¬ ∀ x : ℍ[K, algebraMap ℚ K a, algebraMap ℚ K b], x ≠ 0 → IsUnit x := by
    intro hall
    apply hndiv
    intro x hx
    have hx' : φ₀ x ≠ 0 := by
      intro h0; apply hx; simpa using congrArg φ₀.symm h0
    have hu := hall (φ₀ x) hx'
    simpa using hu.map φ₀.symm

  have h2 : (2 : K) ≠ 0 := by
    have := (algebraMap ℚ K).injective.ne (show (2 : ℚ) ≠ 0 by norm_num)
    simpa using this
  have haK : algebraMap ℚ K a ≠ 0 := by simpa using (algebraMap ℚ K).injective.ne ha
  have hbK : algebraMap ℚ K b ≠ 0 := by simpa using (algebraMap ℚ K).injective.ne hb
  have hiso : ∃ x₀ x₁ x₂ x₃ : K, ¬ (x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ∧
      x₀ ^ 2 - algebraMap ℚ K a * x₁ ^ 2 - algebraMap ℚ K b * x₂ ^ 2 + algebraMap ℚ K a * algebraMap ℚ K b * x₃ ^ 2 = 0 := by
    by_contra hno
    apply hK
    refine (QuaternionAlgebra.forall_isUnit_iff_forall_normForm_eq_zero K (algebraMap ℚ K a) (algebraMap ℚ K b)).2 fun x₀ x₁ x₂ x₃ h0 => ?_
    by_contra hne
    exact hno ⟨x₀, x₁, x₂, x₃, hne, h0⟩
  obtain ⟨x₀, x₁, x₂, x₃, hx, h0⟩ := hiso
  obtain ⟨ψ⟩ := QuaternionAlgebra.nonempty_algEquiv_matrix_of_normForm_eq_zero K h2 (algebraMap ℚ K a) (algebraMap ℚ K b) haK hbK x₀ x₁ x₂ x₃ hx h0

  obtain ⟨φ, hφ, -⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv (R := ℚ) (S := K) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ K a) (d₂ := (0 : K)) (d₃ := algebraMap ℚ K b) rfl (map_zero _) rfl ψ
  exact ⟨φ, hφ⟩

end EichlerIndexGen50

namespace P2Loc50

variable {D : Type*} [Ring D] [Algebra ℚ D]

theorem localBox_mul (Λ Λ' : Submodule ℤ D) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox (Λ * Λ') v =
      AddSubgroup.closure ((Submodule.localBox Λ v : Set (D ⊗[ℚ] v.adicCompletion ℚ)) * (Submodule.localBox Λ' v : Set _)) := by
  classical
  apply le_antisymm
  ·
    refine (AddSubgroup.closure_le _).2 ?_
    rintro x ⟨w, hw, c, hc, rfl⟩

    induction hw using Submodule.mul_induction_on' with
    | mem_mul_mem x hx y hy =>
      have : (x * y) ⊗ₜ[ℚ] c = (x ⊗ₜ[ℚ] c) * (y ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      rw [this]
      exact AddSubgroup.subset_closure (Set.mul_mem_mul
        (AddSubgroup.subset_closure ⟨x, hx, c, hc, rfl⟩)
        (AddSubgroup.subset_closure ⟨y, hy, 1, one_mem _, rfl⟩))
    | add x hx y hy ihx ihy =>
      rw [TensorProduct.add_tmul]
      exact add_mem ihx ihy
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro x ⟨p, hp, q, hq, rfl⟩
    show p * q ∈ Submodule.localBox (Λ * Λ') v

    induction hp using AddSubgroup.closure_induction generalizing q with
    | mem p hp' =>
      obtain ⟨z, hz, c, hc, rfl⟩ := hp'
      induction hq using AddSubgroup.closure_induction with
      | mem q hq' =>
        obtain ⟨z', hz', c', hc', rfl⟩ := hq'
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        exact AddSubgroup.subset_closure ⟨z * z', Submodule.mul_mem_mul hz hz', c * c', mul_mem hc hc', rfl⟩
      | zero => rw [mul_zero]; exact zero_mem _
      | add q q' _ _ ihq ihq' => rw [mul_add]; exact add_mem ihq ihq'
      | neg q _ ihq =>
        have e : z ⊗ₜ[ℚ] c * -q = -(z ⊗ₜ[ℚ] c * q) := by
          rw [eq_neg_iff_add_eq_zero, ← mul_add, neg_add_cancel, mul_zero]
        rw [e]; exact neg_mem ihq
    | zero => rw [zero_mul]; exact zero_mem _
    | add p p' _ _ ihp ihp' => rw [add_mul]; exact add_mem (ihp q hq) (ihp' q hq)
    | neg p _ ihp =>
      have e : -p * q = -(p * q) := by
        rw [eq_neg_iff_add_eq_zero, ← add_mul, neg_add_cancel, zero_mul]
      rw [e]; exact neg_mem (ihp q hq)

variable {a b : ℚ}

theorem localBox_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox Λ v := by
  induction hx using AddSubgroup.closure_induction generalizing y with
  | mem p hp' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hp'
    induction hy using AddSubgroup.closure_induction with
    | mem q hq' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hq'
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact AddSubgroup.subset_closure ⟨z * z', hΛ.mul_mem hz hz', c * c', mul_mem hc hc', rfl⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add q q' _ _ ihq ihq' => rw [mul_add]; exact add_mem ihq ihq'
    | neg q _ ihq =>
      have e : z ⊗ₜ[ℚ] c * -q = -(z ⊗ₜ[ℚ] c * q) := by
        rw [eq_neg_iff_add_eq_zero, ← mul_add, neg_add_cancel, mul_zero]
      rw [e]; exact neg_mem ihq
  | zero => rw [zero_mul]; exact zero_mem _
  | add p p' _ _ ihp ihp' => rw [add_mul]; exact add_mem (ihp hy) (ihp' hy)
  | neg p _ ihp =>
    have e : -p * y = -(p * y) := by
      rw [eq_neg_iff_add_eq_zero, ← add_mul, neg_add_cancel, zero_mul]
    rw [e]; exact neg_mem (ihp hy)

theorem one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v := by
  have : (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) := rfl
  rw [this]
  exact AddSubgroup.subset_closure ⟨1, hΛ.one_mem, 1, one_mem _, rfl⟩

theorem div_case {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    (heq : Submodule.localBox Λ v = Submodule.localBox Λ' v) :
    (Submodule.localBox Λ v).relIndex (Submodule.localBox (Λ * Λ') v) =
      ((Submodule.localBox Λ v ⊓ Submodule.localBox Λ' v).relIndex (Submodule.localBox Λ v)) ^ 2 := by
  have hprod : Submodule.localBox (Λ * Λ') v = Submodule.localBox Λ v := by
    rw [localBox_mul, ← heq]
    apply le_antisymm
    · refine (AddSubgroup.closure_le _).2 ?_
      rintro x ⟨p, hp, q, hq, rfl⟩
      exact localBox_mul_mem hΛ v hp hq
    · intro x hx
      exact AddSubgroup.subset_closure ⟨x, hx, 1, one_mem_localBox hΛ v, (mul_one x)⟩
  rw [hprod, ← heq, inf_idem, AddSubgroup.relIndex_self, one_pow]

section Split

variable (v : HeightOneSpectrum (𝓞 ℚ))

def intMat : AddSubgroup (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) where
  carrier := {m | ∀ i j, m i j ∈ v.adicCompletionIntegers ℚ}
  zero_mem' := fun i j => by simp only [Matrix.zero_apply]; exact zero_mem _
  add_mem' := fun {m m'} hm hm' i j => by simp only [Matrix.add_apply]; exact add_mem (hm i j) (hm' i j)
  neg_mem' := fun {m} hm i j => by simp only [Matrix.neg_apply]; exact neg_mem (hm i j)

theorem mem_intMat_iff (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    m ∈ intMat v ↔ ∀ i j, m i j ∈ v.adicCompletionIntegers ℚ := Iff.rfl

theorem intMat_mul_mem {m m' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)} (hm : m ∈ intMat v) (hm' : m' ∈ intMat v) :
    m * m' ∈ intMat v := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => mul_mem (hm i k) (hm' k j)

theorem one_mem_intMat : (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) ∈ intMat v := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem mul_diagonal_mem_intMat_iff (n : v.adicCompletion ℚ) (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    X * Matrix.diagonal ![(1 : v.adicCompletion ℚ), n] ∈ intMat v ↔
      (∀ i, X i 0 ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i, X i 1 * n ∈ v.adicCompletionIntegers ℚ) := by
  rw [mem_intMat_iff]
  have h0 : ∀ i, (X * Matrix.diagonal ![(1 : v.adicCompletion ℚ), n]) i 0 = X i 0 := fun i => by
    rw [Matrix.mul_diagonal]; simp
  have h1 : ∀ i, (X * Matrix.diagonal ![(1 : v.adicCompletion ℚ), n]) i 1 = X i 1 * n := fun i => by
    rw [Matrix.mul_diagonal]; simp
  constructor
  · intro H
    exact ⟨fun i => by rw [← h0 i]; exact H i 0, fun i => by rw [← h1 i]; exact H i 1⟩
  · rintro ⟨H0, H1⟩ i j
    fin_cases j
    · exact (h0 i).symm ▸ H0 i
    · exact (h1 i).symm ▸ H1 i

theorem mem_span_iff {n : v.adicCompletion ℚ} (hn : n ≠ 0) (nR : v.adicCompletionIntegers ℚ)
    (hnR : (nR : v.adicCompletion ℚ) = n) (r : v.adicCompletionIntegers ℚ) :
    r ∈ Ideal.span {nR} ↔ n⁻¹ * (r : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a', rfl⟩
    have : n⁻¹ * ((a' * nR : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) = a' := by
      push_cast
      rw [hnR, mul_comm (a' : v.adicCompletion ℚ) n, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
    rw [this]
    exact a'.2
  · intro H
    refine ⟨⟨n⁻¹ * (r : v.adicCompletion ℚ), H⟩, Subtype.ext ?_⟩
    push_cast
    rw [hnR, mul_comm n⁻¹, inv_mul_cancel_right₀ hn]

theorem relIndex_intMat_comap_mulRight (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal) (e : ℕ) :
    (intMat v).relIndex ((intMat v).comap
      (AddMonoidHom.mulRight (Matrix.diagonal ![(1 : v.adicCompletion ℚ), (ℓ : v.adicCompletion ℚ) ^ e]))) = (ℓ ^ e) ^ 2 := by
  classical
  haveI : CharZero (v.adicCompletion ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective
  set n : v.adicCompletion ℚ := (ℓ : v.adicCompletion ℚ) ^ e with hn_def
  have hn : n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hℓ.ne_zero)
  have hnR : n ∈ v.adicCompletionIntegers ℚ := pow_mem (natCast_mem _ ℓ) e
  let nR : v.adicCompletionIntegers ℚ := ((ℓ ^ e : ℕ) : v.adicCompletionIntegers ℚ)
  have hnR' : (nR : v.adicCompletion ℚ) = n := by push_cast [nR]; rfl
  let d : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := Matrix.diagonal ![(1 : v.adicCompletion ℚ), n]
  let d' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := Matrix.diagonal ![(1 : v.adicCompletion ℚ), n⁻¹]
  have hdd' : d * d' = 1 := by
    simp only [d, d', Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp [mul_inv_cancel₀ hn]
  have hd'd : d' * d = 1 := by
    simp only [d, d', Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp [inv_mul_cancel₀ hn]
  let ρ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) →+ Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := AddMonoidHom.mulRight d
  have hρ : ∀ X, ρ X = X * d := fun _ => rfl
  have hρinj : Function.Injective ρ := by
    intro X Y h
    have := congrArg (fun Z => Z * d') h
    simpa only [hρ, mul_assoc, hdd', mul_one] using this
  have hρsurj : Function.Surjective ρ := fun Y => ⟨Y * d', by rw [hρ, mul_assoc, hd'd, mul_one]⟩
  let M := intMat v
  let P : AddSubgroup (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := M.comap ρ
  show M.relIndex P = (ℓ ^ e) ^ 2

  let Q : AddSubgroup (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := M.map ρ
  have hstep : M.relIndex P = Q.relIndex M := by
    have hM : M = Q.comap ρ := (AddSubgroup.comap_map_eq_self_of_injective hρinj M).symm
    conv_lhs => rw [hM]
    rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hρsurj]
  rw [hstep]

  have hmemQ : ∀ Y, Y ∈ Q ↔ Y ∈ M ∧ ∀ i, n⁻¹ * Y i 1 ∈ v.adicCompletionIntegers ℚ := by
    intro Y
    constructor
    · rintro ⟨X, hX, rfl⟩
      refine ⟨?_, fun i => ?_⟩
      · have hdM : d ∈ intMat v := by
          intro i j
          simp only [d, Matrix.diagonal_apply]
          split_ifs with h
          · fin_cases i
            · exact one_mem _
            · exact hnR
          · exact zero_mem _
        rw [hρ]; exact intMat_mul_mem v hX hdM
      · rw [hρ, Matrix.mul_diagonal]
        have : n⁻¹ * (X i 1 * n) = X i 1 := by rw [mul_comm, mul_assoc, mul_inv_cancel₀ hn, mul_one]
        simpa [this] using hX i 1
    · rintro ⟨hY, hY1⟩
      refine ⟨Y * d', fun i j => ?_, by rw [hρ, mul_assoc, hd'd, mul_one]⟩
      rw [Matrix.mul_diagonal]
      fin_cases j
      · simpa using hY i 0
      · simpa [mul_comm] using hY1 i
  let I : Ideal (v.adicCompletionIntegers ℚ) := Ideal.span {nR}
  let g₁ : M →+ v.adicCompletionIntegers ℚ :=
    { toFun := fun Y => ⟨(Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1, Y.2 0 1⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let g₂ : M →+ v.adicCompletionIntegers ℚ :=
    { toFun := fun Y => ⟨(Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1, Y.2 1 1⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let g : M →+ (v.adicCompletionIntegers ℚ ⧸ I) × (v.adicCompletionIntegers ℚ ⧸ I) :=
    (AddMonoidHom.prodMap (Ideal.Quotient.mk I).toAddMonoidHom (Ideal.Quotient.mk I).toAddMonoidHom).comp (g₁.prod g₂)
  have hg : ∀ Y : M, g Y = (Ideal.Quotient.mk I (g₁ Y), Ideal.Quotient.mk I (g₂ Y)) := by
    intro Y
    simp only [g, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.prod_apply, AddMonoidHom.coe_prodMap, Prod.map_apply]
    rfl
  have hg₁ : ∀ Y : M, ((g₁ Y : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) = (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1 :=
    fun _ => rfl
  have hg₂ : ∀ Y : M, ((g₂ Y : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) = (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 :=
    fun _ => rfl
  have hker : g.ker = Q.addSubgroupOf M := by
    ext Y
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, hg, Prod.mk_eq_zero, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.Quotient.eq_zero_iff_mem, mem_span_iff v hn nR hnR', mem_span_iff v hn nR hnR', hg₁, hg₂, hmemQ]
    constructor
    · rintro ⟨h0, h1⟩
      refine ⟨Y.2, fun i => ?_⟩
      fin_cases i
      · exact h0
      · exact h1
    · rintro ⟨-, H⟩; exact ⟨H 0, H 1⟩
  have hsurj : Function.Surjective g := by
    rintro ⟨q0, q1⟩
    obtain ⟨r0, rfl⟩ := Ideal.Quotient.mk_surjective q0
    obtain ⟨r1, rfl⟩ := Ideal.Quotient.mk_surjective q1
    let Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := !![0, (r0 : v.adicCompletion ℚ); 0, (r1 : v.adicCompletion ℚ)]
    have hY : Y ∈ M := by
      intro i j; fin_cases i <;> fin_cases j
      · exact zero_mem _
      · exact r0.2
      · exact zero_mem _
      · exact r1.2
    refine ⟨⟨Y, hY⟩, ?_⟩
    rw [hg]
    rfl
  have hcard : Nat.card (v.adicCompletionIntegers ℚ ⧸ I) = ℓ ^ e := by
    rw [IsDedekindDomain.HeightOneSpectrum.natCard_adicCompletionIntegers_rat_quotient_span_natCast_eq_prime_pow_factorization
      v ℓ hℓ hℓv (ℓ ^ e) (pow_ne_zero e hℓ.ne_zero), Nat.factorization_pow_self hℓ]
  calc Q.relIndex M = (Q.addSubgroupOf M).index := rfl
    _ = g.ker.index := by rw [hker]
    _ = Nat.card g.range := AddSubgroup.index_ker g
    _ = Nat.card ((v.adicCompletionIntegers ℚ ⧸ I) × (v.adicCompletionIntegers ℚ ⧸ I)) := by
        rw [AddMonoidHom.range_eq_top.mpr hsurj, AddSubgroup.card_top]
    _ = (ℓ ^ e) ^ 2 := by rw [Nat.card_prod, hcard, pow_two]

theorem diag_mul_diag_inv {K : Type*} [Field K] {n : K} (hn : n ≠ 0) :
    Matrix.diagonal ![(1 : K), n] * Matrix.diagonal ![(1 : K), n⁻¹] = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp [mul_inv_cancel₀ hn]

theorem diag_inv_mul_diag {K : Type*} [Field K] {n : K} (hn : n ≠ 0) :
    Matrix.diagonal ![(1 : K), n⁻¹] * Matrix.diagonal ![(1 : K), n] = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp [inv_mul_cancel₀ hn]

theorem col_decomp {K : Type*} [Field K] {n : K} (hn : n ≠ 0) (Y : Matrix (Fin 2) (Fin 2) K) :
    Y = !![Y 0 0, 0; Y 1 0, 0] * 1 + !![Y 0 1 * n, 0; Y 1 1 * n, 0] * !![0, n⁻¹; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_assoc, mul_inv_cancel₀ hn]

theorem diag_conj_F {K : Type*} [Field K] {n : K} (hn : n ≠ 0) :
    Matrix.diagonal ![(1 : K), n⁻¹] * !![0, n⁻¹; 0, 0] * Matrix.diagonal ![(1 : K), n] = !![(0 : K), 1; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ hn]

theorem mul_diag_apply {K : Type*} [Field K] (n : K) (Y : Matrix (Fin 2) (Fin 2) K) (i : Fin 2) :
    (Y * Matrix.diagonal ![(1 : K), n]) i 0 = Y i 0 ∧ (Y * Matrix.diagonal ![(1 : K), n]) i 1 = Y i 1 * n := by
  constructor <;> (rw [Matrix.mul_diagonal]; simp)

def unitsConjAddEquiv {R : Type*} [Ring R] (h : Rˣ) : R ≃+ R where
  toFun m := (↑h⁻¹ : R) * m * ↑h
  invFun m := (↑h : R) * m * ↑h⁻¹
  left_inv m := by
    show (↑h : R) * ((↑h⁻¹ : R) * m * ↑h) * ↑h⁻¹ = m
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, Units.mul_inv_cancel_right]
  right_inv m := by
    show (↑h⁻¹ : R) * ((↑h : R) * m * ↑h⁻¹) * ↑h = m
    rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, Units.inv_mul_cancel_right]
  map_add' m m' := by
    show (↑h⁻¹ : R) * (m + m') * ↑h = (↑h⁻¹ : R) * m * ↑h + (↑h⁻¹ : R) * m' * ↑h
    rw [mul_add, add_mul]

theorem unitsConjAddEquiv_mul {R : Type*} [Ring R] (h : Rˣ) (m m' : R) :
    unitsConjAddEquiv h (m * m') = unitsConjAddEquiv h m * unitsConjAddEquiv h m' := by
  show (↑h⁻¹ : R) * (m * m') * ↑h = (↑h⁻¹ : R) * m * ↑h * ((↑h⁻¹ : R) * m' * ↑h)
  simp only [mul_assoc, Units.mul_inv_cancel_left]

theorem mul_mem_comap_P {A : Type*} [Ring A] (ψ : A ≃+ Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hψmul : ∀ x y, ψ (x * y) = ψ x * ψ y) {n : v.adicCompletion ℚ} (hn : n ≠ 0) (hnR : n ∈ v.adicCompletionIntegers ℚ)
    {p q : A} (hp : ψ p ∈ intMat v)
    (hq : Matrix.diagonal ![(1 : v.adicCompletion ℚ), n⁻¹] * ψ q * Matrix.diagonal ![(1 : v.adicCompletion ℚ), n] ∈ intMat v) :
    ψ (p * q) * Matrix.diagonal ![(1 : v.adicCompletion ℚ), n] ∈ intMat v := by
  have hdM : Matrix.diagonal ![(1 : v.adicCompletion ℚ), n] ∈ intMat v := by
    intro i j
    rw [Matrix.diagonal_apply]
    split_ifs
    · fin_cases i
      · exact one_mem _
      · exact hnR
    · exact zero_mem _
  have e : ψ q * Matrix.diagonal ![(1 : v.adicCompletion ℚ), n] =
      Matrix.diagonal ![(1 : v.adicCompletion ℚ), n] *
        (Matrix.diagonal ![(1 : v.adicCompletion ℚ), n⁻¹] * ψ q * Matrix.diagonal ![(1 : v.adicCompletion ℚ), n]) := by
    rw [← mul_assoc, ← mul_assoc, diag_mul_diag_inv hn, one_mul]
  rw [hψmul, mul_assoc, e, ← mul_assoc]
  exact intMat_mul_mem v (intMat_mul_mem v hp hdM) hq

theorem exists_decomp {A : Type*} [Ring A] (ψ : A ≃+ Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hψmul : ∀ x y, ψ (x * y) = ψ x * ψ y) {n : v.adicCompletion ℚ} (hn : n ≠ 0)
    {x : A} (hx : ψ x * Matrix.diagonal ![(1 : v.adicCompletion ℚ), n] ∈ intMat v) :
    ∃ p₁ q₁ p₂ q₂ : A, x = p₁ * q₁ + p₂ * q₂ ∧ ψ p₁ ∈ intMat v ∧ ψ p₂ ∈ intMat v ∧
      Matrix.diagonal ![(1 : v.adicCompletion ℚ), n⁻¹] * ψ q₁ * Matrix.diagonal ![(1 : v.adicCompletion ℚ), n] ∈ intMat v ∧
      Matrix.diagonal ![(1 : v.adicCompletion ℚ), n⁻¹] * ψ q₂ * Matrix.diagonal ![(1 : v.adicCompletion ℚ), n] ∈ intMat v := by
  set Y := ψ x with hY
  let Y₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := !![Y 0 0, 0; Y 1 0, 0]
  let Y₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := !![Y 0 1 * n, 0; Y 1 1 * n, 0]
  let F : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := !![0, n⁻¹; 0, 0]
  have hYd : ∀ i, (Y * Matrix.diagonal ![(1 : v.adicCompletion ℚ), n]) i 0 = Y i 0 ∧
      (Y * Matrix.diagonal ![(1 : v.adicCompletion ℚ), n]) i 1 = Y i 1 * n := fun i => mul_diag_apply n Y i
  have hY₀ : Y₀ ∈ intMat v := by
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [Y₀] using (hYd 0).1 ▸ hx 0 0
    · simp [Y₀]
    · simpa [Y₀] using (hYd 1).1 ▸ hx 1 0
    · simp [Y₀]
  have hY₁ : Y₁ ∈ intMat v := by
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [Y₁] using (hYd 0).2 ▸ hx 0 1
    · simp [Y₁]
    · simpa [Y₁] using (hYd 1).2 ▸ hx 1 1
    · simp [Y₁]
  have h1 : Matrix.diagonal ![(1 : v.adicCompletion ℚ), n⁻¹] * (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
      Matrix.diagonal ![(1 : v.adicCompletion ℚ), n] ∈ intMat v := by
    rw [mul_one, diag_inv_mul_diag hn]; exact one_mem_intMat v
  have hF : Matrix.diagonal ![(1 : v.adicCompletion ℚ), n⁻¹] * F * Matrix.diagonal ![(1 : v.adicCompletion ℚ), n] ∈ intMat v := by
    rw [show Matrix.diagonal ![(1 : v.adicCompletion ℚ), n⁻¹] * F * Matrix.diagonal ![(1 : v.adicCompletion ℚ), n] =
      !![(0 : v.adicCompletion ℚ), 1; 0, 0] from diag_conj_F hn]
    intro i j
    fin_cases i <;> fin_cases j
    · exact zero_mem _
    · exact one_mem _
    · exact zero_mem _
    · exact zero_mem _
  have hψsymm_mul : ∀ X Z, ψ.symm (X * Z) = ψ.symm X * ψ.symm Z := by
    intro X Z
    apply ψ.injective
    rw [hψmul, ψ.apply_symm_apply, ψ.apply_symm_apply, ψ.apply_symm_apply]
  refine ⟨ψ.symm Y₀, ψ.symm 1, ψ.symm Y₁, ψ.symm F, ?_, ?_, ?_, ?_, ?_⟩
  · apply ψ.injective
    rw [map_add, hψmul, hψmul, ψ.apply_symm_apply, ψ.apply_symm_apply, ψ.apply_symm_apply, ψ.apply_symm_apply, ← hY]
    exact col_decomp hn Y
  · rw [ψ.apply_symm_apply]; exact hY₀
  · rw [ψ.apply_symm_apply]; exact hY₁
  · rw [ψ.apply_symm_apply]; exact h1
  · rw [ψ.apply_symm_apply]; exact hF

theorem main_split {A : Type*} [Ring A] (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal)
    (φ : A ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (h : GL (Fin 2) (v.adicCompletion ℚ)) (e : ℕ)
    (O O' : AddSubgroup A)
    (hO : ∀ x, x ∈ O ↔ ∀ i j,
      (((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        φ x * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ)
    (hO' : ∀ x, x ∈ O' ↔ ∀ i j,
      (Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((ℓ : v.adicCompletion ℚ) ^ e)⁻¹] *
        ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        φ x * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        Matrix.diagonal ![(1 : v.adicCompletion ℚ), (ℓ : v.adicCompletion ℚ) ^ e]) i j
          ∈ v.adicCompletionIntegers ℚ) :
    O.relIndex (AddSubgroup.closure ((O : Set A) * (O' : Set A))) = (ℓ ^ e) ^ 2 := by
  classical
  haveI : CharZero (v.adicCompletion ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective
  set n : v.adicCompletion ℚ := (ℓ : v.adicCompletion ℚ) ^ e with hn_def
  have hn : n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hℓ.ne_zero)
  have hnR : n ∈ v.adicCompletionIntegers ℚ := pow_mem (natCast_mem _ ℓ) e
  let ψ : A ≃+ Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := φ.toAddEquiv.trans (unitsConjAddEquiv h)
  have hψ : ∀ x, ψ x =
      (((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        φ x * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) := fun _ => rfl
  have hψmul : ∀ x y, ψ (x * y) = ψ x * ψ y := by
    intro x y
    show unitsConjAddEquiv h (φ (x * y)) = unitsConjAddEquiv h (φ x) * unitsConjAddEquiv h (φ y)
    rw [map_mul, unitsConjAddEquiv_mul]
  let M := intMat v
  let P := M.comap (AddMonoidHom.mulRight (Matrix.diagonal ![(1 : v.adicCompletion ℚ), n]))
  have hOeq : O = M.comap ψ.toAddMonoidHom := by
    ext x; rw [AddSubgroup.mem_comap, hO]; rfl
  have hO'mem : ∀ x, x ∈ O' ↔ Matrix.diagonal ![(1 : v.adicCompletion ℚ), n⁻¹] * ψ x * Matrix.diagonal ![(1 : v.adicCompletion ℚ), n] ∈ intMat v := by
    intro x; rw [hO', hψ, ← mul_assoc, ← mul_assoc]; rfl
  have hclos : AddSubgroup.closure ((O : Set A) * (O' : Set A)) = P.comap ψ.toAddMonoidHom := by
    apply le_antisymm
    · refine (AddSubgroup.closure_le _).2 ?_
      rintro x ⟨p, hp, q, hq, rfl⟩
      rw [SetLike.mem_coe, hOeq, AddSubgroup.mem_comap] at hp
      rw [SetLike.mem_coe, hO'mem] at hq
      show ψ (p * q) * Matrix.diagonal ![(1 : v.adicCompletion ℚ), n] ∈ intMat v
      exact mul_mem_comap_P v ψ hψmul hn hnR hp hq
    · intro x hx
      obtain ⟨p₁, q₁, p₂, q₂, hx', hp₁, hp₂, hq₁, hq₂⟩ := exists_decomp v ψ hψmul hn hx
      rw [hx']
      refine add_mem (AddSubgroup.subset_closure (Set.mul_mem_mul ?_ ?_)) (AddSubgroup.subset_closure (Set.mul_mem_mul ?_ ?_))
      · rw [hOeq]; exact hp₁
      · exact (hO'mem q₁).2 hq₁
      · rw [hOeq]; exact hp₂
      · exact (hO'mem q₂).2 hq₂
  rw [hclos, hOeq, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective ψ.surjective]
  exact relIndex_intMat_comap_mulRight v ℓ hℓ hℓv e

end Split

end P2Loc50

open P2Loc50 EichlerIndexGen50 in
theorem solution
    {a b : ℚ} {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsMaximalOrder Λ) (hΛ' : QuaternionAlgebra.IsMaximalOrder Λ')
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    (Submodule.localBox Λ v).relIndex (Submodule.localBox (Λ * Λ') v) =
      ((Submodule.localBox Λ v ⊓ Submodule.localBox Λ' v).relIndex (Submodule.localBox Λ v)) ^ 2 := by
  classical
  obtain ⟨ha, hb⟩ := QuaternionAlgebra.IsMaximalOrder.ne_zero_and_ne_zero hΛ
  by_cases hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x
  · exact div_case hΛ.isOrder v (QuaternionAlgebra.IsMaximalOrder.localBox_eq_localBox_of_forall_isUnit v hdiv hΛ hΛ')
  · obtain ⟨ℓ, hℓ, hℓv⟩ := exists_prime_natCast_mem_asIdeal v
    obtain ⟨φ, hφ⟩ := exists_splitting_of_not_forall_isUnit ha hb v hdiv
    obtain ⟨e, ⟨h, hO, hO'⟩, -⟩ :=
      QuaternionAlgebra.IsMaximalOrder.exists_pair_localBox_iff_conj_diagonal_pow_mem_adicCompletionIntegers hΛ hΛ' v ℓ hℓ hℓv φ hφ
    rw [localBox_mul, main_split v ℓ hℓ hℓv φ h e _ _ hO hO',
      Matrix.relIndex_inf_conj_diagonal_pow_eq v ℓ hℓ hℓv φ hφ h e _ _ hO hO']

end S_QuaternionAlgebra_IsMaximalOrder_relIndex_localBox_mul_eq_sq
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_relIndex_localBox_mul_eq_sq (solution)
