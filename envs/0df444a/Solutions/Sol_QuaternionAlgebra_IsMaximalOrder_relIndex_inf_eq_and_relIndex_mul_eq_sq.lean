-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.relIndex_inf_eq_and_relIndex_mul_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/0bd543ee-bf90-5430-8ae8-4a265079a8a1

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_Submodule_relIndex_toAddSubgroup_eq_finprod_relIndex_localBox
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Matrix_relIndex_inf_conj_diagonal_pow_eq
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_pair_localBox_iff_conj_diagonal_pow_mem_adicCompletionIntegers
import Theorems.Thm_QuaternionAlgebra_forall_isUnit_iff_forall_normForm_eq_zero
import Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_normForm_eq_zero
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_localBox_eq_localBox_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_ne_zero_and_ne_zero
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_relIndex_localBox_mul_eq_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_relIndex_inf_eq_and_relIndex_mul_eq_sq
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "LocalGL2.swapUnit_val QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star"

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField
open QuaternionAlgebra

namespace IndexSym50

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

theorem localBox_mono {X Y : Submodule ℤ ℍ[ℚ, a, b]} (h : X ≤ Y) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox X v ≤ Submodule.localBox Y v :=
  AddSubgroup.closure_mono fun _ ⟨z, hz, c, hc, e⟩ => ⟨z, h hz, c, hc, e⟩

theorem pairSym_localBox (ha : a ≠ 0) (hb : b ≠ 0)
    {Λ₁ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h₁ : QuaternionAlgebra.IsMaximalOrder Λ₁) (h' : QuaternionAlgebra.IsMaximalOrder Λ')
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    (Submodule.localBox Λ₁ v ⊓ Submodule.localBox Λ' v).relIndex (Submodule.localBox Λ₁ v) =
      (Submodule.localBox Λ₁ v ⊓ Submodule.localBox Λ' v).relIndex (Submodule.localBox Λ' v) := by
  by_cases hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x
  · rw [QuaternionAlgebra.IsMaximalOrder.localBox_eq_localBox_of_forall_isUnit v hdiv h₁ h']
  · obtain ⟨ℓ, hℓ, hℓv⟩ := exists_prime_natCast_mem_asIdeal v
    obtain ⟨φ, hφ⟩ := exists_splitting_of_not_forall_isUnit ha hb v hdiv
    obtain ⟨e, ⟨h, hO, hO'⟩, ⟨k, hP, hP'⟩⟩ := QuaternionAlgebra.IsMaximalOrder.exists_pair_localBox_iff_conj_diagonal_pow_mem_adicCompletionIntegers h₁ h' v ℓ hℓ hℓv φ hφ
    rw [Matrix.relIndex_inf_conj_diagonal_pow_eq v ℓ hℓ hℓv φ hφ h e _ _ hO hO', inf_comm, Matrix.relIndex_inf_conj_diagonal_pow_eq v ℓ hℓ hℓv φ hφ k e _ _ hP hP']

theorem relIndex_localBox_eq (ha : a ≠ 0) (hb : b ≠ 0)
    {Λ Λ₁ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h₁ : QuaternionAlgebra.IsMaximalOrder Λ₁) (h' : QuaternionAlgebra.IsMaximalOrder Λ')
    (hle₁ : Λ ≤ Λ₁) (hle' : Λ ≤ Λ') (v : HeightOneSpectrum (𝓞 ℚ)) :
    (Submodule.localBox Λ v).relIndex (Submodule.localBox Λ' v) = (Submodule.localBox Λ v).relIndex (Submodule.localBox Λ₁ v) := by
  have hM : Submodule.localBox Λ v ≤ Submodule.localBox Λ₁ v ⊓ Submodule.localBox Λ' v :=
    le_inf (localBox_mono hle₁ v) (localBox_mono hle' v)
  rw [← AddSubgroup.relIndex_mul_relIndex (Submodule.localBox Λ v) (Submodule.localBox Λ₁ v ⊓ Submodule.localBox Λ' v)
        (Submodule.localBox Λ' v) hM inf_le_right,
      ← AddSubgroup.relIndex_mul_relIndex (Submodule.localBox Λ v) (Submodule.localBox Λ₁ v ⊓ Submodule.localBox Λ' v)
        (Submodule.localBox Λ₁ v) hM inf_le_left,
      pairSym_localBox ha hb h₁ h' v]

end IndexSym50

namespace IndexSym50

variable {a b : ℚ}

theorem le_mul_of_one_mem {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ') : Λ ≤ Λ * Λ' := by
  intro x hx
  simpa using Submodule.mul_mem_mul hx h1

theorem fg_mul_and_span {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (hΛ' : IsOrder Λ') :
    (Λ * Λ').FG ∧ Submodule.span ℚ ((Λ * Λ' : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) = ⊤ := by
  refine ⟨hΛ.fg.mul hΛ'.fg, ?_⟩
  refine top_unique ?_
  rw [← hΛ.spanTop]
  exact Submodule.span_mono (le_mul_of_one_mem hΛ'.one_mem)

private theorem _root_.IndexSym50.relIndex_localBox_mul_eq_sq (ha : a ≠ 0) (hb : b ≠ 0)
    {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) (hΛ' : IsMaximalOrder Λ') (v : HeightOneSpectrum (𝓞 ℚ)) :
    (Submodule.localBox Λ v).relIndex (Submodule.localBox (Λ * Λ') v) =
      ((Submodule.localBox Λ v ⊓ Submodule.localBox Λ' v).relIndex (Submodule.localBox Λ v)) ^ 2 :=
  QuaternionAlgebra.IsMaximalOrder.relIndex_localBox_mul_eq_sq hΛ hΛ' v

p2m_export "IndexSym50" "relIndex_localBox_mul_eq_sq"

theorem finprod_pow_two {ι : Type*} (f : ι → ℕ) : ∏ᶠ i, f i ^ 2 = (∏ᶠ i, f i) ^ 2 := by
  classical
  by_cases hf : (Function.mulSupport f).Finite
  · exact (finprod_pow hf 2).symm
  · have hf2 : ¬ (Function.mulSupport fun i => f i ^ 2).Finite := by
      rwa [show (Function.mulSupport fun i => f i ^ 2) = Function.mulSupport f from by
        ext i; simp [Function.mem_mulSupport]]
    rw [finprod_of_infinite_mulSupport hf, finprod_of_infinite_mulSupport hf2, one_pow]

end IndexSym50

open IndexSym50 in
theorem solution
    {a b : ℚ} (Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛ' : IsMaximalOrder Λ')
    {N : ℕ} [NeZero N] (hN : (Λ ⊓ Λ').toAddSubgroup.relIndex Λ.toAddSubgroup = N) :
    (Λ ⊓ Λ').toAddSubgroup.relIndex Λ'.toAddSubgroup = N ∧
      Λ.toAddSubgroup.relIndex (Λ * Λ').toAddSubgroup = N ^ 2 := by
  obtain ⟨ha, hb⟩ := QuaternionAlgebra.IsMaximalOrder.ne_zero_and_ne_zero hΛ
  have hI : IsOrder (Λ ⊓ Λ') := hΛ.isOrder.inf hΛ'.isOrder

  have hNv : ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
      (Submodule.localBox Λ v ⊓ Submodule.localBox Λ' v).relIndex (Submodule.localBox Λ v) = N := by
    rw [← hN, Submodule.relIndex_toAddSubgroup_eq_finprod_relIndex_localBox Λ (Λ ⊓ Λ') hΛ.isOrder.fg hΛ.isOrder.spanTop
      hI.fg hI.spanTop inf_le_left]
    exact finprod_congr fun v => by
      rw [Submodule.localBox_inf Λ Λ' hΛ.isOrder.fg hΛ.isOrder.spanTop hΛ'.isOrder.fg hΛ'.isOrder.spanTop v]
  constructor
  ·
    rw [← hNv, Submodule.relIndex_toAddSubgroup_eq_finprod_relIndex_localBox Λ' (Λ ⊓ Λ') hΛ'.isOrder.fg hΛ'.isOrder.spanTop
      hI.fg hI.spanTop inf_le_right]
    exact finprod_congr fun v => by
      rw [Submodule.localBox_inf Λ Λ' hΛ.isOrder.fg hΛ.isOrder.spanTop hΛ'.isOrder.fg hΛ'.isOrder.spanTop v,
        pairSym_localBox ha hb hΛ hΛ' v]
  ·
    obtain ⟨hfg, hsp⟩ := fg_mul_and_span hΛ.isOrder hΛ'.isOrder
    rw [Submodule.relIndex_toAddSubgroup_eq_finprod_relIndex_localBox (Λ * Λ') Λ hfg hsp hΛ.isOrder.fg hΛ.isOrder.spanTop
      (le_mul_of_one_mem hΛ'.isOrder.one_mem), ← hNv, ← finprod_pow_two]
    exact finprod_congr fun v => relIndex_localBox_mul_eq_sq ha hb hΛ hΛ' v

end S_QuaternionAlgebra_IsMaximalOrder_relIndex_inf_eq_and_relIndex_mul_eq_sq
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_relIndex_inf_eq_and_relIndex_mul_eq_sq (solution)
