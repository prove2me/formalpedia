-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.relIndex_eq_of_isMaximalOrder_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/8a4440b5-bfde-5c35-a7b0-31e6d0a8bdbc

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_Submodule_relIndex_toAddSubgroup_eq_finprod_relIndex_localBox
import Theorems.Thm_Matrix_relIndex_inf_conj_diagonal_pow_eq
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_pair_localBox_iff_conj_diagonal_pow_mem_adicCompletionIntegers
import Theorems.Thm_QuaternionAlgebra_forall_isUnit_iff_forall_normForm_eq_zero
import Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_normForm_eq_zero
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_localBox_eq_localBox_of_forall_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_relIndex_eq_of_isMaximalOrder_of_le
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "LocalGL2.swapUnit_val QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star"

set_option autoImplicit false
open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

namespace DEP0

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

theorem pairSym_localBox {q' : ℕ} (hq' : q'.Prime) (hB : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    {Λ₁ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h₁ : QuaternionAlgebra.IsMaximalOrder Λ₁) (h' : QuaternionAlgebra.IsMaximalOrder Λ')
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    (Submodule.localBox Λ₁ v ⊓ Submodule.localBox Λ' v).relIndex (Submodule.localBox Λ₁ v) =
      (Submodule.localBox Λ₁ v ⊓ Submodule.localBox Λ' v).relIndex (Submodule.localBox Λ' v) := by
  by_cases hv : (q' : 𝓞 ℚ) ∈ v.asIdeal
  · rw [QuaternionAlgebra.IsMaximalOrder.localBox_eq_localBox_of_forall_isUnit v ((hB.2.2 v).mpr hv) h₁ h']
  · obtain ⟨ℓ, hℓ, hℓv⟩ := exists_prime_natCast_mem_asIdeal v
    obtain ⟨φ, hφ⟩ := exists_splitting_of_not_forall_isUnit hB.neg_left.ne hB.neg_right.ne v (fun hdiv => hv ((hB.2.2 v).mp hdiv))
    obtain ⟨e, ⟨h, hO, hO'⟩, ⟨k, hP, hP'⟩⟩ := QuaternionAlgebra.IsMaximalOrder.exists_pair_localBox_iff_conj_diagonal_pow_mem_adicCompletionIntegers h₁ h' v ℓ hℓ hℓv φ hφ
    rw [Matrix.relIndex_inf_conj_diagonal_pow_eq v ℓ hℓ hℓv φ hφ h e _ _ hO hO', inf_comm, Matrix.relIndex_inf_conj_diagonal_pow_eq v ℓ hℓ hℓv φ hφ k e _ _ hP hP']

theorem relIndex_localBox_eq {q' : ℕ} (hq' : q'.Prime) (hB : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    {Λ Λ₁ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h₁ : QuaternionAlgebra.IsMaximalOrder Λ₁) (h' : QuaternionAlgebra.IsMaximalOrder Λ')
    (hle₁ : Λ ≤ Λ₁) (hle' : Λ ≤ Λ') (v : HeightOneSpectrum (𝓞 ℚ)) :
    (Submodule.localBox Λ v).relIndex (Submodule.localBox Λ' v) = (Submodule.localBox Λ v).relIndex (Submodule.localBox Λ₁ v) := by
  have hM : Submodule.localBox Λ v ≤ Submodule.localBox Λ₁ v ⊓ Submodule.localBox Λ' v :=
    le_inf (localBox_mono hle₁ v) (localBox_mono hle' v)
  rw [← AddSubgroup.relIndex_mul_relIndex (Submodule.localBox Λ v) (Submodule.localBox Λ₁ v ⊓ Submodule.localBox Λ' v)
        (Submodule.localBox Λ' v) hM inf_le_right,
      ← AddSubgroup.relIndex_mul_relIndex (Submodule.localBox Λ v) (Submodule.localBox Λ₁ v ⊓ Submodule.localBox Λ' v)
        (Submodule.localBox Λ₁ v) hM inf_le_left,
      pairSym_localBox hq' hB h₁ h' v]

end DEP0

open DEP0 in

theorem solution
    {a b : ℚ} {q' : ℕ} (hq' : q'.Prime) (hB : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    {Λ₂ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ₂ : QuaternionAlgebra.IsMaximalOrder Λ₂) (hle₂ : R ≤ Λ₂) :
    R.toAddSubgroup.relIndex Λ₂.toAddSubgroup = N := by
  obtain ⟨Λ₁, h₁, hle₁, hN⟩ := hR.exists_le_isMaximalOrder
  have hRo : QuaternionAlgebra.IsOrder R := hR.isOrder
  rw [← hN, Submodule.relIndex_toAddSubgroup_eq_finprod_relIndex_localBox Λ₂ R hΛ₂.isOrder.fg hΛ₂.isOrder.spanTop hRo.fg hRo.spanTop hle₂,
    Submodule.relIndex_toAddSubgroup_eq_finprod_relIndex_localBox Λ₁ R h₁.isOrder.fg h₁.isOrder.spanTop hRo.fg hRo.spanTop hle₁]
  exact finprod_congr fun v => relIndex_localBox_eq hq' hB h₁ hΛ₂ hle₁ hle₂ v

end S_QuaternionAlgebra_IsEichlerOrder_relIndex_eq_of_isMaximalOrder_of_le
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_relIndex_eq_of_isMaximalOrder_of_le (solution)
