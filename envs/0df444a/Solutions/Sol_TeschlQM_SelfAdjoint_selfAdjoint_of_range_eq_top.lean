-- Prove2me | solution 1 for TeschlQM.SelfAdjoint.selfAdjoint_of_range_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:35:14.715246+00:00
-- url     : https://prove2.me/submissions/3789a997-c0bf-4b57-b46b-542bc70b9230

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_addScalar

open ComplexConjugate
open scoped InnerProductSpace

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (z : ℂ)
    (hz : TeschlQM.SelfAdjoint.rangeAdd A z = ⊤)
    (hz' : TeschlQM.SelfAdjoint.rangeAdd A (conj z) = ⊤) :
    IsSelfAdjoint A := by
  rw [LinearPMap.isSelfAdjoint_def]
  have hdense : Dense (A.domain : Set H) := hA.1
  have hformal : A.IsFormalAdjoint A := fun x y => (hA.2 x y).symm
  have hle : A ≤ A.adjoint := hformal.le_adjoint hdense
  have hadj := LinearPMap.adjoint_isFormalAdjoint hdense (T := A)
  symm
  apply LinearPMap.eq_of_le_of_domain_eq hle
  apply le_antisymm hle.1
  intro ψ hψ
  obtain ⟨ψ', rfl⟩ : ∃ ψ' : A.adjoint.domain, (ψ' : H) = ψ := ⟨⟨ψ, hψ⟩, rfl⟩
  have hsurj' := LinearMap.range_eq_top.mp hz'
  have hsurj := LinearMap.range_eq_top.mp hz
  obtain ⟨φ, hφ⟩ := hsurj' (A.adjoint ψ' + conj z • (ψ' : H))
  let φ₀ : A.domain := ⟨φ, φ.2⟩
  -- `hφ' : (A + z̄) φ = A† ψ + z̄ ψ`
  have hφ' : conj z • (φ₀ : H) + A φ₀ = A.adjoint ψ' + conj z • (ψ' : H) := by
    rw [← hφ]; rfl
  -- for every `χ ∈ 𝔇(A)`, `⟪(A + z) χ, ψ - φ⟫ = 0`
  have hkey : ∀ χ : (TeschlQM.SelfAdjoint.addScalar A z).domain,
      ⟪(TeschlQM.SelfAdjoint.addScalar A z).toFun χ, (ψ' : H) - φ₀⟫_ℂ = 0 := by
    intro χ
    let χ₀ : A.domain := ⟨χ, χ.2⟩
    have e0 : (TeschlQM.SelfAdjoint.addScalar A z).toFun χ = z • (χ₀ : H) + A χ₀ := rfl
    have e1 : ⟪A χ₀, (ψ' : H)⟫_ℂ = ⟪(χ₀ : H), A.adjoint ψ'⟫_ℂ := by
      rw [← inner_conj_symm, ← hadj ψ' χ₀, inner_conj_symm]
    have e2 : ⟪A χ₀, (φ₀ : H)⟫_ℂ = ⟪(χ₀ : H), A φ₀⟫_ℂ := by
      rw [← inner_conj_symm, hA.2 φ₀ χ₀, inner_conj_symm]
    rw [e0, inner_add_left, inner_sub_right, inner_sub_right, e1, e2, inner_smul_left,
      inner_smul_left]
    have e3 : ⟪(χ₀ : H), A.adjoint ψ'⟫_ℂ - ⟪(χ₀ : H), A φ₀⟫_ℂ =
        ⟪(χ₀ : H), A.adjoint ψ' + conj z • (ψ' : H) - (conj z • (φ₀ : H) + A φ₀)⟫_ℂ +
          ((starRingEnd ℂ) z * ⟪(χ₀ : H), (φ₀ : H)⟫_ℂ -
            (starRingEnd ℂ) z * ⟪(χ₀ : H), (ψ' : H)⟫_ℂ) := by
      simp only [inner_add_right, inner_sub_right, inner_smul_right]
      ring
    rw [← hφ', sub_self, inner_zero_right, zero_add] at e3
    linear_combination e3
  obtain ⟨χ, hχ⟩ := hsurj ((ψ' : H) - φ₀)
  have h0 := hkey χ
  rw [hχ, inner_self_eq_zero, sub_eq_zero] at h0
  rw [h0]
  exact φ₀.2

#print axioms solution
