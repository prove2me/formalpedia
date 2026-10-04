-- Prove2me | solution 1 for TeschlQM.SelfAdjoint.cayley_transform_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-03T20:36:17.784172+00:00
-- url     : https://prove2.me/submissions/c51f5462-a3a3-4fe5-8793-389a2a423f0d

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_IsCayleyTransform

open scoped InnerProductSpace

namespace TeschlQM.SelfAdjoint.CayleyAux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma addScalar_toFun_apply (A : H →ₗ.[ℂ] H) (z : ℂ) (ψ : (addScalar A z).domain) :
    (addScalar A z).toFun ψ = A ⟨ψ, ψ.2⟩ + z • (ψ : H) := by
  show z • (ψ : H) + A ⟨ψ, ψ.2⟩ = _
  rw [add_comm]

lemma mem_rangeAdd_iff (A : H →ₗ.[ℂ] H) (z : ℂ) (x : H) :
    x ∈ rangeAdd A z ↔ ∃ ψ : A.domain, A ψ + z • (ψ : H) = x := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨⟨φ, φ.2⟩, (addScalar_toFun_apply A z φ).symm⟩
  · rintro ⟨ψ, rfl⟩
    exact ⟨⟨ψ, ψ.2⟩, addScalar_toFun_apply A z _⟩

/-- For symmetric `A`, `⟪Aψ, ψ⟫` is real, hence `‖Aψ ± iψ‖² = ‖Aψ‖² + ‖ψ‖²`. -/
lemma norm_sq_add_sub_I (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (ψ : A.domain) :
    ‖A ψ + Complex.I • (ψ : H)‖ ^ 2 = ‖A ψ‖ ^ 2 + ‖(ψ : H)‖ ^ 2 ∧
      ‖A ψ - Complex.I • (ψ : H)‖ ^ 2 = ‖A ψ‖ ^ 2 + ‖(ψ : H)‖ ^ 2 := by
  have hre : RCLike.re (⟪A ψ, Complex.I • (ψ : H)⟫_ℂ) = 0 := by
    rw [inner_smul_right]
    have hsym : ⟪A ψ, (ψ : H)⟫_ℂ = ⟪(ψ : H), A ψ⟫_ℂ := (hA.2 ψ ψ).symm
    have hreal : (⟪A ψ, (ψ : H)⟫_ℂ).im = 0 := by
      have h := congrArg Complex.im hsym
      rw [← inner_conj_symm (A ψ) (ψ : H), Complex.conj_im] at h
      rw [hsym]; linarith
    simp [hreal]
  refine ⟨?_, ?_⟩
  · rw [norm_add_sq (𝕜 := ℂ), hre, norm_smul, Complex.norm_I, one_mul]; ring
  · rw [norm_sub_sq (𝕜 := ℂ), hre, norm_smul, Complex.norm_I, one_mul]; ring

/-- `A + i` as a linear map on `𝔇(A)`. -/
noncomputable def plusI (A : H →ₗ.[ℂ] H) : A.domain →ₗ[ℂ] H :=
  A.toFun + Complex.I • A.domain.subtype

/-- `A - i` as a linear map on `𝔇(A)`. -/
noncomputable def minusI (A : H →ₗ.[ℂ] H) : A.domain →ₗ[ℂ] H :=
  A.toFun - Complex.I • A.domain.subtype

lemma plusI_apply (A : H →ₗ.[ℂ] H) (ψ : A.domain) :
    plusI A ψ = A ψ + Complex.I • (ψ : H) := rfl

lemma minusI_apply (A : H →ₗ.[ℂ] H) (ψ : A.domain) :
    minusI A ψ = A ψ - Complex.I • (ψ : H) := rfl

lemma plusI_injective (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) :
    Function.Injective (plusI A) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ψ hψ
  have h := (norm_sq_add_sub_I A hA ψ).1
  rw [← plusI_apply, hψ, norm_zero] at h
  have : ‖(ψ : H)‖ = 0 := by nlinarith [sq_nonneg ‖A ψ‖, sq_nonneg ‖(ψ : H)‖, norm_nonneg (ψ : H)]
  exact Subtype.ext (norm_eq_zero.mp this)

lemma range_plusI (A : H →ₗ.[ℂ] H) : LinearMap.range (plusI A) = rangeAdd A Complex.I := by
  ext x
  rw [mem_rangeAdd_iff, LinearMap.mem_range]
  rfl

/-- The Cayley transform of a symmetric operator. -/
noncomputable def cayley (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) : H →ₗ.[ℂ] H where
  domain := LinearMap.range (plusI A)
  toFun := minusI A ∘ₗ (LinearEquiv.ofInjective (plusI A) (plusI_injective A hA)).symm.toLinearMap

lemma mem_cayley_domain (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (ψ : A.domain) :
    plusI A ψ ∈ (cayley A hA).domain := ⟨ψ, rfl⟩

lemma cayley_apply (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (ψ : A.domain)
    (h : plusI A ψ ∈ (cayley A hA).domain) :
    cayley A hA ⟨plusI A ψ, h⟩ = minusI A ψ := by
  show minusI A ((LinearEquiv.ofInjective (plusI A) (plusI_injective A hA)).symm ⟨plusI A ψ, h⟩) = _
  congr 1
  rw [LinearEquiv.symm_apply_eq]
  ext
  rw [LinearEquiv.ofInjective_apply]

lemma isCayleyTransform_cayley (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) :
    IsCayleyTransform A (cayley A hA) :=
  ⟨range_plusI A, fun ψ h => cayley_apply A hA ψ h⟩

/-- Basic identities for a Cayley transform: on `φ = (A + i)ψ`, `φ - Vφ = 2iψ`, `φ + Vφ = 2Aψ`. -/
lemma cayley_sub_add (A V : H →ₗ.[ℂ] H) (hV : IsCayleyTransform A V) (ψ : A.domain)
    (h : A ψ + Complex.I • (ψ : H) ∈ V.domain) :
    (A ψ + Complex.I • (ψ : H)) - V ⟨_, h⟩ = (2 * Complex.I) • (ψ : H) ∧
      (A ψ + Complex.I • (ψ : H)) + V ⟨_, h⟩ = (2 : ℂ) • A ψ := by
  rw [hV.2 ψ h]
  constructor
  · rw [two_mul, add_smul]; abel
  · rw [two_smul]; abel

lemma mem_domain_of_cayley (A V : H →ₗ.[ℂ] H) (hV : IsCayleyTransform A V) (ψ : A.domain) :
    A ψ + Complex.I • (ψ : H) ∈ V.domain := by
  rw [hV.1, mem_rangeAdd_iff]; exact ⟨ψ, rfl⟩

lemma cayley_unique (A V W : H →ₗ.[ℂ] H) (hV : IsCayleyTransform A V)
    (hW : IsCayleyTransform A W) : V = W := by
  apply LinearPMap.ext (hV.1.trans hW.1.symm)
  intro x hx hx'
  have hx2 : x ∈ rangeAdd A Complex.I := hV.1 ▸ hx
  obtain ⟨ψ, rfl⟩ := (mem_rangeAdd_iff A _ x).mp hx2
  rw [hV.2 ψ hx, hW.2 ψ hx']

lemma le_of_cayley (A B V : H →ₗ.[ℂ] H) (hA : IsCayleyTransform A V)
    (hB : IsCayleyTransform B V) : A ≤ B := by
  have key : ∀ ψ : A.domain, ∃ hψ : (ψ : H) ∈ B.domain, B ⟨ψ, hψ⟩ = A ψ := by
    intro ψ
    have h := mem_domain_of_cayley A V hA ψ
    have h' : A ψ + Complex.I • (ψ : H) ∈ rangeAdd B Complex.I := hB.1 ▸ h
    obtain ⟨χ, hχ⟩ := (mem_rangeAdd_iff B _ _).mp h'
    have hc : B χ + Complex.I • (χ : H) ∈ V.domain := mem_domain_of_cayley B V hB χ
    obtain ⟨e1, e2⟩ := cayley_sub_add A V hA ψ h
    obtain ⟨f1, f2⟩ := cayley_sub_add B V hB χ hc
    have hsame : (⟨_, hc⟩ : V.domain) = ⟨_, h⟩ := Subtype.ext hχ
    rw [hsame, hχ] at f1 f2
    have hψχ : (ψ : H) = χ := by
      have := e1.symm.trans f1
      exact smul_right_injective H (by simp [Complex.I_ne_zero] : (2 * Complex.I) ≠ 0) this
    refine ⟨hψχ ▸ χ.2, ?_⟩
    have hAB : A ψ = B χ := by
      have := e2.symm.trans f2
      exact smul_right_injective H (by norm_num : (2 : ℂ) ≠ 0) this
    rw [hAB]
    congr 1
    exact Subtype.ext hψχ
  refine ⟨fun x hx => (key ⟨x, hx⟩).1, ?_⟩
  intro x y hxy
  obtain ⟨hx, hBx⟩ := key x
  rw [← hBx]
  congr 1
  exact Subtype.ext hxy

end TeschlQM.SelfAdjoint.CayleyAux

open TeschlQM.SelfAdjoint TeschlQM.SelfAdjoint.CayleyAux in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    (∀ A : H →ₗ.[ℂ] H, TeschlQM.Shared.IsSymmetric A →
      ∃ V : H →ₗ.[ℂ] H, IsCayleyTransform A V ∧ IsIsometric V ∧
        Dense (rangeOneSub V : Set H)) ∧
    (∀ A V W : H →ₗ.[ℂ] H, TeschlQM.Shared.IsSymmetric A → IsCayleyTransform A V → IsCayleyTransform A W →
      V = W) ∧
    (∀ A B V : H →ₗ.[ℂ] H, TeschlQM.Shared.IsSymmetric A → TeschlQM.Shared.IsSymmetric B → IsCayleyTransform A V →
      IsCayleyTransform B V → A = B) ∧
    (∀ V : H →ₗ.[ℂ] H, IsIsometric V → Dense (rangeOneSub V : Set H) →
      ∃ A : H →ₗ.[ℂ] H, TeschlQM.Shared.IsSymmetric A ∧ IsCayleyTransform A V) := by
  refine ⟨?_, fun A V W _ hV hW => cayley_unique A V W hV hW,
    fun A B V _ _ hA hB => le_antisymm (le_of_cayley A B V hA hB) (le_of_cayley B A V hB hA), ?_⟩
  · intro A hA
    refine ⟨cayley A hA, isCayleyTransform_cayley A hA, ?_, ?_⟩
    · intro φ
      obtain ⟨ψ, hψ⟩ := LinearMap.mem_range.mp φ.2
      have hφ : φ = ⟨plusI A ψ, mem_cayley_domain A hA ψ⟩ := Subtype.ext hψ.symm
      rw [hφ, cayley_apply]
      show ‖minusI A ψ‖ = ‖plusI A ψ‖
      rw [plusI_apply, minusI_apply]
      have h := norm_sq_add_sub_I A hA ψ
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (h.2.trans h.1.symm)
    · apply hA.1.mono
      intro x hx
      have h2I : (2 * Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
      let ψ : A.domain := ⟨(2 * Complex.I)⁻¹ • x, A.domain.smul_mem _ hx⟩
      refine ⟨⟨plusI A ψ, mem_cayley_domain A hA ψ⟩, ?_⟩
      show plusI A ψ - cayley A hA ⟨plusI A ψ, mem_cayley_domain A hA ψ⟩ = x
      rw [cayley_apply, plusI_apply, minusI_apply]
      have e : A ψ + Complex.I • (ψ : H) - (A ψ - Complex.I • (ψ : H)) =
          (2 * Complex.I) • (ψ : H) := by
        rw [two_mul, add_smul]; abel
      rw [e]
      show (2 * Complex.I) • ((2 * Complex.I)⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ h2I, one_smul]
  · intro V hV hdense
    have h2I : (2 * Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
    let Vi : V.domain →ₗᵢ[ℂ] H := { toLinearMap := V.toFun, norm_map' := hV }
    have hinner : ∀ φ η : V.domain, ⟪V φ, V η⟫_ℂ = ⟪(φ : H), (η : H)⟫_ℂ :=
      fun φ η => Vi.inner_map_map φ η
    let oneSub : V.domain →ₗ[ℂ] H := V.domain.subtype - V.toFun
    have oneSub_apply : ∀ φ : V.domain, oneSub φ = (φ : H) - V φ := fun φ => rfl
    have hinj : Function.Injective oneSub := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro φ hφ
      rw [oneSub_apply] at hφ
      have hφ' : (φ : H) = V φ := sub_eq_zero.mp hφ
      have horth : ∀ y ∈ (rangeOneSub V : Set H), ⟪(φ : H), y⟫_ℂ = 0 := by
        rintro y ⟨η, rfl⟩
        show ⟪(φ : H), (η : H) - V η⟫_ℂ = 0
        rw [inner_sub_right, ← hinner φ η, ← hφ', sub_self]
      have h0 : ⟪(φ : H), (φ : H)⟫_ℂ = 0 :=
        ((isClosed_eq (continuous_const.inner continuous_id) continuous_const).closure_subset_iff.mpr
          horth) (hdense (φ : H))
      exact Subtype.ext (inner_self_eq_zero.mp h0)
    let e := LinearEquiv.ofInjective oneSub hinj
    let A : H →ₗ.[ℂ] H :=
      { domain := LinearMap.range oneSub
        toFun := (Complex.I • (V.domain.subtype + V.toFun)) ∘ₗ e.symm.toLinearMap }
    have memA : ∀ φ : V.domain, oneSub φ ∈ A.domain := fun φ => ⟨φ, rfl⟩
    have hAapp : ∀ (φ : V.domain) (h : oneSub φ ∈ A.domain),
        A ⟨oneSub φ, h⟩ = Complex.I • ((φ : H) + V φ) := by
      intro φ h
      show (Complex.I • (V.domain.subtype + V.toFun)) (e.symm ⟨oneSub φ, h⟩) = _
      have : e.symm ⟨oneSub φ, h⟩ = φ := by
        rw [LinearEquiv.symm_apply_eq]
        ext
        rw [LinearEquiv.ofInjective_apply]
      rw [this]
      rfl
    have hAform : ∀ ψ : A.domain, ∃ φ : V.domain, ∃ h : oneSub φ ∈ A.domain,
        ψ = ⟨oneSub φ, h⟩ := by
      intro ψ
      obtain ⟨φ, hφ⟩ := LinearMap.mem_range.mp ψ.2
      exact ⟨φ, memA φ, Subtype.ext hφ.symm⟩
    have hplus : ∀ (φ : V.domain) (h : oneSub φ ∈ A.domain),
        A ⟨oneSub φ, h⟩ + Complex.I • oneSub φ = (2 * Complex.I) • (φ : H) := by
      intro φ h
      rw [hAapp, oneSub_apply, two_mul, add_smul, smul_add, smul_sub]; abel
    have hminus : ∀ (φ : V.domain) (h : oneSub φ ∈ A.domain),
        A ⟨oneSub φ, h⟩ - Complex.I • oneSub φ = (2 * Complex.I) • V φ := by
      intro φ h
      rw [hAapp, oneSub_apply, two_mul, add_smul, smul_add, smul_sub]; abel
    refine ⟨A, ⟨hdense, ?_⟩, ?_, ?_⟩
    · intro ψ₁ ψ₂
      obtain ⟨φ₁, h₁, rfl⟩ := hAform ψ₁
      obtain ⟨φ₂, h₂, rfl⟩ := hAform ψ₂
      show ⟪oneSub φ₁, A ⟨oneSub φ₂, h₂⟩⟫_ℂ = ⟪A ⟨oneSub φ₁, h₁⟩, oneSub φ₂⟫_ℂ
      rw [hAapp, hAapp, oneSub_apply, oneSub_apply]
      simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
        inner_smul_left, inner_smul_right, hinner, Complex.conj_I]
      ring
    · ext x
      rw [mem_rangeAdd_iff]
      constructor
      · intro hx
        let φ : V.domain := (2 * Complex.I)⁻¹ • ⟨x, hx⟩
        refine ⟨⟨oneSub φ, memA φ⟩, (hplus φ (memA φ)).trans ?_⟩
        show (2 * Complex.I) • ((2 * Complex.I)⁻¹ • x) = x
        rw [smul_smul, mul_inv_cancel₀ h2I, one_smul]
      · rintro ⟨ψ, rfl⟩
        obtain ⟨φ, h, rfl⟩ := hAform ψ
        rw [hplus]
        exact V.domain.smul_mem _ φ.2
    · intro ψ h
      obtain ⟨φ, hφ, rfl⟩ := hAform ψ
      have hel : (⟨_, h⟩ : V.domain) = (2 * Complex.I) • φ := Subtype.ext (hplus φ hφ)
      rw [hel, LinearPMap.map_smul, hminus]

