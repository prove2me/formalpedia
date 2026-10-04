-- Prove2me | solution 1 for TeschlQM.SelfAdjoint.selfAdjoint_extension_domain
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-03T20:53:01.567977+00:00
-- url     : https://prove2.me/submissions/945c5759-f45a-4763-91ad-423cd03580d3

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_IsCayleyTransform
import Definitions.Def_TeschlQM_SelfAdjoint_defectSpace

open scoped InnerProductSpace ComplexConjugate
open Filter Topology

namespace TeschlQM.SelfAdjoint.ExtDomainAux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma mem_rangeAdd_iff (A : H →ₗ.[ℂ] H) (z : ℂ) (x : H) :
    x ∈ rangeAdd A z ↔ ∃ ψ : A.domain, A ψ + z • (ψ : H) = x := by
  constructor
  · rintro ⟨φ, rfl⟩
    refine ⟨⟨φ, φ.2⟩, ?_⟩
    show A ⟨φ, φ.2⟩ + z • (φ : H) = z • (φ : H) + A ⟨φ, φ.2⟩
    rw [add_comm]
  · rintro ⟨ψ, rfl⟩
    refine ⟨⟨ψ, ψ.2⟩, ?_⟩
    show z • (ψ : H) + A ψ = A ψ + z • (ψ : H)
    rw [add_comm]

/-- For symmetric `A`, `‖ψ‖ ≤ ‖Aψ + iψ‖`. -/
lemma norm_le_norm_add_I (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (ψ : A.domain) :
    ‖(ψ : H)‖ ≤ ‖A ψ + Complex.I • (ψ : H)‖ := by
  have hre : RCLike.re (⟪A ψ, Complex.I • (ψ : H)⟫_ℂ) = 0 := by
    rw [inner_smul_right]
    have hsym : ⟪A ψ, (ψ : H)⟫_ℂ = ⟪(ψ : H), A ψ⟫_ℂ := (hA.2 ψ ψ).symm
    have hreal : (⟪A ψ, (ψ : H)⟫_ℂ).im = 0 := by
      have h := congrArg Complex.im hsym
      rw [← inner_conj_symm (A ψ) (ψ : H), Complex.conj_im] at h
      rw [hsym]; linarith
    simp [hreal]
  have h1 : ‖A ψ + Complex.I • (ψ : H)‖ ^ 2 = ‖A ψ‖ ^ 2 + ‖(ψ : H)‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := ℂ), hre, norm_smul, Complex.norm_I, one_mul]; ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    (by rw [h1]; nlinarith [sq_nonneg ‖A ψ‖])

/-- For a closed symmetric `A`, `Ran(A + i)` is closed. -/
lemma isClosed_rangeAdd_I [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A)
    (hAc : A.IsClosed) : IsClosed (rangeAdd A Complex.I : Set H) := by
  refine IsSeqClosed.isClosed fun {y} {y₀} hy hlim => ?_
  have hy' : ∀ n, ∃ ψ : A.domain, A ψ + Complex.I • (ψ : H) = y n := fun n =>
    (mem_rangeAdd_iff A _ _).mp (hy n)
  choose ψ hψ using hy'
  have hcauchy : CauchySeq fun n => (ψ n : H) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq ε hε
    refine ⟨N, fun m hm k hk => ?_⟩
    have h1 := norm_le_norm_add_I A hA (ψ m - ψ k)
    have h2 : A (ψ m - ψ k) + Complex.I • ((ψ m - ψ k : A.domain) : H) = y m - y k := by
      rw [← hψ m, ← hψ k, LinearPMap.map_sub]
      simp only [Submodule.coe_sub, smul_sub]
      abel
    rw [h2] at h1
    rw [dist_eq_norm]
    have h3 := hN m hm k hk
    rw [dist_eq_norm] at h3
    simp only [Submodule.coe_sub] at h1
    exact lt_of_le_of_lt h1 h3
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hAψ : Tendsto (fun n => A (ψ n)) atTop (𝓝 (y₀ - Complex.I • x)) := by
    have : (fun n => A (ψ n)) = fun n => y n - Complex.I • (ψ n : H) := by
      funext n; rw [← hψ n]; abel
    rw [this]
    exact hlim.sub (hx.const_smul Complex.I)
  have hmem : (x, y₀ - Complex.I • x) ∈ A.graph := by
    have hcl : IsClosed (A.graph : Set (H × H)) := hAc
    refine hcl.mem_of_tendsto (hx.prodMk_nhds hAψ) (Eventually.of_forall fun n => ?_)
    exact (LinearPMap.mem_graph_iff A).mpr ⟨ψ n, rfl, rfl⟩
  obtain ⟨x', hx1, hx2⟩ := (LinearPMap.mem_graph_iff A).mp hmem
  refine (mem_rangeAdd_iff A _ _).mpr ⟨x', ?_⟩
  rw [hx2, hx1]
  simp

/-- On `φ = (A₁ + i)χ`, a Cayley transform satisfies `φ - V₁φ = 2iχ` and `φ + V₁φ = 2A₁χ`. -/
lemma cayley_sub_add (A V : H →ₗ.[ℂ] H) (hV : IsCayleyTransform A V) (ψ : A.domain)
    (h : A ψ + Complex.I • (ψ : H) ∈ V.domain) :
    (A ψ + Complex.I • (ψ : H)) - V ⟨_, h⟩ = (2 * Complex.I) • (ψ : H) ∧
      (A ψ + Complex.I • (ψ : H)) + V ⟨_, h⟩ = (2 : ℂ) • A ψ := by
  rw [hV.2 ψ h]
  constructor
  · rw [two_mul, add_smul]; abel
  · rw [two_smul]; abel

end TeschlQM.SelfAdjoint.ExtDomainAux

open TeschlQM.SelfAdjoint TeschlQM.SelfAdjoint.ExtDomainAux in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A A₁ V₁ : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (hAc : A.IsClosed)
    (hA₁ : IsSelfAdjoint A₁) (hAA₁ : A ≤ A₁) (hV₁ : IsCayleyTransform A₁ V₁) :
    (A₁.domain : Set H) =
        {x : H | ∃ ψ : A.domain, ∃ φ : V₁.domain, (φ : H) ∈ defectPlus A ∧
          x = (ψ : H) + (φ : H) - V₁ φ} ∧
      ∀ (ψ : A.domain) (φ : V₁.domain), (φ : H) ∈ defectPlus A →
        ∀ h : (ψ : H) + (φ : H) - V₁ φ ∈ A₁.domain,
          A₁ ⟨(ψ : H) + (φ : H) - V₁ φ, h⟩ = A ψ + Complex.I • (φ : H) + Complex.I • V₁ φ := by
  have h2I : (2 * Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
  -- every `φ ∈ 𝔇(V₁)` is `(A₁ + i)χ`, and then `φ - V₁φ = 2iχ ∈ 𝔇(A₁)`
  have hform : ∀ φ : V₁.domain, ∃ χ : A₁.domain, A₁ χ + Complex.I • (χ : H) = φ := fun φ =>
    (mem_rangeAdd_iff A₁ _ _).mp (hV₁.1 ▸ φ.2)
  have hsub : ∀ φ : V₁.domain, ∃ χ : A₁.domain,
      (φ : H) - V₁ φ = (2 * Complex.I) • (χ : H) ∧ (φ : H) + V₁ φ = (2 : ℂ) • A₁ χ := by
    intro φ
    obtain ⟨χ, hχ⟩ := hform φ
    have hmem : A₁ χ + Complex.I • (χ : H) ∈ V₁.domain := hχ ▸ φ.2
    have hφ : φ = ⟨_, hmem⟩ := Subtype.ext hχ.symm
    refine ⟨χ, ?_⟩
    rw [hφ]
    exact cayley_sub_add A₁ V₁ hV₁ χ hmem
  have hAψ : ∀ ψ : A.domain, ∃ h : (ψ : H) ∈ A₁.domain, A₁ ⟨ψ, h⟩ = A ψ := fun ψ =>
    ⟨hAA₁.1 ψ.2, (hAA₁.2 rfl).symm⟩
  refine ⟨?_, ?_⟩
  · ext x
    constructor
    · intro hx
      -- decompose `(A₁ + i)x = y₁ + y₂` with `y₁ ∈ Ran(A + i)` and `y₂ ∈ K₊`
      have hcl := isClosed_rangeAdd_I A hA hAc
      have : CompleteSpace (rangeAdd A Complex.I) := hcl.completeSpace_coe
      obtain ⟨y₁, hy₁, y₂, hy₂, hy⟩ :=
        (rangeAdd A Complex.I).exists_add_mem_mem_orthogonal (A₁ ⟨x, hx⟩ + Complex.I • x)
      obtain ⟨ψ, hψ⟩ := (mem_rangeAdd_iff A _ _).mp hy₁
      obtain ⟨hψ1, hψ2⟩ := hAψ ψ
      let χ : A₁.domain := ⟨x, hx⟩ - ⟨ψ, hψ1⟩
      have hχ : A₁ χ + Complex.I • (χ : H) = y₂ := by
        simp only [χ, LinearPMap.map_sub, Submodule.coe_sub, hψ2, smul_sub]
        rw [← hψ] at hy
        rw [eq_sub_of_add_eq' hy.symm]
        abel
      have hy₂V : y₂ ∈ V₁.domain := by
        rw [hV₁.1, mem_rangeAdd_iff]; exact ⟨χ, hχ⟩
      let φ : V₁.domain := (2 * Complex.I)⁻¹ • ⟨y₂, hy₂V⟩
      refine ⟨ψ, φ, ?_, ?_⟩
      · exact (defectPlus A).smul_mem _ hy₂
      · have hV : V₁ ⟨y₂, hy₂V⟩ = A₁ χ - Complex.I • (χ : H) := by
          have := hV₁.2 χ (hχ ▸ hy₂V)
          rw [← this]
          congr 1
          exact Subtype.ext hχ.symm
        show x = (ψ : H) + (2 * Complex.I)⁻¹ • y₂ - V₁ ((2 * Complex.I)⁻¹ • ⟨y₂, hy₂V⟩)
        rw [LinearPMap.map_smul, hV, ← hχ, add_sub_assoc, ← smul_sub]
        have : A₁ χ + Complex.I • (χ : H) - (A₁ χ - Complex.I • (χ : H)) =
            (2 * Complex.I) • (χ : H) := by rw [two_mul, add_smul]; abel
        rw [this, smul_smul, inv_mul_cancel₀ h2I, one_smul]
        simp [χ]
    · rintro ⟨ψ, φ, -, rfl⟩
      obtain ⟨χ, hχ1, -⟩ := hsub φ
      obtain ⟨hψ1, -⟩ := hAψ ψ
      rw [SetLike.mem_coe, add_sub_assoc, hχ1]
      exact A₁.domain.add_mem hψ1 (A₁.domain.smul_mem _ χ.2)
  · intro ψ φ _ h
    obtain ⟨χ, hχ1, hχ2⟩ := hsub φ
    obtain ⟨hψ1, hψ2⟩ := hAψ ψ
    have hel : (⟨(ψ : H) + (φ : H) - V₁ φ, h⟩ : A₁.domain) =
        ⟨ψ, hψ1⟩ + (2 * Complex.I) • χ := by
      ext
      simp only [Submodule.coe_add, Submodule.coe_smul]
      rw [add_sub_assoc, hχ1]
    rw [hel, LinearPMap.map_add, LinearPMap.map_smul, hψ2, add_assoc, ← smul_add, hχ2,
      smul_smul]
    congr 1
    rw [mul_comm]
