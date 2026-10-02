-- Prove2me | solution 1 for Transcendence.baker_number_field_basis
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T08:47:54.802592+00:00
-- url     : https://prove2.me/submissions/500a0288-a636-4faa-8c77-9422e16f0b29

import Mathlib
import Theorems.Thm_Diaz_exp_ratMul_isAlgebraic
import Theorems.Thm_Transcendence_schneider_lang_cartesian

/-!
# Baker's theorem over a basis of a number field (DALAG Th. 4.5)

M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups* (2000), Th. 4.5, proved in
§4.2.4 from Cor. 4.3 and Cor. 4.4, both special cases of `Transcendence.schneider_lang_cartesian`.

Let `σ` run over the embeddings `K →ₐ[ℚ] ℂ`, and put `λ_σ = Σ_k σ(β_k) ℓ_k`.

* Lemma 4.6: the matrix `B = (σ β_k)` is regular, since `det B ^ 2` is the discriminant of `β`.
  Its rows and its columns are therefore independent over `ℂ`.
* If every `λ_σ` vanishes, then `ℓ = 0` by the independence of the rows (the book's third case).
* Otherwise put `N = {σ : λ_σ ≠ 0}`, `x_i = (σ β_i)_{σ ∈ N}` and `y_j = (σ(β_j) λ_σ)_{σ ∈ N}`.
  The `x_i` are `ℚ`-independent, as `σ` is injective; the `y_j` span `ℂ^N`, by the independence of
  the columns; and `x_i · y_j = Σ_k Tr(β_iβ_jβ_k) ℓ_k`, because `λ_σ = 0` off `N`, so
  `e^{x_i · y_j}` is algebraic. Cor. 4.3 only asks that the `y_j` contain a basis of `ℂ^N`, while
  `schneider_lang_cartesian` takes a basis, so one is extracted from the `y_j`.
* If `λ` at the inclusion `K ⊂ ℂ` is non-zero, then the coordinate `y_{j,ι₀} = β_j Σ_k β_kℓ_k` is
  algebraic, and `|N| ≤ d < 1 + d` (Cor. 4.2 with `d₀ = 1`, `ι₀ = some`; Cor. 4.4 when `N` is
  everything). Otherwise the inclusion is not in `N`, so `|N| < d` (Cor. 4.3, with `ι₀ = none`).
  Both contradict `schneider_lang_cartesian`.

The book splits into three cases by whether some, none or all of the `λ_σ` vanish, and uses
Cor. 4.3 whenever some `λ_σ` vanishes. The split above, by `λ` at the inclusion, uses `d₀ = 1` also
when `λ` vanishes elsewhere, which Cor. 4.2 allows: it only needs `|N| < d₀ + d₁`.
-/

open Module

namespace E12_baker_number_field_basis

/-- `e^{Σ q_k ℓ_k}` is algebraic when every `e^{ℓ_k}` is and every `q_k` is rational. -/
theorem isAlgebraic_exp_sum_ratCast_mul {ι : Type*} [Fintype ι] (q : ι → ℚ) (ℓ : ι → ℂ)
    (h : ∀ k, IsAlgebraic ℚ (Complex.exp (ℓ k))) :
    IsAlgebraic ℚ (Complex.exp (∑ k, (q k : ℂ) * ℓ k)) := by
  rw [Complex.exp_sum]
  exact mem_algebraicClosure_iff.1
    (prod_mem fun k _ => mem_algebraicClosure_iff.2 (Diaz.exp_ratMul_isAlgebraic (h k) (q k)))

/-- A sum over a subtype is the sum of the extension by zero. -/
theorem sum_dite_mul {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    (g : {a // p a} → ℂ) (F : α → ℂ) :
    ∑ a, (if h : p a then g ⟨a, h⟩ else 0) * F a = ∑ b : {a // p a}, g b * F b.1 := by
  rw [← Fintype.sum_subtype_add_sum_subtype p (fun a => (if h : p a then g ⟨a, h⟩ else 0) * F a)]
  have h2 : ∑ b : {a // ¬p a}, (if h : p b.1 then g ⟨b.1, h⟩ else 0) * F b.1 = 0 :=
    Finset.sum_eq_zero fun b _ => by simp [b.2]
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [b.2]

/-- A linear form on `ℂ^N` is determined by its values on the standard basis. -/
theorem linearMap_apply_eq_sum {N : Type*} [Fintype N] [DecidableEq N] (f : (N → ℂ) →ₗ[ℂ] ℂ)
    (v : N → ℂ) : f v = ∑ ν, v ν * f (Pi.single ν 1) := by
  rw [LinearMap.pi_apply_eq_sum_univ f v]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have : (fun j => if ν = j then (1 : ℂ) else 0) = Pi.single ν 1 := by
    funext j
    simp [Pi.single_apply, eq_comm]
  rw [this, smul_eq_mul]

/-- There are `[K : ℚ]` embeddings of `K` in `ℂ`. -/
theorem card_embeddings (K : IntermediateField ℚ ℂ) {ι : Type*} [Fintype ι] [FiniteDimensional ℚ K]
    (β : Basis ι ℚ K) : Fintype.card (K →ₐ[ℚ] ℂ) = Fintype.card ι := by
  rw [AlgHom.card ℚ K ℂ, Module.finrank_eq_card_basis β]

variable (K : IntermediateField ℚ ℂ) {ι : Type*} [Fintype ι] [FiniteDimensional ℚ K]
  (β : Basis ι ℚ K)

/-- **Lemma 4.6.** The matrix `(σ_j β_k)` is regular: its determinant squared is the discriminant
of `β`, which is non-zero since the trace form is non-degenerate. -/
theorem det_embeddingsMatrixReindex_ne_zero [DecidableEq ι] (e : ι ≃ (K →ₐ[ℚ] ℂ)) :
    (Algebra.embeddingsMatrixReindex ℚ ℂ (fun k => β k) e).det ≠ 0 := by
  intro h
  have h2 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ (fun k => β k) e
  rw [h, zero_pow two_ne_zero, map_eq_zero_iff _ (algebraMap ℚ ℂ).injective] at h2
  exact Algebra.discr_not_zero_of_basis ℚ β h2

/-- The rows `(σ β_k)_k` of `B` are independent: `Σ_k σ(β_k) v_k = 0` for every `σ` forces `v = 0`. -/
theorem eq_zero_of_forall_sum_embeddings_eq_zero (v : ι → ℂ)
    (h : ∀ σ : K →ₐ[ℚ] ℂ, ∑ k, σ (β k) * v k = 0) : v = 0 := by
  classical
  let e : ι ≃ (K →ₐ[ℚ] ℂ) := Fintype.equivOfCardEq (card_embeddings K β).symm
  apply Matrix.eq_zero_of_vecMul_eq_zero (det_embeddingsMatrixReindex_ne_zero K β e)
  funext j
  rw [Pi.zero_apply, ← h (e j)]
  simp [Matrix.vecMul, dotProduct, Algebra.embeddingsMatrixReindex, mul_comm]

/-- The columns `(σ β_k)_σ` of `B` are independent: `Σ_σ c_σ σ(β_k) = 0` for every `k` forces
`c = 0`. -/
theorem eq_zero_of_forall_sum_coeff_embeddings_eq_zero (c : (K →ₐ[ℚ] ℂ) → ℂ)
    (h : ∀ k, ∑ σ, c σ * σ (β k) = 0) : c = 0 := by
  classical
  let e : ι ≃ (K →ₐ[ℚ] ℂ) := Fintype.equivOfCardEq (card_embeddings K β).symm
  have hw : c ∘ e = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero (det_embeddingsMatrixReindex_ne_zero K β e)
    funext k
    rw [Pi.zero_apply, ← h k, ← Equiv.sum_comp e]
    simp [Matrix.mulVec, dotProduct, Algebra.embeddingsMatrixReindex, mul_comm]
  funext σ
  have := congr_fun hw (e.symm σ)
  simpa using this

end E12_baker_number_field_basis

open Module E12_baker_number_field_basis in
theorem solution (K : IntermediateField ℚ ℂ) {ι : Type*} [Fintype ι]
    (β : Module.Basis ι ℚ K) (ℓ : ι → ℂ) (hℓ : ∀ k, IsAlgebraic ℚ (Complex.exp (ℓ k)))
    (hsum : IsAlgebraic ℚ (∑ k, (β k : ℂ) * ℓ k)) : ∀ k, ℓ k = 0 := by
  classical
  have : FiniteDimensional ℚ K := Module.Finite.of_basis β
  -- `λ_σ = Σ_k σ(β_k) ℓ_k`
  let lam : (K →ₐ[ℚ] ℂ) → ℂ := fun σ => ∑ k, σ (β k) * ℓ k
  by_contra hne
  obtain ⟨k₀, hk₀⟩ := not_forall.1 hne
  -- third case of the book: if every `λ_σ` vanishes, then `ℓ = 0`
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ, lam σ ≠ 0 := by
    by_contra hcon
    apply hk₀
    have h0 := eq_zero_of_forall_sum_embeddings_eq_zero K β ℓ
      (fun σ => not_not.1 fun h => hcon ⟨σ, h⟩)
    exact congr_fun h0 k₀
  -- coordinates indexed by `N = {σ : λ_σ ≠ 0}`
  let N := {σ : K →ₐ[ℚ] ℂ // lam σ ≠ 0}
  let eι := Fintype.equivFin ι
  -- `x_i = (σ β_i)_{σ ∈ N}`: algebraic and `ℚ`-independent
  let x : Fin (Fintype.card ι) → N → ℂ := fun i ν => ν.1 (β (eι.symm i))
  have hxalg : ∀ i ν, IsAlgebraic ℚ (x i ν) := fun i ν =>
    (Algebra.IsAlgebraic.isAlgebraic (β (eι.symm i))).algHom ν.1
  have hxind : LinearIndependent ℚ x := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 := congr_fun hg ⟨σ₁, hσ₁⟩
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, x] at h1
    have h2 : σ₁ (∑ i, g i • β (eι.symm i)) = 0 := by
      rw [map_sum]
      simpa [map_rat_smul] using h1
    rw [map_eq_zero σ₁] at h2
    exact Fintype.linearIndependent_iff.1 (β.linearIndependent.comp eι.symm eι.symm.injective) g h2
  -- `y_j = (σ(β_j) λ_σ)_{σ ∈ N}`: they span `ℂ^N`
  let Y : ι → N → ℂ := fun j ν => ν.1 (β j) * lam ν.1
  have hspan : Submodule.span ℂ (Set.range Y) = ⊤ := by
    by_contra hne'
    obtain ⟨f, hf0, hfle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne')
    have hfY : ∀ j, f (Y j) = 0 := fun j => hfle (Submodule.subset_span ⟨j, rfl⟩)
    let c : (K →ₐ[ℚ] ℂ) → ℂ := fun σ =>
      if h : lam σ ≠ 0 then f (Pi.single (⟨σ, h⟩ : N) 1) * lam σ else 0
    have hc : ∀ k, ∑ σ, c σ * σ (β k) = 0 := by
      intro k
      rw [← hfY k, linearMap_apply_eq_sum f (Y k)]
      rw [sum_dite_mul (fun σ => lam σ ≠ 0) (fun ν : N => f (Pi.single ν 1) * lam ν.1)]
      refine Finset.sum_congr rfl fun ν _ => ?_
      ring
    have hc0 := eq_zero_of_forall_sum_coeff_embeddings_eq_zero K β c hc
    apply hf0
    refine (Pi.basisFun ℂ N).ext fun ν => ?_
    have h1 := congr_fun hc0 ν.1
    simp only [c, ν.2, ne_eq, not_false_eq_true, dite_true, Pi.zero_apply] at h1
    rw [Pi.basisFun_apply, LinearMap.zero_apply]
    exact (mul_eq_zero.1 h1).resolve_right ν.2
  -- extract a basis of `ℂ^N` from the `y_j`
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' ℂ Y
  let bκ : Basis κ ℂ (N → ℂ) := Basis.mk hli (by rw [hsp, hspan])
  let eN : N ≃ κ := (Pi.basisFun ℂ N).indexEquiv bκ
  let y : N → N → ℂ := fun n => Y (a (eN n))
  have hy : LinearIndependent ℂ y := hli.comp eN eN.injective
  -- `x_i · y_j = Σ_k Tr(β_iβ_jβ_k) ℓ_k`, since `λ_σ = 0` off `N`
  have hdot : ∀ i j : ι, ∑ ν : N, ν.1 (β i) * Y j ν =
      ∑ k, ((Algebra.trace ℚ K (β i * β j * β k) : ℚ) : ℂ) * ℓ k := by
    intro i j
    have h1 : ∑ ν : N, ν.1 (β i) * Y j ν = ∑ σ, σ (β i) * (σ (β j) * lam σ) := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun σ => lam σ ≠ 0)
        (fun σ => σ (β i) * (σ (β j) * lam σ))]
      have h2 : ∑ ν : {σ // ¬(lam σ ≠ 0)}, ν.1 (β i) * (ν.1 (β j) * lam ν.1) = 0 :=
        Finset.sum_eq_zero fun ν _ => by rw [not_not.1 ν.2, mul_zero, mul_zero]
      rw [h2, add_zero]
    rw [h1]
    simp only [lam, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings ℂ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [map_mul, map_mul]
    ring
  have hexp : ∀ i j, IsAlgebraic ℚ (Complex.exp (∑ ν, x i ν * y j ν)) := by
    intro i j
    show IsAlgebraic ℚ (Complex.exp (∑ ν : N, ν.1 (β (eι.symm i)) * Y (a (eN j)) ν))
    rw [hdot]
    exact isAlgebraic_exp_sum_ratCast_mul _ ℓ hℓ
  have hcard := card_embeddings K β
  by_cases h0 : lam K.val ≠ 0
  · -- Cor. 4.2 with `d₀ = 1`: the inclusion `K ⊂ ℂ` lies in `N`, `y_{j,ι₀} = β_j Σ_k β_kℓ_k` is
    -- algebraic, and `|N| ≤ d`
    refine Transcendence.schneider_lang_cartesian x hxalg hxind y hy (some ⟨K.val, h0⟩) ?_ ?_ hexp
    · have : Fintype.card N ≤ Fintype.card (K →ₐ[ℚ] ℂ) := Fintype.card_subtype_le _
      simp only [Option.elim_some]
      omega
    · rintro k hk j
      obtain rfl := Option.some.inj hk
      exact ((Algebra.IsAlgebraic.isAlgebraic (β (a (eN j)))).algHom K.val).mul hsum
  · -- Cor. 4.3: the inclusion is not in `N`, so `|N| < d`
    refine Transcendence.schneider_lang_cartesian x hxalg hxind y hy none ?_ (by simp) hexp
    have : Fintype.card N < Fintype.card (K →ₐ[ℚ] ℂ) :=
      Fintype.card_subtype_lt (p := fun σ => lam σ ≠ 0) h0
    simp only [Option.elim_none]
    omega
