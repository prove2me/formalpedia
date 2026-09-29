-- Prove2me | solution 1 for QuaternionAlgebra.exists_mul_mul_eq_one_and_forall_apply_mem_of_algHom_matrix_injective_of_isOrder_of_isMaximalOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/3c5057bf-8095-52ab-b0d5-f804cb8c268c

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_matrix_forall_mem_iff_forall_mulVec_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_mul_mul_eq_one_and_forall_apply_mem_of_algHom_matrix_injective_of_isOrder_of_isMaximalOrder
p2m_attr_erase "simp" "QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

namespace P2mIntegralE2

variable {A : Type*} [Ring A]

def conjAlgHom {R : Type*} [CommSemiring R] [Algebra R A] (γ γ' : A) (h : γ * γ' = 1) (h' : γ' * γ = 1) :
    A →ₐ[R] A where
  toFun x := γ' * x * γ
  map_one' := by rw [mul_one, h']
  map_mul' x y := by
    calc γ' * (x * y) * γ = γ' * x * (γ * γ') * y * γ := by rw [h]; noncomm_ring
      _ = γ' * x * γ * (γ' * y * γ) := by noncomm_ring
  map_zero' := by rw [mul_zero, zero_mul]
  map_add' x y := by rw [mul_add, add_mul]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, h']

theorem conjAlgHom_apply {R : Type*} [CommSemiring R] [Algebra R A] (γ γ' : A) (h : γ * γ' = 1) (h' : γ' * γ = 1)
    (x : A) : conjAlgHom (R := R) γ γ' h h' x = γ' * x * γ := rfl

theorem conjAlgHom_injective {R : Type*} [CommSemiring R] [Algebra R A] (γ γ' : A) (h : γ * γ' = 1)
    (h' : γ' * γ = 1) : Function.Injective (conjAlgHom (R := R) γ γ' h h') := by
  intro x y hxy
  rw [conjAlgHom_apply, conjAlgHom_apply] at hxy
  have := congrArg (fun z => γ * z * γ') hxy
  calc x = (γ * γ') * x * (γ * γ') := by rw [h, one_mul, mul_one]
    _ = γ * (γ' * x * γ) * γ' := by noncomm_ring
    _ = γ * (γ' * y * γ) * γ' := this
    _ = (γ * γ') * y * (γ * γ') := by noncomm_ring
    _ = y := by rw [h, one_mul, mul_one]

theorem mul_mul_apply_eq_mulVec (γ' X γ : Matrix (Fin 2) (Fin 2) A) (i l : Fin 2) :
    (γ' * X * γ) i l = (γ'.mulVec (X.mulVec (γ.mulVec (Pi.single l 1)))) i := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  rfl

end P2mIntegralE2

open P2mIntegralE2 in
theorem solution
    {a b c d : ℚ} (q : ℕ) [Fact q.Prime]
    (hH : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt c d q)
    (hBq : ∀ v : HeightOneSpectrum (𝓞 ℚ), (q : 𝓞 ℚ) ∈ v.asIdeal →
      ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : QuaternionAlgebra.IsMaximalOrder O)
    (ρ : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hρ : Function.Injective ρ) :
    ∃ γ γ' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], γ * γ' = 1 ∧ γ' * γ = 1 ∧
      ∀ m ∈ Λ, ∀ i l : Fin 2, (γ' * ρ m * γ) i l ∈ O := by
  classical
  have hO1 : QuaternionAlgebra.IsOrder O := hO.1

  let gen : ℍ[ℚ, a, b] → Fin 2 → ℍ[ℚ, c, d] → (Fin 2 → ℍ[ℚ, c, d]) := fun l k o =>
    (ρ l).mulVec (Pi.single k o)
  let S : Set (Fin 2 → ℍ[ℚ, c, d]) := {x | ∃ l ∈ Λ, ∃ k : Fin 2, ∃ o ∈ O, x = gen l k o}
  let M : Submodule ℤ (Fin 2 → ℍ[ℚ, c, d]) := Submodule.span ℤ S
  have gen_mem : ∀ l ∈ Λ, ∀ (k : Fin 2), ∀ o ∈ O, gen l k o ∈ M := fun l hl k o ho =>
    Submodule.subset_span ⟨l, hl, k, o, ho, rfl⟩

  have gen_add_left : ∀ (l l' : ℍ[ℚ, a, b]) (k : Fin 2) (o : ℍ[ℚ, c, d]),
      gen (l + l') k o = gen l k o + gen l' k o := fun l l' k o => by
    simp only [gen, map_add, Matrix.add_mulVec]
  have gen_smul_left : ∀ (n : ℤ) (l : ℍ[ℚ, a, b]) (k : Fin 2) (o : ℍ[ℚ, c, d]),
      gen (n • l) k o = n • gen l k o := fun n l k o => by
    simp only [gen, map_zsmul, Matrix.smul_mulVec]
  have gen_add_right : ∀ (l : ℍ[ℚ, a, b]) (k : Fin 2) (o o' : ℍ[ℚ, c, d]),
      gen l k (o + o') = gen l k o + gen l k o' := fun l k o o' => by
    simp only [gen, Pi.single_add, Matrix.mulVec_add]
  have gen_smul_right : ∀ (n : ℤ) (l : ℍ[ℚ, a, b]) (k : Fin 2) (o : ℍ[ℚ, c, d]),
      gen l k (n • o) = n • gen l k o := fun n l k o => by
    simp only [gen, Pi.single_smul, Matrix.mulVec_smul]

  have mul_right : ∀ (l : ℍ[ℚ, a, b]) (k : Fin 2) (o o' : ℍ[ℚ, c, d]),
      (fun i => gen l k o i * o') = gen l k (o * o') := fun l k o o' => by
    funext i
    simp only [gen, Matrix.mulVec, dotProduct, Finset.sum_mul, Pi.single_apply, mul_ite, mul_zero, ite_mul,
      zero_mul, mul_assoc]
  have hM : ∀ m ∈ M, ∀ o ∈ O, (fun i => m i * o) ∈ M := by
    intro m hm o ho
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, k, o₁, ho₁, rfl⟩ := hx
      rw [mul_right]
      exact gen_mem l hl k _ (hO1.mul_mem ho₁ ho)
    | zero =>
      have : (fun i => (0 : Fin 2 → ℍ[ℚ, c, d]) i * o) = 0 := by funext i; simp
      rw [this]; exact M.zero_mem
    | add x y _ _ hx hy =>
      have : (fun i => (x + y) i * o) = (fun i => x i * o) + fun i => y i * o := by
        funext i; simp [add_mul]
      rw [this]; exact M.add_mem hx hy
    | smul n x _ hx =>
      have : (fun i => (n • x) i * o) = n • fun i => x i * o := by
        funext i; simp [mul_assoc]
      rw [this]; exact M.smul_mem n hx

  have mul_left : ∀ (l l' : ℍ[ℚ, a, b]) (k : Fin 2) (o : ℍ[ℚ, c, d]),
      (ρ l').mulVec (gen l k o) = gen (l' * l) k o := fun l l' k o => by
    simp only [gen, map_mul, Matrix.mulVec_mulVec]
  have hML : ∀ m ∈ M, ∀ l' ∈ Λ, (ρ l').mulVec m ∈ M := by
    intro m hm l' hl'
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, k, o₁, ho₁, rfl⟩ := hx
      rw [mul_left]
      exact gen_mem _ (hΛ.mul_mem hl' hl) k o₁ ho₁
    | zero => rw [Matrix.mulVec_zero]; exact M.zero_mem
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact M.add_mem hx hy
    | smul n x _ hx => rw [Matrix.mulVec_smul]; exact M.smul_mem n hx

  have hfg : M.FG := by
    obtain ⟨sΛ, hsΛ⟩ := hΛ.fg
    obtain ⟨sO, hsO⟩ := hO1.fg
    let T : Finset (Fin 2 → ℍ[ℚ, c, d]) :=
      ((sΛ ×ˢ (Finset.univ : Finset (Fin 2))) ×ˢ sO).image fun p => gen p.1.1 p.1.2 p.2
    refine ⟨T, le_antisymm ?_ ?_⟩
    · refine Submodule.span_le.2 ?_
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
      obtain ⟨hp11, -⟩ := Finset.mem_product.1 hp1
      exact gen_mem _ (hsΛ ▸ Submodule.subset_span hp11) _ _ (hsO ▸ Submodule.subset_span hp2)
    · refine Submodule.span_le.2 ?_
      rintro x ⟨l, hl, k, o, ho, rfl⟩

      have step1 : ∀ o' ∈ sO, ∀ l' ∈ Λ, gen l' k o' ∈ Submodule.span ℤ (T : Set (Fin 2 → ℍ[ℚ, c, d])) := by
        intro o' ho' l' hl'
        rw [← hsΛ] at hl'
        induction hl' using Submodule.span_induction with
        | mem l₀ hl₀ =>
          refine Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image.2 ⟨((l₀, k), o'), ?_, rfl⟩))
          exact Finset.mem_product.2 ⟨Finset.mem_product.2 ⟨hl₀, Finset.mem_univ _⟩, ho'⟩
        | zero =>
          have : gen 0 k o' = 0 := by simp only [gen, map_zero, Matrix.zero_mulVec]
          rw [this]; exact Submodule.zero_mem _
        | add u w _ _ hu hw => rw [gen_add_left]; exact Submodule.add_mem _ hu hw
        | smul n u _ hu => rw [gen_smul_left]; exact Submodule.smul_mem _ n hu
      have step2 : ∀ o' ∈ O, gen l k o' ∈ Submodule.span ℤ (T : Set (Fin 2 → ℍ[ℚ, c, d])) := by
        intro o' ho'
        rw [← hsO] at ho'
        induction ho' using Submodule.span_induction with
        | mem o₀ ho₀ => exact step1 o₀ ho₀ l hl
        | zero =>
          have : gen l k 0 = 0 := by simp only [gen, Pi.single_zero, Matrix.mulVec_zero]
          rw [this]; exact Submodule.zero_mem _
        | add u w _ _ hu hw => rw [gen_add_right]; exact Submodule.add_mem _ hu hw
        | smul n u _ hu => rw [gen_smul_right]; exact Submodule.smul_mem _ n hu
      exact step2 o ho

  have single_mem : ∀ (k : Fin 2), ∀ o ∈ O, Pi.single k o ∈ M := fun k o ho => by
    have := gen_mem 1 hΛ.one_mem k o ho
    simpa only [gen, map_one, Matrix.one_mulVec] using this
  have hspan : Submodule.span ℚ (M : Set (Fin 2 → ℍ[ℚ, c, d])) = ⊤ := by
    refine top_unique fun x _ => ?_
    have hx : x = ∑ k : Fin 2, Pi.single k (x k) := by
      funext i
      rw [Finset.sum_apply, Fin.sum_univ_two]
      fin_cases i <;> simp
    rw [hx]
    refine Submodule.sum_mem _ fun k _ => ?_

    have hxk : x k ∈ Submodule.span ℚ (O : Set ℍ[ℚ, c, d]) := by rw [hO1.spanTop]; trivial
    generalize x k = y at hxk
    induction hxk using Submodule.span_induction with
    | mem o ho => exact Submodule.subset_span (single_mem k o ho)
    | zero => rw [Pi.single_zero]; exact Submodule.zero_mem _
    | add u w _ _ hu hw => rw [Pi.single_add]; exact Submodule.add_mem _ hu hw
    | smul r u _ hu => rw [Pi.single_smul]; exact Submodule.smul_mem _ r hu

  obtain ⟨γ, γ', hγγ', hγ'γ, hmem⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_matrix_forall_mem_iff_forall_mulVec_mem q hH O hO M hfg hspan hM

  refine ⟨γ, γ', hγγ', hγ'γ, fun m hm i l => ?_⟩
  rw [mul_mul_apply_eq_mulVec]
  have hcol : γ.mulVec (Pi.single l 1) ∈ M := by
    rw [hmem, Matrix.mulVec_mulVec, hγ'γ, Matrix.one_mulVec]
    intro i
    by_cases hil : i = l
    · subst hil; rw [Pi.single_eq_same]; exact hO1.one_mem
    · rw [Pi.single_eq_of_ne hil]; exact O.zero_mem
  exact (hmem _).1 (hML _ hcol m hm) i

end S_QuaternionAlgebra_exists_mul_mul_eq_one_and_forall_apply_mem_of_algHom_matrix_injective_of_isOrder_of_isMaximalOrder
end P2MW
export P2MW.S_QuaternionAlgebra_exists_mul_mul_eq_one_and_forall_apply_mem_of_algHom_matrix_injective_of_isOrder_of_isMaximalOrder (solution)
