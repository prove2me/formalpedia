-- Prove2me | solution 1 for Rep.forall_eq_zero_of_sum_mul_trace_eq_zero_of_isIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ec352ed9-0336-5cf3-9fad-804112df01ee

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_forall_eq_zero_of_sum_mul_trace_eq_zero_of_isIrreducible

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module"
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace TRF

variable {k : Type} [Field k] {G : Type} [Group G]

section one_irreducible

variable [Finite k] (S : Rep.{0} k G) [FiniteDimensional k S]

scoped instance moduleFinite_end :
    Module.Finite k (Module.End (MonoidAlgebra k G) S.ρ.asModule) :=
  Module.Finite.of_injective
    (LinearMap.restrictScalarsₗ k (MonoidAlgebra k G) S.ρ.asModule S.ρ.asModule k)
    (LinearMap.restrictScalars_injective k)

scoped instance finite_end : Finite (Module.End (MonoidAlgebra k G) S.ρ.asModule) :=
  Module.finite_of_finite k

scoped instance moduleFinite_over_end :
    Module.Finite (Module.End (MonoidAlgebra k G) S.ρ.asModule) S.ρ.asModule :=
  Module.Finite.of_restrictScalars_finite k _ _

theorem exists_trace_asAlgebraHom_ne_zero (hS : S.ρ.IsIrreducible) :
    ∃ b : MonoidAlgebra k G, LinearMap.trace k S (S.ρ.asAlgebraHom b) ≠ 0 := by
  haveI := hS

  let V := S.ρ.asModule
  let D := Module.End (MonoidAlgebra k G) V
  haveI : IsSimpleModule (MonoidAlgebra k G) V := inferInstance
  letI : Field D := inferInstance
  haveI : Algebra.IsSeparable k D := inferInstance

  obtain ⟨d, hd⟩ := Algebra.trace_surjective k D 1

  haveI : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra k G) V
  obtain ⟨w, hw⟩ := exists_ne (0 : V)
  let L : Submodule D V := D ∙ w
  obtain ⟨W, hLW⟩ := L.exists_isCompl
  let π : V →ₗ[D] L := L.projectionOnto W hLW
  have hπ : ∀ x : L, π x = x := fun x => Submodule.projectionOnto_apply_left hLW x

  let f₀ : V →ₗ[D] V := L.subtype ∘ₗ (d • π)

  obtain ⟨b, hb⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := MonoidAlgebra k G) (M := V) f₀
  refine ⟨b, ?_⟩
  have hbv : ∀ v : V, S.ρ.asAlgebraHom b v = f₀ v := fun v => by
    have := LinearMap.congr_fun hb v
    exact this

  let e : D ≃ₗ[D] L := LinearEquiv.toSpanNonzeroSingleton D V w hw
  have he : ∀ t : D, ((e t : L) : V) = t • w := fun t => rfl
  haveI : Module.Finite k L := Module.Finite.of_injective (L.subtype.restrictScalars k) L.injective_subtype
  have hres : (S.ρ.asAlgebraHom b : S →ₗ[k] S) = (L.subtype.restrictScalars k) ∘ₗ ((d • π).restrictScalars k) := by
    apply LinearMap.ext
    intro v
    exact hbv v

  have hcomm : ((d • π).restrictScalars k) ∘ₗ (L.subtype.restrictScalars k)
      = (e.restrictScalars k).conj (Algebra.lmul k D d) := by
    rw [LinearEquiv.conj_apply, LinearEquiv.eq_comp_toLinearMap_symm]
    apply LinearMap.ext
    intro y
    show (d • π) ((e y : L) : V) = e (d * y)
    rw [LinearMap.smul_apply, hπ]
    apply Subtype.ext
    show ((d • e y : L) : V) = ((e (d * y) : L) : V)
    rw [Submodule.coe_smul, he, he, mul_smul]
  rw [hres, LinearMap.trace_comp_comm', hcomm, LinearMap.trace_conj', ← Algebra.trace_apply, hd]
  exact one_ne_zero

end one_irreducible

section family

variable {r : ℕ} (S : Fin r → Rep.{0} k G) [∀ i, FiniteDimensional k (S i)]

omit [∀ i, FiniteDimensional k (S i)] in

theorem linearMap_eq_zero_of_ne (hS : ∀ i, (S i).ρ.IsIrreducible) (hij : ∀ i j, Nonempty (S i ≅ S j) → i = j)
    {i j : Fin r} (h : i ≠ j) (φ : (S i).ρ.asModule →ₗ[MonoidAlgebra k G] (S j).ρ.asModule) : φ = 0 := by
  haveI := hS i
  haveI := hS j
  let f : (S i).ρ.IntertwiningMap (S j).ρ :=
    (Representation.IntertwiningMap.equivLinearMapAsModule (S i).ρ (S j).ρ).symm φ
  rcases Representation.IsIrreducible.bijective_or_eq_zero f with hf | hf
  · exact absurd (hij i j ⟨Rep.mkIso (f.ofBijective hf)⟩) h
  · have : φ = Representation.IntertwiningMap.equivLinearMapAsModule (S i).ρ (S j).ρ f :=
      ((Representation.IntertwiningMap.equivLinearMapAsModule (S i).ρ (S j).ρ).apply_symm_apply φ).symm
    rw [this, hf, map_zero]

omit [∀ i, FiniteDimensional k (S i)] in

theorem end_apply_single_apply_eq_zero (hS : ∀ i, (S i).ρ.IsIrreducible)
    (hij : ∀ i j, Nonempty (S i ≅ S j) → i = j)
    (ε : Module.End (MonoidAlgebra k G) (Π i, (S i).ρ.asModule)) {i j : Fin r} (h : i ≠ j)
    (v : (S i).ρ.asModule) : ε (Pi.single i v) j = 0 := by
  let φ : (S i).ρ.asModule →ₗ[MonoidAlgebra k G] (S j).ρ.asModule :=
    (LinearMap.proj j) ∘ₗ ε ∘ₗ (LinearMap.single (MonoidAlgebra k G) (fun i => (S i).ρ.asModule) i)
  have hφ := linearMap_eq_zero_of_ne S hS hij h φ
  exact LinearMap.congr_fun hφ v

scoped instance moduleFinite_pi_over_end :
    Module.Finite (Module.End (MonoidAlgebra k G) (Π i, (S i).ρ.asModule)) (Π i, (S i).ρ.asModule) :=
  Module.Finite.of_restrictScalars_finite k _ _

theorem exists_smul_eq_self_and_smul_eq_zero (hS : ∀ i, (S i).ρ.IsIrreducible)
    (hij : ∀ i j, Nonempty (S i ≅ S j) → i = j) (i₀ : Fin r) :
    ∃ a : MonoidAlgebra k G, (∀ v : (S i₀).ρ.asModule, a • v = v) ∧
      ∀ j, j ≠ i₀ → ∀ v : (S j).ρ.asModule, a • v = 0 := by
  haveI : ∀ i, IsSimpleModule (MonoidAlgebra k G) (S i).ρ.asModule := fun i => by
    haveI := hS i; infer_instance
  let M := Π i, (S i).ρ.asModule
  let E := Module.End (MonoidAlgebra k G) M

  have hdiag : ∀ (ε : E) (m : M), ε (Pi.single i₀ (m i₀)) = Pi.single i₀ (ε m i₀) := by
    intro ε m
    funext j
    by_cases hj : j = i₀
    · subst hj
      rw [Pi.single_eq_same]
      conv_rhs => rw [← Finset.univ_sum_single m]
      rw [map_sum, Finset.sum_apply, Finset.sum_eq_single j]
      · intro i _ hi
        exact end_apply_single_apply_eq_zero S hS hij ε hi (m i)
      · intro h; exact absurd (Finset.mem_univ j) h
    · rw [Pi.single_eq_of_ne hj]
      exact end_apply_single_apply_eq_zero S hS hij ε (Ne.symm hj) (m i₀)
  let F : M →ₗ[E] M :=
    { toFun := fun m => Pi.single i₀ (m i₀)
      map_add' := fun m m' => by
        show (Pi.single i₀ ((m + m') i₀) : M) = (Pi.single i₀ (m i₀) : M) + (Pi.single i₀ (m' i₀) : M)
        rw [Pi.add_apply, Pi.single_add]
      map_smul' := fun ε m => by
        show Pi.single i₀ (ε m i₀) = ε (Pi.single i₀ (m i₀))
        rw [hdiag] }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := MonoidAlgebra k G) (M := M) F
  have ha' : ∀ m : M, a • m = Pi.single i₀ (m i₀) := fun m => LinearMap.congr_fun ha m
  refine ⟨a, fun v => ?_, fun j hj v => ?_⟩
  · have := congr_fun (ha' (Pi.single i₀ v)) i₀
    change a • (Pi.single i₀ v : M) i₀ = (Pi.single i₀ ((Pi.single i₀ v : M) i₀) : M) i₀ at this
    simpa using this
  · have := congr_fun (ha' (Pi.single j v)) j
    change a • (Pi.single j v : M) j = (Pi.single i₀ ((Pi.single j v : M) i₀) : M) j at this
    simpa [Pi.single_apply, hj, Ne.symm hj] using this

end family

theorem forall_eq_zero_of_sum_mul_trace_eq_zero_of_isIrreducible [Finite k]
    {r : ℕ} (S : Fin r → Rep.{0} k G) [∀ i, FiniteDimensional k (S i)]
    (hS : ∀ i, (S i).ρ.IsIrreducible) (hij : ∀ i j, Nonempty (S i ≅ S j) → i = j)
    (c : Fin r → k) (hc : ∀ g : G, ∑ i, c i * LinearMap.trace k (S i) ((S i).ρ g) = 0) :
    ∀ i, c i = 0 := by
  intro i₀

  have hc' : ∀ x : MonoidAlgebra k G, ∑ i, c i * LinearMap.trace k (S i) ((S i).ρ.asAlgebraHom x) = 0 := by
    intro x
    induction x using MonoidAlgebra.induction_on with
    | of g => simpa only [Representation.asAlgebraHom_of] using hc g
    | add x y hx hy => simp only [map_add, mul_add, Finset.sum_add_distrib, hx, hy, add_zero]
    | smul t x hx =>
      simp only [map_smul, smul_eq_mul] at hx ⊢
      calc ∑ i, c i * (t * LinearMap.trace k (S i) ((S i).ρ.asAlgebraHom x))
          = t * ∑ i, c i * LinearMap.trace k (S i) ((S i).ρ.asAlgebraHom x) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [hx, mul_zero]

  obtain ⟨a, ha1, ha0⟩ := exists_smul_eq_self_and_smul_eq_zero S hS hij i₀
  obtain ⟨b, hb⟩ := exists_trace_asAlgebraHom_ne_zero (S i₀) (hS i₀)
  have hz : ∀ i, i ≠ i₀ → (S i).ρ.asAlgebraHom (a * b) = 0 := by
    intro i hi
    rw [map_mul]
    apply LinearMap.ext
    intro v
    exact ha0 i hi _
  have he : (S i₀).ρ.asAlgebraHom (a * b) = (S i₀).ρ.asAlgebraHom b := by
    rw [map_mul]
    apply LinearMap.ext
    intro v
    exact ha1 _
  have key := hc' (a * b)
  rw [Finset.sum_eq_single i₀ (fun i _ hi => by rw [hz i hi, map_zero, mul_zero])
    (fun h => absurd (Finset.mem_univ i₀) h), he] at key
  exact (mul_eq_zero.1 key).resolve_right hb

end TRF
p2m_reactivate "P2MW.S_Rep_forall_eq_zero_of_sum_mul_trace_eq_zero_of_isIrreducible.TRF"

theorem solution
    {k : Type} [Field k] [Finite k] {G : Type} [Group G]
    {r : ℕ} (S : Fin r → Rep.{0} k G) [∀ i, FiniteDimensional k (S i)]
    (hS : ∀ i, (S i).ρ.IsIrreducible) (hij : ∀ i j, Nonempty (S i ≅ S j) → i = j)
    (c : Fin r → k) (hc : ∀ g : G, ∑ i, c i * LinearMap.trace k (S i) ((S i).ρ g) = 0) :
    ∀ i, c i = 0 :=
  TRF.forall_eq_zero_of_sum_mul_trace_eq_zero_of_isIrreducible S hS hij c hc

end S_Rep_forall_eq_zero_of_sum_mul_trace_eq_zero_of_isIrreducible
end P2MW
export P2MW.S_Rep_forall_eq_zero_of_sum_mul_trace_eq_zero_of_isIrreducible (solution)
