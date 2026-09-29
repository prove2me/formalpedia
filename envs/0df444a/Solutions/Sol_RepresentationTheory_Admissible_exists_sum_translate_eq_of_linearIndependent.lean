-- Prove2me | solution 1 for RepresentationTheory.Admissible.exists_sum_translate_eq_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/53106567-4b4f-533f-bad7-7ec75560551a

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Definitions.Def_RepTheory_SmoothAdmissibleSchurCommutant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RepresentationTheory_Admissible_exists_sum_translate_eq_of_linearIndependent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace GamDens

open FLT.SmoothAdmissibleSchurCommutant

variable {G : Type} [Group G]

def rightRep (V : Submodule ℂ (G → ℂ)) (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V) :
    Representation ℂ G V where
  toFun h :=
    { toFun := fun W => ⟨fun g => (W : G → ℂ) (g * h), hstab W W.2 h⟩
      map_add' := fun W₁ W₂ => by ext g; rfl
      map_smul' := fun c W => by ext g; rfl }
  map_one' := by
    refine LinearMap.ext fun W => Subtype.ext (funext fun g => ?_)
    show (W : G → ℂ) (g * 1) = (W : G → ℂ) g
    rw [mul_one]
  map_mul' h₁ h₂ := by
    refine LinearMap.ext fun W => Subtype.ext (funext fun g => ?_)
    show (W : G → ℂ) (g * (h₁ * h₂)) = (W : G → ℂ) (g * h₁ * h₂)
    rw [mul_assoc]

theorem rightRep_apply (V : Submodule ℂ (G → ℂ)) (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V)
    (h : G) (W : V) (g : G) : ((rightRep V hstab h W : V) : G → ℂ) g = (W : G → ℂ) (g * h) := rfl

end GamDens

open GamDens FLT.SmoothAdmissibleSchurCommutant in

theorem solution
    (G : Type) [Group G] [TopologicalSpace G]
    (V : Submodule ℂ (G → ℂ))
    (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V)
    (hirr : ∀ W₀ ∈ V, W₀ ≠ 0 → ∀ W ∈ V,
      W ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => W₀ (g * h)))
    (hadm : ∀ U : Subgroup G, IsOpen (U : Set G) →
      ∃ B : Finset (G → ℂ), ∀ W ∈ V, (∀ k ∈ U, ∀ g : G, W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (G → ℂ)))
    (hsm : ∀ W ∈ V, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, W (g * k) = W g)
    (n : ℕ) (u : Fin n → G → ℂ) (hu : ∀ i, u i ∈ V) (hind : LinearIndependent ℂ u)
    (v : Fin n → G → ℂ) (hv : ∀ i, v i ∈ V) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (x : Fin m → G),
      ∀ i : Fin n, (fun g : G => ∑ j, c j * u i (g * x j)) = v i := by
  classical

  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨0, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i⟩

  have hu0 : u ⟨0, hn⟩ ≠ 0 := hind.ne_zero _
  obtain ⟨π, hπ⟩ : ∃ π : Representation ℂ G V, π = rightRep V hstab := ⟨_, rfl⟩
  have hπap : ∀ (h : G) (W : V) (g : G), ((π h W : V) : G → ℂ) g = (W : G → ℂ) (g * h) := fun h W g => by
    rw [hπ]; rfl

  have hirr' : IsIrreducibleRep π := by
    refine ⟨⟨⟨u ⟨0, hn⟩, hu _⟩, fun h => hu0 (congrArg Subtype.val h)⟩, fun W hW => ?_⟩
    by_cases hbot : W = ⊥
    · exact Or.inl hbot
    · right
      obtain ⟨w₀, hw₀W, hw₀ne⟩ := (Submodule.ne_bot_iff W).1 hbot
      refine eq_top_iff.2 fun x _ => ?_
      have hx := hirr w₀ w₀.2 (fun h => hw₀ne (Subtype.ext h)) x x.2

      have hle : Submodule.span ℂ (Set.range fun h : G => fun g : G => (w₀ : G → ℂ) (g * h)) ≤ W.map V.subtype := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨h, rfl⟩
        exact ⟨π h w₀, hW h w₀ hw₀W, funext fun g => hπap h w₀ g⟩
      obtain ⟨y, hyW, hyx⟩ := hle hx
      have : y = x := Subtype.ext hyx
      exact this ▸ hyW

  obtain ⟨U, hUo, hUfix⟩ := hsm (u ⟨0, hn⟩) (hu _)
  obtain ⟨B, hB⟩ := hadm U hUo
  have hfd : FiniteDimensional ℂ (fixedVectors π U) := by
    have hle : (fixedVectors π U).map V.subtype ≤ Submodule.span ℂ (B : Set (G → ℂ)) := by
      rintro _ ⟨W, hW, rfl⟩
      refine hB W W.2 fun k hk g => ?_
      have h : ((π k W : V) : G → ℂ) g = (W : G → ℂ) g :=
        congrArg (fun z : V => (z : G → ℂ) g) ((mem_fixedVectors π).1 hW k hk)
      rw [hπap] at h
      exact h
    haveI : FiniteDimensional ℂ (Submodule.span ℂ (B : Set (G → ℂ))) := FiniteDimensional.span_finset ℂ B
    haveI : FiniteDimensional ℂ ((fixedVectors π U).map V.subtype) := Submodule.finiteDimensional_of_le hle
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective V.subtype V.injective_subtype (fixedVectors π U)).symm
  have hfix0 : ∀ k ∈ U, π k ⟨u ⟨0, hn⟩, hu _⟩ = ⟨u ⟨0, hn⟩, hu _⟩ :=
    fun k hk => Subtype.ext (funext fun g => by rw [hπap]; exact hUfix k hk g)
  have hne0 : (⟨u ⟨0, hn⟩, hu _⟩ : V) ≠ 0 := fun h => hu0 (congrArg Subtype.val h)

  have schur : ∀ T : Module.End ℂ V, (∀ g : G, π g * T = T * π g) → ∃ c : ℂ, ∀ x : V, T x = c • x :=
    fun T hT => exists_forall_eq_smul_of_commute_of_fixed π hirr' hT hne0 hfix0 hfd

  let M := π.asModule
  let e : π.asModule ≃ₗ[ℂ] V := π.asModuleEquiv
  have hsmul : ∀ (g : G) (x : π.asModule), e (MonoidAlgebra.of ℂ G g • x) = π g (e x) := by
    intro g x
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]

  haveI : IsSimpleModule (MonoidAlgebra ℂ G) π.asModule := by
    refine { toNontrivial := ?_, eq_bot_or_eq_top := fun N => ?_ }
    · refine ⟨⟨⊥, ⊤, fun h => ?_⟩⟩
      have : (e.symm ⟨u ⟨0, hn⟩, hu _⟩ : π.asModule) ∈ (⊥ : Submodule (MonoidAlgebra ℂ G) π.asModule) := by
        rw [h]; exact Submodule.mem_top
      rw [Submodule.mem_bot] at this
      exact hne0 (by simpa using congrArg e this)
    ·
      let N' : Submodule ℂ V := (N.restrictScalars ℂ).map (e : π.asModule →ₗ[ℂ] V)
      have hN' : ∀ (g : G) (y : V), y ∈ N' → π g y ∈ N' := by
        rintro g _ ⟨x, hx, rfl⟩
        exact ⟨MonoidAlgebra.of ℂ G g • x, N.smul_mem _ hx, hsmul g x⟩
      rcases hirr'.2 N' hN' with h | h
      · left
        refine eq_bot_iff.2 fun x hx => ?_
        have : e x ∈ N' := ⟨x, hx, rfl⟩
        rw [h, Submodule.mem_bot] at this
        rw [Submodule.mem_bot]
        exact e.injective (by rw [this, map_zero])
      · right
        refine eq_top_iff.2 fun x _ => ?_
        have : e x ∈ N' := by rw [h]; exact Submodule.mem_top
        obtain ⟨y, hy, hyx⟩ := this
        exact (e.injective hyx) ▸ hy

  let u' : Fin n → V := fun i => ⟨u i, hu i⟩
  have hind' : LinearIndependent ℂ u' := LinearIndependent.of_comp V.subtype (by exact hind)
  obtain ⟨F, hF⟩ : ∃ F : V →ₗ[ℂ] V, ∀ i, F (u' i) = ⟨v i, hv i⟩ := by
    let S : Submodule ℂ V := Submodule.span ℂ (Set.range u')
    let bS := Module.Basis.span hind'
    let F₀ : S →ₗ[ℂ] V := bS.constr ℂ fun i => (⟨v i, hv i⟩ : V)
    obtain ⟨F, hF⟩ := LinearMap.exists_extend F₀
    refine ⟨F, fun i => ?_⟩
    have h1 : F (S.subtype (bS i)) = F₀ (bS i) := by rw [← hF]; rfl
    have h2 : (S.subtype (bS i) : V) = u' i := Module.Basis.coe_span_apply hind' i
    rw [← h2, h1]
    exact Module.Basis.constr_basis bS ℂ (fun i => (⟨v i, hv i⟩ : V)) i

  let f : Module.End (Module.End (MonoidAlgebra ℂ G) π.asModule) π.asModule :=
    { toFun := fun x => e.symm (F (e x))
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun T x => by

        have hcomm : ∀ g : G, π g * ((e : π.asModule →ₗ[ℂ] V).comp ((T.restrictScalars ℂ).comp (e.symm : V →ₗ[ℂ] π.asModule))) =
            ((e : π.asModule →ₗ[ℂ] V).comp ((T.restrictScalars ℂ).comp (e.symm : V →ₗ[ℂ] π.asModule))) * π g := by
          intro g
          refine LinearMap.ext fun y => ?_
          show π g (e (T (e.symm y))) = e (T (e.symm (π g y)))
          rw [Representation.asModuleEquiv_symm_map_rho, map_smul, hsmul]
        obtain ⟨c, hc⟩ := schur _ hcomm
        have hT : ∀ y : π.asModule, T y = c • y := by
          intro y
          have h := hc (e y)
          simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
            LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h
          apply e.injective
          rw [h, LinearEquiv.map_smul]
        show e.symm (F (e (T x))) = T (e.symm (F (e x)))
        rw [hT, hT]
        simp only [map_smul, LinearEquiv.map_smul] }

  obtain ⟨r, hr⟩ := jacobson_density f (Finset.univ.image fun i => e.symm (u' i))

  refine ⟨r.coeff.support.card, fun j => r.coeff (r.coeff.support.equivFin.symm j), fun j => (r.coeff.support.equivFin.symm j : G), fun i => ?_⟩
  have hi := hr (e.symm (u' i)) (Finset.mem_image_of_mem _ (Finset.mem_univ i))

  have hfi : f (e.symm (u' i)) = e.symm ⟨v i, hv i⟩ := by
    show e.symm (F (e (e.symm (u' i)))) = _
    rw [LinearEquiv.apply_symm_apply, hF]
  rw [hfi] at hi
  have hvi : (⟨v i, hv i⟩ : V) = e (r • e.symm (u' i)) := by rw [← hi, LinearEquiv.apply_symm_apply]
  rw [Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply] at hvi

  have hexp : (π.asAlgebraHom r) (u' i) = ∑ g ∈ r.coeff.support, r.coeff g • π g (u' i) := by
    conv_lhs => rw [← MonoidAlgebra.sum_coeff_single r]
    rw [map_finsuppSum]
    simp only [Finsupp.sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Representation.asAlgebraHom_single, LinearMap.smul_apply]
  have hval := congrArg Subtype.val hvi
  rw [hexp] at hval
  funext g
  have hg := congrFun hval g
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hg
  rw [hg, ← Finset.sum_coe_sort r.coeff.support]
  exact Fintype.sum_equiv r.coeff.support.equivFin.symm _ _ fun j => by simp only [hπap]; rfl

end S_RepresentationTheory_Admissible_exists_sum_translate_eq_of_linearIndependent
end P2MW
export P2MW.S_RepresentationTheory_Admissible_exists_sum_translate_eq_of_linearIndependent (solution)
