-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.card_quot_span_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:34:49.301399+00:00
-- url     : https://prove2.me/submissions/ff80946e-94fb-427c-99fa-9fb40974a097

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Inertia
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain ValuativeRel
namespace ReciprocityTheory.Neutral.Cmp
theorem _root_.solution {R C ι : Type*} [CommRing R] [CommRing C] [Algebra R C] [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι R C) (r : R) :
    Nat.card (C ⧸ Ideal.span {algebraMap R C r}) = Nat.card (R ⧸ Ideal.span {r}) ^ Fintype.card ι := by
  let φ : C →ₗ[R] (ι → R ⧸ Ideal.span {r}) :=
    LinearMap.pi fun i => (Ideal.span {r}).mkQ ∘ₗ b.coord i
  have hφ : Function.Surjective φ := by
    intro y
    choose c hc using fun i => Ideal.Quotient.mk_surjective (y i)
    refine ⟨b.equivFun.symm c, ?_⟩
    funext i
    have h1 : b.repr (b.equivFun.symm c) i = c i := by
      rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
    simp only [φ, LinearMap.pi_apply, LinearMap.comp_apply, Module.Basis.coord_apply, Submodule.mkQ_apply, h1]
    exact hc i
  have hker : LinearMap.ker φ = (Ideal.span {algebraMap R C r}).restrictScalars R := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem, Ideal.mem_span_singleton']
    constructor
    · intro hx
      have : ∀ i, ∃ a, a * r = b.repr x i := fun i => by
        rw [← Ideal.mem_span_singleton', ← Ideal.Quotient.eq_zero_iff_mem]
        simpa [φ] using congrFun hx i
      choose a ha using this
      refine ⟨b.equivFun.symm a, ?_⟩
      apply b.repr.injective
      ext i
      rw [mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, ← b.equivFun_apply,
        LinearEquiv.apply_symm_apply, ← ha, smul_eq_mul, mul_comm]
    · rintro ⟨a, rfl⟩
      funext i
      rw [mul_comm, ← Algebra.smul_def]
      simp only [φ, LinearMap.pi_apply, LinearMap.comp_apply, Module.Basis.coord_apply, map_smul,
        Submodule.mkQ_apply, Pi.zero_apply]
      exact (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton.2 (dvd_mul_right _ _))
  have e := ((Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {algebraMap R C r})).symm.trans
    (Submodule.quotEquivOfEq _ _ hker.symm)).trans (φ.quotKerEquivOfSurjective hφ)
  rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]
end ReciprocityTheory.Neutral.Cmp
