-- Prove2me | solution 1 for TwistedUnipotentTerm.continuous_semiLocalCharacter_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c59a0c12-5410-50ca-ae2e-eae632521fea

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwistedUnipotentTerm_continuous_semiLocalCharacter_of_continuous

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

namespace SlK7

open NumberField.AdelicLevel Topology Filter

section EmbUnit

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

omit [NumberField F] in
theorem cofinite_le_principal_compl_singleton :
    (cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ 𝓟 ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
  Filter.le_principal_iff.mpr (Set.finite_singleton v).compl_mem_cofinite

open scoped Classical in

noncomputable def finSinglePrincipal (c : v.adicCompletion F) :
    RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      (𝓟 ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F)))) :=
  ⟨Function.update (1 : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F) v c,
    Filter.eventually_principal.mpr fun w hw => by
      have hwv : w ≠ v := by simpa using hw
      show Function.update (1 : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F) v c w ∈ _
      rw [Function.update_of_ne hwv]
      exact one_mem _⟩

open scoped Classical in
theorem continuous_finSinglePrincipal : Continuous (finSinglePrincipal (F := F) v) := by
  refine RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr fun w => ?_
  show Continuous fun c : v.adicCompletion F =>
    Function.update (1 : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F) v c w
  by_cases hw : w = v
  · subst hw
    simp only [Function.update_self]
    exact continuous_id
  · simp only [Function.update_of_ne hw]
    exact continuous_const

open scoped Classical in
theorem localUnit_val_eq (t : (v.adicCompletion F)ˣ) :
    ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)
      = RestrictedProduct.inclusion (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
          (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
          (cofinite_le_principal_compl_singleton v) (finSinglePrincipal v (t : v.adicCompletion F)) :=
  RestrictedProduct.ext (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) fun _ => rfl

theorem continuous_localUnit_val :
    Continuous fun t : (v.adicCompletion F)ˣ =>
      ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) := by
  have h : (fun t : (v.adicCompletion F)ˣ =>
      ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
      = (RestrictedProduct.inclusion (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
          (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
          (cofinite_le_principal_compl_singleton v)) ∘ (finSinglePrincipal v) ∘ Units.val :=
    funext fun t => localUnit_val_eq v t
  rw [h]
  exact (RestrictedProduct.continuous_inclusion _).comp
    ((continuous_finSinglePrincipal v).comp Units.continuous_val)

theorem continuous_embUnit :
    Continuous fun t : (v.adicCompletion F)ˣ =>
      Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F) (localUnit (𝓞 F) F v t) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun t : (v.adicCompletion F)ˣ =>
      (((1 : InfiniteAdeleRing F), ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
        : AdeleRing (𝓞 F) F)
    exact continuous_const.prodMk (continuous_localUnit_val v)
  · have h : (fun t : (v.adicCompletion F)ˣ =>
        (((Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F) (localUnit (𝓞 F) F v t))⁻¹ :
          (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))
        = (fun t : (v.adicCompletion F)ˣ =>
            ((Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F) (localUnit (𝓞 F) F v t) :
              AdeleRing (𝓞 F) F))) ∘ (fun t => t⁻¹) := by
      funext t
      simp only [Function.comp_apply, map_inv]
    rw [h]
    refine Continuous.comp ?_ continuous_inv
    show Continuous fun t : (v.adicCompletion F)ˣ =>
      (((1 : InfiniteAdeleRing F), ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
        : AdeleRing (𝓞 F) F)
    exact continuous_const.prodMk (continuous_localUnit_val v)

theorem det_heckeGenAt (t : (v.adicCompletion F)ˣ) :
    Matrix.GeneralLinearGroup.det (heckeGenAt (𝓞 F) F v t) =
      Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F) (localUnit (𝓞 F) F v t) := by
  apply Units.ext
  change Matrix.det (Matrix.diagonal ![((Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F)
      (localUnit (𝓞 F) F v t) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 1]) = _
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp

end EmbUnit

section Component

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

theorem continuous_semiLocalUnitComponent :
    Continuous (TwistedUnipotentTerm.semiLocalUnitComponent K L v w) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI : IsTopologicalGroup (L ⊗[K] v.adicCompletion K)ˣ := inferInstance
  have hbc : Continuous (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v) :=
    (AutomorphicForm.semiLocalHomeomorph K L v).continuous.congr fun _ => rfl
  have h1 : Continuous fun ζ : (L ⊗[K] v.adicCompletion K)ˣ =>
      (TwistedUnipotentTerm.semiLocalUnitComponent K L v w ζ : w.1.adicCompletion L) := by
    have : (fun ζ : (L ⊗[K] v.adicCompletion K)ˣ =>
        (TwistedUnipotentTerm.semiLocalUnitComponent K L v w ζ : w.1.adicCompletion L)) =
        fun ζ : (L ⊗[K] v.adicCompletion K)ˣ =>
          HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v ζ.val w :=
      funext fun _ => rfl
    rw [this]
    exact (continuous_apply w).comp (hbc.comp Units.continuous_val)
  refine Units.continuous_iff.mpr ⟨h1, ?_⟩
  have : (fun ζ : (L ⊗[K] v.adicCompletion K)ˣ =>
      (((TwistedUnipotentTerm.semiLocalUnitComponent K L v w ζ)⁻¹ : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L)) =
      (fun ζ => (TwistedUnipotentTerm.semiLocalUnitComponent K L v w ζ : w.1.adicCompletion L)) ∘ fun ζ => ζ⁻¹ := by
    funext ζ
    simp only [Function.comp_apply, TwistedUnipotentTerm.semiLocalUnitComponent, map_inv]
  rw [this]
  exact h1.comp continuous_inv

end Component

end SlK7

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (TwistedUnipotentTerm.semiLocalCharacter K L ξL v) := by
  classical
  haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  haveI : Fintype (v.Extension (𝓞 L)) := Fintype.ofFinite _
  have e : TwistedUnipotentTerm.semiLocalCharacter K L ξL v = fun ζ =>
      ∏ w : v.Extension (𝓞 L),
        ((ξL ⟨Matrix.GeneralLinearGroup.det
            (NumberField.AdelicLevel.heckeGenAt (𝓞 L) L w.1 (TwistedUnipotentTerm.semiLocalUnitComponent K L v w ζ)),
          Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by
    funext ζ
    exact finprod_eq_prod_of_fintype _
  rw [e]
  refine continuous_finsetProd _ fun w _ => ?_
  have hg : Continuous fun ζ : (L ⊗[K] v.adicCompletion K)ˣ =>
      Matrix.GeneralLinearGroup.det
        (NumberField.AdelicLevel.heckeGenAt (𝓞 L) L w.1 (TwistedUnipotentTerm.semiLocalUnitComponent K L v w ζ)) := by
    simp only [SlK7.det_heckeGenAt]
    exact (SlK7.continuous_embUnit w.1).comp (SlK7.continuous_semiLocalUnitComponent K L v w)
  exact hξc.comp hg

end S_TwistedUnipotentTerm_continuous_semiLocalCharacter_of_continuous
end P2MW
export P2MW.S_TwistedUnipotentTerm_continuous_semiLocalCharacter_of_continuous (solution)
