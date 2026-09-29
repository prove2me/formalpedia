-- Prove2me | solution 1 for TwistedUnipotentTerm.semiLocalCharacter_congr_eq_of_forall_unitsAct_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/faea0bd0-76d3-5b45-98ec-ce542a295f8a

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Theorems.Thm_AutomorphicForm_semiLocalEval_act_eq_congr_and_semiLocalIdele_unitsAct_and_semiLocalComponent_sigmaAdelicAct
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwistedUnipotentTerm_semiLocalCharacter_congr_eq_of_forall_unitsAct_eq

set_option autoImplicit false

open IsDedekindDomain NumberField
open NumberField.AdelicLevel TensorProduct AutomorphicForm
open scoped TensorProduct

noncomputable section

namespace TwistedUnipotentTermK7c

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev SL (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Type :=
  L ⊗[K] v.adicCompletion K

scoped instance instFiniteExtension (v : HeightOneSpectrum (𝓞 K)) : Finite (v.Extension (𝓞 L)) :=
  HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v

noncomputable scoped instance instFintypeExtension (v : HeightOneSpectrum (𝓞 K)) : Fintype (v.Extension (𝓞 L)) :=
  Fintype.ofFinite _

variable (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)

def ξfun (t : (AdeleRing (𝓞 L) L)ˣ) : ℂ := ((ξL ⟨t, Subgroup.mem_top t⟩ : ℂˣ) : ℂ)

def ξhom : (AdeleRing (𝓞 L) L)ˣ →* ℂ where
  toFun := ξfun ξL
  map_one' := by
    simp only [ξfun]
    have : (⟨(1 : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ)) = 1 := rfl
    rw [this, map_one, Units.val_one]
  map_mul' s t := by
    simp only [ξfun]
    have : (⟨s * t, Subgroup.mem_top _⟩ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ)) =
        ⟨s, Subgroup.mem_top s⟩ * ⟨t, Subgroup.mem_top t⟩ := rfl
    rw [this, map_mul, Units.val_mul]

theorem ξhom_apply (t : (AdeleRing (𝓞 L) L)ˣ) : ξhom ξL t = ((ξL ⟨t, Subgroup.mem_top t⟩ : ℂˣ) : ℂ) := rfl

variable (K L)
variable (v : HeightOneSpectrum (𝓞 K))

def idele (ζ : (SL K L v)ˣ) : (AdeleRing (𝓞 L) L)ˣ :=
  ∏ w : v.Extension (𝓞 L),
    Matrix.GeneralLinearGroup.det
      (heckeGenAt (𝓞 L) L w.1 (TwistedUnipotentTerm.semiLocalUnitComponent K L v w ζ))

theorem semiLocalCharacter_eq (ζ : (SL K L v)ˣ) :
    TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ = ξhom ξL (idele K L v ζ) := by
  unfold TwistedUnipotentTerm.semiLocalCharacter idele
  rw [finprod_eq_prod_of_fintype, map_prod]
  rfl

omit [NumberField K] in
theorem det_diagOne {A : Type*} [CommRing A] (a : Aˣ) :
    Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det (Matrix.diagonal ![(a : A), 1]) = a
  rw [Matrix.det_diagonal]
  simp

theorem val_det_heckeGenAt (w : HeightOneSpectrum (𝓞 L)) (t : (w.adicCompletion L)ˣ) :
    ((Matrix.GeneralLinearGroup.det (heckeGenAt (𝓞 L) L w t) : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) =
      finIncl (𝓞 L) L (localUnit (𝓞 L) L w t : (FiniteAdeleRing (𝓞 L) L)ˣ) := by
  unfold heckeGenAt
  rw [MonoidHom.comp_apply, det_diagOne]
  rfl

theorem val_det_heckeGenAt_fst (w : HeightOneSpectrum (𝓞 L)) (t : (w.adicCompletion L)ˣ) :
    ((Matrix.GeneralLinearGroup.det (heckeGenAt (𝓞 L) L w t) : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 = 1 := by
  rw [val_det_heckeGenAt]; rfl

theorem val_det_heckeGenAt_snd (w : HeightOneSpectrum (𝓞 L)) (t : (w.adicCompletion L)ˣ) :
    ((Matrix.GeneralLinearGroup.det (heckeGenAt (𝓞 L) L w t) : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 =
      (localUnit (𝓞 L) L w t : (FiniteAdeleRing (𝓞 L) L)ˣ) := by
  rw [val_det_heckeGenAt]; rfl

omit [NumberField K] in
theorem fst_prod {ι : Type*} (s : Finset ι) (f : ι → AdeleRing (𝓞 L) L) :
    (∏ i ∈ s, f i).1 = ∏ i ∈ s, (f i).1 :=
  map_prod (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) f s

omit [NumberField K] in
theorem snd_prod {ι : Type*} (s : Finset ι) (f : ι → AdeleRing (𝓞 L) L) :
    (∏ i ∈ s, f i).2 = ∏ i ∈ s, (f i).2 :=
  map_prod (RingHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) f s

theorem val_idele_fst (ζ : (SL K L v)ˣ) : ((idele K L v ζ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 = 1 := by
  unfold idele
  rw [Units.coe_prod, fst_prod]
  exact Finset.prod_eq_one fun w _ => val_det_heckeGenAt_fst L _ _

theorem val_idele_snd (ζ : (SL K L v)ˣ) :
    ((idele K L v ζ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 =
      ∏ w : v.Extension (𝓞 L),
        ((localUnit (𝓞 L) L w.1 (TwistedUnipotentTerm.semiLocalUnitComponent K L v w ζ) :
          (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) := by
  unfold idele
  rw [Units.coe_prod, snd_prod]
  exact Finset.prod_congr rfl fun w _ => val_det_heckeGenAt_snd L _ _

theorem semiLocalEval_apply (v' : HeightOneSpectrum (𝓞 K)) (x : FiniteAdeleRing (𝓞 L) L) :
    semiLocalEval K L v' x =
      (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v').symm (fun w => x w.1) := by
  simp only [AutomorphicForm.semiLocalEval, RingHom.coe_comp, Function.comp_apply]
  rfl

theorem baseChangeAlgEquiv_semiLocalEval (v' : HeightOneSpectrum (𝓞 K)) (x : FiniteAdeleRing (𝓞 L) L) :
    HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v' (semiLocalEval K L v' x) =
      fun w : v'.Extension (𝓞 L) => x w.1 := by
  rw [semiLocalEval_apply, AlgEquiv.apply_symm_apply]

theorem eq_of_forall_semiLocalEval_eq {x y : FiniteAdeleRing (𝓞 L) L}
    (h : ∀ v' : HeightOneSpectrum (𝓞 K), semiLocalEval K L v' x = semiLocalEval K L v' y) : x = y := by
  refine FiniteAdeleRing.ext L fun w₀ => ?_
  have h1 := baseChangeAlgEquiv_semiLocalEval K L (w₀.under (𝓞 K)) x
  have h2 := baseChangeAlgEquiv_semiLocalEval K L (w₀.under (𝓞 K)) y
  rw [h (w₀.under (𝓞 K)), h2] at h1
  exact (congrFun h1 ⟨w₀, rfl⟩).symm

theorem localUnit_apply_of_under_ne {v' : HeightOneSpectrum (𝓞 K)} (hv : v' ≠ v) (w : v.Extension (𝓞 L))
    (w' : v'.Extension (𝓞 L)) (t : (w.1.adicCompletion L)ˣ) :
    ((localUnit (𝓞 L) L w.1 t : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) w'.1 = 1 := by
  refine localUnit_apply_of_ne (𝓞 L) L w.1 t fun h => hv ?_
  rw [← w'.2, ← w.2, h]

theorem semiLocalEval_localUnit_of_ne {v' : HeightOneSpectrum (𝓞 K)} (hv : v' ≠ v) (w : v.Extension (𝓞 L))
    (t : (w.1.adicCompletion L)ˣ) :
    semiLocalEval K L v' ((localUnit (𝓞 L) L w.1 t : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) = 1 := by
  rw [semiLocalEval_apply]
  have : (fun w' : v'.Extension (𝓞 L) =>
      ((localUnit (𝓞 L) L w.1 t : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) w'.1) = 1 := by
    funext w'
    exact localUnit_apply_of_under_ne K L v hv w w' t
  rw [this, map_one]

open scoped Classical in
theorem localUnit_apply_extension (w w' : v.Extension (𝓞 L)) (t : (w.1.adicCompletion L)ˣ) :
    ((localUnit (𝓞 L) L w.1 t : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) w'.1 =
      (Pi.mulSingle w (t : w.1.adicCompletion L) : ∀ w'' : v.Extension (𝓞 L), w''.1.adicCompletion L) w' := by
  by_cases h : w' = w
  · subst h
    rw [Pi.mulSingle_eq_same]
    exact localUnit_apply_self (𝓞 L) L w'.1 t
  · rw [Pi.mulSingle_eq_of_ne h]
    exact localUnit_apply_of_ne (𝓞 L) L w.1 t fun h' => h (Subtype.ext h')

open scoped Classical in
theorem semiLocalEval_localUnit_self (w : v.Extension (𝓞 L)) (t : (w.1.adicCompletion L)ˣ) :
    semiLocalEval K L v ((localUnit (𝓞 L) L w.1 t : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) =
      (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
        (Pi.mulSingle w (t : w.1.adicCompletion L)) := by
  rw [semiLocalEval_apply]
  congr 1
  funext w'
  exact localUnit_apply_extension K L v w w' t

theorem semiLocalEval_idele_of_ne {v' : HeightOneSpectrum (𝓞 K)} (hv : v' ≠ v) (ζ : (SL K L v)ˣ) :
    semiLocalEval K L v' ((idele K L v ζ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 = 1 := by
  rw [val_idele_snd, map_prod]
  exact Finset.prod_eq_one fun w _ => semiLocalEval_localUnit_of_ne K L v hv w _

open scoped Classical in

theorem semiLocalEval_idele_self (ζ : (SL K L v)ˣ) :
    semiLocalEval K L v ((idele K L v ζ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 = ζ := by
  rw [val_idele_snd, map_prod]
  simp_rw [semiLocalEval_localUnit_self]
  rw [← map_prod, Finset.univ_prod_mulSingle]
  have : (fun w : v.Extension (𝓞 L) =>
      ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w ζ : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L)) =
      HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v (ζ : SL K L v) := by
    funext w
    rfl
  rw [this, AlgEquiv.symm_apply_apply]

variable [IsGalois K L]

theorem unitsAct_idele (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (ζ : (SL K L v)ˣ) :
    M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (idele K L v ζ) =
      idele K L v (Units.mapEquiv (Algebra.TensorProduct.congr σ
        (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv ζ) := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : D = M4aHerbrand.GenuineDescent.genuineDescentDatum K L := Subsingleton.elim _ _
  refine Units.ext (Prod.ext ?_ ?_)
  ·
    rw [val_idele_fst]
    show ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ
      ((idele K L v ζ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)).1 = 1
    funext w'
    rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply K L σ _ (smul_inv_smul σ w'),
      val_idele_fst]
    exact map_one _
  ·
    refine eq_of_forall_semiLocalEval_eq K L fun v' => ?_
    have key := (AutomorphicForm.semiLocalEval_act_eq_congr_and_semiLocalIdele_unitsAct_and_semiLocalComponent_sigmaAdelicAct
      K L (M4aHerbrand.GenuineDescent.genuineDescentDatum K L) σ v').1
      ((idele K L v ζ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)
    show semiLocalEval K L v' ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ
      ((idele K L v ζ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)).2 = _
    rw [key]
    by_cases hv : v' = v
    · subst hv
      rw [semiLocalEval_idele_self, semiLocalEval_idele_self]
      rfl
    · rw [semiLocalEval_idele_of_ne K L v hv, semiLocalEval_idele_of_ne K L v hv, map_one]

end TwistedUnipotentTermK7c
p2m_reactivate "P2MW.S_TwistedUnipotentTerm_semiLocalCharacter_congr_eq_of_forall_unitsAct_eq.TwistedUnipotentTermK7c"

end
p2m_reactivate "P2MW.S_TwistedUnipotentTerm_semiLocalCharacter_congr_eq_of_forall_unitsAct_eq.TwistedUnipotentTermK7c"

open scoped TensorProduct TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξσ : ∀ z₀ : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨M4aHerbrand.IdeleGaloisDescent.unitsAct D σ z₀, Subgroup.mem_top _⟩ = ξL ⟨z₀, Subgroup.mem_top z₀⟩)
    (v : HeightOneSpectrum (𝓞 K)) (ζ : (L ⊗[K] v.adicCompletion K)ˣ) :
    TwistedUnipotentTerm.semiLocalCharacter K L ξL v
        (Units.mapEquiv (Algebra.TensorProduct.congr σ
          (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv ζ) =
      TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ := by
  rw [TwistedUnipotentTermK7c.semiLocalCharacter_eq, TwistedUnipotentTermK7c.semiLocalCharacter_eq,
    ← TwistedUnipotentTermK7c.unitsAct_idele K L v D σ ζ, TwistedUnipotentTermK7c.ξhom_apply,
    TwistedUnipotentTermK7c.ξhom_apply, hξσ]

end S_TwistedUnipotentTerm_semiLocalCharacter_congr_eq_of_forall_unitsAct_eq
end P2MW
export P2MW.S_TwistedUnipotentTerm_semiLocalCharacter_congr_eq_of_forall_unitsAct_eq (solution)
