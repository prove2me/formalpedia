-- Prove2me | solution 1 for TwoChartCech.exists_twoTermComplex_kerMapBaseChange_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/e161e9b7-6984-5138-b925-0ef6105081b9

import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.FinitePresentation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwoChartCech_exists_twoTermComplex_kerMapBaseChange_bijective

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

universe u

namespace TwoChartCech
p2m_export "TwoChartCech" "kerMapBaseChange"
p2m_open "TwoChartCech"

namespace Truncation

variable {R : Type u} [CommRing R]

theorem flat_prod {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Flat R M] [Module.Flat R N] : Module.Flat R (M × N) := by
  rw [Module.Flat.iff_rTensor_injectiveₛ]
  intro P _ _ Q
  have hM : Function.Injective (Q.subtype.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Q.subtype_injective
  have hN : Function.Injective (Q.subtype.rTensor N) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Q.subtype_injective
  have key : (TensorProduct.prodRight R R P M N).toLinearMap ∘ₗ (Q.subtype.rTensor (M × N))
      = ((Q.subtype.rTensor M).prodMap (Q.subtype.rTensor N)) ∘ₗ
          (TensorProduct.prodRight R R Q M N).toLinearMap := by
    apply TensorProduct.ext'
    intro a mn
    simp [TensorProduct.prodRight_tmul]
  intro x y hxy
  have hL : ((TensorProduct.prodRight R R P M N).toLinearMap ∘ₗ (Q.subtype.rTensor (M × N))) x
      = ((TensorProduct.prodRight R R P M N).toLinearMap ∘ₗ (Q.subtype.rTensor (M × N))) y := by
    simp only [LinearMap.comp_apply, hxy]
  rw [key] at hL
  simp only [LinearMap.comp_apply] at hL
  exact (TensorProduct.prodRight R R Q M N).injective ((hM.prodMap hN) hL)

theorem flat_ker_of_surjective {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Flat R M] [Module.Flat R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Module.Flat R (LinearMap.ker f) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro Q' Q _ _ _ _ i hi
  have hι_Q' : Function.Injective ((LinearMap.ker f).subtype.lTensor Q') :=
    LinearMap.lTensor_injective_of_exact_of_flat f hf _ (LinearMap.ker f).subtype_injective
      (LinearMap.exact_subtype_ker_map f) Q'
  have hi_M : Function.Injective (i.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap i hi
  intro x y hxy
  apply hι_Q'
  apply hi_M
  calc (i.rTensor M) (((LinearMap.ker f).subtype.lTensor Q') x)
      = ((LinearMap.ker f).subtype.lTensor Q) ((i.rTensor (LinearMap.ker f)) x) := by
        rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
            LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
    _ = ((LinearMap.ker f).subtype.lTensor Q) ((i.rTensor (LinearMap.ker f)) y) := by rw [hxy]
    _ = (i.rTensor M) (((LinearMap.ker f).subtype.lTensor Q') y) := by
        rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
            LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

variable {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
variable (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]

def rank : ℕ := (Module.Finite.exists_fin' R (C1 ⧸ LinearMap.range d)).choose

def quot : (Fin (rank d) → R) →ₗ[R] (C1 ⧸ LinearMap.range d) :=
  (Module.Finite.exists_fin' R (C1 ⧸ LinearMap.range d)).choose_spec.choose

theorem quot_surjective : Function.Surjective (quot d) :=
  (Module.Finite.exists_fin' R (C1 ⧸ LinearMap.range d)).choose_spec.choose_spec

def lift : (Fin (rank d) → R) →ₗ[R] C1 :=
  (Module.projective_lifting_property (LinearMap.range d).mkQ (quot d)
    (LinearMap.range d).mkQ_surjective).choose

theorem mkQ_comp_lift : (LinearMap.range d).mkQ ∘ₗ lift d = quot d :=
  (Module.projective_lifting_property (LinearMap.range d).mkQ (quot d)
    (LinearMap.range d).mkQ_surjective).choose_spec

theorem surjective_coprod : Function.Surjective (d.coprod (lift d)) := by
  intro y
  obtain ⟨v, hv⟩ := quot_surjective d ((LinearMap.range d).mkQ y)
  have hy : y - lift d v ∈ LinearMap.range d := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, ← hv,
      ← LinearMap.comp_apply, mkQ_comp_lift, sub_self]
  obtain ⟨x, hx⟩ := hy
  exact ⟨(x, v), by simp only [LinearMap.coprod_apply, hx, sub_add_cancel]⟩

abbrev K0 : Submodule R (C0 × (Fin (rank d) → R)) := LinearMap.ker (d.coprod (lift d))

def dK : K0 d →ₗ[R] (Fin (rank d) → R) := (LinearMap.snd R C0 (Fin (rank d) → R)).comp (K0 d).subtype

def iota0 : K0 d →ₗ[R] C0 := (LinearMap.fst R C0 (Fin (rank d) → R)).comp (K0 d).subtype

@[scoped simp] theorem dK_apply (z : K0 d) : dK d z = (z : C0 × (Fin (rank d) → R)).2 := rfl
@[scoped simp] theorem iota0_apply (z : K0 d) : iota0 d z = (z : C0 × (Fin (rank d) → R)).1 := rfl

theorem comm : d ∘ₗ iota0 d = (-(lift d)) ∘ₗ dK d := by
  ext ⟨⟨x, v⟩, hxv⟩
  have hxv' : d x + lift d v = 0 := by
    have := (LinearMap.mem_ker).mp hxv; simpa [LinearMap.coprod_apply] using this
  simp only [LinearMap.comp_apply, iota0_apply, dK_apply, LinearMap.neg_apply, eq_neg_iff_add_eq_zero]
  exact hxv'

def h0ToK0 : LinearMap.ker d →ₗ[R] K0 d :=
  LinearMap.codRestrict (K0 d)
    ((LinearMap.inl R C0 (Fin (rank d) → R)).comp (LinearMap.ker d).subtype)
    (fun ⟨x, hx⟩ => by
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.inl_apply,
        LinearMap.coprod_apply, map_zero, add_zero]
      exact hx)

def kerEquiv : LinearMap.ker (dK d) ≃ₗ[R] LinearMap.ker d := by
  refine LinearEquiv.ofLinear
    (LinearMap.codRestrict (LinearMap.ker d) ((iota0 d).comp (LinearMap.ker (dK d)).subtype) ?_)
    (LinearMap.codRestrict (LinearMap.ker (dK d)) (h0ToK0 d) (fun x => by
      simp only [LinearMap.mem_ker, dK_apply]; rfl))
    ?_ ?_
  · rintro ⟨⟨⟨x, v⟩, hxv⟩, hv⟩
    have hxv' : d x + lift d v = 0 := by
      have := (LinearMap.mem_ker).mp hxv; simpa [LinearMap.coprod_apply] using this
    have hv' : v = 0 := (LinearMap.mem_ker).mp hv
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype, iota0_apply]
    simpa [hv', map_zero, add_zero] using hxv'
  · apply LinearMap.ext; rintro ⟨x, hx⟩; rfl
  · apply LinearMap.ext; rintro ⟨⟨⟨x, v⟩, hxv⟩, hv⟩
    have hv' : v = 0 := (LinearMap.mem_ker).mp hv
    apply Subtype.ext; apply Subtype.ext
    show ((x, 0) : C0 × _) = (x, v)
    rw [hv']

theorem finite_K0 [IsNoetherianRing R] [Module.Finite R (LinearMap.ker d)] : Module.Finite R (K0 d) := by
  haveI hker : Module.Finite R (LinearMap.ker (dK d)) := Module.Finite.equiv (kerEquiv d).symm
  haveI hquot : Module.Finite R (K0 d ⧸ LinearMap.ker (dK d)) := by
    haveI : Module.Finite R (LinearMap.range (dK d)) := inferInstance
    exact Module.Finite.equiv (dK d).quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker (dK d))

theorem flat_K0 [Module.Flat R C0] [Module.Flat R C1] : Module.Flat R (K0 d) :=
  haveI : Module.Flat R (C0 × (Fin (rank d) → R)) := flat_prod
  flat_ker_of_surjective (d.coprod (lift d)) (surjective_coprod d)

theorem free_K0 [IsNoetherianRing R] [IsLocalRing R] [Module.Flat R C0] [Module.Flat R C1]
    [Module.Finite R (LinearMap.ker d)] : Module.Free R (K0 d) :=
  haveI := finite_K0 d; haveI := flat_K0 d
  Module.free_of_flat_of_isLocalRing

section BaseChange

variable (A : Type u) [CommRing A] [Algebra R A]

theorem d_baseChange_comp_iota0_baseChange :
    (d.baseChange A) ∘ₗ ((iota0 d).baseChange A)
      = -(((lift d).baseChange A) ∘ₗ ((dK d).baseChange A)) := by
  rw [← LinearMap.baseChange_comp, comm, LinearMap.baseChange_comp, LinearMap.baseChange_neg,
    LinearMap.neg_comp]

variable [Module.Flat R C1]

theorem subtype_baseChange_injective :
    Function.Injective ((K0 d).subtype.baseChange A) := by
  rw [LinearMap.baseChange_eq_ltensor]
  exact LinearMap.lTensor_injective_of_exact_of_flat (d.coprod (lift d))
    (surjective_coprod d) _ (K0 d).subtype_injective (LinearMap.exact_subtype_ker_map _) A

omit [Module.Flat R C1] in

theorem mem_range_subtype_baseChange (w : A ⊗[R] (C0 × (Fin (rank d) → R))) :
    ((d.coprod (lift d)).baseChange A) w = 0 ↔ ∃ z, ((K0 d).subtype.baseChange A) z = w := by
  have heqι : ⇑((K0 d).subtype.baseChange A) = ⇑((K0 d).subtype.lTensor A) :=
    LinearMap.baseChange_eq_ltensor _
  have heqc : ⇑((d.coprod (lift d)).baseChange A) = ⇑((d.coprod (lift d)).lTensor A) :=
    LinearMap.baseChange_eq_ltensor _
  rw [heqc]
  simp only [heqι]
  exact lTensor_exact A (LinearMap.exact_subtype_ker_map _) (surjective_coprod d) w

omit [Module.Flat R C1] in
theorem prodRight_apply_eq_baseChange {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (w : A ⊗[R] (M × N)) :
    (TensorProduct.prodRight R A A M N) w
      = (((LinearMap.fst R M N).baseChange A) w, ((LinearMap.snd R M N).baseChange A) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact rfl
  | tmul a x => simp [TensorProduct.prodRight_tmul]
  | add x y hx hy => simp only [map_add, hx, hy, Prod.mk_add_mk]

omit [Module.Flat R C1] in
theorem prodRight_subtype_baseChange (z : A ⊗[R] K0 d) :
    (TensorProduct.prodRight R A A C0 (Fin (rank d) → R)) (((K0 d).subtype.baseChange A) z)
      = (((iota0 d).baseChange A) z, ((dK d).baseChange A) z) := by
  rw [prodRight_apply_eq_baseChange]
  refine Prod.ext ?_ ?_
  · show ((LinearMap.fst R C0 (Fin (rank d) → R)).baseChange A) (((K0 d).subtype.baseChange A) z) = _
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]; rfl
  · show ((LinearMap.snd R C0 (Fin (rank d) → R)).baseChange A) (((K0 d).subtype.baseChange A) z) = _
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]; rfl

omit [Module.Flat R C1] in
theorem coprod_baseChange_apply (w : A ⊗[R] (C0 × (Fin (rank d) → R))) :
    ((d.coprod (lift d)).baseChange A) w
      = (d.baseChange A) ((TensorProduct.prodRight R A A C0 (Fin (rank d) → R)) w).1
        + ((lift d).baseChange A) ((TensorProduct.prodRight R A A C0 (Fin (rank d) → R)) w).2 := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, Prod.fst_zero, Prod.snd_zero, add_zero]
  | tmul a x => simp [TensorProduct.prodRight_tmul, LinearMap.coprod_apply, TensorProduct.tmul_add]
  | add x y hx hy => simp only [map_add, hx, hy, Prod.fst_add, Prod.snd_add]; abel

theorem kerMap_injective' [Module.Flat R C0] :
    Function.Injective (kerMapBaseChange (dK d) d (iota0 d) (-(lift d)) (comm d) A) := by
  rintro ⟨z, hz⟩ ⟨z', hz'⟩ hzz'
  apply Subtype.ext
  apply subtype_baseChange_injective d A
  apply (TensorProduct.prodRight R A A C0 (Fin (rank d) → R)).injective
  rw [prodRight_subtype_baseChange d A z, prodRight_subtype_baseChange d A z']
  have h1 : ((dK d).baseChange A) z = 0 := hz
  have h2 : ((dK d).baseChange A) z' = 0 := hz'
  rw [h1, h2]
  exact congrArg (·, (0 : A ⊗[R] (Fin (rank d) → R))) (congrArg Subtype.val hzz')

omit [Module.Flat R C1] in
theorem kerMap_surjective' [Module.Flat R C0] :
    Function.Surjective (kerMapBaseChange (dK d) d (iota0 d) (-(lift d)) (comm d) A) := by
  rintro ⟨w, hw⟩
  set w' : A ⊗[R] (C0 × (Fin (rank d) → R)) :=
    ((LinearMap.inl R C0 (Fin (rank d) → R)).baseChange A) w with hw'def
  have hker : ((d.coprod (lift d)).baseChange A) w' = 0 := by
    rw [hw'def, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.coprod_inl]
    exact hw
  obtain ⟨z, hz⟩ := (mem_range_subtype_baseChange d A w').mp hker
  have hpr : (TensorProduct.prodRight R A A C0 (Fin (rank d) → R)) w' = (w, 0) := by
    rw [prodRight_apply_eq_baseChange, hw'def, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp,
      LinearMap.fst_comp_inl R C0 (Fin (rank d) → R),
      LinearMap.snd_comp_inl R C0 (Fin (rank d) → R),
      LinearMap.baseChange_id, LinearMap.baseChange_zero, LinearMap.id_apply,
      LinearMap.zero_apply]
  have hpair : (((iota0 d).baseChange A) z, ((dK d).baseChange A) z) = (w, 0) := by
    rw [← prodRight_subtype_baseChange d A z, hz, hpr]
  refine ⟨⟨z, (Prod.ext_iff.mp hpair).2⟩, ?_⟩
  exact Subtype.ext (Prod.ext_iff.mp hpair).1

end BaseChange

section Free

variable [IsNoetherianRing R] [Module.Flat R C0] [Module.Flat R C1] [Module.Finite R (LinearMap.ker d)]

theorem projective_K0 : Module.Projective R (K0 d) := by
  haveI := finite_K0 d; haveI := flat_K0 d
  haveI : Module.FinitePresentation R (K0 d) := Module.finitePresentation_of_finite R _
  exact Module.Flat.projective_of_finitePresentation

def n : ℕ := by haveI := finite_K0 d; exact (Module.Finite.exists_fin' R (K0 d)).choose

def pi : (Fin (n d) → R) →ₗ[R] K0 d := by
  haveI := finite_K0 d; exact (Module.Finite.exists_fin' R (K0 d)).choose_spec.choose
omit [Module.Flat R C0] [Module.Flat R C1] in
theorem pi_surjective : Function.Surjective (pi d) := by
  haveI := finite_K0 d; exact (Module.Finite.exists_fin' R (K0 d)).choose_spec.choose_spec

def sec : K0 d →ₗ[R] (Fin (n d) → R) :=
  haveI := projective_K0 d
  (Module.projective_lifting_property (pi d) (LinearMap.id) (pi_surjective d)).choose
theorem pi_comp_sec : pi d ∘ₗ sec d = LinearMap.id :=
  haveI := projective_K0 d
  (Module.projective_lifting_property (pi d) (LinearMap.id) (pi_surjective d)).choose_spec
theorem pi_sec (k : K0 d) : pi d (sec d k) = k := by
  rw [← LinearMap.comp_apply, pi_comp_sec, LinearMap.id_apply]

def dG : (Fin (n d) → R) →ₗ[R] (Fin (rank d) → R) × (Fin (n d) → R) :=
  (dK d ∘ₗ pi d).prod (LinearMap.id - sec d ∘ₗ pi d)

theorem fst_comp_dG : LinearMap.fst R _ _ ∘ₗ dG d = dK d ∘ₗ pi d := LinearMap.fst_prod _ _
theorem snd_comp_dG : LinearMap.snd R _ _ ∘ₗ dG d = LinearMap.id - sec d ∘ₗ pi d := LinearMap.snd_prod _ _

def freeModel : CoherentBaseChange.TwoTermComplex.{u, u} R :=
  { C0 := Fin (n d) → R, C1 := (Fin (rank d) → R) × (Fin (n d) → R), d := dG d }

theorem comm_free : d ∘ₗ (iota0 d ∘ₗ pi d) = ((-(lift d)) ∘ₗ LinearMap.fst R _ _) ∘ₗ dG d := by
  rw [← LinearMap.comp_assoc, comm, LinearMap.comp_assoc, LinearMap.comp_assoc, fst_comp_dG]

variable (A : Type u) [CommRing A] [Algebra R A]

theorem mem_ker_dG_baseChange_iff (z : A ⊗[R] (Fin (n d) → R)) :
    (dG d).baseChange A z = 0 ↔
      ((dK d).baseChange A) (((pi d).baseChange A) z) = 0 ∧ z = ((sec d).baseChange A) (((pi d).baseChange A) z) := by
  have hinj := (TensorProduct.prodRight R A A (Fin (rank d) → R) (Fin (n d) → R)).injective
  constructor
  · intro h
    have h1 := congrArg (fun w => ((LinearMap.fst R _ _).baseChange A) w) h
    have h2 := congrArg (fun w => ((LinearMap.snd R _ _).baseChange A) w) h
    simp only [map_zero, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, fst_comp_dG, snd_comp_dG] at h1 h2
    rw [LinearMap.baseChange_comp, LinearMap.comp_apply] at h1
    rw [LinearMap.baseChange_sub, LinearMap.sub_apply, LinearMap.baseChange_id, LinearMap.id_apply,
      LinearMap.baseChange_comp, LinearMap.comp_apply, sub_eq_zero] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    apply hinj
    rw [map_zero, prodRight_apply_eq_baseChange, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, fst_comp_dG,
      ← LinearMap.comp_apply ((LinearMap.snd R _ _).baseChange A), ← LinearMap.baseChange_comp, snd_comp_dG,
      LinearMap.baseChange_comp, LinearMap.comp_apply, h1, LinearMap.baseChange_sub, LinearMap.sub_apply,
      LinearMap.baseChange_id, LinearMap.id_apply, LinearMap.baseChange_comp, LinearMap.comp_apply, ← h2, sub_self]
    rfl

theorem bijective_kerMap_free_to_K :
    Function.Bijective (kerMapBaseChange (dG d) (dK d) (pi d) (LinearMap.fst R _ _) (fst_comp_dG d).symm A) := by
  constructor
  · rintro ⟨z, hz⟩ ⟨z', hz'⟩ h
    have h' : ((pi d).baseChange A) z = ((pi d).baseChange A) z' := congrArg Subtype.val h
    obtain ⟨-, hz2⟩ := (mem_ker_dG_baseChange_iff d A z).mp hz
    obtain ⟨-, hz2'⟩ := (mem_ker_dG_baseChange_iff d A z').mp hz'
    apply Subtype.ext
    show z = z'
    rw [hz2, hz2', h']
  · rintro ⟨w, hw⟩
    refine ⟨⟨((sec d).baseChange A) w, (mem_ker_dG_baseChange_iff d A _).mpr ⟨?_, ?_⟩⟩, Subtype.ext ?_⟩
    · have h5 : ((pi d).baseChange A) (((sec d).baseChange A) w) = w := by
        rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, pi_comp_sec, LinearMap.baseChange_id, LinearMap.id_apply]
      rw [h5]
      exact hw
    · rw [← LinearMap.comp_apply ((pi d).baseChange A), ← LinearMap.baseChange_comp, pi_comp_sec, LinearMap.baseChange_id,
        LinearMap.id_apply]
    · show ((pi d).baseChange A) (((sec d).baseChange A) w) = w
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, pi_comp_sec, LinearMap.baseChange_id, LinearMap.id_apply]

theorem kerMap_free_eq_comp (z : LinearMap.ker ((dG d).baseChange A)) :
    kerMapBaseChange (dG d) d (iota0 d ∘ₗ pi d) ((-(lift d)) ∘ₗ LinearMap.fst R _ _) (comm_free d) A z
      = kerMapBaseChange (dK d) d (iota0 d) (-(lift d)) (comm d) A
          (kerMapBaseChange (dG d) (dK d) (pi d) (LinearMap.fst R _ _) (fst_comp_dG d).symm A z) := by
  apply Subtype.ext
  show ((iota0 d ∘ₗ pi d).baseChange A) z.1 = ((iota0 d).baseChange A) (((pi d).baseChange A) z.1)
  rw [LinearMap.baseChange_comp, LinearMap.comp_apply]

theorem bijective_kerMap_free :
    Function.Bijective
      (kerMapBaseChange (dG d) d (iota0 d ∘ₗ pi d) ((-(lift d)) ∘ₗ LinearMap.fst R _ _) (comm_free d) A) := by
  have h : (kerMapBaseChange (dG d) d (iota0 d ∘ₗ pi d) ((-(lift d)) ∘ₗ LinearMap.fst R _ _) (comm_free d) A : _ → _)
      = (kerMapBaseChange (dK d) d (iota0 d) (-(lift d)) (comm d) A)
        ∘ (kerMapBaseChange (dG d) (dK d) (pi d) (LinearMap.fst R _ _) (fst_comp_dG d).symm A) :=
    funext (kerMap_free_eq_comp d A)
  rw [h]
  exact Function.Bijective.comp ⟨kerMap_injective' d A, kerMap_surjective' d A⟩ (bijective_kerMap_free_to_K d A)

end Free

end Truncation
p2m_reactivate "P2MW.S_TwoChartCech_exists_twoTermComplex_kerMapBaseChange_bijective.TwoChartCech.Truncation"

end TwoChartCech
p2m_reactivate "P2MW.S_TwoChartCech_exists_twoTermComplex_kerMapBaseChange_bijective.TwoChartCech.Truncation P2MW.S_TwoChartCech_exists_twoTermComplex_kerMapBaseChange_bijective.TwoChartCech"

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    ∃ (G : CoherentBaseChange.TwoTermComplex.{u, u} R) (ι0 : G.C0 →ₗ[R] C0) (ι1 : G.C1 →ₗ[R] C1)
      (comm : d ∘ₗ ι0 = ι1 ∘ₗ G.d),
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerMapBaseChange G.d d ι0 ι1 comm A) :=
  ⟨TwoChartCech.Truncation.freeModel d, TwoChartCech.Truncation.iota0 d ∘ₗ TwoChartCech.Truncation.pi d,
    (-(TwoChartCech.Truncation.lift d)) ∘ₗ LinearMap.fst R _ _, TwoChartCech.Truncation.comm_free d,
    fun A _ _ => TwoChartCech.Truncation.bijective_kerMap_free d A⟩

end
p2m_reactivate "P2MW.S_TwoChartCech_exists_twoTermComplex_kerMapBaseChange_bijective.TwoChartCech.Truncation P2MW.S_TwoChartCech_exists_twoTermComplex_kerMapBaseChange_bijective.TwoChartCech"

end S_TwoChartCech_exists_twoTermComplex_kerMapBaseChange_bijective
end P2MW
export P2MW.S_TwoChartCech_exists_twoTermComplex_kerMapBaseChange_bijective (solution)
