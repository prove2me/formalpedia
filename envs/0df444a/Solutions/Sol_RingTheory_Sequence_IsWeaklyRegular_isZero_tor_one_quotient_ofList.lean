-- Prove2me | solution 1 for RingTheory.Sequence.IsWeaklyRegular.isZero_tor_one_quotient_ofList
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/16235228-6343-5044-ab77-eb7d529fc3d0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingTheory_Sequence_IsWeaklyRegular_isZero_tor_one_quotient_ofList

set_option autoImplicit false
set_option maxHeartbeats 3200000

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TensorProduct

noncomputable section

namespace TorRegSeq

section TorLES
variable {R : Type u} [CommRing R]

theorem torLES_tensorRight_shortExact {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) (M : ModuleCat.{u} R) [Module.Flat R M] :
    (S.map (tensorRight M)).ShortExact :=
  ShortComplex.shortExact_of_iso (S.mapNatIso (BraidedCategory.tensorLeftIsoTensorRight M))
    (hS.map_of_exact (tensorLeft M))

@[reducible, simps]
noncomputable def torLES_resolutionTensorSES (S : ShortComplex (ModuleCat.{u} R))
    {Y : ModuleCat.{u} R} (P : ProjectiveResolution Y) :
    ShortComplex (HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ)) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map S.f)
      (ComplexShape.down ℕ)).app P.complex)
    ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map S.g)
      (ComplexShape.down ℕ)).app P.complex)
    (by
      ext i : 1
      change S.f ▷ P.complex.X i ≫ S.g ▷ P.complex.X i = 0
      rw [← MonoidalCategory.comp_whiskerRight, S.zero, MonoidalPreadditive.zero_whiskerRight])

theorem torLES_resolutionTensorSES_shortExact (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) {Y : ModuleCat.{u} R} (P : ProjectiveResolution Y) :
    (torLES_resolutionTensorSES S P).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  exact torLES_tensorRight_shortExact hS (P.complex.X i)

variable {Y : ModuleCat.{u} R} (P : ProjectiveResolution Y)

noncomputable def torLES_torIso (X : ModuleCat.{u} R) (n : ℕ) :
    ((Tor (ModuleCat.{u} R) n).obj X).obj Y ≅
      ((((curriedTensor (ModuleCat.{u} R)).obj X).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).homology n :=
  P.isoLeftDerivedObj ((curriedTensor (ModuleCat.{u} R)).obj X) n

theorem torLES_torMap_app_eq {X X' : ModuleCat.{u} R} (f : X ⟶ X') (n : ℕ) :
    ((Tor (ModuleCat.{u} R) n).map f).app Y =
      (torLES_torIso P X n).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map f)
            (ComplexShape.down ℕ)).app P.complex) n ≫
        (torLES_torIso P X' n).inv :=
  P.leftDerived_app_eq ((curriedTensor (ModuleCat.{u} R)).map f) n

noncomputable def torLES_torDelta (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (n : ℕ) :
    ((Tor (ModuleCat.{u} R) (n + 1)).obj S.X₃).obj Y ⟶
      ((Tor (ModuleCat.{u} R) n).obj S.X₁).obj Y :=
  (torLES_torIso P S.X₃ (n + 1)).hom ≫
    (torLES_resolutionTensorSES_shortExact S hS P).δ (n + 1) n (by simp) ≫
    (torLES_torIso P S.X₁ n).inv

include P in

theorem torLES_torMap_comp_eq_zero (S : ShortComplex (ModuleCat.{u} R)) (n : ℕ) :
    ((Tor (ModuleCat.{u} R) n).map S.f).app Y ≫
      ((Tor (ModuleCat.{u} R) n).map S.g).app Y = 0 := by
  have hz : HomologicalComplex.homologyMap (torLES_resolutionTensorSES S P).f n ≫
      HomologicalComplex.homologyMap (torLES_resolutionTensorSES S P).g n = 0 := by
    rw [← HomologicalComplex.homologyMap_comp, (torLES_resolutionTensorSES S P).zero,
      HomologicalComplex.homologyMap_zero]
  simp only [torLES_resolutionTensorSES_X₁, torLES_resolutionTensorSES_X₂,
    torLES_resolutionTensorSES_X₃] at hz
  rw [torLES_torMap_app_eq P S.f n, torLES_torMap_app_eq P S.g n]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  slice_lhs 2 3 => rw [hz]
  simp

theorem torLES_torMap_comp_torDelta_eq_zero (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (n : ℕ) :
    ((Tor (ModuleCat.{u} R) (n + 1)).map S.g).app Y ≫ torLES_torDelta P S hS n = 0 := by
  have hz := (torLES_resolutionTensorSES_shortExact S hS P).comp_δ (n + 1) n (by simp)
  simp only [torLES_resolutionTensorSES_X₁, torLES_resolutionTensorSES_X₂,
    torLES_resolutionTensorSES_X₃] at hz
  dsimp only [torLES_torDelta]
  rw [torLES_torMap_app_eq P S.g (n + 1)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  slice_lhs 2 3 => rw [hz]
  simp

theorem torLES_torDelta_comp_eq_zero (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (n : ℕ) :
    torLES_torDelta P S hS n ≫ ((Tor (ModuleCat.{u} R) n).map S.f).app Y = 0 := by
  have hz := (torLES_resolutionTensorSES_shortExact S hS P).δ_comp (n + 1) n (by simp)
  simp only [torLES_resolutionTensorSES_X₁, torLES_resolutionTensorSES_X₂,
    torLES_resolutionTensorSES_X₃] at hz
  dsimp only [torLES_torDelta]
  rw [torLES_torMap_app_eq P S.f n]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  slice_lhs 2 3 => rw [hz]
  simp

theorem torLES_tor_exact₂ (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (n : ℕ) :
    (ShortComplex.mk (((Tor (ModuleCat.{u} R) n).map S.f).app Y)
      (((Tor (ModuleCat.{u} R) n).map S.g).app Y)
      (torLES_torMap_comp_eq_zero P S n)).Exact := by
  refine ShortComplex.exact_of_iso
    (ShortComplex.isoMk (torLES_torIso P S.X₁ n).symm (torLES_torIso P S.X₂ n).symm
      (torLES_torIso P S.X₃ n).symm ?_ ?_)
    ((torLES_resolutionTensorSES_shortExact S hS P).homology_exact₂ n)
  · dsimp only
    rw [torLES_torMap_app_eq P S.f n]
    simp
  · dsimp only
    rw [torLES_torMap_app_eq P S.g n]
    simp

theorem torLES_tor_exact₃ (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (n : ℕ) :
    (ShortComplex.mk (((Tor (ModuleCat.{u} R) (n + 1)).map S.g).app Y)
      (torLES_torDelta P S hS n)
      (torLES_torMap_comp_torDelta_eq_zero P S hS n)).Exact := by
  refine ShortComplex.exact_of_iso
    (ShortComplex.isoMk (torLES_torIso P S.X₂ (n + 1)).symm
      (torLES_torIso P S.X₃ (n + 1)).symm (torLES_torIso P S.X₁ n).symm ?_ ?_)
    ((torLES_resolutionTensorSES_shortExact S hS P).homology_exact₃ (n + 1) n (by simp))
  · dsimp only
    rw [torLES_torMap_app_eq P S.g (n + 1)]
    simp
  · dsimp only [torLES_torDelta]
    simp

theorem torLES_tor_exact₁ (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (n : ℕ) :
    (ShortComplex.mk (torLES_torDelta P S hS n)
      (((Tor (ModuleCat.{u} R) n).map S.f).app Y)
      (torLES_torDelta_comp_eq_zero P S hS n)).Exact := by
  refine ShortComplex.exact_of_iso
    (ShortComplex.isoMk (torLES_torIso P S.X₃ (n + 1)).symm
      (torLES_torIso P S.X₁ n).symm (torLES_torIso P S.X₂ n).symm ?_ ?_)
    ((torLES_resolutionTensorSES_shortExact S hS P).homology_exact₁ (n + 1) n (by simp))
  · dsimp only [torLES_torDelta]
    simp
  · dsimp only
    rw [torLES_torMap_app_eq P S.f n]
    simp

include P in

theorem torLES_tor_isZero_X₂ (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (n : ℕ) (h₁ : IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj S.X₁).obj Y))
    (h₃ : IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj S.X₃).obj Y)) :
    IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj S.X₂).obj Y) :=
  (torLES_tor_exact₂ P S hS (n + 1)).isZero_X₂
    (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

end TorLES

section TorFV
variable {R : Type u} [CommRing R]

theorem torFV_resolutionTensor_exactAt (M : ModuleCat.{u} R) [Module.Flat R M]
    {Y : ModuleCat.{u} R} (P : ProjectiveResolution Y) (n : ℕ) :
    ((((curriedTensor (ModuleCat.{u} R)).obj M).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj P.complex).ExactAt (n + 1) :=
  Module.Flat.lTensor_shortComplex_exact M (P.complex.sc (n + 1))
    (P.complex_exactAt_succ n)

theorem torFV_tor_succ_isZero_of_flat_res (M : ModuleCat.{u} R) [Module.Flat R M]
    {Y : ModuleCat.{u} R} (P : ProjectiveResolution Y) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj M).obj Y) := by
  refine IsZero.of_iso ?_ (torLES_torIso P M (n + 1))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact torFV_resolutionTensor_exactAt M P n

theorem torFV_tor_succ_isZero_of_flat (M : ModuleCat.{u} R) [Module.Flat R M]
    (Y : ModuleCat.{u} R) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj M).obj Y) := by
  obtain ⟨P⟩ : Nonempty (ProjectiveResolution Y) := HasProjectiveResolution.out
  exact torFV_tor_succ_isZero_of_flat_res M P n

theorem torFV_tor_one_isZero_of_flat (M : ModuleCat.{u} R) [Module.Flat R M]
    (Y : ModuleCat.{u} R) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj M).obj Y) :=
  torFV_tor_succ_isZero_of_flat M Y 0

theorem torFV_tor_succ_isZero_of_isZero (X : ModuleCat.{u} R) (hX : IsZero X)
    (Y : ModuleCat.{u} R) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj X).obj Y) := by
  obtain ⟨P⟩ : Nonempty (ProjectiveResolution Y) := HasProjectiveResolution.out
  refine IsZero.of_iso ?_ (torLES_torIso P X (n + 1))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact HomologicalComplex.ExactAt.of_isZero
    ((tensorRight (P.complex.X (n + 1))).map_isZero hX)

theorem torFV_tor_one_isZero_of_isZero (X : ModuleCat.{u} R) (hX : IsZero X)
    (Y : ModuleCat.{u} R) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj X).obj Y) :=
  torFV_tor_succ_isZero_of_isZero X hX Y 0

end TorFV

section TorZeroBridge
variable {R : Type u} [CommRing R]

theorem ar_opcyclesMap_fromLeftDerivedZero'_naturality
    {Y : ModuleCat.{u} R} (P : ProjectiveResolution Y) {X X' : ModuleCat.{u} R}
    (f : X ⟶ X') :
    HomologicalComplex.opcyclesMap
        ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map f)
          (ComplexShape.down ℕ)).app P.complex) 0 ≫
        P.fromLeftDerivedZero' ((curriedTensor (ModuleCat.{u} R)).obj X') =
      P.fromLeftDerivedZero' ((curriedTensor (ModuleCat.{u} R)).obj X) ≫
        ((curriedTensor (ModuleCat.{u} R)).map f).app Y := by
  rw [← cancel_epi (HomologicalComplex.pOpcycles
    ((((curriedTensor (ModuleCat.{u} R)).obj X).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj P.complex) 0)]
  rw [HomologicalComplex.p_opcyclesMap_assoc,
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero', ← Category.assoc,
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero']
  exact (((curriedTensor (ModuleCat.{u} R)).map f).naturality (P.π.f 0)).symm

theorem ar_tor0_map_fromLeftDerivedZero_naturality
    {Y : ModuleCat.{u} R} (P : ProjectiveResolution Y) {X X' : ModuleCat.{u} R}
    (f : X ⟶ X') :
    ((Tor (ModuleCat.{u} R) 0).map f).app Y ≫
        ((curriedTensor (ModuleCat.{u} R)).obj X').fromLeftDerivedZero.app Y =
      ((curriedTensor (ModuleCat.{u} R)).obj X).fromLeftDerivedZero.app Y ≫
        ((curriedTensor (ModuleCat.{u} R)).map f).app Y := by
  have hM : ((Tor (ModuleCat.{u} R) 0).map f).app Y =
      (torLES_torIso P X 0).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map f)
            (ComplexShape.down ℕ)).app P.complex) 0 ≫
        (torLES_torIso P X' 0).inv :=
    torLES_torMap_app_eq P f 0
  have hF : ((curriedTensor (ModuleCat.{u} R)).obj X).fromLeftDerivedZero.app Y =
      (P.isoLeftDerivedObj ((curriedTensor (ModuleCat.{u} R)).obj X) 0).hom ≫
        HomologicalComplex.homologyι
          ((((curriedTensor (ModuleCat.{u} R)).obj X).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P.complex) 0 ≫
        P.fromLeftDerivedZero' ((curriedTensor (ModuleCat.{u} R)).obj X) :=
    ProjectiveResolution.fromLeftDerivedZero_eq P
      ((curriedTensor (ModuleCat.{u} R)).obj X)
  have hG : ((curriedTensor (ModuleCat.{u} R)).obj X').fromLeftDerivedZero.app Y =
      (P.isoLeftDerivedObj ((curriedTensor (ModuleCat.{u} R)).obj X') 0).hom ≫
        HomologicalComplex.homologyι
          ((((curriedTensor (ModuleCat.{u} R)).obj X').mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P.complex) 0 ≫
        P.fromLeftDerivedZero' ((curriedTensor (ModuleCat.{u} R)).obj X') :=
    ProjectiveResolution.fromLeftDerivedZero_eq P
      ((curriedTensor (ModuleCat.{u} R)).obj X')
  have hι : HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map f)
          (ComplexShape.down ℕ)).app P.complex) 0 ≫
        HomologicalComplex.homologyι
          ((((curriedTensor (ModuleCat.{u} R)).obj X').mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P.complex) 0 =
      HomologicalComplex.homologyι
          ((((curriedTensor (ModuleCat.{u} R)).obj X).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P.complex) 0 ≫
        HomologicalComplex.opcyclesMap
          ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).map f)
            (ComplexShape.down ℕ)).app P.complex) 0 := by
    apply HomologicalComplex.homologyι_naturality
  have hO := ar_opcyclesMap_fromLeftDerivedZero'_naturality P f
  have hbr : ∀ {Z : ModuleCat.{u} R}
      (h : ((((curriedTensor (ModuleCat.{u} R)).obj X').mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).homology 0 ⟶ Z),
      (torLES_torIso P X' 0).inv ≫
        (P.isoLeftDerivedObj ((curriedTensor (ModuleCat.{u} R)).obj X') 0).hom ≫ h = h :=
    fun {Z} h => (torLES_torIso P X' 0).inv_hom_id_assoc h
  have hbr2 : (torLES_torIso P X 0).hom =
      (P.isoLeftDerivedObj ((curriedTensor (ModuleCat.{u} R)).obj X) 0).hom := rfl
  rw [hM, hF, hG]
  simp only [Category.assoc]

  refine Eq.trans (whisker_eq _ (whisker_eq _ (hbr _))) ?_
  refine Eq.trans (whisker_eq _ ((Category.assoc _ _ _).symm)) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker hι _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ hO)) ?_
  exact eq_whisker hbr2 _

end TorZeroBridge

section Main
variable {R : Type u} [CommRing R]

theorem dv_tor_isZero_of_iso {X X' Y : ModuleCat.{u} R} (e : X ≅ X') (n : ℕ)
    (h : IsZero (((Tor (ModuleCat.{u} R) n).obj X').obj Y)) :
    IsZero (((Tor (ModuleCat.{u} R) n).obj X).obj Y) :=
  h.of_iso (((Tor (ModuleCat.{u} R) n).mapIso e).app Y)

theorem tor1_isZero_of_rTensor_injective
    {A N M : Type u} [AddCommGroup A] [Module R A] [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] (e : N →ₗ[R] A) (he : Function.Injective e)
    (hA : IsZero (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R A)).obj (ModuleCat.of R M)))
    (hinj : Function.Injective (LinearMap.rTensor M e)) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R (A ⧸ LinearMap.range e))).obj (ModuleCat.of R M)) := by
  classical
  set S₀ : ShortComplex (ModuleCat.{u} R) := ShortComplex.mk (ModuleCat.ofHom e)
    (ModuleCat.ofHom (LinearMap.range e).mkQ)
    (by
      have hz : (LinearMap.range e).mkQ ∘ₗ e = 0 := LinearMap.ext fun a => by
        simpa [Submodule.Quotient.mk_eq_zero] using LinearMap.mem_range_self e a
      rw [← ModuleCat.ofHom_comp, hz]
      rfl) with hS₀def
  have hS : S₀.ShortExact := by
    refine ModuleCat.shortComplex_shortExact S₀ ?_ ?_ ?_
    · exact LinearMap.exact_map_mkQ_range e
    · exact he
    · exact Submodule.mkQ_surjective _
  obtain ⟨P⟩ : Nonempty (ProjectiveResolution (ModuleCat.of R M)) :=
    HasProjectiveResolution.out

  have hzero : ((Tor (ModuleCat.{u} R) 1).map S₀.g).app (ModuleCat.of R M) = 0 := hA.eq_of_src _ _
  haveI hδmono : Mono (torLES_torDelta P S₀ hS 0) := (torLES_tor_exact₃ P S₀ hS 0).mono_g hzero

  haveI : PreservesFiniteColimits ((curriedTensor (ModuleCat.{u} R)).obj S₀.X₁) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  haveI : PreservesFiniteColimits ((curriedTensor (ModuleCat.{u} R)).obj S₀.X₂) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have hm2 : Mono (((curriedTensor (ModuleCat.{u} R)).map S₀.f).app (ModuleCat.of R M)) :=
    (ModuleCat.mono_iff_injective
      (((curriedTensor (ModuleCat.{u} R)).map S₀.f).app (ModuleCat.of R M))).mpr hinj
  have hsq := ar_tor0_map_fromLeftDerivedZero_naturality P S₀.f
  have hfac : ((Tor (ModuleCat.{u} R) 0).map S₀.f).app (ModuleCat.of R M) =
      (((curriedTensor (ModuleCat.{u} R)).obj S₀.X₁).fromLeftDerivedZero.app (ModuleCat.of R M) ≫
        ((curriedTensor (ModuleCat.{u} R)).map S₀.f).app (ModuleCat.of R M)) ≫
      inv (((curriedTensor (ModuleCat.{u} R)).obj S₀.X₂).fromLeftDerivedZero.app (ModuleCat.of R M)) :=
    (IsIso.eq_comp_inv (((curriedTensor (ModuleCat.{u} R)).obj S₀.X₂).fromLeftDerivedZero.app (ModuleCat.of R M))).mpr hsq
  haveI hmonoF : Mono (((curriedTensor (ModuleCat.{u} R)).obj S₀.X₁).fromLeftDerivedZero.app
      (ModuleCat.of R M)) := IsIso.mono_of_iso _
  haveI hmonoG : Mono (inv (((curriedTensor (ModuleCat.{u} R)).obj
      S₀.X₂).fromLeftDerivedZero.app (ModuleCat.of R M))) := IsIso.mono_of_iso _
  haveI hTor0mono : Mono (((Tor (ModuleCat.{u} R) 0).map S₀.f).app (ModuleCat.of R M)) := by
    rw [hfac]
    exact mono_comp' (mono_comp' hmonoF hm2) hmonoG

  have hδ0 : torLES_torDelta P S₀ hS 0 = 0 :=
    zero_of_comp_mono _ (torLES_torDelta_comp_eq_zero P S₀ hS 0)
  have : Mono (0 : ((Tor (ModuleCat.{u} R) 1).obj S₀.X₃).obj (ModuleCat.of R M) ⟶
      ((Tor (ModuleCat.{u} R) 0).obj S₀.X₁).obj (ModuleCat.of R M)) := by rw [← hδ0]; exact hδmono
  exact IsZero.of_mono_zero _ (((Tor (ModuleCat.{u} R) 0).obj S₀.X₁).obj (ModuleCat.of R M))

theorem step {M : Type u} [AddCommGroup M] [Module R M] (I : Ideal R) (x : R)
    (hI : IsZero (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R M)))
    (hx : IsSMulRegular (M ⧸ (I • ⊤ : Submodule R M)) x) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R (R ⧸ (I ⊔ Ideal.span {x})))).obj (ModuleCat.of R M)) := by
  classical

  let φ : (R ⧸ I) →ₗ[R] (R ⧸ I) := x • LinearMap.id
  have hφapp : ∀ a : R ⧸ I, φ a = x • a := fun a => rfl
  let N : Submodule R (R ⧸ I) := LinearMap.range φ
  have hxA : IsSMulRegular ((R ⧸ I) ⊗[R] M) x :=
    ((TensorProduct.quotTensorEquivQuotSMul M I).isSMulRegular_congr x).mpr hx
  have hφinj : Function.Injective (LinearMap.rTensor M φ) := by
    intro a b hab
    apply hxA
    have e1 : LinearMap.rTensor M φ = x • LinearMap.id := by
      show LinearMap.rTensor M (x • LinearMap.id) = x • LinearMap.id
      rw [LinearMap.rTensor_smul, LinearMap.rTensor_id]
    have ha : LinearMap.rTensor M φ a = x • a := by rw [e1]; rfl
    have hb : LinearMap.rTensor M φ b = x • b := by rw [e1]; rfl
    show x • a = x • b
    rw [← ha, ← hb, hab]
  have hcomp : LinearMap.rTensor M φ = LinearMap.rTensor M N.subtype ∘ₗ LinearMap.rTensor M φ.rangeRestrict := by
    rw [← LinearMap.rTensor_comp]
    rfl
  have hinj : Function.Injective (LinearMap.rTensor M N.subtype) := by
    have h1 : Function.Injective (LinearMap.rTensor M N.subtype ∘ LinearMap.rTensor M φ.rangeRestrict) := by
      have h2 := hφinj
      rw [hcomp] at h2
      exact h2
    exact h1.of_comp_right (LinearMap.rTensor_surjective M (LinearMap.surjective_rangeRestrict φ))
  have hB := tor1_isZero_of_rTensor_injective N.subtype N.injective_subtype hI hinj

  have hNeq : Submodule.map (Submodule.mkQ I) (I ⊔ Ideal.span {x}) = LinearMap.range N.subtype := by
    rw [Submodule.range_subtype]
    apply le_antisymm
    · rintro y ⟨t, ht, rfl⟩
      obtain ⟨i, hi, s, hs, rfl⟩ := Submodule.mem_sup.mp ht
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hs
      refine ⟨Submodule.mkQ I r, ?_⟩
      rw [hφapp, map_add]
      simp only [Submodule.mkQ_apply]
      rw [(Submodule.Quotient.mk_eq_zero I).mpr hi, zero_add, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_comm]
    · rintro y ⟨a, rfl⟩
      obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective I a
      refine ⟨x * r, Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨r, mul_comm r x⟩), ?_⟩
      rw [hφapp]
      simp only [Submodule.mkQ_apply]
      rw [← Submodule.Quotient.mk_smul, smul_eq_mul]
  let e₁ : ((R ⧸ I) ⧸ LinearMap.range N.subtype) ≃ₗ[R] ((R ⧸ I) ⧸ Submodule.map (Submodule.mkQ I) (I ⊔ Ideal.span {x})) :=
    Submodule.quotEquivOfEq _ _ hNeq.symm
  let e₂ : ((R ⧸ I) ⧸ Submodule.map (Submodule.mkQ I) (I ⊔ Ideal.span {x})) ≃ₗ[R] (R ⧸ (I ⊔ Ideal.span {x})) :=
    Submodule.quotientQuotientEquivQuotient I (I ⊔ Ideal.span {x}) le_sup_left
  exact dv_tor_isZero_of_iso ((e₁ ≪≫ₗ e₂).symm.toModuleIso) 1 hB

theorem main {M : Type u} [AddCommGroup M] [Module R M] {rs : List R}
    (hM : RingTheory.Sequence.IsWeaklyRegular M rs) :
    ∀ n, n ≤ rs.length →
      IsZero (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R (R ⧸ Ideal.ofList (rs.take n)))).obj (ModuleCat.of R M)) := by
  intro n
  induction n with
  | zero =>
    intro _
    have h0 : Ideal.ofList (rs.take 0) = (⊥ : Ideal R) := by rw [List.take_zero, Ideal.ofList_nil]
    let e : (R ⧸ Ideal.ofList (rs.take 0)) ≃ₗ[R] R :=
      Submodule.quotEquivOfEq _ _ h0 ≪≫ₗ Submodule.quotEquivOfEqBot _ rfl
    exact dv_tor_isZero_of_iso e.toModuleIso 1 (torFV_tor_one_isZero_of_flat (ModuleCat.of R R) (ModuleCat.of R M))
  | succ n ih =>
    intro hn
    have hlt : n < rs.length := Nat.lt_of_succ_le hn
    have hI := ih hlt.le
    have hx := hM.regular_mod_prev n hlt
    have hstep := step (Ideal.ofList (rs.take n)) (rs[n]) hI hx
    have heq : Ideal.ofList (rs.take (n + 1)) = Ideal.ofList (rs.take n) ⊔ Ideal.span {rs[n]} := by
      rw [List.take_succ_eq_append_getElem hlt, Ideal.ofList_append, Ideal.ofList_singleton]
    exact dv_tor_isZero_of_iso (Submodule.quotEquivOfEq _ _ heq).toModuleIso 1 hstep

end Main

end TorRegSeq

end

theorem solution
    {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    {rs : List R} (hM : RingTheory.Sequence.IsWeaklyRegular M rs) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R (R ⧸ Ideal.ofList rs))).obj
      (ModuleCat.of R M)) := by
  have h := TorRegSeq.main hM rs.length le_rfl
  have heq : Ideal.ofList (rs.take rs.length) = Ideal.ofList rs := by rw [List.take_length]
  exact TorRegSeq.dv_tor_isZero_of_iso (Submodule.quotEquivOfEq _ _ heq.symm).toModuleIso 1 h

end S_RingTheory_Sequence_IsWeaklyRegular_isZero_tor_one_quotient_ofList
end P2MW
export P2MW.S_RingTheory_Sequence_IsWeaklyRegular_isZero_tor_one_quotient_ofList (solution)
