-- Prove2me | solution 1 for RingHom.Flat.of_pullbackRing_of_isPushout_of_surjective_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/a7a1144d-6dcf-5286-87ad-3ba097e7b236

import Mathlib
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingHom_Flat_of_pullbackRing_of_isPushout_of_surjective_of_isNilpotent

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CerednikDrinfeld.SpecialFormal.ModuliPackage
open scoped TensorProduct

namespace B26F

theorem half {P B' B'' B : Type} [CommRing P] [CommRing B'] [CommRing B''] [CommRing B]
    [Algebra P B'] [Algebra P B''] [Algebra B' B] [Algebra B'' B]
    (hlift : ∀ (b' : B') (b'' : B''), algebraMap B' B b' = algebraMap B'' B b'' → ∃ x : P, algebraMap P B' x = b' ∧ algebraMap P B'' x = b'')
    {M' M'' MB N : Type} [AddCommGroup M'] [AddCommGroup M''] [AddCommGroup MB] [AddCommGroup N]
    [Module B' M'] [Module P M'] [IsScalarTower P B' M']
    [Module B'' M''] [Module P M''] [IsScalarTower P B'' M'']
    [Module B MB] [Module B' MB] [IsScalarTower B' B MB] [Module B'' MB] [IsScalarTower B'' B MB]
    [Module P N]
    (g' : M' →ₗ[B'] MB) (g'' : M'' →ₗ[B''] MB)
    (hg's : Function.Surjective g') (hg''s : Function.Surjective g'')
    (hg''k : LinearMap.ker g'' = (RingHom.ker (algebraMap B'' B)) • ⊤)
    (k' : N →ₗ[P] M') (k'' : N →ₗ[P] M'')
    (hk : ∀ n : N, g' (k' n) = g'' (k'' n))
    (hkinj : ∀ n : N, k' n = 0 → k'' n = 0 → n = 0)
    (hklift : ∀ (m' : M') (m'' : M''), g' m' = g'' m'' → ∃ n : N, k' n = m' ∧ k'' n = m'') :
    Function.Surjective k' ∧ LinearMap.ker k' = (RingHom.ker (algebraMap P B')) • ⊤ := by
  constructor
  · intro m'
    obtain ⟨m'', hm''⟩ := hg''s (g' m')
    obtain ⟨n, hn, _⟩ := hklift m' m'' hm''.symm
    exact ⟨n, hn⟩
  apply le_antisymm
  · intro n hn
    rw [LinearMap.mem_ker] at hn
    have hy : k'' n ∈ (RingHom.ker (algebraMap B'' B)) • (⊤ : Submodule B'' M'') := by
      rw [← hg''k, LinearMap.mem_ker, ← hk, hn, map_zero]

    have key : ∀ y ∈ (RingHom.ker (algebraMap B'' B)) • (⊤ : Submodule B'' M''),
        ∃ n₁ : N, k' n₁ = 0 ∧ k'' n₁ = y ∧ n₁ ∈ (RingHom.ker (algebraMap P B')) • (⊤ : Submodule P N) := by
      intro y hy
      refine Submodule.smul_induction_on hy ?_ ?_
      · intro j hj m'' _
        obtain ⟨m', hm'⟩ := hg's (g'' m'')
        obtain ⟨n₀, h₀', h₀''⟩ := hklift m' m'' hm'
        obtain ⟨x, hx', hx''⟩ := hlift 0 j (by rw [map_zero]; exact (RingHom.mem_ker.1 hj).symm)
        refine ⟨x • n₀, ?_, ?_, ?_⟩
        · rw [map_smul, ← algebraMap_smul B' x, hx', zero_smul]
        · rw [map_smul, ← algebraMap_smul B'' x, hx'', h₀'']
        · exact Submodule.smul_mem_smul (RingHom.mem_ker.2 hx') Submodule.mem_top
      · rintro y₁ y₂ ⟨n₁, a₁, b₁, c₁⟩ ⟨n₂, a₂, b₂, c₂⟩
        exact ⟨n₁ + n₂, by rw [map_add, a₁, a₂, add_zero], by rw [map_add, b₁, b₂], Submodule.add_mem _ c₁ c₂⟩
    obtain ⟨n₁, a₁, b₁, c₁⟩ := key _ hy
    have : n = n₁ := by
      have := hkinj (n - n₁) (by rw [map_sub, hn, a₁, sub_zero]) (by rw [map_sub, b₁, sub_self])
      exact sub_eq_zero.1 this
    rw [this]; exact c₁
  · refine Submodule.smul_le.2 fun x hx n _ => ?_
    rw [LinearMap.mem_ker, map_smul, ← algebraMap_smul B' x, RingHom.mem_ker.1 hx, zero_smul]

theorem lTensor_injective_of_ker_eq_smul_top {P : Type} [CommRing P] {W N M : Type}
    [AddCommGroup W] [AddCommGroup N] [AddCommGroup M] [Module P W] [Module P N] [Module P M]
    (J : Ideal P) (hW : ∀ j ∈ J, ∀ w : W, j • w = 0)
    (k : N →ₗ[P] M) (hk : Function.Surjective k) (hker : LinearMap.ker k = J • ⊤) :
    Function.Injective (LinearMap.lTensor W k) := by
  have hex : Function.Exact (J • (⊤ : Submodule P N)).subtype k := by
    intro n
    rw [← LinearMap.mem_ker, hker]
    constructor
    · intro h; exact ⟨⟨n, h⟩, rfl⟩
    · rintro ⟨y, rfl⟩; exact y.2
  have hT := lTensor_exact W hex hk
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨y, rfl⟩ := (hT x).1 hx

  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    rw [map_add] at hx ⊢
    have ha0 : LinearMap.lTensor W k (LinearMap.lTensor W (J • (⊤ : Submodule P N)).subtype a) = 0 := by
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hex.linearMap_comp_eq_zero, LinearMap.lTensor_zero,
        LinearMap.zero_apply]
    have hb0 : LinearMap.lTensor W k (LinearMap.lTensor W (J • (⊤ : Submodule P N)).subtype b) = 0 := by
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hex.linearMap_comp_eq_zero, LinearMap.lTensor_zero,
        LinearMap.zero_apply]
    rw [ha ha0, hb hb0, add_zero]
  | tmul w y =>
    rw [LinearMap.lTensor_tmul, Submodule.subtype_apply]
    obtain ⟨y, hy⟩ := y
    refine Submodule.smul_induction_on (p := fun y => w ⊗ₜ[P] y = 0) hy ?_ ?_
    · intro j hj n _
      rw [← TensorProduct.smul_tmul, hW j hj, TensorProduct.zero_tmul]
    · intro a b ha hb
      rw [TensorProduct.tmul_add, ha, hb, add_zero]

section main

variable {P B' B'' B : Type} [CommRing P] [CommRing B'] [CommRing B''] [CommRing B]
    [Algebra P B'] [Algebra P B''] [Algebra B' B] [Algebra B'' B]
    (hinj : ∀ x : P, algebraMap P B' x = 0 → algebraMap P B'' x = 0 → x = 0)
    (hlift : ∀ (b' : B') (b'' : B''), algebraMap B' B b' = algebraMap B'' B b'' → ∃ x : P, algebraMap P B' x = b' ∧ algebraMap P B'' x = b'')
    (hs' : Function.Surjective (algebraMap B' B)) (hs'' : Function.Surjective (algebraMap B'' B))
    {M' M'' MB N : Type} [AddCommGroup M'] [AddCommGroup M''] [AddCommGroup MB] [AddCommGroup N]
    [Module B' M'] [Module P M'] [IsScalarTower P B' M']
    [Module B'' M''] [Module P M''] [IsScalarTower P B'' M'']
    [Module B MB] [Module B' MB] [IsScalarTower B' B MB] [Module B'' MB] [IsScalarTower B'' B MB]
    [Module P N]
    (g' : M' →ₗ[B'] MB) (g'' : M'' →ₗ[B''] MB)
    (k' : N →ₗ[P] M') (k'' : N →ₗ[P] M'')

theorem inj_aux {S : Type} [CommRing S] [Algebra P S] (hsurj : Function.Surjective (algebraMap P S))
    {M : Type} [AddCommGroup M] [Module S M] [Module P M] [IsScalarTower P S M] [Module.Flat S M]
    (k : N →ₗ[P] M) (hk : Function.Surjective k) (hker : LinearMap.ker k = (RingHom.ker (algebraMap P S)) • ⊤)
    (K : Submodule P P) (hK : ∀ x ∈ K, algebraMap P S x = 0 → x = 0)
    (z : ↥K ⊗[P] N)
    (hz : k (TensorProduct.lid P N (LinearMap.rTensor N K.subtype z)) = 0) : z = 0 := by

  let KS : Ideal S := Ideal.map (algebraMap P S) (K : Ideal P)
  have hKS : ∀ x : ↥K, algebraMap P S x ∈ KS := fun x => Ideal.mem_map_of_mem _ x.2
  let gK : ↥K →ₗ[P] ↥KS :=
    { toFun := fun x => ⟨algebraMap P S x, hKS x⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun c a => Subtype.ext (by simp [Algebra.smul_def]) }
  have hgK : Function.Bijective gK := by
    constructor
    · intro a b h
      have h' : algebraMap P S (a - b : P) = 0 := by
        have := congrArg Subtype.val h
        simp only [gK] at this
        change algebraMap P S a = algebraMap P S b at this
        rw [map_sub, this, sub_self]
      exact Subtype.ext (sub_eq_zero.1 (hK _ (K.sub_mem a.2 b.2) h'))
    · rintro ⟨s, hs⟩
      rw [Ideal.mem_map_iff_of_surjective _ hsurj] at hs
      obtain ⟨x, hx, rfl⟩ := hs
      exact ⟨⟨x, hx⟩, rfl⟩
  let eK : ↥K ≃ₗ[P] ↥KS := LinearEquiv.ofBijective gK hgK

  haveI : TensorProduct.CompatibleSMul P S (↥KS) M := TensorProduct.CompatibleSMul.of_algebraMap_surjective _ _ hsurj

  have i1 : Function.Injective (LinearMap.lTensor (↥KS) k) :=
    lTensor_injective_of_ker_eq_smul_top (RingHom.ker (algebraMap P S)) (fun j hj w => by
      apply Subtype.ext
      show j • (w : S) = 0
      rw [Algebra.smul_def, RingHom.mem_ker.1 hj, zero_mul]) k hk hker
  have i2 : Function.Injective ((TensorProduct.equivOfCompatibleSMul P S S (↥KS) M).symm) :=
    (TensorProduct.equivOfCompatibleSMul P S S (↥KS) M).symm.injective
  have i3 : Function.Injective (LinearMap.rTensor M KS.subtype) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ KS.injective_subtype
  have i4 : Function.Injective (TensorProduct.lid S M) := (TensorProduct.lid S M).injective
  have i0 : Function.Injective (LinearMap.rTensor N eK.toLinearMap) := (LinearEquiv.rTensor N eK).injective

  have hcomp : ∀ z : ↥K ⊗[P] N,
      TensorProduct.lid S M (LinearMap.rTensor M KS.subtype ((TensorProduct.equivOfCompatibleSMul P S S (↥KS) M).symm
        (LinearMap.lTensor (↥KS) k (LinearMap.rTensor N eK.toLinearMap z)))) =
      k (TensorProduct.lid P N (LinearMap.rTensor N K.subtype z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul x n =>
      rw [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, Submodule.subtype_apply,
        TensorProduct.lid_tmul, map_smul]
      show TensorProduct.lid S M (LinearMap.rTensor M KS.subtype
        ((TensorProduct.equivOfCompatibleSMul P S S (↥KS) M).symm ((gK x) ⊗ₜ[P] k n))) = (x : P) • k n
      have : (TensorProduct.equivOfCompatibleSMul P S S (↥KS) M).symm ((gK x) ⊗ₜ[P] k n) = (gK x) ⊗ₜ[S] k n := rfl
      rw [this, LinearMap.rTensor_tmul, Submodule.subtype_apply, TensorProduct.lid_tmul]
      show algebraMap P S x • k n = (x : P) • k n
      rw [algebraMap_smul]
  apply i0; apply i1; apply i2; apply i3; apply i4
  rw [map_zero, map_zero, map_zero, map_zero, map_zero, hcomp, hz]

end main

end B26F

theorem B26F.flat_patch
    {P B' B'' B : Type} [CommRing P] [CommRing B'] [CommRing B''] [CommRing B]
    [Algebra P B'] [Algebra P B''] [Algebra B' B] [Algebra B'' B]
    (hsq : ∀ x : P, algebraMap B' B (algebraMap P B' x) = algebraMap B'' B (algebraMap P B'' x))
    (hinj : ∀ x : P, algebraMap P B' x = 0 → algebraMap P B'' x = 0 → x = 0)
    (hlift : ∀ (b' : B') (b'' : B''), algebraMap B' B b' = algebraMap B'' B b'' → ∃ x : P, algebraMap P B' x = b' ∧ algebraMap P B'' x = b'')
    (hs' : Function.Surjective (algebraMap B' B)) (hs'' : Function.Surjective (algebraMap B'' B))
    (hn' : IsNilpotent (RingHom.ker (algebraMap B' B))) (hn'' : IsNilpotent (RingHom.ker (algebraMap B'' B)))
    {M' M'' MB N : Type} [AddCommGroup M'] [AddCommGroup M''] [AddCommGroup MB] [AddCommGroup N]
    [Module B' M'] [Module P M'] [IsScalarTower P B' M']
    [Module B'' M''] [Module P M''] [IsScalarTower P B'' M'']
    [Module B MB] [Module B' MB] [IsScalarTower B' B MB] [Module B'' MB] [IsScalarTower B'' B MB]
    [Module P N]
    (g' : M' →ₗ[B'] MB) (g'' : M'' →ₗ[B''] MB)
    (hg's : Function.Surjective g') (hg''s : Function.Surjective g'')
    (hg'k : LinearMap.ker g' = (RingHom.ker (algebraMap B' B)) • ⊤)
    (hg''k : LinearMap.ker g'' = (RingHom.ker (algebraMap B'' B)) • ⊤)
    (k' : N →ₗ[P] M') (k'' : N →ₗ[P] M'')
    (hk : ∀ n : N, g' (k' n) = g'' (k'' n))
    (hkinj : ∀ n : N, k' n = 0 → k'' n = 0 → n = 0)
    (hklift : ∀ (m' : M') (m'' : M''), g' m' = g'' m'' → ∃ n : N, k' n = m' ∧ k'' n = m'')
    [Module.Flat B' M'] [Module.Flat B'' M''] :
    Module.Flat P N := by
  obtain ⟨hk's, hk'k⟩ := B26F.half hlift g' g'' hg's hg''s hg''k k' k'' hk hkinj hklift
  obtain ⟨hk''s, hk''k⟩ := B26F.half (fun b'' b' h => by obtain ⟨x, h1, h2⟩ := hlift b' b'' h.symm; exact ⟨x, h2, h1⟩)
    g'' g' hg''s hg's hg'k k'' k' (fun n => (hk n).symm) (fun n h1 h2 => hkinj n h2 h1)
    (fun m'' m' h => by obtain ⟨n, h1, h2⟩ := hklift m' m'' h.symm; exact ⟨n, h2, h1⟩)
  have hp' : Function.Surjective (algebraMap P B') := by
    intro b'; obtain ⟨b'', h⟩ := hs'' (algebraMap B' B b'); obtain ⟨x, hx, _⟩ := hlift b' b'' h.symm; exact ⟨x, hx⟩
  have hp'' : Function.Surjective (algebraMap P B'') := by
    intro b''; obtain ⟨b', h⟩ := hs' (algebraMap B'' B b''); obtain ⟨x, _, hx⟩ := hlift b' b'' h; exact ⟨x, hx⟩
  rw [Module.Flat.iff_rTensor_injective']
  intro I

  let J' : Submodule P P := RingHom.ker (algebraMap P B')
  let K : Submodule P P := I ⊓ J'
  let IB : Ideal B' := Ideal.map (algebraMap P B') I
  let gI : ↥I →ₗ[P] ↥IB :=
    { toFun := fun x => ⟨algebraMap P B' x, Ideal.mem_map_of_mem _ x.2⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun c a => Subtype.ext (by simp [Algebra.smul_def]) }
  have hgI : Function.Surjective gI := by
    rintro ⟨s, hs⟩
    rw [Ideal.mem_map_iff_of_surjective _ hp'] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    exact ⟨⟨x, hx⟩, rfl⟩
  have hex : Function.Exact (Submodule.inclusion (inf_le_left : K ≤ I)) gI := by
    intro x
    constructor
    · intro hx
      have hx' : algebraMap P B' (x : P) = 0 := congrArg Subtype.val hx
      exact ⟨⟨x, x.2, hx'⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact Subtype.ext y.2.2
  have hT := rTensor_exact N hex hgI

  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hxN : TensorProduct.lid P N (LinearMap.rTensor N I.subtype x) = 0 := by rw [hx, map_zero]
  have hIB : LinearMap.rTensor N gI x = 0 := by

    haveI : TensorProduct.CompatibleSMul P B' (↥IB) M' := TensorProduct.CompatibleSMul.of_algebraMap_surjective _ _ hp'
    have i1 : Function.Injective (LinearMap.lTensor (↥IB) k') :=
      B26F.lTensor_injective_of_ker_eq_smul_top (RingHom.ker (algebraMap P B')) (fun j hj w => by
        apply Subtype.ext
        show j • (w : B') = 0
        rw [Algebra.smul_def, RingHom.mem_ker.1 hj, zero_mul]) k' hk's hk'k
    have i3 : Function.Injective (LinearMap.rTensor M' IB.subtype) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ IB.injective_subtype
    have hcomp : ∀ y : ↥I ⊗[P] N,
        TensorProduct.lid B' M' (LinearMap.rTensor M' IB.subtype ((TensorProduct.equivOfCompatibleSMul P B' B' (↥IB) M').symm
          (LinearMap.lTensor (↥IB) k' (LinearMap.rTensor N gI y)))) =
        k' (TensorProduct.lid P N (LinearMap.rTensor N I.subtype y)) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul i n =>
        rw [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, Submodule.subtype_apply,
          TensorProduct.lid_tmul, map_smul]
        have : (TensorProduct.equivOfCompatibleSMul P B' B' (↥IB) M').symm ((gI i) ⊗ₜ[P] k' n) = (gI i) ⊗ₜ[B'] k' n := rfl
        rw [this, LinearMap.rTensor_tmul, Submodule.subtype_apply, TensorProduct.lid_tmul]
        show algebraMap P B' i • k' n = (i : P) • k' n
        rw [algebraMap_smul]
    apply i1; apply (TensorProduct.equivOfCompatibleSMul P B' B' (↥IB) M').symm.injective; apply i3
    apply (TensorProduct.lid B' M').injective
    rw [map_zero, map_zero, map_zero, map_zero, hcomp, hxN, map_zero]
  obtain ⟨z, rfl⟩ := (hT x).1 hIB

  have hzero := B26F.inj_aux (N := N) hp'' k'' hk''s hk''k K
    (fun y hy h0 => hinj y hy.2 h0) z
    (by
      have : LinearMap.rTensor N K.subtype z = LinearMap.rTensor N I.subtype (LinearMap.rTensor N (Submodule.inclusion inf_le_left) z) := by
        rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]; rfl
      rw [this, hxN, map_zero])
  rw [hzero, map_zero]

namespace B26F

theorem surjective_and_ker_of_isPushout_of_surjective {B B' A' A₀ : Type} [CommRing B] [CommRing B'] [CommRing A'] [CommRing A₀]
    (φ : B' →+* B) (a : B' →+* A') (a₀ : B →+* A₀) (g : A' →+* A₀)
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom a) (CommRingCat.ofHom a₀) (CommRingCat.ofHom g))
    (hφ : Function.Surjective φ) :
    Function.Surjective g ∧ RingHom.ker g = Ideal.map a (RingHom.ker φ) := by
  have hw : ∀ b', g (a b') = a₀ (φ b') := fun b' => by
    have := H.w
    have h2 := congrArg (fun k => (CommRingCat.Hom.hom k) b') this
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h2
    exact h2.symm
  let J : Ideal A' := Ideal.map a (RingHom.ker φ)

  let q : A' →+* A' ⧸ J := Ideal.Quotient.mk J
  have hker_le : RingHom.ker φ ≤ RingHom.ker (q.comp a) := by
    intro x hx
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hx
  let lft : B' ⧸ RingHom.ker φ →+* A' ⧸ J := Ideal.Quotient.lift (RingHom.ker φ) (q.comp a) fun x hx => hker_le hx
  let r : B →+* A' ⧸ J := lft.comp (RingHom.quotientKerEquivOfSurjective hφ).symm.toRingHom
  have hr : ∀ b', r (φ b') = q (a b') := by
    intro b'
    have he : (RingHom.quotientKerEquivOfSurjective hφ).symm (φ b') = Ideal.Quotient.mk _ b' := by
      apply (RingHom.quotientKerEquivOfSurjective hφ).injective
      rw [RingEquiv.apply_symm_apply]; rfl
    show lft ((RingHom.quotientKerEquivOfSurjective hφ).symm (φ b')) = _
    rw [he]
    exact Ideal.Quotient.lift_mk _ _ _

  let d : A₀ →+* A' ⧸ J := CommRingCat.Hom.hom (H.desc (CommRingCat.ofHom r) (CommRingCat.ofHom q) (by
    ext b'; simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]; exact hr b'))
  have hdg : ∀ m, d (g m) = q m := by
    intro m
    have := H.inr_desc (CommRingCat.ofHom r) (CommRingCat.ofHom q) (by
      ext b'; simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]; exact hr b')
    have h2 := congrArg (fun k => (CommRingCat.Hom.hom k) m) this
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h2
    exact h2
  have hJg : ∀ x ∈ J, g x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      rw [hw, RingHom.mem_ker.1 hj, map_zero]
    | zero => exact map_zero g
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [smul_eq_mul, map_mul, hx, mul_zero]
  let u : A' ⧸ J →+* A₀ := Ideal.Quotient.lift J g hJg
  have hud : ∀ y, d (u y) = y := by
    intro y
    obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.lift_mk]; exact hdg m
  constructor
  ·
    have hdu : ∀ z, u (d z) = z := by
      intro z
      have key : (CommRingCat.ofHom (u.comp d)) = 𝟙 (CommRingCat.of A₀) := by
        apply H.hom_ext
        · ext b
          obtain ⟨b', rfl⟩ := hφ b
          simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply]
          rw [← hw, hdg, Ideal.Quotient.lift_mk]
        · ext m
          simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply]
          rw [hdg, Ideal.Quotient.lift_mk]
      have h2 := congrArg (fun k => (CommRingCat.Hom.hom k) z) key
      simp only [CommRingCat.hom_ofHom, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at h2
      exact h2
    intro z
    obtain ⟨m, hm⟩ := Ideal.Quotient.mk_surjective (d z)
    refine ⟨m, ?_⟩
    rw [← hdu z, ← hm, Ideal.Quotient.lift_mk]
  · ext x
    rw [RingHom.mem_ker]
    constructor
    · intro hx
      have := hdg x
      rw [hx, map_zero] at this
      exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm
    · exact hJg x

end B26F

theorem solution
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))
    {A' A'' A₀ : Type} [CommRing A'] [CommRing A''] [CommRing A₀]
    (a' : B' →+* A') (a'' : B'' →+* A'') (a₀ : B →+* A₀) (g' : A' →+* A₀) (g'' : A'' →+* A₀)
    (H' : IsPushout (CommRingCat.ofHom φ') (CommRingCat.ofHom a') (CommRingCat.ofHom a₀) (CommRingCat.ofHom g'))
    (H'' : IsPushout (CommRingCat.ofHom φ'') (CommRingCat.ofHom a'') (CommRingCat.ofHom a₀) (CommRingCat.ofHom g''))
    (hfl' : a'.Flat) (hfl'' : a''.Flat)
    (a : pullbackRing φ' φ'' →+* pullbackRing g' g'')
    (ha' : (pullbackFst g' g'').comp a = a'.comp (pullbackFst φ' φ''))
    (ha'' : (pullbackSnd g' g'').comp a = a''.comp (pullbackSnd φ' φ'')) :
    a.Flat := by
  obtain ⟨hg's, hg'k⟩ := B26F.surjective_and_ker_of_isPushout_of_surjective φ' a' a₀ g' H' hφ's
  obtain ⟨hg''s, hg''k⟩ := B26F.surjective_and_ker_of_isPushout_of_surjective φ'' a'' a₀ g'' H'' hφ''s
  have hw' : ∀ b', g' (a' b') = a₀ (φ' b') := fun b' => by
    have h2 := congrArg (fun k => (CommRingCat.Hom.hom k) b') H'.w
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h2
    exact h2.symm
  have hw'' : ∀ b'', g'' (a'' b'') = a₀ (φ'' b'') := fun b'' => by
    have h2 := congrArg (fun k => (CommRingCat.Hom.hom k) b'') H''.w
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h2
    exact h2.symm

  letI i1 : Algebra (pullbackRing φ' φ'') B' := (pullbackFst φ' φ'').toAlgebra
  letI i2 : Algebra (pullbackRing φ' φ'') B'' := (pullbackSnd φ' φ'').toAlgebra
  letI i3 : Algebra B' B := φ'.toAlgebra
  letI i4 : Algebra B'' B := φ''.toAlgebra
  letI i5 : Algebra B' A' := a'.toAlgebra
  letI i6 : Algebra B'' A'' := a''.toAlgebra
  letI i7 : Algebra (pullbackRing φ' φ'') A' := (a'.comp (pullbackFst φ' φ'')).toAlgebra
  letI i8 : Algebra (pullbackRing φ' φ'') A'' := (a''.comp (pullbackSnd φ' φ'')).toAlgebra
  haveI : IsScalarTower (pullbackRing φ' φ'') B' A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (pullbackRing φ' φ'') B'' A'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI i9 : Algebra B A₀ := a₀.toAlgebra
  letI i10 : Algebra B' A₀ := (a₀.comp φ').toAlgebra
  letI i11 : Algebra B'' A₀ := (a₀.comp φ'').toAlgebra
  haveI : IsScalarTower B' B A₀ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower B'' B A₀ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI i12 : Algebra (pullbackRing φ' φ'') (pullbackRing g' g'') := a.toAlgebra
  haveI hF' : Module.Flat B' A' := hfl'
  haveI hF'' : Module.Flat B'' A'' := hfl''

  let G' : A' →ₗ[B'] A₀ :=
    { toFun := g', map_add' := fun x y => map_add g' x y
      map_smul' := fun c x => by
        show g' (a' c * x) = (a₀ (φ' c)) * g' x
        rw [map_mul, hw'] }
  let G'' : A'' →ₗ[B''] A₀ :=
    { toFun := g'', map_add' := fun x y => map_add g'' x y
      map_smul' := fun c x => by
        show g'' (a'' c * x) = (a₀ (φ'' c)) * g'' x
        rw [map_mul, hw''] }
  have ha1 : ∀ x, (a x).1.1 = a' x.1.1 := fun x => by
    have := congrArg (fun f => f x) ha'; exact this
  have ha2 : ∀ x, (a x).1.2 = a'' x.1.2 := fun x => by
    have := congrArg (fun f => f x) ha''; exact this
  let K' : ↥(pullbackRing g' g'') →ₗ[pullbackRing φ' φ''] A' :=
    { toFun := fun n => n.1.1, map_add' := fun x y => rfl
      map_smul' := fun c n => by
        show (a c * n).1.1 = a' c.1.1 * n.1.1
        rw [← ha1]; rfl }
  let K'' : ↥(pullbackRing g' g'') →ₗ[pullbackRing φ' φ''] A'' :=
    { toFun := fun n => n.1.2, map_add' := fun x y => rfl
      map_smul' := fun c n => by
        show (a c * n).1.2 = a'' c.1.2 * n.1.2
        rw [← ha2]; rfl }
  have hker' : LinearMap.ker G' = (RingHom.ker (algebraMap B' B)) • (⊤ : Submodule B' A') := by
    rw [Ideal.smul_top_eq_map]
    ext x
    show g' x = 0 ↔ x ∈ Ideal.map (algebraMap B' A') (RingHom.ker φ')
    rw [← RingHom.mem_ker, hg'k]; rfl
  have hker'' : LinearMap.ker G'' = (RingHom.ker (algebraMap B'' B)) • (⊤ : Submodule B'' A'') := by
    rw [Ideal.smul_top_eq_map]
    ext x
    show g'' x = 0 ↔ x ∈ Ideal.map (algebraMap B'' A'') (RingHom.ker φ'')
    rw [← RingHom.mem_ker, hg''k]; rfl
  exact B26F.flat_patch
    (hsq := fun x => x.2) (hinj := fun x h1 h2 => Subtype.ext (Prod.ext h1 h2))
    (hlift := fun b' b'' h => ⟨⟨(b', b''), h⟩, rfl, rfl⟩) hφ's hφ''s hφ'n hφ''n
    G' G'' hg's hg''s hker' hker'' K' K'' (fun n => n.2) (fun n h1 h2 => Subtype.ext (Prod.ext h1 h2))
    (fun m' m'' h => ⟨⟨(m', m''), h⟩, rfl, rfl⟩)

end S_RingHom_Flat_of_pullbackRing_of_isPushout_of_surjective_of_isNilpotent
end P2MW
export P2MW.S_RingHom_Flat_of_pullbackRing_of_isPushout_of_surjective_of_isNilpotent (solution)
