-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.sylow_normal_of_elementary_normal_P_theorem
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:52:24.15338+00:00
-- url     : https://prove2.me/submissions/7711cef2-078f-4eeb-b996-eebb079998e8

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch03_SplitExtensions/Theorem315.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7A1_JpGL2p.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7A2_NormalPThm75.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Basic
import Definitions.Def_OddOrder_GroupTheory_OpResidual
import Definitions.Def_OddOrder_GroupTheory_OmegaSubgroup
import Definitions.Def_OddOrder_GroupTheory_ThompsonSubgroup
import Definitions.Def_OddOrder_Isaacs_Ch02_Subnormality_Theorem211Wielandt
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Main
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_Main
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A1_JpGL2p
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Theorem315
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_OddOrder_Isaacs_Ch04_prime_dvd_card_of_faithful_iterCommutator_eq_bot
import Theorems.Thm_OddOrder_Isaacs_Ch07_lem73_aux
import Theorems.Thm_OddOrder_Isaacs_Ch07_gl2_pSubgroup_card_le_prime
import Theorems.Thm_OddOrder_Isaacs_Ch07_opCore_eq_bot_of_sylow_card_le_prime_of_not_normal
import Theorems.Thm_OddOrder_Isaacs_Ch07_quotient_two_subgroup_abelian

-- ===== OddOrder/Isaacs/Ch03_SplitExtensions/Theorem315.lean =====
namespace OddOrder.Isaacs.Ch03

open SemidirectProduct

open scoped Pointwise

section

variable {G : Type*} [Group G]

set_option backward.isDefEq.respectTransparency false in
/-- The π-Fitting series is contained in the complementary π-Fitting series.

The successor step maps the quotient by `F_n(π)` onto the quotient by `F_n(π')`;
`O_π` and `O_{π'}` are then carried into the two summands on the complementary side. -/
theorem piFittingSeries_le_compl (π : Set ℕ) (G : Type*) [Group G] [Finite G] :
    ∀ n, piFittingSeries π G n ≤ piFittingSeries {p | p ∉ π} G n := by
  intro n
  induction n with
  | zero =>
      rw [piFittingSeries_zero, piFittingSeries_zero]
  | succ n ih =>
      intro x hx
      set π' : Set ℕ := {p | p ∉ π} with hπ'_def
      set F : Subgroup G := piFittingSeries π G n with hF_def
      set F' : Subgroup G := piFittingSeries π' G n with hF'_def
      have hF_le_F' : F ≤ F' := by
        intro y hy
        exact ih hy
      set Q : G ⧸ F →* G ⧸ F' :=
        QuotientGroup.map F F' (MonoidHom.id G) hF_le_F' with hQ_def
      have hQsurj : Function.Surjective Q := by
        intro y
        rcases QuotientGroup.mk'_surjective F' y with ⟨g, rfl⟩
        exact ⟨QuotientGroup.mk' F g, by simp [Q]⟩
      have hQ_eq : (QuotientGroup.mk' F') x = Q ((QuotientGroup.mk' F) x) := by
        simp [Q]
      rw [piFittingSeries_succ, Subgroup.mem_comap] at hx
      rw [piFittingSeries_succ, Subgroup.mem_comap]
      rw [show ({q | q ∉ π'} : Set ℕ) = π by
        ext q
        simp [π']]
      change (QuotientGroup.mk' F') x ∈
        oPiCore π' (G ⧸ F') ⊔ oPiCore π (G ⧸ F')
      rw [hQ_eq]
      have hxF : (QuotientGroup.mk' F) x ∈
          oPiCore π (G ⧸ F) ⊔ oPiCore π' (G ⧸ F) := by
        simpa [F, π', hπ'_def] using hx
      have hMapSup :
          (oPiCore π (G ⧸ F) ⊔ oPiCore π' (G ⧸ F)).map Q ≤
            oPiCore π' (G ⧸ F') ⊔ oPiCore π (G ⧸ F') := by
        calc
          (oPiCore π (G ⧸ F) ⊔ oPiCore π' (G ⧸ F)).map Q =
              (oPiCore π (G ⧸ F)).map Q ⊔ (oPiCore π' (G ⧸ F)).map Q := by
            rw [Subgroup.map_sup]
          _ ≤ oPiCore π (G ⧸ F') ⊔ oPiCore π' (G ⧸ F') :=
            sup_le_sup (oPiCore.map_le_of_surjective π Q hQsurj)
              (oPiCore.map_le_of_surjective π' Q hQsurj)
          _ = oPiCore π' (G ⧸ F') ⊔ oPiCore π (G ⧸ F') := by
            rw [sup_comm]
      exact hMapSup ⟨_, hxF, rfl⟩

/-- π-separability is symmetric under replacing `π` by its complement. -/
theorem isPiSeparable_compl (π : Set ℕ) (G : Type*) [Group G] [Finite G]
    (hG : IsPiSeparable π G) : IsPiSeparable {p | p ∉ π} G := by
  rcases hG.exists_top with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hle := piFittingSeries_le_compl π G n
  rw [hn] at hle
  exact top_le_iff.mp hle

end

end OddOrder.Isaacs.Ch03

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7A1_JpGL2p.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- Hall-Higman final-step form for Isaacs Thm 7.5.

If the usual `p`-core is trivial, then Hall-Higman can be applied with
`π = {p}'`, so the `p'`-core is self-centralizing. -/
theorem centralizer_oPiCore_compl_le_of_opCore_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp : OddOrder.Isaacs.Ch01.opCore p G = ⊥) :
    Subgroup.centralizer
        (OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G : Set G) ≤
      OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G := by
  classical
  set π' : Set ℕ := {q | q ∉ ({p} : Set ℕ)} with hπ'_def
  have hPiSepCompl : OddOrder.Isaacs.Ch03.IsPiSeparable π' G :=
    OddOrder.Isaacs.Ch03.isPiSeparable_compl ({p} : Set ℕ) G inferInstance
  have hCoreCompl : OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ π'} G = ⊥ := by
    rw [show ({q | q ∉ π'} : Set ℕ) = ({p} : Set ℕ) by
      ext q
      simp [π']]
    rw [OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p]
    exact hOp
  simpa [π', hπ'_def] using
    (OddOrder.Isaacs.Ch03.hall_higman_1_2_3 (G := G) π' hCoreCompl)

/-- A Sylow `p`-subgroup contained in `O_{p'}(G)` is trivial.

This is the final coprime contradiction in Isaacs Thm 7.5 after Hall-Higman puts
`C_G(O_{p'}(G))` inside `O_{p'}(G)`. -/
theorem sylow_eq_bot_of_le_oPiCore_compl
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hP_le :
      (P : Subgroup G) ≤
        OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G) :
    (P : Subgroup G) = ⊥ := by
  have hP_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) (P : Subgroup G) :=
    OddOrder.Isaacs.Ch04.isPiGroup_singleton_of_isPGroup P.isPGroup'
  have hL_pi :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)}
        (OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G) :=
    OddOrder.Isaacs.Ch03.oPiCore.isPiGroup {q | q ∉ ({p} : Set ℕ)}
  have hP_pi' :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)} (P : Subgroup G) :=
    OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le hP_le hL_pi
  have hcop : Nat.Coprime (Nat.card (P : Subgroup G)) (Nat.card (P : Subgroup G)) :=
    OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      Nat.card_pos.ne' Nat.card_pos.ne' hP_pi hP_pi'
  have hInf : (P : Subgroup G) ⊓ (P : Subgroup G) = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  simpa using hInf

/-- **Isaacs Lemma 7.3** ⭐ (GL(2,p) 補題). `p ≠ 2` prime, `P ≤ GL(2, ZMod p)`
p-subgroup が `L ≤ GL(2, ZMod p)` を normalize し, `(|L|, p) = 1` かつ `L` 内の
任意の 2-部分群が abelian ⇒ P は L を centralize.

**Sylow 2-subgroup abelian の hereditary form**: 仮説 `hL2abelian` は「L 内の任意の
2-部分群が abelian」と述べる. Isaacs 原本の「L の Sylow 2 が abelian」と同値だが
(任意の 2-部分群は Sylow 2 に含まれ, abelian 群の部分群は abelian), 帰納法
(IH 適用時の継承) で便利な形.

**proof** (詳細はファイル上部 §7A docstring 参照): `|L|`-strong induction を
[`lem73_aux`](#) で展開. P-invariant Sylow 取得, proper commutator branch, `q = 2`
cyclicity branch, odd `q` orbit-count branch をすべて同補助定理内で処理する. -/
theorem gl2_pSubgroup_centralizes_of_normalizes
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P L : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))}
    (hPp : IsPGroup p P) (hPnorm : P ≤ Subgroup.normalizer (L : Set _))
    (hLcop : ¬ p ∣ Nat.card L)
    (hL2abelian : ∀ S : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)),
      S ≤ L → IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x) :
    P ≤ Subgroup.centralizer (L : Set _) :=
  lem73_aux hp2 hPp (Nat.card L) hPnorm hLcop hL2abelian le_rfl

end OddOrder.Isaacs.Ch07

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7A2_NormalPThm75.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- Reinterpret automorphisms of an abelian group of exponent dividing `p` as `ZMod p`-linear
automorphisms of its additive type.

The `ZMod p`-module structure is supplied explicitly because in Thm 7.5 it is built from the
elementary-abelian hypothesis on a quotient. -/
noncomputable def mulAutZModGeneralLinearEquiv
    (V : Type*) [Group V] [IsMulCommutative V] (p : ℕ)
    [Module (ZMod p) (Additive V)] :
    MulAut V ≃* LinearMap.GeneralLinearGroup (ZMod p) (Additive V) where
  toFun φ :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Additive V)).symm
      ((MulEquiv.toAdditive φ).toLinearEquiv
        (fun c x => ZMod.map_smul (MulEquiv.toAdditive φ).toAddMonoidHom c x))
  invFun φ :=
    (MulEquiv.toAdditive (G := V) (H := V)).symm φ.toLinearEquiv.toAddEquiv
  left_inv φ := by
    ext x
    rfl
  right_inv φ := by
    ext x
    rfl
  map_mul' φ ψ := by
    ext x
    rfl

/-- A chosen `ZMod p`-basis of size `2` identifies `Aut(V)` with `GL(2,p)`.

This is the explicit bridge needed to feed the action on an elementary-abelian quotient into
Isaacs Lemma 7.3 (`gl2_pSubgroup_centralizes_of_normalizes`). -/
noncomputable def mulAutGLTwoEquivOfBasis
    (V : Type*) [Group V] [IsMulCommutative V] (p : ℕ)
    [Module (ZMod p) (Additive V)]
    (b : Module.Basis (Fin 2) (ZMod p) (Additive V)) :
    MulAut V ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod p) :=
  (mulAutZModGeneralLinearEquiv V p).trans (Matrix.GeneralLinearGroup.toLin' b).symm

/-- The `ZMod p` scalar-torsion condition supplied by an elementary-abelian multiplicative group.
-/
private lemma additive_nsmul_eq_zero_of_isElementaryAbelian
    {V : Type*} [Group V] {p : ℕ}
    (hV : OddOrder.GroupTheory.IsElementaryAbelian p V) :
    ∀ x : Additive V, (p : ℕ) • x = 0 := by
  intro x
  apply Additive.toMul.injective
  show (p • x).toMul = (0 : Additive V).toMul
  rw [toMul_nsmul, toMul_zero]
  exact hV.pow_eq_one x.toMul

/-- An elementary-abelian group of order `p^2` has automorphism group identified with `GL(2,p)`.

The basis is chosen noncomputably from the finite `ZMod p`-vector-space structure on the
additive type. -/
noncomputable def mulAutGLTwoEquivOfIsElementaryAbelianCard
    (V : Type*) [Group V] [Finite V] {p : ℕ} [Fact p.Prime]
    (hV : OddOrder.GroupTheory.IsElementaryAbelian p V) (hcard : Nat.card V = p ^ 2) :
    MulAut V ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod p) := by
  classical
  haveI : IsMulCommutative V := ⟨⟨hV.comm⟩⟩
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype (Additive V) := Fintype.ofEquiv V Additive.ofMul
  haveI : Module (ZMod p) (Additive V) :=
    AddCommGroup.zmodModule (additive_nsmul_eq_zero_of_isElementaryAbelian hV)
  have hfinrank : Module.finrank (ZMod p) (Additive V) = 2 := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
    calc
      p ^ Module.finrank (ZMod p) (Additive V)
          = Fintype.card (ZMod p) ^ Module.finrank (ZMod p) (Additive V) := by
              rw [ZMod.card]
      _ = Fintype.card (Additive V) := (Module.card_eq_pow_finrank
              (K := ZMod p) (V := Additive V)).symm
      _ = Nat.card (Additive V) := by rw [Nat.card_eq_fintype_card]
      _ = Nat.card V := (Nat.card_congr Additive.ofMul).symm
      _ = p ^ 2 := hcard
  let b0 := Module.Free.chooseBasis (ZMod p) (Additive V)
  have hidx_card : Fintype.card (Module.Free.ChooseBasisIndex (ZMod p) (Additive V)) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex]
    exact hfinrank
  let eidx : Module.Free.ChooseBasisIndex (ZMod p) (Additive V) ≃ Fin 2 :=
    Fintype.equivOfCardEq (by rw [hidx_card, Fintype.card_fin])
  exact mulAutGLTwoEquivOfBasis V p (b0.reindex eidx)

/-- Transport Isaacs Lemma 7.3 back from `GL(2,p)` to automorphism subgroups.

The hypotheses are stated for the images of `P` and `L` under a chosen identification
`Aut(V) ≃ GL(2,p)`.  The conclusion is the original centralizer statement in `Aut(V)`. -/
theorem mulAut_centralizes_of_gl2_image_hypotheses
    {V : Type*} [Group V] {p : ℕ} [Fact p.Prime]
    (e : MulAut V ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) (hp2 : p ≠ 2)
    {P L : Subgroup (MulAut V)}
    (hPp : IsPGroup p (P.map e.toMonoidHom))
    (hPnorm : P.map e.toMonoidHom ≤
      Subgroup.normalizer ((L.map e.toMonoidHom) : Set _))
    (hLcop : ¬ p ∣ Nat.card (L.map e.toMonoidHom))
    (hL2abelian :
      ∀ S : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)),
        S ≤ L.map e.toMonoidHom → IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x) :
    P ≤ Subgroup.centralizer (L : Set _) := by
  have hGL : P.map e.toMonoidHom ≤ Subgroup.centralizer ((L.map e.toMonoidHom) : Set _) :=
    gl2_pSubgroup_centralizes_of_normalizes hp2 hPp hPnorm hLcop hL2abelian
  intro x hxP
  rw [Subgroup.mem_centralizer_iff]
  intro y hyL
  have hxGL : e x ∈ P.map e.toMonoidHom :=
    Subgroup.mem_map_of_mem e.toMonoidHom hxP
  have hyGL : e y ∈ L.map e.toMonoidHom :=
    Subgroup.mem_map_of_mem e.toMonoidHom hyL
  have hcommGL : e y * e x = e x * e y :=
    (Subgroup.mem_centralizer_iff.mp (hGL hxGL)) (e y) hyGL
  apply e.injective
  simpa [map_mul] using hcommGL

/-- Pull a centralizer conclusion back through an injective homomorphism.

This is the faithful-action transfer used in Isaacs Thm 7.5: once the images of `P` and
`L` centralize inside `Aut(V)`, the original subgroups centralize in the acting group. -/
theorem le_centralizer_of_map_le_centralizer_of_injective
    {A B : Type*} [Group A] [Group B] {φ : A →* B} (hφ : Function.Injective φ)
    {P L : Subgroup A}
    (hmap : P.map φ ≤ Subgroup.centralizer ((L.map φ) : Set B)) :
    P ≤ Subgroup.centralizer (L : Set A) := by
  intro x hxP
  rw [Subgroup.mem_centralizer_iff]
  intro y hyL
  have hxmap : φ x ∈ P.map φ := Subgroup.mem_map_of_mem φ hxP
  have hymap : φ y ∈ L.map φ := Subgroup.mem_map_of_mem φ hyL
  have hcomm : φ y * φ x = φ x * φ y :=
    (Subgroup.mem_centralizer_iff.mp (hmap hxmap)) (φ y) hymap
  apply hφ
  simpa [map_mul] using hcomm

/-- Isaacs Thm 7.5 GL(2,p) centralizer step for a faithful action.

This combines the `Aut(V) ≃ GL(2,p)` bridge with the injective-action transfer, so the
conclusion is directly in the acting group rather than in `MulAut V`. -/
theorem subgroup_centralizes_of_mulAut_gl2_image_hypotheses
    {A V : Type*} [Group A] [Group V] {p : ℕ} [Fact p.Prime]
    {φ : A →* MulAut V} (hφ : Function.Injective φ)
    (e : MulAut V ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) (hp2 : p ≠ 2)
    {P L : Subgroup A}
    (hPp : IsPGroup p ((P.map φ).map e.toMonoidHom))
    (hPnorm : (P.map φ).map e.toMonoidHom ≤
      Subgroup.normalizer (((L.map φ).map e.toMonoidHom) : Set _))
    (hLcop : ¬ p ∣ Nat.card ((L.map φ).map e.toMonoidHom))
    (hL2abelian :
      ∀ S : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)),
        S ≤ (L.map φ).map e.toMonoidHom → IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x) :
    P ≤ Subgroup.centralizer (L : Set A) :=
  le_centralizer_of_map_le_centralizer_of_injective hφ
    (mulAut_centralizes_of_gl2_image_hypotheses e hp2 hPp hPnorm hLcop hL2abelian)

/-- A `p'`-subgroup remains `p'` after an injective homomorphic image. -/
theorem not_dvd_card_map_of_isPiGroup_compl_of_injective
    {A B : Type*} [Group A] [Group B] [Finite A] {p : ℕ} [Fact p.Prime]
    {φ : A →* B} (hφ : Function.Injective φ) {L : Subgroup A}
    (hLpi :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)} L) :
    ¬ p ∣ Nat.card (L.map φ) := by
  intro hp_dvd
  have hcard : Nat.card (L.map φ) = Nat.card L :=
    Nat.card_congr (Subgroup.equivMapOfInjective L φ hφ).symm.toEquiv
  have hp_L_pf : p ∈ (Nat.card L).primeFactors := by
    exact Nat.mem_primeFactors.mpr ⟨Fact.out, by rwa [hcard] at hp_dvd, Nat.card_pos.ne'⟩
  exact hLpi p hp_L_pf (by simp)

/-- Transfer the hereditary "all 2-subgroups are abelian" hypothesis through an injective
image.

This is the hypothesis adapter for Lemma 7.3 in the reduced Thm 7.5 branch: a 2-subgroup
inside the image of `L` is pulled back to a 2-subgroup of the original group, where the
global Sylow-2-abelian hypothesis is available. -/
theorem two_subgroup_abelian_of_le_map_of_injective
    {A B : Type*} [Group A] [Group B] {φ : A →* B} (hφ : Function.Injective φ)
    (h2abelian : ∀ S : Subgroup A, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    {L : Subgroup A} {T : Subgroup B}
    (hT_le : T ≤ L.map φ) (hT2 : IsPGroup 2 T) :
    ∀ x y : ↥T, x * y = y * x := by
  let H : Subgroup A := T.comap φ
  let ψ : H →* T := {
    toFun a := ⟨φ a, a.property⟩
    map_one' := by ext; simp
    map_mul' a b := by ext; simp }
  have hψ_inj : Function.Injective ψ := by
    intro a b hab
    apply Subtype.ext
    apply hφ
    exact congrArg Subtype.val hab
  have hH2 : IsPGroup 2 H := hT2.of_injective ψ hψ_inj
  have hHcomm := h2abelian H hH2
  intro x y
  obtain ⟨a, haL, hax⟩ := hT_le x.property
  obtain ⟨b, hbL, hby⟩ := hT_le y.property
  have haT : φ a ∈ T := by rw [hax]; exact x.property
  have hbT : φ b ∈ T := by rw [hby]; exact y.property
  have hab : a * b = b * a :=
    congrArg Subtype.val (hHcomm ⟨a, haT⟩ ⟨b, hbT⟩)
  apply Subtype.ext
  change (x : B) * (y : B) = (y : B) * (x : B)
  rw [← hax, ← hby, ← map_mul, hab, map_mul]

/-- Reduced elementary-abelian branch of Isaacs Thm 7.5.

After the minimal-counterexample quotient reduction has replaced `V` by a faithful
elementary-abelian group of order `p²`, the `GL(2,p)` embedding, Lemma 7.3, and
Hall-Higman force the chosen Sylow `p`-subgroup to be normal. -/
theorem sylow_normal_of_elementaryAbelian_card_prime_sq_of_faithful
    {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
    {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hp2 : p ≠ 2)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    {φ : G →* MulAut V} (hφ : Function.Injective φ)
    (hVelem : OddOrder.GroupTheory.IsElementaryAbelian p V)
    (hVcard : Nat.card V = p ^ 2) (P : Sylow p G) :
    (P : Subgroup G).Normal := by
  by_contra hP_not_normal
  let e := mulAutGLTwoEquivOfIsElementaryAbelianCard V (p := p) hVelem hVcard
  have hφGL : Function.Injective (e.toMonoidHom.comp φ) := by
    intro a b hab
    exact hφ (e.injective hab)
  have hPp : IsPGroup p (((P : Subgroup G).map φ).map e.toMonoidHom) :=
    (P.isPGroup'.map φ).map e.toMonoidHom
  have hP_image_card_le :
      Nat.card (((P : Subgroup G).map φ).map e.toMonoidHom) ≤ p :=
    gl2_pSubgroup_card_le_prime _ hPp
  have hP_map_phi_card :
      Nat.card ((P : Subgroup G).map φ) = Nat.card (P : Subgroup G) :=
    Nat.card_congr
      (Subgroup.equivMapOfInjective (P : Subgroup G) φ hφ).symm.toEquiv
  have hP_map_GL_card :
      Nat.card (((P : Subgroup G).map φ).map e.toMonoidHom) =
        Nat.card ((P : Subgroup G).map φ) :=
    Nat.card_congr
      (Subgroup.equivMapOfInjective ((P : Subgroup G).map φ) e.toMonoidHom
        e.injective).symm.toEquiv
  have hP_card_le : Nat.card (P : Subgroup G) ≤ p := by
    rwa [hP_map_GL_card, hP_map_phi_card] at hP_image_card_le
  have hOp : OddOrder.Isaacs.Ch01.opCore p G = ⊥ :=
    opCore_eq_bot_of_sylow_card_le_prime_of_not_normal P hP_card_le hP_not_normal
  set L : Subgroup G := OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G with hL_def
  have hLnormal : L.Normal := by
    dsimp [L]
    infer_instance
  have hPnorm :
      ((P : Subgroup G).map φ).map e.toMonoidHom ≤
        Subgroup.normalizer (((L.map φ).map e.toMonoidHom) : Set _) := by
    have hcomp :
        (P : Subgroup G).map (e.toMonoidHom.comp φ) ≤
          Subgroup.normalizer ((L.map (e.toMonoidHom.comp φ)) : Set _) :=
      map_le_normalizer_map_of_normal
        (φ := e.toMonoidHom.comp φ) (P := (P : Subgroup G)) (L := L)
    simpa [Subgroup.map_map] using hcomp
  have hLpi :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)} L := by
    simpa [L, hL_def] using
      (OddOrder.Isaacs.Ch03.oPiCore.isPiGroup
        (G := G) {q | q ∉ ({p} : Set ℕ)})
  have hLcop :
      ¬ p ∣ Nat.card ((L.map φ).map e.toMonoidHom) := by
    have hcomp :
        ¬ p ∣ Nat.card (L.map (e.toMonoidHom.comp φ)) :=
      not_dvd_card_map_of_isPiGroup_compl_of_injective
        (p := p) (φ := e.toMonoidHom.comp φ) hφGL hLpi
    simpa [Subgroup.map_map] using hcomp
  have hL2abelian :
      ∀ S : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)),
        S ≤ (L.map φ).map e.toMonoidHom → IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x := by
    intro S hS_le hS2
    have hS_le_comp : S ≤ L.map (e.toMonoidHom.comp φ) := by
      simpa [Subgroup.map_map] using hS_le
    exact two_subgroup_abelian_of_le_map_of_injective hφGL h2abelian hS_le_comp hS2
  have hPcentral : (P : Subgroup G) ≤ Subgroup.centralizer (L : Set G) :=
    subgroup_centralizes_of_mulAut_gl2_image_hypotheses
      (φ := φ) hφ e hp2 hPp hPnorm hLcop hL2abelian
  have hcentral_le_L : Subgroup.centralizer (L : Set G) ≤ L := by
    simpa [L, hL_def] using
      (centralizer_oPiCore_compl_le_of_opCore_eq_bot (G := G) (p := p) hOp)
  have hP_le_L : (P : Subgroup G) ≤ L := hPcentral.trans hcentral_le_L
  have hP_bot : (P : Subgroup G) = ⊥ :=
    sylow_eq_bot_of_le_oPiCore_compl P (by simpa [L, hL_def] using hP_le_L)
  apply hP_not_normal
  rw [hP_bot]
  infer_instance

/-- Cyclic branch of Isaacs Thm 7.5: a group acting faithfully by automorphisms on a cyclic
group is commutative, hence every acting subgroup is normal.

The proof uses mathlib's explicit `Aut(V) ≃ (ZMod |V|)ˣ` identification for cyclic groups.
This is the formal version of the book step "if `V` is cyclic, then `Aut(V)` is abelian, so
`G` is abelian and `P` is normal." -/
theorem subgroup_normal_of_injective_mulAut_of_isCyclic
    {A V : Type*} [Group A] [Group V] [IsCyclic V]
    {φ : A →* MulAut V} (hφ : Function.Injective φ) (P : Subgroup A) :
    P.Normal := by
  let e := IsCyclic.mulAutMulEquiv V
  let : CommGroup (MulAut V) := e.toMonoidHom.commGroupOfInjective e.injective
  let : CommGroup A := φ.commGroupOfInjective hφ
  infer_instance

/-- A subgroup of a finite `p`-group with index at most `p` is normal. -/
theorem normal_of_isPGroup_index_le_prime
    {V : Type*} [Group V] [Finite V] {p : ℕ} [Fact p.Prime]
    (hV : IsPGroup p V) {H : Subgroup V} (hH : H.index ≤ p) :
    H.Normal := by
  have : H.FiniteIndex := inferInstance
  obtain ⟨n, hn⟩ := hV.index H
  rcases n with _ | n
  · exact Subgroup.normal_of_index_eq_one (by simpa using hn)
  rcases n with _ | n
  · have hindex : H.index = p := by simpa using hn
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hV
    have hm_ne_zero : m ≠ 0 := by
      intro hm_zero
      have hcard_one : Nat.card V = 1 := by
        rw [hm, hm_zero, pow_zero]
      have hdiv : p ∣ 1 := by
        rw [← hcard_one, ← hindex]
        exact H.index_dvd_card
      exact (Fact.out : Nat.Prime p).not_dvd_one hdiv
    have hmin : (Nat.card V).minFac = p := by
      rw [hm, (Fact.out : Nat.Prime p).pow_minFac hm_ne_zero]
    exact Subgroup.normal_of_index_eq_minFac_card (by rw [hindex, hmin])
  · have hpow_le : p ^ 2 ≤ p := by
      have hpow : p ^ 2 ≤ p ^ (n + 2) := by
        exact Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : Nat.Prime p)) (by omega)
      have hindex_le : p ^ (n + 2) ≤ p := by
        simpa [hn, pow_succ] using hH
      exact hpow.trans hindex_le
    have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    nlinarith [hpow_le, hp_two]

/-- The index of the fixed subgroup for `P ⊔ Q` is bounded by the product of the two
individual fixed-subgroup indices. -/
theorem actionCentralizer_sup_index_le {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) (P Q : Subgroup A) :
    (actionCentralizer φ (P ⊔ Q)).index ≤
      (actionCentralizer φ P).index * (actionCentralizer φ Q).index := by
  rw [actionCentralizer_sup]
  exact Subgroup.index_inf_le

/-- A packaged version of `actionCentralizer_sup_index_le` with external bounds. -/
theorem actionCentralizer_sup_index_le_of_le {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) (P Q : Subgroup A) {m n : ℕ}
    (hP : (actionCentralizer φ P).index ≤ m)
    (hQ : (actionCentralizer φ Q).index ≤ n) :
    (actionCentralizer φ (P ⊔ Q)).index ≤ m * n :=
  (actionCentralizer_sup_index_le φ P Q).trans (Nat.mul_le_mul hP hQ)

/-- The Theorem 7.5 index estimate: if both fixed subgroups have index at most `p`, then
the fixed subgroup of `P ⊔ Q` has index at most `p^2`. -/
theorem actionCentralizer_sup_index_le_sq {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) (P Q : Subgroup A) {p : ℕ}
    (hP : (actionCentralizer φ P).index ≤ p)
    (hQ : (actionCentralizer φ Q).index ≤ p) :
    (actionCentralizer φ (P ⊔ Q)).index ≤ p ^ 2 := by
  calc
    (actionCentralizer φ (P ⊔ Q)).index ≤ p * p :=
      actionCentralizer_sup_index_le_of_le φ P Q hP hQ
    _ = p ^ 2 := by ring

/-- The same Theorem 7.5 index estimate, in the `U = C_V(P) ∩ C_V(Q)` form used in
the book proof. -/
theorem actionCentralizer_inf_index_le_sq {A V : Type*} [Group A] [Group V]
    (φ : A →* MulAut V) (P Q : Subgroup A) {p : ℕ}
    (hP : (actionCentralizer φ P).index ≤ p)
    (hQ : (actionCentralizer φ Q).index ≤ p) :
    (actionCentralizer φ P ⊓ actionCentralizer φ Q).index ≤ p ^ 2 := by
  rw [← actionCentralizer_sup]
  exact actionCentralizer_sup_index_le_sq φ P Q hP hQ

/-- If `V` is a finite `p`-group and both `C_V(P)` and `C_V(Q)` have index at most `p`,
then `C_V(P) ∩ C_V(Q)` is normal in `V`.

This supplies the `U ⊴ V` bridge before the quotient `V/U` in Isaacs Thm 7.5. -/
theorem actionCentralizer_inf_normal_of_index_le_prime
    {A V : Type*} [Group A] [Group V] [Finite V]
    {p : ℕ} [Fact p.Prime] (hV : IsPGroup p V)
    {φ : A →* MulAut V} {P Q : Subgroup A}
    (hP : (actionCentralizer φ P).index ≤ p)
    (hQ : (actionCentralizer φ Q).index ≤ p) :
    (actionCentralizer φ P ⊓ actionCentralizer φ Q).Normal := by
  have hPN : (actionCentralizer φ P).Normal :=
    normal_of_isPGroup_index_le_prime hV hP
  have hQN : (actionCentralizer φ Q).Normal :=
    normal_of_isPGroup_index_le_prime hV hQ
  let : (actionCentralizer φ P).Normal := hPN
  let : (actionCentralizer φ Q).Normal := hQN
  infer_instance

/-- Quotient-cardinality form of the Theorem 7.5 index estimate:
if both `C_V(P)` and `C_V(Q)` have index at most `p`, then
`|V / (C_V(P) ∩ C_V(Q))| ≤ p²`. -/
theorem quotient_card_le_prime_sq_of_actionCentralizer_inf
    {A V : Type*} [Group A] [Group V] (φ : A →* MulAut V) (P Q : Subgroup A)
    {p : ℕ} [(actionCentralizer φ P ⊓ actionCentralizer φ Q).Normal]
    (hP : (actionCentralizer φ P).index ≤ p)
    (hQ : (actionCentralizer φ Q).index ≤ p) :
    Nat.card (V ⧸ (actionCentralizer φ P ⊓ actionCentralizer φ Q)) ≤ p ^ 2 := by
  simpa [Subgroup.index_eq_card] using actionCentralizer_inf_index_le_sq φ P Q hP hQ

/-- The Theorem 7.5 quotient reduction: in the `U = C_V(P) ∩ C_V(Q)` quotient, if the
quotient is noncyclic then it is elementary abelian of order `p²`.

This packages the index estimate with the small-order noncyclic `p`-group bridge from
`OddOrder.GroupTheory.ElementaryAbelian`. -/
theorem quotient_isElementaryAbelian_card_prime_sq_of_actionCentralizer_inf_not_isCyclic
    {A V : Type*} [Group A] [Group V] [Finite V]
    {p : ℕ} [Fact p.Prime] (φ : A →* MulAut V) (P Q : Subgroup A)
    [(actionCentralizer φ P ⊓ actionCentralizer φ Q).Normal]
    (hV : IsPGroup p V)
    (hP : (actionCentralizer φ P).index ≤ p)
    (hQ : (actionCentralizer φ Q).index ≤ p)
    (hNotCyclic : ¬ IsCyclic (V ⧸ (actionCentralizer φ P ⊓ actionCentralizer φ Q))) :
    OddOrder.GroupTheory.IsElementaryAbelian p
        (V ⧸ (actionCentralizer φ P ⊓ actionCentralizer φ Q)) ∧
      Nat.card (V ⧸ (actionCentralizer φ P ⊓ actionCentralizer φ Q)) = p ^ 2 :=
  IsPGroup.isElementaryAbelian_card_prime_sq_of_card_le_prime_sq_of_not_isCyclic
    (hV.to_quotient (actionCentralizer φ P ⊓ actionCentralizer φ Q))
    (quotient_card_le_prime_sq_of_actionCentralizer_inf φ P Q hP hQ)
    hNotCyclic

/-- The action of `A/K` on `V/U` is faithful by construction. -/
theorem quotientActionFaithfulHom_injective {A V : Type*} [Group A] [Group V]
    {φ : A →* MulAut V} {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) :
    Function.Injective (quotientActionFaithfulHom φ hU) := by
  dsimp [quotientActionFaithfulHom, quotientActionKernel]
  exact QuotientGroup.kerLift_injective (quotientActionHom φ hU)

/-- If `K` lies in the kernel of the quotient action on `V/U`, then `[V,K] ≤ U`.

This is the formal quotient-kernel bridge used in Isaacs Thm 7.5 after passing from
`V` to `V/U`. -/
theorem actionCommutator_le_of_le_quotientActionKernel
    {A V : Type*} [Group A] [Group V] {φ : A →* MulAut V}
    {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U)
    {K : Subgroup A} (hK : K ≤ quotientActionKernel φ hU) :
    OddOrder.Isaacs.Ch04.actionCommutator (φ.comp K.subtype) ≤ U := by
  rw [OddOrder.Isaacs.Ch04.actionCommutator_le_iff_left]
  intro k v
  have hk : quotientActionHom φ hU (k : A) = 1 := by
    change (k : A) ∈ (quotientActionHom φ hU).ker
    exact hK k.property
  have hq :
      quotientActionHom φ hU (k : A) (QuotientGroup.mk' U v) =
        (1 : MulAut (V ⧸ U)) (QuotientGroup.mk' U v) := by
    rw [hk]
  rw [quotientActionHom_apply_mk'] at hq
  simp only [MulAut.one_apply] at hq
  change (((φ (k : A)) v : V) : V ⧸ U) = (v : V ⧸ U) at hq
  rw [QuotientGroup.eq] at hq
  simpa [mul_inv_rev] using U.inv_mem hq

/-- If `U` is fixed pointwise by the whole acting group and `K` acts trivially on `V/U`,
then `K` acts trivially on `[V,K]`.

This is the Ch07-side formalization of the Thm 7.5 step `[V,K,K] = 1`. -/
theorem actionCommutator_le_fixedPoints_of_le_quotientActionKernel
    {A V : Type*} [Group A] [Group V] {φ : A →* MulAut V}
    {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U)
    (hU_top : U ≤ actionCentralizer φ (⊤ : Subgroup A))
    {K : Subgroup A} (hK : K ≤ quotientActionKernel φ hU) :
    OddOrder.Isaacs.Ch04.actionCommutator (φ.comp K.subtype) ≤
      Subgroup.fixedPointsOfMulAut (φ.comp K.subtype) := by
  intro v hv k
  have hvU : v ∈ U := actionCommutator_le_of_le_quotientActionKernel hU hK hv
  exact (mem_actionCentralizer_top.mp (hU_top hvU)) (k : A)

/-- Kernel-specialized form: the kernel `K` of the quotient action satisfies `[V,K,K]=1`
when `U` is fixed pointwise by the original action. -/
theorem actionCommutator_quotientActionKernel_le_fixedPoints
    {A V : Type*} [Group A] [Group V] {φ : A →* MulAut V}
    {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U)
    (hU_top : U ≤ actionCentralizer φ (⊤ : Subgroup A)) :
    OddOrder.Isaacs.Ch04.actionCommutator
        (φ.comp (quotientActionKernel φ hU).subtype) ≤
      Subgroup.fixedPointsOfMulAut (φ.comp (quotientActionKernel φ hU).subtype) :=
  actionCommutator_le_fixedPoints_of_le_quotientActionKernel hU hU_top le_rfl

/-- Semidirect-product bridge: the condition `[V,A,A]=1`, expressed as
`[V,A] ≤ C_V(A)`, gives the length-two iterated commutator vanishing used by the Ch.4
faithful-action prime-divisor theorem. -/
theorem iterCommutator_inl_inr_two_eq_bot_of_actionCommutator_le_fixedPoints
    {A V : Type*} [Group A] [Group V] (φ : A →* MulAut V)
    (h_triv : OddOrder.Isaacs.Ch04.actionCommutator φ ≤
      Subgroup.fixedPointsOfMulAut φ) :
    OddOrder.Isaacs.Ch04.iterCommutator
        (SemidirectProduct.inl : V →* V ⋊[φ] A).range
        (SemidirectProduct.inr : A →* V ⋊[φ] A).range 2 = ⊥ := by
  rw [OddOrder.Isaacs.Ch04.iterCommutator_succ,
    OddOrder.Isaacs.Ch04.iterCommutator_succ,
    OddOrder.Isaacs.Ch04.iterCommutator_zero]
  rw [← OddOrder.Isaacs.Ch04.actionCommutator_map_inl φ]
  rw [eq_bot_iff, Subgroup.commutator_le]
  rintro _ ⟨v, hv, rfl⟩ _ ⟨a, rfl⟩
  rw [SemidirectProduct.commutator_inl_inr, Subgroup.mem_bot]
  have h_fix : (φ a) v = v := h_triv hv a
  rw [show (φ a) v⁻¹ = ((φ a) v)⁻¹ from map_inv (φ a) v,
    h_fix, mul_inv_cancel]
  exact map_one _

/-- If a faithful finite group action on a finite `p`-group has quotient-action kernel `K`
with `[V,K,K]=1`, then `K` is a `p`-group.

This packages the Ch.4 faithful iterated-commutator theorem for the kernel arising in
Isaacs Thm 7.5. -/
theorem quotientActionKernel_isPGroup_of_faithful_of_isPGroup
    {A V : Type*} [Group A] [Group V] [Finite A] [Finite V]
    {p : ℕ} [Fact p.Prime] {φ : A →* MulAut V}
    {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U)
    (hφ : Function.Injective φ) (hV : IsPGroup p V)
    (hU_top : U ≤ actionCentralizer φ (⊤ : Subgroup A)) :
    IsPGroup p (quotientActionKernel φ hU) := by
  set K : Subgroup A := quotientActionKernel φ hU with hK_def
  let ψ : K →* MulAut V := φ.comp K.subtype
  have hψ : Function.Injective ψ := by
    intro x y hxy
    apply Subtype.ext
    exact hφ hxy
  have h_triv : OddOrder.Isaacs.Ch04.actionCommutator ψ ≤
      Subgroup.fixedPointsOfMulAut ψ := by
    simpa [ψ, K, hK_def] using
      actionCommutator_quotientActionKernel_le_fixedPoints hU hU_top
  have h_iter :
      OddOrder.Isaacs.Ch04.iterCommutator
          (SemidirectProduct.inl : V →* V ⋊[ψ] K).range
          (SemidirectProduct.inr : K →* V ⋊[ψ] K).range 2 = ⊥ :=
    iterCommutator_inl_inr_two_eq_bot_of_actionCommutator_le_fixedPoints ψ h_triv
  have hK_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ)
      (⊤ : Subgroup K) := by
    intro q hq
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hq_dvd_K : q ∣ Nat.card K := by
      simpa [Subgroup.card_top] using Nat.dvd_of_mem_primeFactors hq
    have hq_dvd_V : q ∣ Nat.card V :=
      OddOrder.Isaacs.Ch04.prime_dvd_card_of_faithful_iterCommutator_eq_bot
        ψ hψ (m := 2) (by norm_num) h_iter hq_prime hq_dvd_K
    have hV_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ)
        (⊤ : Subgroup V) :=
      OddOrder.Isaacs.Ch04.isPiGroup_singleton_of_isPGroup
        (G := V) (H := (⊤ : Subgroup V)) (hV.to_subgroup _)
    have hqV : q ∈ (Nat.card (⊤ : Subgroup V)).primeFactors := by
      rw [Subgroup.card_top]
      exact Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd_V, Nat.card_pos.ne'⟩
    exact hV_pi q hqV
  have hK_top_p : IsPGroup p (⊤ : Subgroup K) :=
    OddOrder.Isaacs.Ch04.isPGroup_of_isPiGroup_singleton
      (G := K) (H := (⊤ : Subgroup K)) hK_pi
  simpa [K, hK_def] using hK_top_p.of_equiv Subgroup.topEquiv

/-- The `U = C_V(P) ∩ C_V(Q)` specialization of
`quotientActionKernel_isPGroup_of_faithful_of_isPGroup`.

Normality of this fixed-point intersection is kept as an explicit hypothesis; in the book proof
this is the preceding `U ⊴ V` step. -/
theorem actionCentralizer_inf_quotientActionKernel_isPGroup_of_sup_eq_top
    {A V : Type*} [Group A] [Group V] [Finite A] [Finite V]
    {p : ℕ} [Fact p.Prime] {φ : A →* MulAut V}
    {P Q : Subgroup A}
    [hU_normal : (actionCentralizer φ P ⊓ actionCentralizer φ Q).Normal]
    (hPQ : P ⊔ Q = ⊤) (hφ : Function.Injective φ) (hV : IsPGroup p V) :
    IsPGroup p (quotientActionKernel φ
      (actionCentralizer_inf_isAInvariant_of_sup_eq_top (φ := φ) hPQ)) := by
  apply quotientActionKernel_isPGroup_of_faithful_of_isPGroup
  · exact hφ
  · exact hV
  · rw [← actionCentralizer_sup, hPQ]

/-- Normality of the image of `P` in `G/K` pulls back to normality of `P`, provided
`K ≤ P`.

This is the quotient-correspondence bridge used in Isaacs Thm 7.5 after proving the image
of a Sylow subgroup is normal in the faithful quotient action. -/
theorem normal_of_quotient_image_normal_of_le
    {G : Type*} [Group G] {K P : Subgroup G} [K.Normal]
    (hKP : K ≤ P)
    (hPbar : (P.map (QuotientGroup.mk' K)).Normal) :
    P.Normal := by
  have hcomap :
      Subgroup.comap (QuotientGroup.mk' K) (P.map (QuotientGroup.mk' K)) = P := by
    rw [QuotientGroup.comap_map_mk']
    exact sup_eq_right.mpr hKP
  rw [← hcomap]
  exact hPbar.comap (QuotientGroup.mk' K)

/-- A normal `p`-subgroup is contained in every Sylow `p`-subgroup. -/
private theorem normal_isPGroup_le_sylow
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)]
    {K : Subgroup G} [K.Normal] (hK : IsPGroup p K) (P : Sylow p G) :
    K ≤ (P : Subgroup G) :=
  (OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hK).trans
    (OddOrder.Isaacs.Ch01.opCore_le P)

/-- If a normal `p`-subgroup `K` is quotiented out, normality of the image of a Sylow
`p`-subgroup pulls back to normality of the original Sylow subgroup. -/
theorem sylow_normal_of_quotient_image_normal_of_normal_isPGroup
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)]
    (P : Sylow p G) {K : Subgroup G} [K.Normal] (hK : IsPGroup p K)
    (hPbar : (((P : Subgroup G).map (QuotientGroup.mk' K))).Normal) :
    P.Normal :=
  normal_of_quotient_image_normal_of_le (normal_isPGroup_le_sylow hK P) hPbar

/-- Elementary-abelian quotient branch of Isaacs Thm 7.5 after passing to the faithful
action of `G/K` on `V/U`.

This is the quotient-condition bundle for the reduced theorem:
`p`-separability descends by Ch03, the `2`-subgroup abelian hypothesis descends by
`quotient_two_subgroup_abelian`, and faithfulness is by construction of
`quotientActionFaithfulHom`. -/
theorem quotient_sylow_normal_of_elementaryAbelian_card_prime_sq_of_actionKernel
    {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
    {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hp2 : p ≠ 2)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    {φ : G →* MulAut V} {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U)
    (hVelem : OddOrder.GroupTheory.IsElementaryAbelian p (V ⧸ U))
    (hVcard : Nat.card (V ⧸ U) = p ^ 2) (P : Sylow p G) :
    (((P.mapSurjective (QuotientGroup.mk'_surjective (quotientActionKernel φ hU)) :
          Sylow p (G ⧸ quotientActionKernel φ hU)) : Subgroup
          (G ⧸ quotientActionKernel φ hU))).Normal := by
  have hSepQuot :
      OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ)
        (G ⧸ quotientActionKernel φ hU) :=
    OddOrder.Isaacs.Ch03.quotient_isPiSeparable
      ({p} : Set ℕ) G (quotientActionKernel φ hU)
  exact sylow_normal_of_elementaryAbelian_card_prime_sq_of_faithful
    (G := G ⧸ quotientActionKernel φ hU) (V := V ⧸ U) (p := p)
    hp2 (quotient_two_subgroup_abelian h2abelian)
    (φ := quotientActionFaithfulHom φ hU)
    (quotientActionFaithfulHom_injective hU) hVelem hVcard
    (P.mapSurjective (QuotientGroup.mk'_surjective (quotientActionKernel φ hU)))

/-- Contradiction form of the elementary-abelian quotient branch of Isaacs Thm 7.5.

If the action kernel `K` is a normal `p`-subgroup and the faithful quotient action on `V/U`
has elementary-abelian order `p²`, the reduced branch proves the image of `P` normal in
`G/K`; pulling normality back contradicts a counterexample assumption upstairs. -/
theorem false_of_quotient_elementaryAbelian_card_prime_sq_of_sylow_not_normal
    {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
    {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hp2 : p ≠ 2)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    {φ : G →* MulAut V} {U : Subgroup V} [U.Normal]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U)
    (hK : IsPGroup p (quotientActionKernel φ hU))
    (hVelem : OddOrder.GroupTheory.IsElementaryAbelian p (V ⧸ U))
    (hVcard : Nat.card (V ⧸ U) = p ^ 2) (P : Sylow p G)
    (hP_not_normal : ¬ (P : Subgroup G).Normal) : False :=
  hP_not_normal
    (sylow_normal_of_quotient_image_normal_of_normal_isPGroup
      (G := G) (p := p) P (K := quotientActionKernel φ hU) hK
      (quotient_sylow_normal_of_elementaryAbelian_card_prime_sq_of_actionKernel
        hp2 h2abelian hU hVelem hVcard P))

/-- Cyclic quotient branch of Isaacs Thm 7.5 after passing to the faithful action of
`G/K` on `V/U`.

If `V/U` is cyclic, then `Aut(V/U)` is abelian. Since the quotient action is faithful,
`G/K` is abelian, so the image of any Sylow subgroup is normal. -/
theorem quotient_sylow_normal_of_isCyclic_of_actionKernel
    {G V : Type*} [Group G] [Finite G] [Group V]
    {p : ℕ} [Fact p.Prime]
    {φ : G →* MulAut V} {U : Subgroup V} [U.Normal] [IsCyclic (V ⧸ U)]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U) (P : Sylow p G) :
    (((P.mapSurjective (QuotientGroup.mk'_surjective (quotientActionKernel φ hU)) :
          Sylow p (G ⧸ quotientActionKernel φ hU)) : Subgroup
          (G ⧸ quotientActionKernel φ hU))).Normal :=
  subgroup_normal_of_injective_mulAut_of_isCyclic
    (A := G ⧸ quotientActionKernel φ hU) (V := V ⧸ U)
    (φ := quotientActionFaithfulHom φ hU)
    (quotientActionFaithfulHom_injective hU)
    ((P.mapSurjective (QuotientGroup.mk'_surjective (quotientActionKernel φ hU)) :
      Sylow p (G ⧸ quotientActionKernel φ hU)) : Subgroup
        (G ⧸ quotientActionKernel φ hU))

/-- Contradiction form of the cyclic quotient branch of Isaacs Thm 7.5. -/
theorem false_of_quotient_isCyclic_of_sylow_not_normal
    {G V : Type*} [Group G] [Finite G] [Group V]
    {p : ℕ} [Fact p.Prime]
    {φ : G →* MulAut V} {U : Subgroup V} [U.Normal] [IsCyclic (V ⧸ U)]
    (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U)
    (hK : IsPGroup p (quotientActionKernel φ hU)) (P : Sylow p G)
    (hP_not_normal : ¬ (P : Subgroup G).Normal) : False :=
  hP_not_normal
    (sylow_normal_of_quotient_image_normal_of_normal_isPGroup
      (G := G) (p := p) P (K := quotientActionKernel φ hU) hK
      (quotient_sylow_normal_of_isCyclic_of_actionKernel hU P))

/-- Descend the action-centralizer index hypothesis from `G` to a subgroup `H`.

For every Sylow `R : Sylow p H`, the image `R.map H.subtype` is a `p`-subgroup of `G`,
hence contained in some Sylow `S : Sylow p G`.  Antitonicity of `actionCentralizer`
then gives `(actionCentralizer (φ.comp H.subtype) R).index ≤ (actionCentralizer φ S).index`,
which is bounded by `p` by the upstairs hypothesis. -/
private theorem actionCentralizer_comp_subtype_index_le_of_globalHypothesis
    {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
    {p : ℕ} [Fact p.Prime]
    {φ : G →* MulAut V}
    (h_centralizer_index :
      ∀ (P : Sylow p G), (actionCentralizer φ (P : Subgroup G)).index ≤ p)
    (H : Subgroup G) (R : Sylow p H) :
    (actionCentralizer (φ.comp H.subtype) (R : Subgroup H)).index ≤ p := by
  -- The image of `R` in `G` is a `p`-subgroup of `G`.
  have hRG_p : IsPGroup p ((R : Subgroup H).map H.subtype) :=
    R.isPGroup'.map H.subtype
  obtain ⟨S, hS_le⟩ := hRG_p.exists_le_sylow
  have h_eq :
      actionCentralizer (φ.comp H.subtype) (R : Subgroup H) =
        actionCentralizer φ ((R : Subgroup H).map H.subtype) := by
    ext v
    simp only [mem_actionCentralizer]
    constructor
    · intro hv g
      rcases g.property with ⟨r, hrR, hrg⟩
      have hfix := hv ⟨r, hrR⟩
      change (φ ((r : H) : G)) v = v at hfix
      rw [show (g : G) = ((r : H) : G) from hrg.symm]
      exact hfix
    · intro hv r
      have hr_mem : ((r : H) : G) ∈ (R : Subgroup H).map H.subtype :=
        Subgroup.mem_map_of_mem H.subtype r.property
      exact hv ⟨((r : H) : G), hr_mem⟩
  rw [h_eq]
  -- Antitonicity in P direction: bigger P → smaller actionCentralizer.
  have h_anti :
      actionCentralizer φ (S : Subgroup G) ≤
        actionCentralizer φ ((R : Subgroup H).map H.subtype) :=
    actionCentralizer_antitone hS_le
  exact (Subgroup.index_antitone h_anti).trans (h_centralizer_index S)

/-- **Isaacs Thm 7.5** (normal-P theorem).

If `G` is `p`-solvable with `p ≠ 2`, every `2`-subgroup of `G` is abelian, `G` acts
faithfully on a finite `p`-group `V`, and `|V : C_V(P)| ≤ p` for every Sylow `p`-subgroup
`P`, then every Sylow `p`-subgroup of `G` is normal.

The proof is by strong induction on `|G|`.  If `G` has a unique Sylow `p`-subgroup, the
result is trivial.  Otherwise pick two distinct Sylows `P, Q`.  If `⟨P, Q⟩ ≠ G`, descend
to the subgroup `⟨P, Q⟩` and apply the induction hypothesis there.  When `⟨P, Q⟩ = G`,
the action-centralizer index estimate forces `|V/U| ≤ p²` for `U := C_V(P) ∩ C_V(Q)`, and
splitting on whether `V/U` is cyclic produces the contradiction via the elementary-abelian
or cyclic branch built up above. -/
theorem _root_.solution
    {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
    {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hp2 : p ≠ 2)
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    {φ : G →* MulAut V} (hφ : Function.Injective φ)
    (hV : IsPGroup p V)
    (h_centralizer_index :
      ∀ (P : Sylow p G), (actionCentralizer φ (P : Subgroup G)).index ≤ p)
    (P : Sylow p G) : (P : Subgroup G).Normal := by
  classical
  -- Strong induction on |G|, using an explicit motive.
  let motive : ℕ → Prop := fun n =>
    ∀ (G : Type _) [Group G] [Finite G] [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
      (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
      (φ : G →* MulAut V) (_hφ : Function.Injective φ)
      (_h_centralizer_index :
        ∀ (P : Sylow p G), (actionCentralizer φ (P : Subgroup G)).index ≤ p)
      (P : Sylow p G), Nat.card G = n → (P : Subgroup G).Normal
  suffices hmain : motive (Nat.card G) by
    exact hmain G h2abelian φ hφ h_centralizer_index P rfl
  refine Nat.strong_induction_on (Nat.card G) ?_
  intro n ih G _ _ _ h2abelian φ hφ h_centralizer_index P hcard
  by_contra hP_not_normal
  -- Sylows are not subsingleton, else `P` would be normal.
  have hNotSub : ¬ Subsingleton (Sylow p G) := by
    intro hSub
    exact hP_not_normal (Sylow.normal_of_subsingleton P)
  -- Pick Q ≠ P.
  have : Nontrivial (Sylow p G) := not_subsingleton_iff_nontrivial.mp hNotSub
  obtain ⟨Q, hQP⟩ := exists_ne P
  -- We have Q ≠ P; consider H := ⟨P, Q⟩ = P ⊔ Q.
  set H : Subgroup G := (P : Subgroup G) ⊔ (Q : Subgroup G) with hH_def
  by_cases hH_top : H = ⊤
  · -- §7A closing branch: H = ⊤.
    -- U := C_V(P) ∩ C_V(Q) is normal, A-invariant, with |V/U| ≤ p².
    have hPidx : (actionCentralizer φ (P : Subgroup G)).index ≤ p :=
      h_centralizer_index P
    have hQidx : (actionCentralizer φ (Q : Subgroup G)).index ≤ p :=
      h_centralizer_index Q
    have hU_normal :
        (actionCentralizer φ (P : Subgroup G) ⊓
            actionCentralizer φ (Q : Subgroup G)).Normal :=
      actionCentralizer_inf_normal_of_index_le_prime hV hPidx hQidx
    have hPQ_top : (P : Subgroup G) ⊔ (Q : Subgroup G) = ⊤ := by
      simpa [H, hH_def] using hH_top
    have hU_invariant :
        OddOrder.Isaacs.Ch03.IsAInvariant φ
          (actionCentralizer φ (P : Subgroup G) ⊓
            actionCentralizer φ (Q : Subgroup G)) :=
      actionCentralizer_inf_isAInvariant_of_sup_eq_top hPQ_top
    -- The action kernel K on V/U is a p-group.
    have hK_p :
        IsPGroup p (quotientActionKernel φ hU_invariant) := by
      have := actionCentralizer_inf_quotientActionKernel_isPGroup_of_sup_eq_top
        (φ := φ) (P := (P : Subgroup G)) (Q := (Q : Subgroup G))
        hPQ_top hφ hV
      simpa using this
    -- Split on cyclicity of V/U.
    by_cases hVU_cyclic :
        IsCyclic (V ⧸ (actionCentralizer φ (P : Subgroup G) ⊓
          actionCentralizer φ (Q : Subgroup G)))
    · -- Cyclic branch.
      have := hVU_cyclic
      exact
        false_of_quotient_isCyclic_of_sylow_not_normal
          (φ := φ) hU_invariant hK_p P hP_not_normal
    · -- Non-cyclic ⇒ elementary abelian of order p².
      obtain ⟨hVU_elem, hVU_card⟩ :=
        quotient_isElementaryAbelian_card_prime_sq_of_actionCentralizer_inf_not_isCyclic
          φ (P : Subgroup G) (Q : Subgroup G) hV hPidx hQidx hVU_cyclic
      exact
        false_of_quotient_elementaryAbelian_card_prime_sq_of_sylow_not_normal
          (φ := φ) hp2 h2abelian hU_invariant hK_p hVU_elem hVU_card P hP_not_normal
  · -- Generation reduction: descend to H = ⟨P, Q⟩ ≠ ⊤.
    have hHidx_gt : 1 < H.index :=
      Subgroup.one_lt_index_of_ne_top hH_top
    have hH_card_lt : Nat.card H < Nat.card G := by
      have hmul : Nat.card H * H.index = Nat.card G := Subgroup.card_mul_index H
      have hcard_pos : 0 < Nat.card H := Nat.card_pos
      calc
        Nat.card H = Nat.card H * 1 := (mul_one _).symm
        _ < Nat.card H * H.index := (Nat.mul_lt_mul_left hcard_pos).mpr hHidx_gt
        _ = Nat.card G := hmul
    -- P and Q sit inside H.
    have hP_le_H : (P : Subgroup G) ≤ H := by simp [H]
    have hQ_le_H : (Q : Subgroup G) ≤ H := by simp [H]
    -- View P as a Sylow of H.
    let P' : Sylow p H := P.subtype hP_le_H
    -- Descend hypothesis (i): IsPiSeparable on H.
    have : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) H :=
      OddOrder.Isaacs.Ch03.Subgroup.isPiSeparable_of_isPiSeparable ({p} : Set ℕ) H
    -- Descend hypothesis (iii): 2-subgroup abelian.
    have h2abelian' :
        ∀ S : Subgroup H, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x := by
      intro S hS2
      have hSG2 : IsPGroup 2 (S.map H.subtype) := hS2.map H.subtype
      have hSGcomm := h2abelian (S.map H.subtype) hSG2
      intro a b
      apply Subtype.ext
      apply Subtype.ext
      let ag : ↥(S.map H.subtype) :=
        ⟨((a : H) : G), ⟨(a : H), a.property, rfl⟩⟩
      let bg : ↥(S.map H.subtype) :=
        ⟨((b : H) : G), ⟨(b : H), b.property, rfl⟩⟩
      have h := congrArg (fun z : ↥(S.map H.subtype) => (z : G)) (hSGcomm ag bg)
      simpa using h
    -- Descend hypothesis (iv): φ ∘ H.subtype is injective.
    have hφ' : Function.Injective (φ.comp H.subtype) := by
      intro a b hab
      apply Subtype.ext
      exact hφ hab
    -- Descend hypothesis (v).
    have h_centralizer_index' :
        ∀ (R : Sylow p H), (actionCentralizer (φ.comp H.subtype)
          (R : Subgroup H)).index ≤ p :=
      fun R =>
        actionCentralizer_comp_subtype_index_le_of_globalHypothesis
          (φ := φ) h_centralizer_index H R
    have hcard_lt : Nat.card H < n := by rw [← hcard]; exact hH_card_lt
    -- Apply IH to H.
    have hP'_normal : (P' : Subgroup H).Normal :=
      ih (Nat.card H) hcard_lt H h2abelian' (φ.comp H.subtype) hφ'
        h_centralizer_index' P' rfl
    -- The same IH applied to Q.
    let Q' : Sylow p H := Q.subtype hQ_le_H
    have hQ'_normal : (Q' : Subgroup H).Normal :=
      ih (Nat.card H) hcard_lt H h2abelian' (φ.comp H.subtype) hφ'
        h_centralizer_index' Q' rfl
    -- In `H`, both `P'` and `Q'` are normal Sylow p-subgroups, hence equal.
    have hPQ_eq : P' = Q' := by
      have := Sylow.unique_of_normal P' hP'_normal
      exact Subsingleton.elim P' Q'
    have hPQsubgroup_eq : (P : Subgroup G) = (Q : Subgroup G) := by
      have h := congrArg (fun R : Sylow p H => (R : Subgroup H)) hPQ_eq
      simp only [P', Q', Sylow.coe_subtype] at h
      have hPmap :
          ((P : Subgroup G).subgroupOf H).map H.subtype = (P : Subgroup G) := by
        rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, H.range_subtype]
        exact inf_eq_right.mpr hP_le_H
      have hQmap :
          ((Q : Subgroup G).subgroupOf H).map H.subtype = (Q : Subgroup G) := by
        rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, H.range_subtype]
        exact inf_eq_right.mpr hQ_le_H
      have := congrArg (fun K : Subgroup H => K.map H.subtype) h
      simpa [hPmap, hQmap] using this
    exact hQP (Sylow.ext hPQsubgroup_eq.symm)

end OddOrder.Isaacs.Ch07
