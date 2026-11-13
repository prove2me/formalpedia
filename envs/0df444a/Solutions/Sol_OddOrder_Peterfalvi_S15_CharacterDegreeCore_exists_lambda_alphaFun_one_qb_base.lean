-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.CharacterDegreeCore.exists_lambda_alphaFun_one_qb_base
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:03:19.057436+00:00
-- url     : https://prove2.me/submissions/d140cc1a-1ec4-416c-a61c-fa137f12c395

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Algebra/GaloisRationalInteger.lean
--   OddOrder/GroupTheory/RepresentationTheory/InducedIrreducible.lean
--   OddOrder/Peterfalvi/S09_Building78C.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean
--   OddOrder/Peterfalvi/S15_CharacterDegreeEnginesSSide.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/HSharpChosenBase.lean
--   OddOrder/Peterfalvi/S15_CharacterDegreeEngines.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/LambdaCorrection.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Theorems.Thm_OddOrder_Peterfalvi_S15_H_sharp_hypothesis76_base_cCoeff_int
import Theorems.Thm_OddOrder_Peterfalvi_S15_lambda_tau1_cCoeff_base
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_q_not_dvd_card_H

-- ===== OddOrder/Algebra/GaloisRationalInteger.lean =====
namespace OddOrder.Algebra

open Polynomial IntermediateField

open OddOrder.RepresentationTheory in
/-- **Virtual characters have integer degree**: `φ(1) ∈ ℤ` for `φ ∈ ℤ[Irr G]` — irreducible
characters have `χ(1) = dim ∈ ℕ` (`Representation.char_one`), and the value at `1` is
`ℤ`-linear in `φ`. -/
theorem exists_int_apply_one_of_mem_ZIrr {G : Type*} [Group G] [Finite G]
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) :
    ∃ z : ℤ, φ 1 = (z : ℂ) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨V, _, _, _, ρ, hchar⟩ := IsIrreducibleCharacter.isCharacter hx
      refine ⟨Module.finrank ℂ V, ?_⟩
      rw [show x 1 = ρ.character 1 from congrFun hchar 1, Representation.char_one]
      push_cast
      ring
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
      obtain ⟨za, hza⟩ := ha
      obtain ⟨zb, hzb⟩ := hb
      refine ⟨za + zb, ?_⟩
      rw [ClassFunction.add_apply, hza, hzb]
      push_cast
      ring
  | smul n a _ ha =>
      obtain ⟨za, hza⟩ := ha
      refine ⟨n * za, ?_⟩
      rw [ClassFunction.zsmul_apply, hza, zsmul_eq_mul]
      push_cast
      ring

end OddOrder.Algebra

-- ===== OddOrder/GroupTheory/RepresentationTheory/InducedIrreducible.lean =====
namespace OddOrder.RepresentationTheory

open ClassFunction

variable {G : Type*} [Group G] {H : Subgroup G} [hH : H.Normal]

variable {k : Type*} [CommRing k]

variable [Fintype G] [Invertible (Nat.card H : k)]

section Complex

variable [Fintype H] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card H : ℂ)]

open scoped Classical in
omit [Fintype ↥H] in
omit [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card H : ℂ)] in
/-- **The conjugate-orbit sum is a virtual character**: each summand of the orbit
`{θ^{x⁻¹} : x ∈ G}` is (the coercion of) an irreducible character of `H`
(`IrreducibleCharacter.conjBy`), so the sum lies in `ℤ[Irr H]`.  Together with
`card_smul_restrict_induce_eq_inertia_smul_orbitSum` this makes
`(1/‖Ind θ‖²)·Res_H(Ind θ)` a genuine (ℕ-combination) character — the integrality carrier of
Peterfalvi (13.5.a). -/
theorem orbitSum_mem_ZIrr [Finite H] (θ : IrreducibleCharacter H) :
    (∑ ψ ∈ Finset.univ.image
        (fun x : G => ClassFunction.conjBy x⁻¹ (θ : ClassFunction ↥H ℂ)), ψ) ∈ ZIrr ↥H := by
  refine Submodule.sum_mem _ (fun ψ hψ => ?_)
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hψ
  rw [← IrreducibleCharacter.coe_conjBy]
  exact (IrreducibleCharacter.conjBy x⁻¹ θ).2.mem_ZIrr

end Complex

end OddOrder.RepresentationTheory

-- ===== OddOrder/Peterfalvi/S09_Building78C.lean =====
namespace OddOrder.Peterfalvi.S09.Cert

open OddOrder.RepresentationTheory

variable {L : Type*} [Group L] [Fintype L]

/-- **The chosen-base normalization pins `ζ₀ = Ind_H^L φ₀`.** -/
theorem hypothesis76OfDadeBase_zeta_zero
    {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H71 : Hypothesis71 G A L)
    (hτ : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := L) H71.τ)
    (H : Subgroup G) (hHL : H ≤ L)
    (hHnorm : ∀ (l : ↥L) {h : G}, h ∈ H → (l : G) * h * (l : G)⁻¹ ∈ H)
    (hAH : A = (H : Set G) \ {1})
    (φ₀ :
      haveI : Fintype ↥(H.subgroupOf L) := Fintype.ofFinite _
      IrreducibleCharacter ↥(H.subgroupOf L)) :
    haveI : Fintype ↥(H.subgroupOf L) := Fintype.ofFinite _
    haveI : Invertible (Nat.card ↥(H.subgroupOf L) : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    (hypothesis76OfDadeBase H71 hτ H hHL hHnorm hAH φ₀).zeta 0
      = ClassFunction.induce (H.subgroupOf L) (φ₀ : ClassFunction ↥(H.subgroupOf L) ℂ) := by
  have hKnorm : (H.subgroupOf L).Normal := subgroupOf_normal_of_conj hHnorm
  let : Fintype ↥(H.subgroupOf L) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(H.subgroupOf L) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  unfold hypothesis76OfDadeBase hypothesis76OfFamily
  dsimp only
  rw [Equiv.swap_apply_left]
  have h := Classical.choose_spec ((distinctInducedFamily (H.subgroupOf L)).cover φ₀)
  dsimp only at h
  exact h

end OddOrder.Peterfalvi.S09.Cert

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **TI-subset `ρ`-map collapse** (the `χ = χ^ρ` bridge of Peterfalvi (13.5.a)): when the local
subgroups of a (7.1) datum are trivial (`H(a) = ⊥`, as for the TI-subset Dade construction
`H_sharp_dadeHypothesis`), the `ρ`-map is the identity on the support — `χ^ρ(a) = χ(a)` for `a ∈ A`.
Direct from the `chiRho` definition: the average `|H(a)|⁻¹ ∑_{x∈H(a)} χ(a·x)` over `H(a) = ⊥` is the
single term `χ(a·1) = χ(a)`.  This identifies the (13.5.a) point formula's left side with `χ`
itself,
so the (7.7.a) `chiRho_explicit_formula` decomposition reads off `χ(x)` on `H^#` directly. -/
theorem chiRho_eq_self_of_H_eq_bot {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    (H71 : OddOrder.Peterfalvi.S09.Hypothesis71 G A L)
    (hHbot : ∀ a : {a : G // a ∈ A}, H71.hyp.H a = ⊥)
    (χ : ClassFunction G ℂ) (a : L) (ha : (a : G) ∈ A) :
    H71.chiRho χ a = χ (a : G) := by
  rw [OddOrder.Peterfalvi.S09.Hypothesis71.chiRho, dif_pos ha, hHbot ⟨(a : G), ha⟩,
    Subgroup.card_bot, Nat.cast_one, inv_one, one_mul]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [show ((default : ↥(⊥ : Subgroup G)) : G) = 1 from
    Subgroup.mem_bot.mp (default : ↥(⊥ : Subgroup G)).2, mul_one]

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section GenericAlpha

variable {A : Set G} {L : Subgroup G}

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- Generic (13.5.a) point formula with a distinguished index (`a ≠ 0` form): the `P'`-non-kernel
middle coefficients vanish, leaving the `i₁`-term plus the `P'`-kernel tail. -/
theorem hypothesis76_point_formula [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L)
    (hHbot : ∀ a : {a : G // a ∈ A}, H76.hyp71.hyp.H a = ⊥)
    (P' : Subgroup ↥L) (χ : ClassFunction G ℂ)
    (i₁ : Fin (H76.n + 1)) (hi₁ : 0 < i₁)
    (hi₁ker : ¬ ((P' : Set ↥L) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i₁)))
    (hmiddle : ∀ i : Fin (H76.n + 1), 0 < i → i ≠ i₁ →
      ¬ ((P' : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)) →
      H76.cCoeff χ i = 0)
    (a : ↥L) (ha : (a : G) ∈ A) :
    χ (a : G) =
      (star (H76.cCoeff χ i₁) / H76.zetaNormSq i₁) * H76.zeta i₁ a
      + ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
            (fun i => (P' : Set ↥L) ⊆
              OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)),
          (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a := by
  classical
  have hbase : χ (a : G) = ∑ i ∈ Finset.Ioi (0 : Fin (H76.n + 1)),
      (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a :=
    (chiRho_eq_self_of_H_eq_bot H76.hyp71 hHbot χ a ha).symm.trans
      (OddOrder.Peterfalvi.S09.Hypothesis76.chiRho_explicit_formula H76 χ ha)
  rw [hbase, ← Finset.add_sum_erase _ _ (Finset.mem_Ioi.mpr hi₁)]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Ioi 0).erase i₁)
      (fun i => (P' : Set ↥L) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i))]
  have hmid0 : ∑ i ∈ ((Finset.Ioi 0).erase i₁).filter (fun i =>
      ¬ ((P' : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i))),
      (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    simp only [Finset.mem_filter, Finset.mem_erase] at hi
    rw [hmiddle i (Finset.mem_Ioi.mp hi.1.2) hi.1.1 hi.2, star_zero, zero_div, zero_mul]
  have hi₁notin : i₁ ∉ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
      (fun i => (P' : Set ↥L) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)) := by
    rw [Finset.mem_filter]
    exact fun h => hi₁ker h.2
  rw [hmid0, add_zero, Finset.filter_erase, Finset.erase_eq_self.mpr hi₁notin]

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The generic correction is constant on `P'`. -/
theorem hypothesis76AlphaFun_const [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ) :
    ∀ x ∈ P', hypothesis76AlphaFun H76 P' χ x = hypothesis76AlphaFun H76 P' χ 1 := by
  classical
  intro x hx
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hker := (Finset.mem_filter.mp hi).2
  rw [show H76.zeta i x = H76.zeta i 1 from hker hx]

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- For an abstract (7.6) datum, restriction of a family member to its inducing normal
subgroup is its squared norm times the orbit sum of an inducing irreducible character. -/
theorem hypothesis76_restrict_zeta_eq_orbitSum [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L)
    (j : Fin (H76.n + 1)) :
    ∃ θ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(H76.H.subgroupOf L),
      H76.zeta j = ClassFunction.induce (H76.H.subgroupOf L)
          (θ : ClassFunction ↥(H76.H.subgroupOf L) ℂ) ∧
      (haveI : (H76.H.subgroupOf L).Normal :=
        OddOrder.Peterfalvi.S09.Cert.subgroupOf_normal_of_conj H76.H_normal_in_L
      ClassFunction.restrict (H76.H.subgroupOf L) (H76.zeta j)
        = H76.zetaNormSq j •
            ∑ ψ ∈ Finset.univ.image (fun x : ↥L =>
              ClassFunction.conjBy x⁻¹
                (θ : ClassFunction ↥(H76.H.subgroupOf L) ℂ)), ψ) := by
  classical
  set K : Subgroup ↥L := H76.H.subgroupOf L with hKdef
  have hKnorm : K.Normal :=
    OddOrder.Peterfalvi.S09.Cert.subgroupOf_normal_of_conj H76.H_normal_in_L
  obtain ⟨θ₀, hθ₀⟩ := H76.zeta_induced j
  have hθ : H76.zeta j = ClassFunction.induce K (θ₀ : ClassFunction ↥K ℂ) := by
    rw [hθ₀]
  refine ⟨θ₀, hθ, ?_⟩
  have hK0 : (Nat.card ↥K : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have horbit := OddOrder.RepresentationTheory.card_smul_restrict_induce_eq_inertia_smul_orbitSum
    (G := ↥L) (H := K) (k := ℂ) (θ₀ : ClassFunction ↥K ℂ)
  have hinertia := OddOrder.RepresentationTheory.card_mul_inner_self_induce_eq_card_inertia
    (G := ↥L) (H := K) θ₀
  have hnormval : (Nat.card ↥K : ℂ) * H76.zetaNormSq j
      = (Nat.card ↥(ClassFunction.inertia (G := ↥L)
          (θ₀ : ClassFunction ↥K ℂ)) : ℂ) := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis76.zetaNormSq, hθ]
    exact hinertia
  have hIKnorm : ((Nat.card ↥K : ℂ))⁻¹ *
      (Nat.card ↥(ClassFunction.inertia (G := ↥L)
        (θ₀ : ClassFunction ↥K ℂ)) : ℂ) = H76.zetaNormSq j := by
    rw [← hnormval]
    field_simp
  have h1 : (Nat.card ↥K : ℂ) • ClassFunction.restrict K (H76.zeta j)
      = ((Nat.card ↥(ClassFunction.inertia (G := ↥L)
          (θ₀ : ClassFunction ↥K ℂ)) : ℕ) : ℂ) •
          ∑ ψ ∈ Finset.univ.image
            (fun x : ↥L => ClassFunction.conjBy x⁻¹ (θ₀ : ClassFunction ↥K ℂ)), ψ := by
    rw [← Nat.cast_smul_eq_nsmul (R := ℂ)] at horbit
    rw [hθ]
    exact horbit
  have h2 := congrArg (fun φ => ((Nat.card ↥K : ℂ))⁻¹ • φ) h1
  simp only [smul_smul, inv_mul_cancel₀ hK0, one_smul] at h2
  rw [h2, hIKnorm]

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The normalized restriction `Res ζ_i / ‖ζ_i‖²` of an abstract (7.6) family member is a
virtual character: it is the orbit sum of the inducing irreducible character. -/
theorem hypothesis76_inv_normSq_restrict_zeta_mem_ZIrr [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L)
    (i : Fin (H76.n + 1)) :
    (H76.zetaNormSq i)⁻¹ •
        ClassFunction.restrict (H76.H.subgroupOf L) (H76.zeta i)
      ∈ ZIrr ↥(H76.H.subgroupOf L) := by
  classical
  set K : Subgroup ↥L := H76.H.subgroupOf L with hKdef
  have hKnorm : K.Normal :=
    OddOrder.Peterfalvi.S09.Cert.subgroupOf_normal_of_conj H76.H_normal_in_L
  obtain ⟨θ₀, hθ₀⟩ := H76.zeta_induced i
  have hθ : H76.zeta i = ClassFunction.induce K (θ₀ : ClassFunction ↥K ℂ) := by
    rw [hθ₀]
  have hinertia := OddOrder.RepresentationTheory.card_mul_inner_self_induce_eq_card_inertia
    (G := ↥L) (H := K) θ₀
  have hnormval : (Nat.card ↥K : ℂ) * H76.zetaNormSq i
      = (Nat.card ↥(ClassFunction.inertia (G := ↥L)
          (θ₀ : ClassFunction ↥K ℂ)) : ℂ) := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis76.zetaNormSq, hθ]
    exact hinertia
  have hI0 : (Nat.card ↥(ClassFunction.inertia (G := ↥L)
      (θ₀ : ClassFunction ↥K ℂ)) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hnorm0 : H76.zetaNormSq i ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hnormval
    exact hI0 hnormval.symm
  obtain ⟨θ, -, hres⟩ := hypothesis76_restrict_zeta_eq_orbitSum H76 i
  have hmain : (H76.zetaNormSq i)⁻¹ •
      ClassFunction.restrict K (H76.zeta i)
      = ∑ ψ ∈ Finset.univ.image (fun x : ↥L =>
          ClassFunction.conjBy x⁻¹ (θ : ClassFunction ↥K ℂ)), ψ := by
    rw [hres, smul_smul, inv_mul_cancel₀ hnorm0, one_smul]
  rw [hmain]
  exact OddOrder.RepresentationTheory.orbitSum_mem_ZIrr (G := ↥L) θ

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- If the (7.7.a) coefficients are integral, the generic `P'`-kernel correction restricts
to a virtual character of `H76.H`. -/
theorem hypothesis76AlphaCF_restrict_mem_ZIrr [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ)
    (hc : ∀ i, ∃ z : ℤ, H76.cCoeff χ i = (z : ℂ)) :
    ClassFunction.restrict (H76.H.subgroupOf L) (hypothesis76AlphaCF H76 P' χ)
      ∈ ZIrr ↥(H76.H.subgroupOf L) := by
  classical
  set K : Subgroup ↥L := H76.H.subgroupOf L with hKdef
  have hlin : ClassFunction.restrict K (hypothesis76AlphaCF H76 P' χ)
      = ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
            (fun i => (P' : Set ↥L) ⊆
              OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)),
          (star (H76.cCoeff χ i) / H76.zetaNormSq i) •
            ClassFunction.restrict K (H76.zeta i) := by
    ext x
    rw [ClassFunction.restrict_apply, hypothesis76AlphaCF,
      OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply,
      OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [ClassFunction.smul_apply, ClassFunction.smul_apply, ClassFunction.restrict_apply])
  rw [hlin]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  obtain ⟨z, hz⟩ := hc i
  rw [hz, star_intCast, div_eq_mul_inv, mul_smul, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ z (hypothesis76_inv_normSq_restrict_zeta_mem_ZIrr H76 i)

end GenericAlpha

/-- **Regularity of mixed products**: for `x ∈ W₁ ∖ {1}` and `y ∈ W₂ ∖ {1}` the product `x·y`
avoids `W₁ ∪ W₂` — otherwise one factor would lie in `W₁ ⊓ W₂ = ⊥`.  The membership feed of
`tau3_apply_of_regular` in the (1.10) congruence computations. -/
theorem Hypothesis.mul_notMem_W1_union_W2 (hyp : Hypothesis (G := G))
    {x y : G} (hx : x ∈ hyp.W1) (hy : y ∈ hyp.W2) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    x * y ∉ (hyp.W1 : Set G) ∪ (hyp.W2 : Set G) := by
  rintro (hmem | hmem)
  · have hyW1 : y ∈ hyp.W1 := by
      have h := mul_mem (inv_mem hx) hmem
      rwa [inv_mul_cancel_left] at h
    have hbot : y ∈ hyp.W1 ⊓ hyp.W2 := ⟨hyW1, hy⟩
    rw [hyp.W1_inf_W2_eq_bot, Subgroup.mem_bot] at hbot
    exact hy1 hbot
  · have hxW2 : x ∈ hyp.W2 := by
      have h := mul_mem hmem (inv_mem hy)
      rwa [mul_inv_cancel_right] at h
    have hbot : x ∈ hyp.W1 ⊓ hyp.W2 := ⟨hx, hxW2⟩
    rw [hyp.W1_inf_W2_eq_bot, Subgroup.mem_bot] at hbot
    exact hx1 hbot

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CharacterDegreeEnginesSSide.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **The chosen-base `(S, H^#)` family pins `ζ₀ = Ind_{PC}^S φ₀`.** -/
theorem H_sharp_hypothesis76_base_zeta_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.H.subgroupOf hyp.S)) :
    (H_sharp_hypothesis76_base hG hyp φ₀).zeta 0
      = ClassFunction.induce (hyp.H.subgroupOf hyp.S)
          (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ) := by
  unfold H_sharp_hypothesis76_base
  exact OddOrder.Peterfalvi.S09.Cert.hypothesis76OfDadeBase_zeta_zero _ _ _ _ _ _ _

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseBEndgameSupply/HSharpChosenBase.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

open scoped FiniteInduce in
/-- **Peterfalvi (13.2.d)/(13.3), Core form**: `λ^{τ₁}` is a norm-one virtual
character.  The `P`-nonkernel witness stored in `LambdaClusterData` is exactly the guard needed
by the honest `CharacterDegreeCore` coherence fields. -/
theorem lambda_tau1_norm_one_core [Finite G] {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp) :
    core.tau1S lam.lambda ∈ ZIrr G ∧
      ClassFunction.inner (core.tau1S lam.lambda) (core.tau1S lam.lambda) = 1 ∧
      ClassFunction.inner lam.lambda lam.lambda = 1 := by
  have := hyp.finiteG
  obtain ⟨θ, hθirr, -, hlamEq, x₀, hx₀P, hx₀ker⟩ :=
    lam.lambda_induced_from_PC_linear
  have hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
      Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ) := by
    intro hsub
    exact hx₀ker (hsub (by
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hx₀P))
  have hnorm : ClassFunction.inner lam.lambda lam.lambda = 1 := by
    have h := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨lam.lambda, lam.lambda_irreducible⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
      ⟨lam.lambda, lam.lambda_irreducible⟩
    simpa using h
  refine ⟨?_, ?_, hnorm⟩
  · rw [hlamEq]
    exact core.tau1S_induce_mem_ZIrr θ hθirr hθP
  · rw [hlamEq, core.tau1S_inner_induce θ θ hθirr hθirr hθP hθP, ← hlamEq]
    exact hnorm

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3)/(13.5), chosen-base membership half**: `λ = Ind_H^S θ` occurs
in the (7.6) family based at `φ₀`.  It occurs at a positive index because the chosen base
induction is assumed distinct from `λ`; its `P`-nonkernel witness descends through induction. -/
theorem LambdaClusterData.exists_hSharpFamilyIndex_base [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (lam : LambdaClusterData hyp)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S))
    (hφ₀ne : ClassFunction.induce (hyp.H.subgroupOf hyp.S)
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ) ≠ lam.lambda) :
    ∃ i₁ : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1), 0 < i₁ ∧
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁)) ∧
      (H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁ = lam.lambda := by
  classical
  obtain ⟨θ, hθirr, -, hlamEq, x₀, hx₀P, hx₀ker⟩ :=
    lam.lambda_induced_from_PC_linear
  obtain ⟨i₁, hi₁⟩ :=
    (H_sharp_hypothesis76_base hG hyp φ₀).zeta_family_cover ⟨θ, hθirr⟩
  have heq : (H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁ = lam.lambda := by
    rw [hi₁, hlamEq]
    congr!
  have hker : ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁)) := by
    intro hsub
    refine hx₀ker ?_
    have hx₀S : ((x₀ : ↥hyp.S)) ∈ hyp.P.subgroupOf hyp.S :=
      Subgroup.mem_subgroupOf.mpr hx₀P
    have hmem : ((x₀ : ↥hyp.S)) ∈ OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ) := by
      have h1 := hsub hx₀S
      rw [heq, hlamEq] at h1
      exact h1
    have hbridge := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
      (L := ↥hyp.S) (H := hyp.H.subgroupOf hyp.S) hθirr x₀.2 hmem
    rwa [show (⟨((x₀ : ↥hyp.S)), x₀.2⟩ : ↥(hyp.H.subgroupOf hyp.S)) = x₀ from rfl]
      at hbridge
  refine ⟨i₁, ?_, hker, heq⟩
  rw [Fin.pos_iff_ne_zero]
  intro hzero
  apply hφ₀ne
  rw [← heq, hzero, H_sharp_hypothesis76_base_zeta_zero]

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3)/(13.5), chosen-base distinguished index**: combines family
membership with the guarded (7.7.a) coefficient computation.  This is the honest
`CharacterDegreeCore`/`LambdaClusterData` replacement for the legacy `exists_lambda_index`. -/
theorem CharacterDegreeCore.exists_lambda_index_base [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S))
    (hφ₀P : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)))
    (hφ₀ne : ClassFunction.induce (hyp.H.subgroupOf hyp.S)
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ) ≠ lam.lambda) :
    ∃ i₁ : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1), 0 < i₁ ∧
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁)) ∧
      (H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁ = lam.lambda ∧
      (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff (core.tau1S lam.lambda) i₁ = 1 ∧
      (∀ i : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1), 0 < i → i ≠ i₁ →
        ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i)) →
        (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff (core.tau1S lam.lambda) i = 0) := by
  obtain ⟨i₁, hpos, hker, heq⟩ := lam.exists_hSharpFamilyIndex_base hG φ₀ hφ₀ne
  obtain ⟨hc1, hmid⟩ := lambda_tau1_cCoeff_base hG core lam φ₀ hφ₀P hφ₀ne i₁ heq
  exact ⟨i₁, hpos, hker, heq, hc1, fun i _ hine hiP => hmid i hine hiP⟩

end

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CharacterDegreeEngines.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section GenericAlphaIntegrality

variable {A : Set G} {L : Subgroup G}

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- **Generic (13.5.a) integrality of the correction at `1`**: with integer (7.7.a) coefficients
`c_i ∈ ℤ`, the `P'`-kernel tail `α = hypothesis76AlphaFun` restricts on `K = H76.H` to
`∑ c_i • ((1/‖ζ_i‖²)·Res ζ_i) ∈ ℤ[Irr K]` (each normalized restriction is the conjugate-orbit
character, `hypothesis76_inv_normSq_restrict_zeta_mem_ZIrr`), so `α(1) ∈ ℤ`
(`exists_int_apply_one_of_mem_ZIrr`).  The generic form of the
`H_sharp_alphaCF_restrict_mem_ZIrr`-route to Peterfalvi (13.5) "`α(1) = qb` with `b` an
integer"; instantiated by the `T`-side at `Q_sharp_hypothesis76_base`
(`exists_etaT_alphaFun_one_int_core`). -/
theorem hypothesis76AlphaFun_one_int [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ)
    (hc : ∀ i : Fin (H76.n + 1), ∃ z : ℤ, H76.cCoeff χ i = (z : ℂ)) :
    ∃ α1 : ℤ, hypothesis76AlphaFun H76 P' χ 1 = (α1 : ℂ) := by
  classical
  have hres := hypothesis76AlphaCF_restrict_mem_ZIrr H76 P' χ hc
  obtain ⟨z, hz⟩ := OddOrder.Algebra.exists_int_apply_one_of_mem_ZIrr hres
  refine ⟨z, ?_⟩
  simpa [ClassFunction.restrict_apply] using hz

end GenericAlphaIntegrality

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseBEndgameSupply/LambdaCorrection.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

open scoped FiniteInduce in
/-- **Peterfalvi (13.6), `λ(xy)=0` in chosen-base form**: the chosen family member for
`λ` vanishes off `H`, while the mixed product `x·y` has order divisible by `q` and therefore
cannot lie in `H`. -/
theorem LambdaClusterData.apply_mul_eq_zero_base [Finite G]
    [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (lam : LambdaClusterData hyp)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S))
    (hφ₀ne : ClassFunction.induce (hyp.H.subgroupOf hyp.S)
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ) ≠ lam.lambda)
    {x y : G} (hx : x ∈ hyp.W2) (hy : y ∈ hyp.W1) (hy1 : y ≠ 1)
    (hxyS : x * y ∈ hyp.S) :
    lam.lambda ⟨x * y, hxyS⟩ = 0 := by
  obtain ⟨i₁, -, -, hi₁eq⟩ := lam.exists_hSharpFamilyIndex_base hG φ₀ hφ₀ne
  rw [← hi₁eq]
  refine (H_sharp_hypothesis76_base hG hyp φ₀).zeta_eq_zero_of_not_mem_H i₁ _
    (fun hmem => ?_)
  have hmem' : x * y ∈ hyp.H := by
    rwa [show (H_sharp_hypothesis76_base hG hyp φ₀).H = hyp.H from rfl] at hmem
  have hyq : orderOf y = hyp.q := by
    have h2 : orderOf y = orderOf (⟨y, hy⟩ : ↥hyp.W1) :=
      orderOf_injective hyp.W1.subtype Subtype.coe_injective ⟨y, hy⟩
    have h1 : orderOf (⟨y, hy⟩ : ↥hyp.W1) ∣ hyp.q := by
      rw [hyp.q_eq_card_W1]
      exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime hyp.q_prime).mp h1 with h | h
    · exact absurd (congrArg Subtype.val (orderOf_eq_one_iff.mp h)) hy1
    · rw [h2, h]
  have hxord : orderOf x ∣ hyp.p := by
    have h2 : orderOf x = orderOf (⟨x, hx⟩ : ↥hyp.W2) :=
      orderOf_injective hyp.W2.subtype Subtype.coe_injective ⟨x, hx⟩
    rw [h2, hyp.p_eq_card_W2]
    exact orderOf_dvd_natCard _
  have hcomm : Commute y x := hyp.W1_commutes_W2 y hy x hx
  have hcop : Nat.Coprime (orderOf y) (orderOf x) := by
    rw [hyq]
    exact Nat.Coprime.coprime_dvd_right hxord
      ((Nat.coprime_primes hyp.q_prime hyp.p_prime).mpr (Ne.symm hyp.p_ne_q))
  have hqdvd : hyp.q ∣ orderOf (x * y) := by
    rw [show x * y = y * x from hcomm.eq.symm,
      hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hyq]
    exact dvd_mul_right _ _
  have hdvdH : orderOf (x * y) ∣ Nat.card ↥hyp.H := by
    have h2 : orderOf (x * y) = orderOf (⟨x * y, hmem'⟩ : ↥hyp.H) :=
      orderOf_injective hyp.H.subtype Subtype.coe_injective ⟨x * y, hmem'⟩
    rw [h2]
    exact orderOf_dvd_natCard _
  exact hyp.q_not_dvd_card_H hG (hqdvd.trans hdvdH)

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.6), Core form of `λ^{τ₁}(xy)=0`**: the honest coherence field
gives orthogonality against every `η`-grid member for the nonkernel inducing character of
`λ`; (3.2.d) then gives vanishing on the regular mixed section. -/
theorem lambda_tau1_apply_mul_eq_zero_core [Finite G]
    [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis (G := G)} (core : CharacterDegreeCore hyp)
    (lam : LambdaClusterData hyp)
    {x y : G} (hx : x ∈ hyp.W2) (hy : y ∈ hyp.W1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    core.tau1S lam.lambda (x * y) = 0 := by
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨θ, hθirr, -, hlamEq, x₀, hx₀P, hx₀ker⟩ :=
    lam.lambda_induced_from_PC_linear
  have hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
      Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ) := by
    intro hsub
    exact hx₀ker (hsub (by
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hx₀P))
  have hW1W : hyp.W1 ≤ hyp.W := by
    rw [hyp.W_eq_join]
    exact le_sup_left
  have hW2W : hyp.W2 ≤ hyp.W := by
    rw [hyp.W_eq_join]
    exact le_sup_right
  have hcomm : Commute y x := hyp.W1_commutes_W2 y hy x hx
  have hnot : x * y ∉ (hyp.W1 : Set G) ∪ (hyp.W2 : Set G) := by
    rw [show x * y = y * x from hcomm.eq.symm]
    exact hyp.mul_notMem_W1_union_W2 hy hx hy1 hx1
  refine hyp.vanish_of_inner_eta_eq_zero (core.tau1S lam.lambda) (fun i j => ?_)
    (mul_mem (hW2W hx) (hW1W hy)) hnot
  rw [hlamEq]
  exact core.tau1S_induce_inner_eta i j θ hθirr hθP (hlamEq ▸ lam.lambda_irreducible)

open scoped FiniteInduce in
/-- **Peterfalvi (13.5.a), `α(1) ∈ ℤ` in Core form**: generic correction
integrality applied to the chosen-base family and the integer coefficient supply above. -/
theorem CharacterDegreeCore.exists_lambda_alphaFun_one_int_base [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S)) :
    ∃ m : ℤ, hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
      (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda) 1 = (m : ℂ) := by
  exact hypothesis76AlphaFun_one_int (H_sharp_hypothesis76_base hG hyp φ₀)
    (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda)
    (H_sharp_hypothesis76_base_cCoeff_int hG hyp φ₀
      (lambda_tau1_norm_one_core core lam).1)

open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.6), chosen-base congruence**: the correction value at `1` is an
integer multiple of `q`.  At nonidentity `x ∈ W₂` the point formula identifies the
correction with `λ^{τ₁}(x) - λ(x)`.  Comparing both characters at `x` and `yx`, for
nonidentity `y ∈ W₁`, makes that integer divisible by `1 - ε` for a primitive `q`-th root;
(1.10.b) then gives divisibility by `q`. -/
theorem _root_.solution [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S))
    (hφ₀P : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)))
    (hφ₀ne : ClassFunction.induce (hyp.H.subgroupOf hyp.S)
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ) ≠ lam.lambda) :
    ∃ b : ℤ, hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
      (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda) 1
        = (hyp.q : ℂ) * (b : ℂ) := by
  classical
  obtain ⟨m, hm⟩ := core.exists_lambda_alphaFun_one_int_base hG lam φ₀
  obtain ⟨i₁, hi₁pos, hi₁ker, hi₁eq, hi₁c, hmiddle⟩ :=
    core.exists_lambda_index_base hG lam φ₀ hφ₀P hφ₀ne
  obtain ⟨hZtau, -, hnormLam⟩ := lambda_tau1_norm_one_core core lam
  obtain ⟨x', hx'⟩ : ∃ x' : ↥hyp.W2, x' ≠ 1 := by
    have : Nontrivial ↥hyp.W2 := Finite.one_lt_card_iff_nontrivial.mp
      (by rw [← hyp.p_eq_card_W2]; exact hyp.p_prime.one_lt)
    exact exists_ne 1
  obtain ⟨y', hy'⟩ : ∃ y' : ↥hyp.W1, y' ≠ 1 := by
    have : Nontrivial ↥hyp.W1 := Finite.one_lt_card_iff_nontrivial.mp
      (by rw [← hyp.q_eq_card_W1]; exact hyp.q_prime.one_lt)
    exact exists_ne 1
  have hxW2 : (x' : G) ∈ hyp.W2 := x'.2
  have hyW1 : (y' : G) ∈ hyp.W1 := y'.2
  have hx1 : (x' : G) ≠ 1 := fun h => hx' (Subtype.ext h)
  have hy1 : (y' : G) ≠ 1 := fun h => hy' (Subtype.ext h)
  have hxP : (x' : G) ∈ hyp.P := W2_le_P hG hyp hxW2
  have hPS : hyp.P ≤ hyp.S := by
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  have hxS : (x' : G) ∈ hyp.S := hPS hxP
  have hxH : (x' : G) ∈ hyp.H := (le_sup_left : hyp.P ≤ hyp.H) hxP
  have hWS : hyp.W ≤ hyp.S := by
    rw [hyp.W_eq_inter]
    exact inf_le_left
  have hW1W : hyp.W1 ≤ hyp.W := by
    rw [hyp.W_eq_join]
    exact le_sup_left
  have hyS : (y' : G) ∈ hyp.S := hWS (hW1W hyW1)
  have hns : (H_sharp_hypothesis76_base hG hyp φ₀).zetaNormSq i₁ = 1 := by
    rw [show (H_sharp_hypothesis76_base hG hyp φ₀).zetaNormSq i₁
      = ClassFunction.inner ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁)
        ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁) from rfl, hi₁eq]
    exact hnormLam
  have hpf : core.tau1S lam.lambda (x' : G)
      = lam.lambda ⟨(x' : G), hxS⟩
        + hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
          (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda) ⟨(x' : G), hxS⟩ := by
    have h := hypothesis76_point_formula (H_sharp_hypothesis76_base hG hyp φ₀)
      (fun _ => rfl) (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda)
      i₁ hi₁pos hi₁ker hmiddle ⟨(x' : G), hxS⟩
      (by rw [OddOrder.Peterfalvi.S04.mem_sharp]; exact ⟨hxH, hx1⟩)
    rwa [hi₁c, hns, star_one, div_one, one_mul, hi₁eq] at h
  have hZlam : lam.lambda ∈ ZIrr ↥hyp.S := by
    rw [← hi₁eq]
    obtain ⟨θ, hθ⟩ := (H_sharp_hypothesis76_base hG hyp φ₀).zeta_induced i₁
    rw [hθ]
    exact OddOrder.RepresentationTheory.ClassFunction.induce_mem_ZIrr _ (θ.2.mem_ZIrr)
  have hε : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / hyp.q)) hyp.q :=
    Complex.isPrimitiveRoot_exp hyp.q hyp.q_prime.pos.ne'
  set ε : ℂ := Complex.exp (2 * Real.pi * Complex.I / hyp.q) with hεdef
  have hyq : (y' : G) ^ hyp.q = 1 := by
    have h1 : y' ^ hyp.q = 1 := by
      rw [hyp.q_eq_card_W1]
      exact pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
  have hcommG : Commute (y' : G) (x' : G) :=
    hyp.W1_commutes_W2 _ hyW1 _ hxW2
  obtain ⟨z₂, hz₂int, hz₂⟩ :=
    OddOrder.RepresentationTheory.exists_integral_apply_sub_of_commute hyp.q_prime.pos hε
      hZtau hyq hcommG
  have htau0 : core.tau1S lam.lambda ((y' : G) * (x' : G)) = 0 := by
    rw [hcommG.eq]
    exact lambda_tau1_apply_mul_eq_zero_core core lam hxW2 hyW1 hx1 hy1
  have hyqS : (⟨(y' : G), hyS⟩ : ↥hyp.S) ^ hyp.q = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact hyq
  have hcommS : Commute (⟨(y' : G), hyS⟩ : ↥hyp.S)
      (⟨(x' : G), hxS⟩ : ↥hyp.S) := Subtype.ext hcommG.eq
  obtain ⟨z₁, hz₁int, hz₁⟩ :=
    OddOrder.RepresentationTheory.exists_integral_apply_sub_of_commute hyp.q_prime.pos hε
      hZlam hyqS hcommS
  have hlam0 : lam.lambda
      ((⟨(y' : G), hyS⟩ : ↥hyp.S) * ⟨(x' : G), hxS⟩) = 0 := by
    have hmulS : ((⟨(y' : G), hyS⟩ : ↥hyp.S) * ⟨(x' : G), hxS⟩ : ↥hyp.S)
        = ⟨(x' : G) * (y' : G), mul_mem hxS hyS⟩ := Subtype.ext hcommG.eq
    rw [hmulS]
    exact lam.apply_mul_eq_zero_base hG φ₀ hφ₀ne hxW2 hyW1 hy1 _
  have hconst := hypothesis76AlphaFun_const (H_sharp_hypothesis76_base hG hyp φ₀)
    (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda)
    ⟨(x' : G), hxS⟩ (Subgroup.mem_subgroupOf.mpr hxP)
  have hcast : ((m : ℤ) : ℂ) = (1 - ε) * (z₁ - z₂) := by
    rw [htau0, zero_sub] at hz₂
    rw [hlam0, zero_sub] at hz₁
    have e1 : core.tau1S lam.lambda (x' : G) = -((1 - ε) * z₂) := by
      linear_combination -hz₂
    have e2 : lam.lambda ⟨(x' : G), hxS⟩ = -((1 - ε) * z₁) := by
      linear_combination -hz₁
    have e3 : hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
        (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda) ⟨(x' : G), hxS⟩
          = (1 - ε) * (z₁ - z₂) := by
      have e4 := hpf
      rw [e1, e2] at e4
      linear_combination -e4
    calc
      (m : ℂ) = hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
          (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda) 1 := hm.symm
      _ = hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
          (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda)
            ⟨(x' : G), hxS⟩ := hconst.symm
      _ = (1 - ε) * (z₁ - z₂) := e3
  have hdvd : (hyp.q : ℤ) ∣ m :=
    OddOrder.RepresentationTheory.int_dvd_of_one_sub_primRoot_dvd hyp.q_prime hε
      (hz₁int.sub hz₂int) hcast
  obtain ⟨b, hb⟩ := hdvd
  refine ⟨b, ?_⟩
  calc
    hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
        (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda) 1 = (m : ℂ) := hm
    _ = (((hyp.q : ℤ) * b : ℤ) : ℂ) := by rw [hb]
    _ = (hyp.q : ℂ) * (b : ℂ) := by
      push_cast
      rfl

end

end OddOrder.Peterfalvi.S15
