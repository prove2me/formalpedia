-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.Hypothesis.exists_caseB_data_eta10_T_core
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:01:38.917323+00:00
-- url     : https://prove2.me/submissions/c9896556-ea64-4df9-a2be-a474e5fd4c39

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Algebra/GaloisRationalInteger.lean
--   OddOrder/GroupTheory/RepresentationTheory/InducedIrreducible.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean
--   OddOrder/Peterfalvi/S15_CharacterDegreeEngines.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/Eta10Correction.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_exists_qSharpBase_orthogonal_eta10_core
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_exists_muT_index_core_of_base_condition
import Theorems.Thm_OddOrder_Peterfalvi_S15_hypothesis76_zeta_inner_alphaFun_eq_zero

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

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Self inner-sum as a real squared-norm sum** (general `ClassFunction` identity).

For any class function `α : H → ℂ`, the unscaled self inner sum `Σ_g α(g)·conj(α(g))` equals the
real sum of squared norms `Σ_g ‖α(g)‖²` cast to `ℂ`.  This is the bridge between the abstract
`ClassFunction.innerSum`/`inner` API and the concrete `Σ |α(g)|²` quantities of Peterfalvi's norm
estimates (13.6)–(13.10); combined with `Σ_{H#} = Σ_H − |α(1)|²` it converts every Dade-norm
inequality into an elementary squared-norm sum.  A general fact for any finite group `H`. -/
theorem innerSum_self_eq_sum_normSq {H : Type*} [Group H] [Fintype H]
    (α : ClassFunction H ℂ) :
    ClassFunction.innerSum α α = ((∑ g : H, ‖α g‖ ^ 2 : ℝ) : ℂ) := by
  rw [ClassFunction.innerSum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← starRingEnd_apply, RCLike.mul_conj]
  norm_cast

/-- **Parseval identity for class functions** (general): `Σ_g ‖α(g)‖² = |H| · ⟨α, α⟩`.

The full squared-norm sum equals `|H|` times the normalized self inner product `⟨α,α⟩ = ‖α‖²`.
Combined with `Σ_{H#} = Σ_H − ‖α(1)‖²` this is precisely the Parseval relation `s + d² = |H|·n`
consumed by `caseB_eta_norm_core` (the (13.7) core): it lets the cascade read off `s = ∑_{H#}|α|²`
from the abstract inner product `n = ⟨α,α⟩`.  Immediate from `innerSum_self_eq_sum_normSq` and
`ClassFunction.card_mul_inner`. -/
theorem sum_normSq_eq_card_mul_inner {H : Type*} [Group H] [Fintype H]
    [Invertible (Nat.card H : ℂ)] (α : ClassFunction H ℂ) :
    ((∑ g : H, ‖α g‖ ^ 2 : ℝ) : ℂ) = (Nat.card H : ℂ) * ClassFunction.inner α α := by
  rw [← innerSum_self_eq_sum_normSq, ClassFunction.card_mul_inner]

/-- **Inflation norm lower bound — the carrier-free core of Peterfalvi (13.5.c)**.

If a function `α : H → ℂ` is constant on a finite subgroup `P ≤ H` (equal to `α 1` on all of `P`)
— the situation when `P` lies in the kernel of every irreducible constituent of `α`, so `α` is
inflated from `H/P` — then its squared-norm sum over the nonidentity elements `H#` is at least
`(|P| − 1)·|α(1)|²`.  This is exactly Peterfalvi (13.5.c)
`∑_{x∈H#} |α(x)|² ≥ (|P|−1)·α(1)²` in self-contained, carrier-free form: it uses only that `α`
equals `α 1` on `P` and that the remaining squared norms are nonnegative (one sums over the
nonidentity elements of `P` alone, `P# ⊆ H#`).  Specialises to `H = ↥hyp.H`, `P = S_F` in the full
(13.5) TI-subset calculation. -/
theorem sum_normSq_erase_one_ge_of_const_on_subgroup {H : Type*} [Group H] [Fintype H]
    (P : Subgroup H) (α : H → ℂ) (hP : ∀ x ∈ P, α x = α 1) :
    ((Nat.card ↥P : ℝ) - 1) * ‖α 1‖ ^ 2 ≤ (∑ x : H, ‖α x‖ ^ 2) - ‖α 1‖ ^ 2 := by
  classical
  -- card of the subgroup as a filtered finset.
  have hcard : (Finset.univ.filter (· ∈ P)).card = Nat.card ↥P := by
    rw [Nat.card_eq_fintype_card]; simp [Fintype.card_subtype]
  -- the `P`-sum equals `|P|·‖α 1‖²` (every term is `‖α 1‖²`).
  have hPsum : ∑ x ∈ Finset.univ.filter (· ∈ P), ‖α x‖ ^ 2 = (Nat.card ↥P : ℝ) * ‖α 1‖ ^ 2 := by
    rw [Finset.sum_congr rfl (g := fun _ => ‖α 1‖ ^ 2)
        (fun x hx => by rw [hP x (Finset.mem_filter.mp hx).2]),
      Finset.sum_const, nsmul_eq_mul, hcard]
  -- the `P`-sum is at most the full sum (squared norms nonnegative).
  have hmono : ∑ x ∈ Finset.univ.filter (· ∈ P), ‖α x‖ ^ 2 ≤ ∑ x : H, ‖α x‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => by positivity)
  have hkey : (Nat.card ↥P : ℝ) * ‖α 1‖ ^ 2 ≤ ∑ x : H, ‖α x‖ ^ 2 := hPsum ▸ hmono
  have hexp : ((Nat.card ↥P : ℝ) - 1) * ‖α 1‖ ^ 2
      = (Nat.card ↥P : ℝ) * ‖α 1‖ ^ 2 - ‖α 1‖ ^ 2 := by ring
  rw [hexp]; linarith [hkey]

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
/-- The generic correction vanishes off `H76.H`. -/
theorem hypothesis76AlphaFun_eq_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ) :
    ∀ x : ↥L, (x : G) ∉ H76.H → hypothesis76AlphaFun H76 P' χ x = 0 := by
  classical
  intro x hx
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [H76.zeta_eq_zero_of_not_mem_H i x hx, mul_zero]

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- Generic (13.5.c): the inflation bound for the correction over any sharp `Finset` of the
`H76.H`-members (instance-free `F`-interface). -/
theorem hypothesis76AlphaFun_inflation [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ)
    (F : Finset ↥L) (hF : ∀ x : ↥L, x ∈ F ↔ ((x : G) ∈ H76.H ∧ x ≠ 1))
    (_hP'H : ∀ x : ↥L, x ∈ P' → (x : G) ∈ H76.H) :
    ((Nat.card ↥P' : ℝ) - 1) * ‖hypothesis76AlphaFun H76 P' χ 1‖ ^ 2
      ≤ ∑ x ∈ F, ‖hypothesis76AlphaFun H76 P' χ x‖ ^ 2 := by
  classical
  set α := hypothesis76AlphaFun H76 P' χ with hαdef
  have hcore := sum_normSq_erase_one_ge_of_const_on_subgroup P' α
    (hypothesis76AlphaFun_const H76 P' χ)
  -- The ambient `↥L`-sum equals the `F`-sum plus the identity term (α vanishes off `H76.H`).
  have hFeq : F = (Finset.univ.filter (fun x : ↥L => (x : G) ∈ H76.H)).erase 1 := by
    ext x
    rw [hF, Finset.mem_erase, Finset.mem_filter]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, Finset.mem_univ _, h1⟩, fun ⟨h2, _, h1⟩ => ⟨h1, h2⟩⟩
  have hsupp : ∑ x : ↥L, ‖α x‖ ^ 2
      = ∑ x ∈ Finset.univ.filter (fun x : ↥L => (x : G) ∈ H76.H), ‖α x‖ ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x : ↥L => (x : G) ∈ H76.H)]
    have h0 : ∑ x ∈ Finset.univ.filter (fun x : ↥L => ¬ (x : G) ∈ H76.H), ‖α x‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero (fun x hx => ?_)
      rw [hαdef, hypothesis76AlphaFun_eq_zero H76 P' χ x (Finset.mem_filter.mp hx).2]
      simp
    rw [h0, add_zero]
  have h1mem : (1 : ↥L) ∈ Finset.univ.filter (fun x : ↥L => (x : G) ∈ H76.H) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [OneMemClass.coe_one]
    exact H76.H.one_mem
  have hsharp : ∑ x ∈ F, ‖α x‖ ^ 2
      = (∑ x ∈ Finset.univ.filter (fun x : ↥L => (x : G) ∈ H76.H), ‖α x‖ ^ 2)
        - ‖α 1‖ ^ 2 := by
    rw [hFeq, ← Finset.add_sum_erase _ _ h1mem]
    ring
  rw [hsharp, ← hsupp]
  exact hcore

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

open scoped FiniteInduce in
/-- **`η₁₀` is a virtual character of `G`** — real content of the 3002-threaded grid:
`η₁₀ = τ₃(ω₁₀)` (`eta_eq_tau_omega`), `ω₁₀ ∈ ZIrr W` (`omega_mem_ZIrr`), and `τ₃` preserves
virtual characters (`tau3_mem_ZIrr`). -/
theorem Hypothesis.eta10_mem_ZIrr [Finite G] (hyp : Hypothesis (G := G)) :
    hyp.eta10 ∈ ZIrr G := by
  rw [Hypothesis.eta10, hyp.eta_eq_tau_omega]
  exact hyp.tau3_mem_ZIrr _ (hyp.omega_mem_ZIrr _ _)

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

open scoped Classical in
open scoped FiniteInduce in
/-- **The `T`-side (7.7.a) coefficients of a virtual character are integers** (mirror of
`H_sharp_cCoeff_int` over the chosen-base `(T, Q^#)` family): `c_i = ⟨τψ_i, χ⟩` with both
arguments virtual characters — `ψ_i = ζ_i − d_i ζ_0` has `d_i = 1` (all family degrees are
`[T : Q]` since `Q` is abelian, the explicit input `hQcomm` — the abelian half of the
(13.2.b)-for-`T` "Q elementary abelian") and the Dade image `τψ_i ∈ ℤ[Irr G]` ((2.10)
`preserves_virtualCharacters` of the `(T, Q^#)` TI-isometry). -/
theorem Q_sharp_hypothesis76_base_cCoeff_int [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (hQcomm : IsMulCommutative ↥hyp.Q)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.T))
    {χ : ClassFunction G ℂ} (hχ : χ ∈ ZIrr G) :
    ∀ i : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1),
      ∃ z : ℤ, (Q_sharp_hypothesis76_base hG hyp hvd φ₀).cCoeff χ i = (z : ℂ) := by
  classical
  intro i
  set K : Subgroup ↥hyp.T := (Q_sharp_hypothesis76_base hG hyp hvd φ₀).H.subgroupOf hyp.T
    with hKdef
  have hKnorm : K.Normal :=
    OddOrder.Peterfalvi.S09.Cert.subgroupOf_normal_of_conj
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).H_normal_in_L
  -- `K ≅ Q` is abelian, so every `θ_j` is linear and all `ζ_j` have degree `[T:K]`.
  have hQT : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  have hKcomm : IsMulCommutative ↥K := by
    have e := Subgroup.subgroupOfEquivOfLe
      (show (Q_sharp_hypothesis76_base hG hyp hvd φ₀).H ≤ hyp.T from hQT)
    exact ⟨⟨fun a b => e.injective (by
      rw [map_mul, map_mul]
      exact hQcomm.is_comm.comm (e a) (e b))⟩⟩
  -- Degrees: `ζ_j(1) = [T:K]` for every `j`, so the degree ratio is `1`.
  have hzeta_one : ∀ j : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1),
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta j 1 = (K.index : ℂ) := by
    intro j
    obtain ⟨θ, hθ⟩ := (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta_induced j
    have hθ1 : (θ : ClassFunction ↥K ℂ) 1 = 1 :=
      OddOrder.RepresentationTheory.IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative
        θ.2
    rw [hθ, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ1, mul_one]
  have hidx0 : (K.index : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite (H := K)
  have hd1 : (Q_sharp_hypothesis76_base hG hyp hvd φ₀).d i = 1 := by
    have h := (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta_one_eq_d_mul i
    rw [hzeta_one i, hzeta_one 0] at h
    field_simp at h
    exact h.symm
  -- `ψ_i = ζ_i − ζ_0 ∈ ℤ[Irr T]`.
  have hzetaZ : ∀ j : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1),
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta j ∈ ZIrr ↥hyp.T := by
    intro j
    obtain ⟨θ, hθ⟩ := (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta_induced j
    rw [hθ]
    exact OddOrder.RepresentationTheory.ClassFunction.induce_mem_ZIrr K (θ.2.mem_ZIrr)
  have hψZ : ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).psiSupp i : ClassFunction ↥hyp.T ℂ)
      ∈ ZIrr ↥hyp.T := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis76.psiSupp_coe, hd1, one_smul]
    exact Submodule.sub_mem _ (hzetaZ i) (hzetaZ 0)
  -- The Dade image is a virtual character ((2.10) `preserves_virtualCharacters`).
  have hτeq : (Q_sharp_hypothesis76_base hG hyp hvd φ₀).hyp71.τ
      = ((Q_sharp_dadeHypothesis hG hyp hvd).fullDadeIsometryData).toDadeIsometryData.toDadeMap
          := rfl
  have hpres : (Q_sharp_hypothesis76_base hG hyp hvd φ₀).hyp71.τ
      ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).psiSupp i) ∈ ZIrr G := by
    rw [hτeq]
    exact ((Q_sharp_dadeHypothesis hG hyp
        hvd).fullDadeIsometryData).preserves_virtualCharacters _ hψZ
  -- `c_i = ⟨τψ_i, χ⟩ ∈ ℤ`.
  rw [OddOrder.Peterfalvi.S09.Hypothesis76.cCoeff]
  exact ClassFunction.inner_mem_ZIrr_int hpres hχ

open scoped Classical in
open scoped FiniteInduce in
/-- **The `T`-side correction has integer value at `1`** over the chosen base — the core
restatement of `exists_etaT_alphaFun_one_int` (Peterfalvi (13.5.a)-for-`T` integrality,
issue 2035 #22 T-side twin): `α(1) ∈ ℤ` for the `Q`-kernel tail `α = hypothesis76AlphaFun` of
the `(T, Q^#)` (7.7.a) decomposition of `η₁₀`.  The commutativity of `Q` (the abelian half of
the (13.2.b)-for-`T` `Q_elementaryAbelian`, available before (14.9)) enters as the explicit
input `hQcomm`: it makes `α|_Q ∈ ℤ[Irr Q]`
via the integer (7.7.a) coefficients (`Q_sharp_hypothesis76_base_cCoeff_int`, using
`η₁₀ ∈ ℤ[Irr G]` = `eta10_mem_ZIrr`) through the generic route
(`hypothesis76AlphaFun_one_int`). -/
theorem Hypothesis.exists_etaT_alphaFun_one_int_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1)
    (hQcomm : IsMulCommutative ↥hyp.Q)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.T)) :
    ∃ α1 : ℤ, hypothesis76AlphaFun (Q_sharp_hypothesis76_base hG hyp hvd φ₀)
      (hyp.Q.subgroupOf hyp.T) hyp.eta10 1 = (α1 : ℂ) :=
  hypothesis76AlphaFun_one_int (Q_sharp_hypothesis76_base hG hyp hvd φ₀)
    (hyp.Q.subgroupOf hyp.T) hyp.eta10
    (Q_sharp_hypothesis76_base_cCoeff_int hG hyp hvd hQcomm φ₀ hyp.eta10_mem_ZIrr)

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseBEndgameSupply/Eta10Correction.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (13.8), distinguished `T`-side index with an honestly selected base**:
the coefficient-zero `ν`-row base supplies the base condition of
`exists_muT_index_core_of_base_condition`, yielding the nonzero distinguished index and all
coefficient, norm, and degree conclusions without an irreducibly induced base hypothesis. -/
theorem Hypothesis.exists_muT_index_caseB_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hD : hyp.D = ⊥) (hQcomm : IsMulCommutative ↥hyp.Q) :
    ∃ (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
          ↥(hyp.Q.subgroupOf hyp.T))
        (i₁ : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1)) (δ : ℤ),
      ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) :
          Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ)) ∧
      0 < i₁ ∧
      ¬ ((hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i₁)) ∧
      δ ^ 2 = 1 ∧
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).cCoeff hyp.eta10 i₁ = (δ : ℂ) ∧
      (∀ i : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1), 0 < i → i ≠ i₁ →
        ¬ ((hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i)) →
        (Q_sharp_hypothesis76_base hG hyp hvd φ₀).cCoeff hyp.eta10 i = 0) ∧
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zetaNormSq i₁ = (hyp.p : ℂ) ∧
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i₁ 1
        = ((hyp.p * hyp.v : ℕ) : ℂ) := by
  obtain ⟨φ₀, hφ₀Q, hφ₀orth⟩ :=
    hyp.exists_qSharpBase_orthogonal_eta10_core hG hnoV pins hvd hTP Tdata hU hW1 hW2
      chief hD
  obtain ⟨i₁, δ, hi₁, hi₁Q, hδ, hc, hmid, hnorm, hdeg⟩ :=
    hyp.exists_muT_index_core_of_base_condition hG hnoV pins hvd hTP Tdata hU hW1 hW2
      chief hD hQcomm φ₀ hφ₀Q (Or.inr hφ₀orth)
  exact ⟨φ₀, i₁, δ, hφ₀Q, hi₁, hi₁Q, hδ, hc, hmid, hnorm, hdeg⟩

open OddOrder.Peterfalvi.S11 in
open scoped Classical in
open scoped FiniteInduce in
/-- **Peterfalvi (13.5)/(13.8), Core `T`-side correction package**: under `D = ⊥` and
commutative `Q`, the honestly selected coefficient-zero base yields the normalized
distinguished row `ζ`, the `Q`-kernel tail `α`, the point formula on `Q^#`, the exact first
term `|T'| - v²`, and the `(q^p-1)α(1)²` inflation bound. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hD : hyp.D = ⊥) (hQcomm : IsMulCommutative ↥hyp.Q)
    (pins : NuGridSupplyData hyp) :
    ∃ (ζ α : ↥hyp.T → ℂ) (α1 δ : ℤ),
      (∀ x : ↥hyp.T, x ∉ hyp.Q.subgroupOf hyp.T → ζ x = 0) ∧
      (∑ x ∈ Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T),
        ζ x * (starRingEnd ℂ) (α x)) = 0 ∧
      (∀ x ∈ (Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T)).erase 1,
        hyp.eta10 ↑x = (δ : ℂ) * ζ x + α x) ∧
      ((∑ x : ↥hyp.T, ‖ζ x‖ ^ 2) - ‖ζ 1‖ ^ 2
        = (Nat.card ↥(derivedInG hyp.T) : ℝ) - (hyp.v : ℝ) ^ 2) ∧
      ((ζ 1 * (starRingEnd ℂ) (α 1)).re = (hyp.v : ℝ) * (α1 : ℝ)) ∧
      δ ^ 2 = 1 ∧
      ((hyp.q ^ hyp.p - 1 : ℕ) : ℝ) * ((α1 : ℤ) : ℝ) ^ 2
        ≤ ∑ x ∈ (Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T)).erase 1, ‖α x‖ ^ 2 := by
  have hnoV := OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG
  have hvd : hyp.v * hyp.d ≠ 1 := hyp.vd_ne_one hG
  have hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T := hyp.T_isTypeP hG
  obtain ⟨Tdata, hU, hW1, hW2⟩ := reconciled_typePData_T hG hyp
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG
    (hyp.toTypesIIIIIIVSetupT hG hvd)
  obtain ⟨φ₀, i₁, δ, _hφ₀Q, hi₁pos, hi₁ker, hδ2, hi₁c, hmiddle, hnormP, hdeg⟩ :=
    hyp.exists_muT_index_caseB_core hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief hD hQcomm
  obtain ⟨α1, hα1⟩ := hyp.exists_etaT_alphaFun_one_int_core hG hvd hQcomm φ₀
  let H76 := Q_sharp_hypothesis76_base hG hyp hvd φ₀
  have hpC : (hyp.p : ℂ) ≠ 0 := by
    exact_mod_cast (show hyp.p ≠ 0 from hyp.p_prime.ne_zero)
  have hpR : (hyp.p : ℝ) ≠ 0 := by
    exact_mod_cast (show hyp.p ≠ 0 from hyp.p_prime.ne_zero)
  have hvanishZ : ∀ x : ↥hyp.T, x ∉ hyp.Q.subgroupOf hyp.T → H76.zeta i₁ x = 0 :=
    fun x hx => H76.zeta_eq_zero_of_not_mem_H i₁ x
      (fun hmem => hx (Subgroup.mem_subgroupOf.mpr hmem))
  refine ⟨fun x => ((hyp.p : ℂ))⁻¹ * H76.zeta i₁ x,
    hypothesis76AlphaFun H76 (hyp.Q.subgroupOf hyp.T) hyp.eta10, α1, δ,
    ?_, ?_, ?_, ?_, ?_, hδ2, ?_⟩
  · intro x hx
    change ((hyp.p : ℂ))⁻¹ * H76.zeta i₁ x = 0
    rw [hvanishZ x hx, mul_zero]
  · have hfull := hypothesis76_zeta_inner_alphaFun_eq_zero H76
      (hyp.Q.subgroupOf hyp.T) hyp.eta10 i₁ hi₁ker
    have hext : (∑ x ∈ Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T),
        H76.zeta i₁ x * (starRingEnd ℂ)
          (hypothesis76AlphaFun H76 (hyp.Q.subgroupOf hyp.T) hyp.eta10 x))
        = ∑ x : ↥hyp.T, H76.zeta i₁ x * (starRingEnd ℂ)
            (hypothesis76AlphaFun H76 (hyp.Q.subgroupOf hyp.T) hyp.eta10 x) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (· ∈ hyp.Q.subgroupOf hyp.T)
        (fun x => H76.zeta i₁ x * (starRingEnd ℂ)
          (hypothesis76AlphaFun H76 (hyp.Q.subgroupOf hyp.T) hyp.eta10 x))]
      have h0 : ∑ x ∈ Finset.univ.filter (fun x => ¬ x ∈ hyp.Q.subgroupOf hyp.T),
          H76.zeta i₁ x * (starRingEnd ℂ)
            (hypothesis76AlphaFun H76 (hyp.Q.subgroupOf hyp.T) hyp.eta10 x) = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        rw [hvanishZ x (Finset.mem_filter.mp hx).2, zero_mul]
      rw [h0, add_zero]
    calc
      ∑ x ∈ Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T),
          ((hyp.p : ℂ))⁻¹ * H76.zeta i₁ x * (starRingEnd ℂ)
            (hypothesis76AlphaFun H76 (hyp.Q.subgroupOf hyp.T) hyp.eta10 x)
          = ((hyp.p : ℂ))⁻¹ * ∑ x ∈ Finset.univ.filter
              (· ∈ hyp.Q.subgroupOf hyp.T), H76.zeta i₁ x * (starRingEnd ℂ)
                (hypothesis76AlphaFun H76 (hyp.Q.subgroupOf hyp.T) hyp.eta10 x) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun x _ => by ring
      _ = 0 := by rw [hext, hfull, mul_zero]
  · intro x hx
    obtain ⟨hx1, hxmem⟩ := Finset.mem_erase.mp hx
    have hxQ : (↑x : G) ∈ hyp.Q :=
      Subgroup.mem_subgroupOf.mp (Finset.mem_filter.mp hxmem).2
    have hxsharp : (↑x : G) ∈ OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G) := by
      refine OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨hxQ, ?_⟩
      intro h1
      exact hx1 (Subtype.ext h1)
    have hpt := hypothesis76_point_formula H76 (fun _ => rfl)
      (hyp.Q.subgroupOf hyp.T) hyp.eta10 i₁ hi₁pos hi₁ker hmiddle x hxsharp
    have htail : (∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
          (fun i => (hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
            OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)),
        (star (H76.cCoeff hyp.eta10 i) / H76.zetaNormSq i) * H76.zeta i x)
        = hypothesis76AlphaFun H76 (hyp.Q.subgroupOf hyp.T) hyp.eta10 x := rfl
    rw [hpt, htail, hi₁c, star_intCast, hnormP]
    ring
  · have hpars : ((∑ x : ↥hyp.T, ‖H76.zeta i₁ x‖ ^ 2 : ℝ) : ℂ)
        = (Nat.card ↥hyp.T : ℂ) * (hyp.p : ℂ) := by
      rw [sum_normSq_eq_card_mul_inner, ← OddOrder.Peterfalvi.S09.Hypothesis76.zetaNormSq,
        hnormP]
    have hparsR : ∑ x : ↥hyp.T, ‖H76.zeta i₁ x‖ ^ 2
        = (Nat.card ↥hyp.T : ℝ) * (hyp.p : ℝ) := by
      exact_mod_cast hpars
    have hscale : ∀ x : ↥hyp.T,
        ‖((hyp.p : ℂ))⁻¹ * H76.zeta i₁ x‖ ^ 2
          = ((hyp.p : ℝ))⁻¹ ^ 2 * ‖H76.zeta i₁ x‖ ^ 2 := by
      intro x
      rw [norm_mul, mul_pow, norm_inv, Complex.norm_natCast]
    have hζ1 : ‖((hyp.p : ℂ))⁻¹ * H76.zeta i₁ 1‖ ^ 2 = (hyp.v : ℝ) ^ 2 := by
      rw [hdeg, norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_natCast]
      rw [show ((hyp.p * hyp.v : ℕ) : ℝ) = (hyp.p : ℝ) * (hyp.v : ℝ) from by
        push_cast; ring]
      field_simp
    have hTp : (Nat.card ↥hyp.T : ℝ)
        = (Nat.card ↥(derivedInG hyp.T) : ℝ) * (hyp.p : ℝ) := by
      exact_mod_cast hyp.card_T_eq_deriv_mul_p hG
    rw [Finset.sum_congr rfl (fun x _ => hscale x), ← Finset.mul_sum, hparsR, hζ1, hTp]
    field_simp
  · have hζ1v : ((hyp.p : ℂ))⁻¹ * H76.zeta i₁ 1 = ((hyp.v : ℕ) : ℂ) := by
      rw [hdeg, show ((hyp.p * hyp.v : ℕ) : ℂ) = (hyp.p : ℂ) * (hyp.v : ℂ) from by
        push_cast; ring]
      field_simp
    change ((((hyp.p : ℂ))⁻¹ * H76.zeta i₁ 1) *
        (starRingEnd ℂ) (hypothesis76AlphaFun H76
          (hyp.Q.subgroupOf hyp.T) hyp.eta10 1)).re = (hyp.v : ℝ) * (α1 : ℝ)
    rw [hζ1v, hα1]
    rw [show ((hyp.v : ℕ) : ℂ) = (((hyp.v : ℕ) : ℝ) : ℂ) from by push_cast; ring,
      show ((α1 : ℤ) : ℂ) = (((α1 : ℤ) : ℝ) : ℂ) from by push_cast; ring,
      Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  · have hF : ∀ x : ↥hyp.T,
        x ∈ (Finset.univ.filter (· ∈ hyp.Q.subgroupOf hyp.T)).erase 1 ↔
          ((x : G) ∈ H76.H ∧ x ≠ 1) := by
      intro x
      rw [Finset.mem_erase, Finset.mem_filter]
      constructor
      · rintro ⟨h1, -, h2⟩
        exact ⟨Subgroup.mem_subgroupOf.mp h2, h1⟩
      · rintro ⟨h2, h1⟩
        exact ⟨h1, Finset.mem_univ _, Subgroup.mem_subgroupOf.mpr h2⟩
    have hP'H : ∀ x : ↥hyp.T, x ∈ hyp.Q.subgroupOf hyp.T → (x : G) ∈ H76.H :=
      fun x hx => Subgroup.mem_subgroupOf.mp hx
    have hinfl := hypothesis76AlphaFun_inflation H76 (hyp.Q.subgroupOf hyp.T)
      hyp.eta10 _ hF hP'H
    have hQT : hyp.Q ≤ hyp.T := by
      rw [hyp.Q_eq_TF]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
    have hcardQT : Nat.card ↥(hyp.Q.subgroupOf hyp.T) = hyp.q ^ hyp.p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQT).toEquiv]
      exact hyp.card_Q_eq_qp hG
    have hqp1 : (1 : ℕ) ≤ hyp.q ^ hyp.p :=
      Nat.one_le_pow _ _ (by have := hyp.three_le_q; omega)
    have hcoeff : ((Nat.card ↥(hyp.Q.subgroupOf hyp.T) : ℝ)) - 1
        = ((hyp.q ^ hyp.p - 1 : ℕ) : ℝ) := by
      rw [hcardQT, Nat.cast_sub hqp1]
      norm_num
    have hval : ‖hypothesis76AlphaFun H76 (hyp.Q.subgroupOf hyp.T) hyp.eta10 1‖ ^ 2
        = ((α1 : ℤ) : ℝ) ^ 2 := by
      rw [hα1, Complex.norm_intCast, sq_abs]
    rw [← hval, ← hcoeff]
    exact hinfl

end

end OddOrder.Peterfalvi.S15
