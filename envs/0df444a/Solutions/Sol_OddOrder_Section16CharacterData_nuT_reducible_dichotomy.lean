-- Prove2me | solution 1 for OddOrder.Section16CharacterData.nuT_reducible_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:53:58.405241+00:00
-- url     : https://prove2.me/submissions/66309877-a449-4f15-b0d0-6ffe9cd7c2fa

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/ClassFunction.lean
--   OddOrder/Peterfalvi/S05_TICyclic.lean
--   OddOrder/FeitThompsonSetup.lean
--   OddOrder/FeitThompsonNuGrid.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_FeitThompsonNuGrid
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

-- ===== OddOrder/GroupTheory/RepresentationTheory/ClassFunction.lean =====
namespace OddOrder.RepresentationTheory

namespace ClassFunction

variable {G : Type*} [Group G] {k : Type*} [CommRing k]

section Inner

variable {G : Type*} [Group G] [Fintype G]

variable {k : Type*} [CommRing k] [StarRing k]

/-- The unscaled inner sum is invariant under pullback along a group **isomorphism**:
reindexing the sum over `H` by `e : H ≃* G` recovers the sum over `G`. -/
theorem innerSum_compHom_mulEquiv {H : Type*} [Group H] [Fintype H] (e : H ≃* G)
    (φ ψ : ClassFunction G k) :
    innerSum (compHom e.toMonoidHom φ) (compHom e.toMonoidHom ψ) = innerSum φ ψ := by
  simpa [innerSum] using e.toEquiv.sum_comp (fun g => φ g * star (ψ g))

/-- The normalized inner product is invariant under pullback along a group isomorphism
(`|H| = |G|`, so the normalizations agree). -/
theorem inner_compHom_mulEquiv {H : Type*} [Group H] [Fintype H] (e : H ≃* G)
    [Invertible (Nat.card H : k)] [Invertible (Nat.card G : k)]
    (φ ψ : ClassFunction G k) :
    inner (compHom e.toMonoidHom φ) (compHom e.toMonoidHom ψ) = inner φ ψ := by
  have hcard : ((Nat.card H : ℕ) : k) = ((Nat.card G : ℕ) : k) := by
    rw [Nat.card_congr e.toEquiv]
  have h := innerSum_compHom_mulEquiv e φ ψ
  calc inner (compHom e.toMonoidHom φ) (compHom e.toMonoidHom ψ)
      = ⅟(Nat.card H : k) * innerSum φ ψ := by rw [inner, h]
    _ = ⅟(Nat.card H : k) * ((Nat.card H : k) * inner φ ψ) := by
        rw [← card_mul_inner, ← hcard]
    _ = inner φ ψ := by rw [← mul_assoc, invOf_mul_self, one_mul]

end Inner

end ClassFunction

end OddOrder.RepresentationTheory

-- ===== OddOrder/Peterfalvi/S05_TICyclic.lean =====
namespace OddOrder.Peterfalvi.S05

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G] [Fintype G]

namespace TICyclicHypothesis

open scoped Classical in
/-- The `ω`-family orthonormality in Kronecker form: `⟨ω(χ), ω(χ')⟩ = δ_{χχ'}`
(`omega_inner_self` + `omega_inner_ne` combined; the shape the §13 grid fields carry). -/
theorem omega_inner (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] (χ χ' : hyp.W →* ℂˣ) :
    ClassFunction.inner (hyp.omega χ : ClassFunction hyp.W ℂ)
      (hyp.omega χ' : ClassFunction hyp.W ℂ) = if χ = χ' then 1 else 0 := by
  split_ifs with h
  · subst h; exact hyp.omega_inner_self χ
  · exact hyp.omega_inner_ne h

end TICyclicHypothesis

end OddOrder.Peterfalvi.S05

-- ===== OddOrder/FeitThompsonSetup.lean =====
namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.RepresentationTheory

open scoped Pointwise

universe u

section

open scoped OddOrder.Peterfalvi.S15.FiniteInduce

namespace Section16CharacterData

variable {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G) (mp : Section16MaximalPair G)

variable (tp : Section16TypePStructure mp)

/-- `|certainTypeT.W₁| = tp.p` (both are `|mp.Kstar|`). -/
theorem cardCertainTypeT_W1 : Nat.card ↥(mp.certainTypeT hG).W1 = tp.p := by
  rw [certainTypeT_W1_eq hG mp,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe mp.Kstar_le_T).toEquiv,
    ← tp.W2_eq_Kstar hG, ← tp.p_eq_card_W2]

/-- `|certainTypeT.W₂| = tp.q` (both are `|mp.K|`). -/
theorem cardCertainTypeT_W2 : Nat.card ↥(mp.certainTypeT hG).W2 = tp.q := by
  rw [certainTypeT_W2_eq hG mp,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (k_le_T hG mp)).toEquiv,
    ← tp.W1_eq_K hG, ← tp.q_eq_card_W1]

variable [NeZero (Nat.card ↥(mp.certainTypeS hG).W1)]

/-- The `eqQ` reindex fixes the base index `0`. -/
theorem eqQ_zero : eqQ hG mp tp ⟨0, tp.q_prime.pos⟩ = 0 := by
  apply Fin.ext; simp [eqQ]

/-- **A linear character of `↥tp.W` is determined by its restrictions to `tp.W1` and `tp.W2`.**
Since `tp.W = tp.W1 ⊔ tp.W2` is an internal product of two commuting subgroups, every `w : ↥tp.W`
factors as `w = a * b` with `a ∈ tp.W1`, `b ∈ tp.W2`; two monoid homs agreeing on `tp.W1` and
`tp.W2`
therefore agree everywhere.  This is the generating-set half of the S/T-shared-`ω` symmetry. -/
theorem monoidHom_eq_of_eqOn_W1_W2 {χ χ' : ↥tp.W →* ℂˣ}
    (h1 : ∀ w : ↥tp.W, (w : G) ∈ tp.W1 → χ w = χ' w)
    (h2 : ∀ w : ↥tp.W, (w : G) ∈ tp.W2 → χ w = χ' w) :
    χ = χ' := by
  have := tp.W_cyclic
  let : CommGroup ↥tp.W := IsCyclic.commGroup
  have hW1le : tp.W1 ≤ tp.W := by rw [tp.W_eq_join]; exact le_sup_left
  have hW2le : tp.W2 ≤ tp.W := by rw [tp.W_eq_join]; exact le_sup_right
  have htop : (tp.W1.subgroupOf tp.W) ⊔ (tp.W2.subgroupOf tp.W) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hW1le hW2le, ← tp.W_eq_join, Subgroup.subgroupOf_self]
  ext w
  have hmem : w ∈ (tp.W1.subgroupOf tp.W) ⊔ (tp.W2.subgroupOf tp.W) := htop ▸ Subgroup.mem_top w
  rw [Subgroup.mem_sup] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  rw [← hab, map_mul, map_mul, h1 a (Subgroup.mem_subgroupOf.mp ha),
    h2 b (Subgroup.mem_subgroupOf.mp hb)]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- **Value of `certainTypeS`'s product character on a transported `mp.K`-element**: only the
`W₁`-factor `a` survives (`wFst` is the identity, `wSnd` is trivial, on a `W₁`-element).  This is
the
`tp.W1`-restriction value used (with its `tp.W2` mirror) to discharge the S/T-shared-`ω` symmetry on
the generators via `monoidHom_eq_of_eqOn_W1_W2`. -/
theorem omegaProdCharS_apply_mem_K
    (a : ((mp.certainTypeS hG).sdiffTICyclicHypothesis.W1.subgroupOf
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (b : ((mp.certainTypeS hG).sdiffTICyclicHypothesis.W2.subgroupOf
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (w : ↥tp.W) (hw : (w : G) ∈ mp.K) :
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar a b (gridEquivE hG mp tp w)
      = a ⟨gridEquivE hG mp tp w, gridEquivE_mem_W1 hG mp tp w hw⟩ := by
  have mem := gridEquivE_mem_W1 hG mp tp w hw
  have hfst : (mp.certainTypeS hG).sdiffTICyclicHypothesis.wFst (gridEquivE hG mp tp w)
      = ⟨gridEquivE hG mp tp w, mem⟩ :=
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.wFst_W1_subtype ⟨gridEquivE hG mp tp w, mem⟩
  have hsnd : (mp.certainTypeS hG).sdiffTICyclicHypothesis.wSnd (gridEquivE hG mp tp w) = 1 :=
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.wSnd_W1_subtype ⟨gridEquivE hG mp tp w, mem⟩
  simp only [Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    MonoidHom.comp_apply]
  rw [hfst, hsnd, map_one, mul_one]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- **Value of `certainTypeS`'s product character on a transported `mp.Kstar`-element**: only the
`W₂`-factor `b` survives.  The `tp.W2`-restriction mirror of `omegaProdCharS_apply_mem_K`. -/
theorem omegaProdCharS_apply_mem_Kstar
    (a : ((mp.certainTypeS hG).sdiffTICyclicHypothesis.W1.subgroupOf
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (b : ((mp.certainTypeS hG).sdiffTICyclicHypothesis.W2.subgroupOf
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (w : ↥tp.W) (hw : (w : G) ∈ mp.Kstar) :
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar a b (gridEquivE hG mp tp w)
      = b ⟨gridEquivE hG mp tp w, gridEquivE_mem_W2 hG mp tp w hw⟩ := by
  have mem := gridEquivE_mem_W2 hG mp tp w hw
  have hfst : (mp.certainTypeS hG).sdiffTICyclicHypothesis.wFst (gridEquivE hG mp tp w) = 1 :=
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.wFst_W2_subtype ⟨gridEquivE hG mp tp w, mem⟩
  have hsnd : (mp.certainTypeS hG).sdiffTICyclicHypothesis.wSnd (gridEquivE hG mp tp w)
      = ⟨gridEquivE hG mp tp w, mem⟩ :=
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.wSnd_W2_subtype ⟨gridEquivE hG mp tp w, mem⟩
  simp only [Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    MonoidHom.comp_apply]
  rw [hfst, hsnd, map_one, one_mul]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- **Value of `certainTypeT`'s product character on a transported `mp.K`-element**: since `mp.K` is
the `W₂`-factor of `T`, only the `W₂`-factor `b` survives.  The T-side mirror of
`omegaProdCharS_apply_mem_Kstar`. -/
theorem omegaProdCharT_apply_mem_K
    (a : ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W1.subgroupOf
        (mp.certainTypeT hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (b : ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W2.subgroupOf
        (mp.certainTypeT hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (w : ↥tp.W) (hw : (w : G) ∈ mp.K) :
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.omegaProdChar a b (gridEquivE_T hG mp tp w)
      = b ⟨gridEquivE_T hG mp tp w, gridEquivE_T_mem_W2 hG mp tp w hw⟩ := by
  have mem := gridEquivE_T_mem_W2 hG mp tp w hw
  have hfst : (mp.certainTypeT hG).sdiffTICyclicHypothesis.wFst (gridEquivE_T hG mp tp w) = 1 :=
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.wFst_W2_subtype ⟨gridEquivE_T hG mp tp w, mem⟩
  have hsnd : (mp.certainTypeT hG).sdiffTICyclicHypothesis.wSnd (gridEquivE_T hG mp tp w)
      = ⟨gridEquivE_T hG mp tp w, mem⟩ :=
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.wSnd_W2_subtype ⟨gridEquivE_T hG mp tp w, mem⟩
  simp only [Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    MonoidHom.comp_apply]
  rw [hfst, hsnd, map_one, one_mul]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- **Value of `certainTypeT`'s product character on a transported `mp.Kstar`-element**: since
`mp.Kstar` is the `W₁`-factor of `T`, only the `W₁`-factor `a` survives.  The T-side mirror of
`omegaProdCharS_apply_mem_K`. -/
theorem omegaProdCharT_apply_mem_Kstar
    (a : ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W1.subgroupOf
        (mp.certainTypeT hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (b : ((mp.certainTypeT hG).sdiffTICyclicHypothesis.W2.subgroupOf
        (mp.certainTypeT hG).sdiffTICyclicHypothesis.W) →* ℂˣ)
    (w : ↥tp.W) (hw : (w : G) ∈ mp.Kstar) :
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.omegaProdChar a b (gridEquivE_T hG mp tp w)
      = a ⟨gridEquivE_T hG mp tp w, gridEquivE_T_mem_W1 hG mp tp w hw⟩ := by
  have mem := gridEquivE_T_mem_W1 hG mp tp w hw
  have hfst : (mp.certainTypeT hG).sdiffTICyclicHypothesis.wFst (gridEquivE_T hG mp tp w)
      = ⟨gridEquivE_T hG mp tp w, mem⟩ :=
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.wFst_W1_subtype ⟨gridEquivE_T hG mp tp w, mem⟩
  have hsnd : (mp.certainTypeT hG).sdiffTICyclicHypothesis.wSnd (gridEquivE_T hG mp tp w) = 1 :=
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.wSnd_W1_subtype ⟨gridEquivE_T hG mp tp w, mem⟩
  simp only [Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    MonoidHom.comp_apply]
  rw [hfst, hsnd, map_one, mul_one]

end Section16CharacterData

end

end OddOrder

-- ===== OddOrder/FeitThompsonNuGrid.lean =====
namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.RepresentationTheory

open scoped Pointwise

section

open scoped OddOrder.Peterfalvi.S15.FiniteInduce

namespace Section16CharacterData

variable {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G)
  (mp : Section16MaximalPair G)

variable (tp : Section16TypePStructure mp)

variable [NeZero (Nat.card ↥(mp.certainTypeS hG).W1)]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- The round-trip through `tp.W`. -/
theorem eTS_gridEquivE_T (w : ↥tp.W) :
    eTS hG mp tp (gridEquivE_T hG mp tp w) = gridEquivE hG mp tp w := by
  simp only [eTS, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

/-- `colT i` agrees with the S-side dual on a transported `mp.K`-element. -/
theorem colT_apply_mem_K (i : Fin tp.q) (w : ↥tp.W) (hw : (w : G) ∈ mp.K) :
    colT hG mp tp i ⟨gridEquivE_T hG mp tp w, gridEquivE_T_mem_W2 hG mp tp w hw⟩
      = (mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i)
          ⟨gridEquivE hG mp tp w, gridEquivE_mem_W1 hG mp tp w hw⟩ := by
  rw [colT, MonoidHom.comp_apply, MonoidHom.comp_apply]
  change (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
      ((mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i)) 1
      (eTS hG mp tp (gridEquivE_T hG mp tp w)) = _
  rw [eTS_gridEquivE_T]
  exact omegaProdCharS_apply_mem_K hG mp tp _ 1 w hw

/-- The base T-side column dual is trivial. -/
theorem colT_zero : colT hG mp tp ⟨0, tp.q_prime.pos⟩ = 1 := by
  ext x
  simp [colT, eqQ_zero, Peterfalvi.S05.TICyclicHypothesis.omegaProdChar]
  rfl

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeS hG mp).W1)] in
/-- `rowDualT j` agrees with the S-side dual on a transported `mp.Kstar`-element. -/
theorem rowDualT_apply_mem_Kstar (j : Fin tp.p) (w : ↥tp.W)
    (hw : (w : G) ∈ mp.Kstar) :
    rowDualT hG mp tp j
        ⟨gridEquivE_T hG mp tp w, gridEquivE_T_mem_W1 hG mp tp w hw⟩
      = chi2enum hG mp tp j
          ⟨gridEquivE hG mp tp w, gridEquivE_mem_W2 hG mp tp w hw⟩ := by
  rw [rowDualT, MonoidHom.comp_apply, MonoidHom.comp_apply]
  change (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
      1 (chi2enum hG mp tp j) (eTS hG mp tp (gridEquivE_T hG mp tp w)) = _
  rw [eTS_gridEquivE_T]
  exact omegaProdCharS_apply_mem_Kstar hG mp tp 1 _ w hw

variable [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)]

set_option backward.isDefEq.respectTransparency false in
/-- The S- and T-side constructions give the same shared `ω`-grid. -/
theorem omegaS_eq_omegaT (i : Fin tp.q) (j : Fin tp.p) :
    omegaS hG mp tp i j = omegaT hG mp tp i j := by
  have hrow : (mp.certainTypeT hG).w1CharEquiv (rowT hG mp tp j) =
      rowDualT hG mp tp j := by
    rw [rowT, Equiv.apply_symm_apply]
  have key : ((mp.certainTypeT hG).sdiffTICyclicHypothesis.omegaProdChar
          (rowDualT hG mp tp j) (colT hG mp tp i)).comp
          (gridEquivE_T hG mp tp).toMonoidHom
      = ((mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
          ((mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i))
          (chi2enum hG mp tp j)).comp (gridEquivE hG mp tp).toMonoidHom := by
    apply monoidHom_eq_of_eqOn_W1_W2
    · intro w hw
      rw [tp.W1_eq_K hG] at hw
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [omegaProdCharT_apply_mem_K hG mp tp _ _ w hw,
        colT_apply_mem_K hG mp tp i w hw]
      exact (omegaProdCharS_apply_mem_K hG mp tp _ _ w hw).symm
    · intro w hw
      rw [tp.W2_eq_Kstar hG] at hw
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [omegaProdCharT_apply_mem_Kstar hG mp tp _ _ w hw,
        rowDualT_apply_mem_Kstar hG mp tp j w hw]
      exact (omegaProdCharS_apply_mem_Kstar hG mp tp _ _ w hw).symm
  simp only [omegaS, omegaT, Peterfalvi.S06.Hypothesis.chiColumn,
    Peterfalvi.S05.TICyclicHypothesis.omega]
  rw [hrow, ClassFunction.compHom_linearIrreducibleCharacter,
    ClassFunction.compHom_linearIrreducibleCharacter, key]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Peterfalvi (3.3)/(3.4)**: the shared `ω`-grid is orthonormal. -/
theorem omegaS_inner (i k : Fin tp.q) (j l : Fin tp.p) :
    ClassFunction.inner (omegaS hG mp tp i j) (omegaS hG mp tp k l)
      = if i = k ∧ j = l then 1 else 0 := by
  rw [omegaS, omegaS, ClassFunction.inner_compHom_mulEquiv (gridEquivE hG mp tp)]
  simp only [Peterfalvi.S06.Hypothesis.chiColumn]
  rw [(mp.certainTypeS hG).sdiffTICyclicHypothesis.omega_inner]
  by_cases h : i = k ∧ j = l
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos rfl, if_pos ⟨rfl, rfl⟩]
  · have hne : (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
        ((mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i)) (chi2enum hG mp tp j)
        ≠ (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
          ((mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp k)) (chi2enum hG mp tp l) := by
      intro hc
      obtain ⟨h1, h2⟩ :=
        (mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar_inj hc
      exact h ⟨(eqQ hG mp tp).injective
          ((mp.certainTypeS hG).w1CharEquiv_injective h1),
        (chi2enum hG mp tp).injective h2⟩
    rw [if_neg hne, if_neg h]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- Distinct index pairs give distinct members of the shared `ω`-grid. -/
theorem omegaS_pair_injective :
    Function.Injective
      (fun ij : Fin tp.q × Fin tp.p => omegaS hG mp tp ij.1 ij.2) := by
  intro ⟨i, j⟩ ⟨k, l⟩ hω
  change omegaS hG mp tp i j = omegaS hG mp tp k l at hω
  by_contra hne
  have h1 := omegaS_inner hG mp tp i k j l
  rw [hω] at h1
  have h2 := omegaS_inner hG mp tp k k l l
  rw [h1] at h2
  have hcond : ¬ (i = k ∧ j = l) := fun ⟨h1', h2'⟩ => hne (by rw [h1', h2'])
  rw [if_neg hcond, if_pos (⟨rfl, rfl⟩ : k = k ∧ l = l)] at h2
  exact zero_ne_one h2

/-- The transported T-side row enumeration is injective. -/
theorem rowT_injective : Function.Injective (rowT hG mp tp) := by
  intro j l hrow
  have hω : omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ j =
      omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ l := by
    rw [omegaS_eq_omegaT hG mp tp, omegaS_eq_omegaT hG mp tp]
    simp only [omegaT, hrow]
  have hp : ((⟨0, tp.q_prime.pos⟩ : Fin tp.q), j) =
      ((⟨0, tp.q_prime.pos⟩ : Fin tp.q), l) :=
    omegaS_pair_injective hG mp tp hω
  exact congrArg Prod.snd hp

/-- The transported T-side column enumeration is injective. -/
theorem colT_injective : Function.Injective (colT hG mp tp) := by
  intro i k hcol
  have hω : omegaS hG mp tp i ⟨0, tp.p_prime.pos⟩ =
      omegaS hG mp tp k ⟨0, tp.p_prime.pos⟩ := by
    rw [omegaS_eq_omegaT hG mp tp, omegaS_eq_omegaT hG mp tp]
    simp only [omegaT, hcol]
  have hp : (i, (⟨0, tp.p_prime.pos⟩ : Fin tp.p)) =
      (k, (⟨0, tp.p_prime.pos⟩ : Fin tp.p)) :=
    omegaS_pair_injective hG mp tp hω
  exact congrArg Prod.fst hp

/-- The transported T-side row enumeration is bijective. -/
theorem rowT_bijective : Function.Bijective (rowT hG mp tp) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨rowT_injective hG mp tp, ?_⟩
  simp only [Fintype.card_fin]
  exact (cardCertainTypeT_W1 hG mp tp).symm

/-- Reindexing equivalence for the T-side rows. -/
noncomputable def rowTEquiv :
    Fin tp.p ≃ Fin (Nat.card ↥(mp.certainTypeT hG).W1) :=
  Equiv.ofBijective (rowT hG mp tp) (rowT_bijective hG mp tp)

/-- The transported T-side column enumeration is bijective in the certain-type column-dual
presentation. -/
theorem colT_bijective : Function.Bijective
    (fun i : Fin tp.q =>
      show (((mp.certainTypeT hG).W2.subgroupOf
        ((mp.certainTypeT hG).W1 ⊔ (mp.certainTypeT hG).W2)) →* ℂˣ) from
        colT hG mp tp i) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨fun _ _ h => colT_injective hG mp tp h, ?_⟩
  have hcard :=
    (mp.certainTypeT hG).sdiffTICyclicHypothesis.card_charGroup_subgroupOf
      (mp.certainTypeT hG).sdiffTICyclicHypothesis.W2_le_W
  change Nat.card (((mp.certainTypeT hG).W2.subgroupOf
      ((mp.certainTypeT hG).W1 ⊔ (mp.certainTypeT hG).W2)) →* ℂˣ) =
    Nat.card ↥(mp.certainTypeT hG).W2 at hcard
  simp only [Fintype.card_fin]
  rw [← Nat.card_eq_fintype_card]
  exact (hcard.trans (cardCertainTypeT_W2 hG mp tp)).symm

/-- Reindexing equivalence for the T-side columns. -/
noncomputable def colTEquiv :
    Fin tp.q ≃
      (((mp.certainTypeT hG).W2.subgroupOf
        ((mp.certainTypeT hG).W1 ⊔ (mp.certainTypeT hG).W2)) →* ℂˣ) :=
  Equiv.ofBijective
    (fun i : Fin tp.q =>
      show (((mp.certainTypeT hG).W2.subgroupOf
        ((mp.certainTypeT hG).W1 ⊔ (mp.certainTypeT hG).W2)) →* ℂˣ) from
        colT hG mp tp i)
    (colT_bijective hG mp tp)

/-- **Peterfalvi (9.8)/(9.11), T-side reverse dichotomy**: every reducible member of a
kernel-filter family over `T'` is a non-anchor canonical `ν`-row sum. -/
theorem _root_.solution {X : Subgroup ↥mp.T} {ψ : ClassFunction ↥mp.T ℂ}
    (hψ : ψ ∈ Peterfalvi.S08.inducedKernelFamily
      ((derivedInG mp.T).subgroupOf mp.T) X)
    (hred : ¬ IsIrreducibleCharacter ψ) :
    ∃ i : Fin tp.q, i ≠ ⟨0, tp.q_prime.pos⟩ ∧
      ψ = ∑ j : Fin tp.p, nuT hG mp tp i j := by
  classical
  have hcyc : IsCyclic ↥((mp.certainTypeT hG).W1 ⊔ (mp.certainTypeT hG).W2) :=
    (mp.certainTypeT hG).isCyclic_sup
  let : CommGroup ↥((mp.certainTypeT hG).W1 ⊔ (mp.certainTypeT hG).W2) :=
    IsCyclic.commGroup
  let : Fintype ↥mp.T := Fintype.ofFinite _
  let : Fintype ↥(mp.certainTypeT hG).K := Fintype.ofFinite _
  let : Fintype ↥((mp.certainTypeT hG).W1 ⊔ (mp.certainTypeT hG).W2) :=
    Fintype.ofFinite _
  obtain ⟨θ, hθne, hθker, rfl⟩ := hψ
  have hFk : ∀ i : Fin tp.q, (∑ j : Fin tp.p, nuT hG mp tp i j) =
      ClassFunction.induce (mp.certainTypeT hG).K
        (((mp.certainTypeT hG).chiRestrict (colTEquiv hG mp tp i) :
          ClassFunction ↥(mp.certainTypeT hG).K ℂ)) := by
    intro i
    rw [(mp.certainTypeT hG).coe_chiRestrict,
      (mp.certainTypeT hG).induce_restrict_certainType_eq]
    simp only [nuT]
    exact Equiv.sum_comp (rowTEquiv hG mp tp)
      (fun j' => (((mp.certainTypeT hG).columnFamily
        (colT hG mp tp i)).mu j' : ClassFunction ↥mp.T ℂ))
  obtain ⟨χ₂', hχ₂'⟩ :=
    ((mp.certainTypeT hG).induce_not_isIrreducible_iff θ).mp hred
  have hχ₂'ne : χ₂' ≠ 1 := by
    rintro rfl
    rw [(mp.certainTypeT hG).chiRestrict_one_eq_trivial] at hχ₂'
    exact hθne hχ₂'.symm
  refine ⟨(colTEquiv hG mp tp).symm χ₂', ?_, ?_⟩
  · intro h0
    apply hχ₂'ne
    calc
      χ₂' = colTEquiv hG mp tp ((colTEquiv hG mp tp).symm χ₂') :=
        (Equiv.apply_symm_apply _ _).symm
      _ = colTEquiv hG mp tp ⟨0, tp.q_prime.pos⟩ := by rw [h0]
      _ = 1 := colT_zero hG mp tp
  · rw [hFk, Equiv.apply_symm_apply, hχ₂']
    exact rfl

end Section16CharacterData

end

end OddOrder
