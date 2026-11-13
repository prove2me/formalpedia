-- Prove2me | solution 1 for OddOrder.Section16CharacterData.tau3W_omegaS_fourcorner_vanish
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T18:04:02.061339+00:00
-- url     : https://prove2.me/submissions/6252c8ab-54ba-40a2-b22c-dd1d174a0401

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
--   OddOrder/FeitThompsonCharacterData.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_FeitThompsonCharacterData
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

variable [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)]

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

end Section16CharacterData

end

end OddOrder

-- ===== OddOrder/FeitThompsonCharacterData.lean =====
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

variable [NeZero (Nat.card ↥(mp.certainTypeS hG).W1)]

variable [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)]

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (3.3), column-`0` normalization** (issue 2033): the column-`0` grid characters
`ω_{i0}` are trivial on `W₂` (`chi2enum 0 = 1` is the trivial `W₂`-dual).  Discharges the
`omega_col_zero_apply_of_mem_W2` field of `Peterfalvi.S15.Hypothesis`. -/
theorem omegaS_col_zero_apply_of_mem_W2 (i : Fin tp.q) (w : ↥tp.W) (hw : (w : G) ∈ tp.W2) :
    omegaS hG mp tp i ⟨0, tp.p_prime.pos⟩ w = 1 := by
  have hwK : (w : G) ∈ mp.Kstar := tp.W2_eq_Kstar hG ▸ hw
  rw [omegaS, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaProdCharS_apply_mem_Kstar hG mp tp _ _ w hwK, chi2enum_zero]
  exact Units.val_one

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (3.3), row-`0` normalization** (issue 2033): the row-`0` grid characters
`ω_{0j}` are trivial on `W₁` (`w1CharEquiv 0 = 1` is the trivial `W₁`-dual).  Discharges the
`omega_row_zero_apply_of_mem_W1` field of `Peterfalvi.S15.Hypothesis`. -/
theorem omegaS_row_zero_apply_of_mem_W1 (j : Fin tp.p) (w : ↥tp.W) (hw : (w : G) ∈ tp.W1) :
    omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ j w = 1 := by
  have hwK : (w : G) ∈ mp.K := tp.W1_eq_K hG ▸ hw
  rw [omegaS, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaProdCharS_apply_mem_K hG mp tp _ _ w hwK, eqQ_zero hG mp tp,
    (mp.certainTypeS hG).w1CharEquiv_zero]
  exact Units.val_one

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- `omegaS i j` is the `tiCyclicW`-grid character of its underlying hom. -/
theorem omegaS_eq_omega_omegaSChar (i : Fin tp.q) (j : Fin tp.p) :
    omegaS hG mp tp i j
      = ((tiCyclicW hG mp tp).omega (omegaSChar hG mp tp i j)).toClassFunction := by
  ext w
  simp only [omegaS, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaSChar]
  rfl

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
set_option backward.isDefEq.respectTransparency false in
/-- Column-independence of the `omegaS`-values on `W₁` (the row character alone survives). -/
theorem omegaS_apply_of_mem_W1_col_eq (i : Fin tp.q) (j j' : Fin tp.p) (w : ↥tp.W)
    (hw : (w : G) ∈ tp.W1) :
    omegaS hG mp tp i j w = omegaS hG mp tp i j' w := by
  have hwK : (w : G) ∈ mp.K := tp.W1_eq_K hG ▸ hw
  rw [omegaS, omegaS, ClassFunction.compHom_apply, ClassFunction.compHom_apply,
    MulEquiv.coe_toMonoidHom, Peterfalvi.S06.Hypothesis.chiColumn,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaProdCharS_apply_mem_K hG mp tp _ _ w hwK,
    omegaProdCharS_apply_mem_K hG mp tp _ _ w hwK]

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
set_option backward.isDefEq.respectTransparency false in
/-- Row-independence of the `omegaS`-values on `W₂` (the column character alone survives). -/
theorem omegaS_apply_of_mem_W2_row_eq (i i' : Fin tp.q) (j : Fin tp.p) (w : ↥tp.W)
    (hw : (w : G) ∈ tp.W2) :
    omegaS hG mp tp i j w = omegaS hG mp tp i' j w := by
  have hwK : (w : G) ∈ mp.Kstar := tp.W2_eq_Kstar hG ▸ hw
  rw [omegaS, omegaS, ClassFunction.compHom_apply, ClassFunction.compHom_apply,
    MulEquiv.coe_toMonoidHom, Peterfalvi.S06.Hypothesis.chiColumn,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaProdCharS_apply_mem_Kstar hG mp tp _ _ w hwK,
    omegaProdCharS_apply_mem_Kstar hG mp tp _ _ w hwK]

omit [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- Values of `omegaSChar` are the `omegaS`-values. -/
theorem omegaSChar_val (i : Fin tp.q) (j : Fin tp.p) (w : ↥tp.W) :
    ((omegaSChar hG mp tp i j w : ℂˣ) : ℂ) = omegaS hG mp tp i j w := by
  rw [omegaS_eq_omega_omegaSChar]
  rfl

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Row alignment**: `omegaSChar i 0` is the product character of the first component of
`omegaSChar i j`'s pair with the trivial second component. -/
theorem omegaSChar_row_align (i : Fin tp.q) (j : Fin tp.p) :
    omegaSChar hG mp tp i ⟨0, tp.p_prime.pos⟩
      = (tiCyclicW hG mp tp).omegaProdChar
          ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).1 1 := by
  have hpair : (tiCyclicW hG mp tp).omegaProdChar
      ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).1
      ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).2
      = omegaSChar hG mp tp i j :=
    (tiCyclicW hG mp tp).omegaProdEquiv.apply_symm_apply (omegaSChar hG mp tp i j)
  refine monoidHom_eq_of_eqOn_W1_W2 mp tp ?_ ?_
  · -- on `W₁`: both equal `omegaSChar i j` there
    intro w hw
    have hsnd : (tiCyclicW hG mp tp).wSnd w = 1 :=
      (tiCyclicW hG mp tp).wSnd_eq_one_of_mem_W1
        (Subgroup.mem_subgroupOf.mpr (show (w : G) ∈ (tiCyclicW hG mp tp).W1 from hw))
    have h1 : omegaSChar hG mp tp i ⟨0, tp.p_prime.pos⟩ w = omegaSChar hG mp tp i j w :=
      Units.ext (by
        rw [omegaSChar_val hG mp tp _ _ w,
          omegaS_apply_of_mem_W1_col_eq hG mp tp i ⟨0, tp.p_prime.pos⟩ j w hw,
          ← omegaSChar_val hG mp tp i j w])
    refine h1.trans ((DFunLike.congr_fun hpair w).symm.trans ?_)
    change _ * ((tiCyclicW hG mp tp).omegaProdEquiv.symm
        (omegaSChar hG mp tp i j)).2 ((tiCyclicW hG mp tp).wSnd w)
      = _ * (1 : (tiCyclicW hG mp tp).W2.subgroupOf (tiCyclicW hG mp tp).W →* ℂˣ)
          ((tiCyclicW hG mp tp).wSnd w)
    rw [hsnd, map_one, map_one]
  · -- on `W₂`: both are `1`
    intro w hw
    have hfst : (tiCyclicW hG mp tp).wFst w = 1 :=
      (tiCyclicW hG mp tp).wFst_eq_one_of_mem_W2
        (Subgroup.mem_subgroupOf.mpr (show (w : G) ∈ (tiCyclicW hG mp tp).W2 from hw))
    have h1 : omegaSChar hG mp tp i ⟨0, tp.p_prime.pos⟩ w = 1 :=
      Units.ext (by
        rw [omegaSChar_val hG mp tp _ _ w,
          omegaS_col_zero_apply_of_mem_W2 hG mp tp i w hw, Units.val_one])
    rw [h1]
    change (1 : ℂˣ) = ((tiCyclicW hG mp tp).omegaProdEquiv.symm
        (omegaSChar hG mp tp i j)).1 ((tiCyclicW hG mp tp).wFst w)
      * (1 : (tiCyclicW hG mp tp).W2.subgroupOf (tiCyclicW hG mp tp).W →* ℂˣ)
          ((tiCyclicW hG mp tp).wSnd w)
    rw [hfst, map_one, MonoidHom.one_apply, one_mul]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Column alignment**: `omegaSChar 0 j` is the product character of the trivial first
component with the second component of `omegaSChar i j`'s pair. -/
theorem omegaSChar_col_align (i : Fin tp.q) (j : Fin tp.p) :
    omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ j
      = (tiCyclicW hG mp tp).omegaProdChar 1
          ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).2 := by
  have hpair : (tiCyclicW hG mp tp).omegaProdChar
      ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).1
      ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).2
      = omegaSChar hG mp tp i j :=
    (tiCyclicW hG mp tp).omegaProdEquiv.apply_symm_apply (omegaSChar hG mp tp i j)
  refine monoidHom_eq_of_eqOn_W1_W2 mp tp ?_ ?_
  · intro w hw
    have hsnd : (tiCyclicW hG mp tp).wSnd w = 1 :=
      (tiCyclicW hG mp tp).wSnd_eq_one_of_mem_W1
        (Subgroup.mem_subgroupOf.mpr (show (w : G) ∈ (tiCyclicW hG mp tp).W1 from hw))
    have h1 : omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ j w = 1 :=
      Units.ext (by
        rw [omegaSChar_val hG mp tp _ _ w,
          omegaS_row_zero_apply_of_mem_W1 hG mp tp j w hw, Units.val_one])
    rw [h1]
    change (1 : ℂˣ) = (1 : (tiCyclicW hG mp tp).W1.subgroupOf (tiCyclicW hG mp tp).W →* ℂˣ)
        ((tiCyclicW hG mp tp).wFst w)
      * ((tiCyclicW hG mp tp).omegaProdEquiv.symm
          (omegaSChar hG mp tp i j)).2 ((tiCyclicW hG mp tp).wSnd w)
    rw [hsnd, map_one, MonoidHom.one_apply, one_mul]
  · intro w hw
    have hfst : (tiCyclicW hG mp tp).wFst w = 1 :=
      (tiCyclicW hG mp tp).wFst_eq_one_of_mem_W2
        (Subgroup.mem_subgroupOf.mpr (show (w : G) ∈ (tiCyclicW hG mp tp).W2 from hw))
    have h1 : omegaSChar hG mp tp ⟨0, tp.q_prime.pos⟩ j w = omegaSChar hG mp tp i j w :=
      Units.ext (by
        rw [omegaSChar_val hG mp tp _ _ w,
          omegaS_apply_of_mem_W2_row_eq hG mp tp ⟨0, tp.q_prime.pos⟩ i j w hw,
          ← omegaSChar_val hG mp tp i j w])
    refine h1.trans ((DFunLike.congr_fun hpair w).symm.trans ?_)
    change ((tiCyclicW hG mp tp).omegaProdEquiv.symm
        (omegaSChar hG mp tp i j)).1 ((tiCyclicW hG mp tp).wFst w) * _
      = (1 : (tiCyclicW hG mp tp).W1.subgroupOf (tiCyclicW hG mp tp).W →* ℂˣ)
          ((tiCyclicW hG mp tp).wFst w) * _
    rw [hfst, map_one, map_one]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (3.4)/(3.5), the four-corner vanishing** (issue-2036 supply): off the
conjugacy saturation of the regular set `V = W ∖ (W₁ ∪ W₂)`,
`1 − η_{i0}(x) − η_{0j}(x) + η_{ij}(x) = 0` for nonzero row and column indices — the `(3.5)`
relation `τ(α_{AB}) = 1_G − χ_{A1} − χ_{1B} + χ_{AB}` evaluated where the `V`-supported
`τ(α)` vanishes, with the `χ`-corners identified with the `η`-grid along the
`omegaSChar`-pair alignments. -/
theorem _root_.solution (i : Fin tp.q) (j : Fin tp.p)
    (hi : i ≠ ⟨0, tp.q_prime.pos⟩) (hj : j ≠ ⟨0, tp.p_prime.pos⟩) {x : G}
    (hx : x ∉ Group.conjugatesOfSet ((tiCyclicW hG mp tp).V)) :
    (1 : ℂ) - tau3W hG mp tp (omegaS hG mp tp i ⟨0, tp.p_prime.pos⟩) x
      - tau3W hG mp tp (omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ j) x
      + tau3W hG mp tp (omegaS hG mp tp i j) x = 0 := by
  classical
  set A := ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).1 with hAdef
  set B := ((tiCyclicW hG mp tp).omegaProdEquiv.symm (omegaSChar hG mp tp i j)).2 with hBdef
  have hpair : (tiCyclicW hG mp tp).omegaProdChar A B = omegaSChar hG mp tp i j :=
    (tiCyclicW hG mp tp).omegaProdEquiv.apply_symm_apply (omegaSChar hG mp tp i j)
  -- distinctness of the grid forces nontrivial components
  have hdistinct : ∀ (k : Fin tp.q) (l : Fin tp.p), (k, l) ≠ (i, j) →
      omegaSChar hG mp tp k l ≠ omegaSChar hG mp tp i j := by
    intro k l hne heq
    have hCF : omegaS hG mp tp k l = omegaS hG mp tp i j := by
      rw [omegaS_eq_omega_omegaSChar, omegaS_eq_omega_omegaSChar, heq]
    have h1 := omegaS_inner hG mp tp k i l j
    rw [hCF] at h1
    have h2 := omegaS_inner hG mp tp i i j j
    rw [h1] at h2
    have hcond : ¬ (k = i ∧ l = j) := fun ⟨h1', h2'⟩ => hne (by rw [h1', h2'])
    rw [if_neg hcond, if_pos ⟨rfl, rfl⟩] at h2
    exact zero_ne_one h2
  have hA1 : A ≠ 1 := by
    intro h1
    refine hdistinct ⟨0, tp.q_prime.pos⟩ j (fun hp => hi (congrArg Prod.fst hp).symm) ?_
    rw [omegaSChar_col_align hG mp tp i j, ← hBdef, ← h1, hAdef]
    exact hpair
  have hB1 : B ≠ 1 := by
    intro h1
    refine hdistinct i ⟨0, tp.p_prime.pos⟩ (fun hp => hj (congrArg Prod.snd hp).symm) ?_
    rw [omegaSChar_row_align hG mp tp i j, ← hAdef, ← h1, hBdef]
    exact hpair
  -- the (3.5) relation, evaluated at `x`
  have hrel := ((tiCyclicW hG mp tp).chiFam_spec rfl (tiCyclicWDadeApp hG mp tp)).2.2.2
    A B hA1 hB1
  have hvanish : (tiCyclicWDadeApp hG mp tp).tau.toDadeMap
      ((tiCyclicW hG mp tp).alpha rfl A B) x = 0 :=
    OddOrder.Peterfalvi.S04.map_eq_zero_of_not_mem_conjugatesOfSet_of_forall_H_eq_bot
      (tiCyclicWDadeApp hG mp tp).tau.toDadeIsometryData.isDadeMap (fun _ => rfl) _ hx
  -- identify the χ-corners with the η-grid
  have hcorner : ∀ (k : Fin tp.q) (l : Fin tp.p)
      (pr : ((tiCyclicW hG mp tp).W1.subgroupOf (tiCyclicW hG mp tp).W →* ℂˣ)
        × ((tiCyclicW hG mp tp).W2.subgroupOf (tiCyclicW hG mp tp).W →* ℂˣ)),
      omegaSChar hG mp tp k l = (tiCyclicW hG mp tp).omegaProdChar pr.1 pr.2 →
      (tiCyclicW hG mp tp).chiFam rfl (tiCyclicWDadeApp hG mp tp) pr
        = tau3W hG mp tp (omegaS hG mp tp k l) := by
    intro k l pr hchar
    have h1 := (tiCyclicW hG mp tp).sigma_omega rfl (tiCyclicWDadeApp hG mp tp)
      ((tiCyclicW hG mp tp).omegaProdChar pr.1 pr.2)
    rw [(tiCyclicW hG mp tp).omegaProdEquiv_symm_omegaProdChar pr.1 pr.2] at h1
    rw [← h1, ← hchar, omegaS_eq_omega_omegaSChar]
    change _ = (tiCyclicW hG mp tp).sigmaIntegral rfl (tiCyclicWDadeApp hG mp tp) _
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
  have hc11 := hcorner i j (A, B) hpair.symm
  have hcA1 := hcorner i ⟨0, tp.p_prime.pos⟩ (A, 1) (omegaSChar_row_align hG mp tp i j)
  have hc1B := hcorner ⟨0, tp.q_prime.pos⟩ j (1, B) (omegaSChar_col_align hG mp tp i j)
  have htriv := ((tiCyclicW hG mp tp).chiFam_spec rfl (tiCyclicWDadeApp hG mp tp)).1
  -- evaluate at `x` and rearrange
  have hev := congrArg (fun f : ClassFunction G ℂ => f x) hrel
  rw [hvanish] at hev
  have hev' : (0 : ℂ) = 1 - tau3W hG mp tp (omegaS hG mp tp i ⟨0, tp.p_prime.pos⟩) x
      - tau3W hG mp tp (omegaS hG mp tp ⟨0, tp.q_prime.pos⟩ j) x
      + tau3W hG mp tp (omegaS hG mp tp i j) x := by
    rw [← hcA1, ← hc1B, ← hc11]
    calc (0 : ℂ) = (trivialClassFunction G
          - (tiCyclicW hG mp tp).chiFam rfl (tiCyclicWDadeApp hG mp tp) (A, 1)
          - (tiCyclicW hG mp tp).chiFam rfl (tiCyclicWDadeApp hG mp tp) (1, B)
          + (tiCyclicW hG mp tp).chiFam rfl (tiCyclicWDadeApp hG mp tp) (A, B)) x := hev
      _ = _ := by
        simp only [ClassFunction.add_apply, ClassFunction.sub_apply,
          trivialClassFunction_apply]
  exact hev'.symm

end Section16CharacterData

end

end OddOrder
