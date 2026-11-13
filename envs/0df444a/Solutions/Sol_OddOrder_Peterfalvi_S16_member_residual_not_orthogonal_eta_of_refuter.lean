-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.member_residual_not_orthogonal_eta_of_refuter
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:17:57.967123+00:00
-- url     : https://prove2.me/submissions/72f563e5-2d6a-45c9-ad06-b711322cb767

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S05_TICyclic.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/TGapGridAlignment.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Theorems.Thm_OddOrder_Peterfalvi_S16_eta_eq_of_norm_one_regular_value_eq
import Theorems.Thm_OddOrder_Peterfalvi_S12_Hypothesis_alignedOmegaSigmaGrid_apply_eq_sourceCharacter

-- ===== OddOrder/Peterfalvi/S05_TICyclic.lean =====
namespace OddOrder.Peterfalvi.S05

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G] [Fintype G]

namespace TICyclicHypothesis

/-- **`omegaProdChar` is bimultiplicative** (`Ŵ₁ × Ŵ₂ → Ŵ` is a group homomorphism): since the dual
codomain `ℂˣ` is abelian, `ω_{(χ₁χ₁'),(χ₂χ₂')} = ω_{χ₁,χ₂} · ω_{χ₁',χ₂'}`.  With
`omegaProdEquiv_symm_omegaProdChar` this makes the index-pair extraction `omegaProdEquiv.symm`
multiplicative — the key step in showing a `W₁`-only character (trivial on `W₂`) has trivial
`W₂`-index, used in the (10.6)(a) column-structure argument. -/
theorem omegaProdChar_mul (hyp : TICyclicHypothesis G)
    (χ₁ χ₁' : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ χ₂' : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    hyp.omegaProdChar (χ₁ * χ₁') (χ₂ * χ₂')
      = hyp.omegaProdChar χ₁ χ₂ * hyp.omegaProdChar χ₁' χ₂' := by
  ext w
  simp only [omegaProdChar, MonoidHom.mul_apply, MonoidHom.comp_apply]
  exact mul_mul_mul_comm _ _ _ _

end TICyclicHypothesis

end OddOrder.Peterfalvi.S05

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TGapGridAlignment.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-- The omega character at `alignedOmegaEtaIndex` is exactly the transported
S12 source character. -/
theorem omegaMonoidHom_alignedOmegaEtaIndex [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W) (hodd : Odd (Nat.card G))
    (i : Fin s12.w1) (j : Fin s12.w2) :
    omegaMonoidHom base (alignedOmegaEtaIndex hG base s12 hW hodd i j).1
        (alignedOmegaEtaIndex hG base s12 hW hodd i j).2 =
      alignedOmegaSourceCharacterOnBase hG base s12 hW hodd i j := by
  exact (omegaMonoidHomEquiv base).apply_symm_apply _

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- The aligned S12 source character separates as its column-zero character
times its row-zero character.  This is the honest factorization used to build
a coordinate-respecting eta reindex; it does not assume that the abstract S15
omega labels are already separable. -/
theorem alignedOmegaSourceCharacter_eq_mul_axes [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin s12.w1) (j : Fin s12.w2) :
    s12.alignedOmegaSourceCharacter hG hodd i j =
      s12.alignedOmegaSourceCharacter hG hodd i 0 *
        s12.alignedOmegaSourceCharacter hG hodd 0 j := by
  classical
  let h := (s12.toCertainTypeHypothesis hG hodd).toHypothesis
  have : NeZero (Nat.card h.W1) :=
    ⟨by have := h.one_lt_card_W1; omega⟩
  have : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : s12.typeP.W1 ≤ M := s12.typeP.W1_le
  have hW2le : s12.typeP.W2 ≤ M :=
    OddOrder.Peterfalvi.S12.typePData_W2_le_self s12.typeP
  have hcardW1 : Nat.card ↥h.W1 = s12.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = s12.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) :=
    ⟨Nat.card_pos.ne'⟩
  let χ₂ : Fin s12.w2 → (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    fun k => OddOrder.Peterfalvi.S12.finCardEquivCharacterGroup _
      (finCongr hcardW2sub.symm k)
  let tic := OddOrder.Peterfalvi.S12.typePData_toTICyclicHypothesis
    s12.typeP hodd
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe
      (OddOrder.Peterfalvi.S12.typePData_W_le_self s12.typeP)).symm.trans
      (MulEquiv.subgroupCongr
        (OddOrder.Peterfalvi.S12.typePData_sup_subgroupOf_eq s12.typeP).symm)
  have hsource : ∀ a b, s12.alignedOmegaSourceCharacter hG hodd a b =
      (h.sdiffTICyclicHypothesis.omegaProdChar
        (h.w1CharEquiv (finCongr hcardW1.symm a)) (χ₂ b)).comp
          e.toMonoidHom := by
    intro a b
    unfold OddOrder.Peterfalvi.S12.Hypothesis.alignedOmegaSourceCharacter
    rfl
  have hrow0 : h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin s12.w1)) = 1 := by
    rw [show finCongr hcardW1.symm (0 : Fin s12.w1) = 0 from by ext; simp,
      h.w1CharEquiv_zero]
  have hcol0 : χ₂ 0 = 1 := by
    change OddOrder.Peterfalvi.S12.finCardEquivCharacterGroup _
      (finCongr hcardW2sub.symm (0 : Fin s12.w2)) = 1
    rw [show finCongr hcardW2sub.symm (0 : Fin s12.w2) = 0 from by ext; simp,
      OddOrder.Peterfalvi.S12.finCardEquivCharacterGroup_zero]
  rw [hsource i j, hsource i 0, hsource 0 j]
  rw [hrow0, hcol0]
  let row : (h.sdiffTICyclicHypothesis.W1.subgroupOf
      h.sdiffTICyclicHypothesis.W) →* ℂˣ :=
    h.w1CharEquiv (finCongr hcardW1.symm i)
  let col : (h.sdiffTICyclicHypothesis.W2.subgroupOf
      h.sdiffTICyclicHypothesis.W) →* ℂˣ := χ₂ j
  have hp := h.sdiffTICyclicHypothesis.omegaProdChar_mul row 1 1 col
  have hrowmul : row * 1 = row := mul_one row
  have hcolmul : 1 * col = col := one_mul col
  rw [hrowmul, hcolmul] at hp
  have hpcomp := congrArg
    (fun f : h.sdiffTICyclicHypothesis.W →* ℂˣ => f.comp e.toMonoidHom) hp
  rw [MonoidHom.mul_comp] at hpcomp
  exact hpcomp

/-- Transporting the honest source factorization to the common subgroup
preserves its product form. -/
theorem alignedOmegaSourceCharacterOnBase_eq_mul_axes [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W) (hodd : Odd (Nat.card G))
    (i : Fin s12.w1) (j : Fin s12.w2) :
    alignedOmegaSourceCharacterOnBase hG base s12 hW hodd i j =
      alignedOmegaSourceCharacterOnBase hG base s12 hW hodd i 0 *
        alignedOmegaSourceCharacterOnBase hG base s12 hW hodd 0 j := by
  apply MonoidHom.ext
  intro x
  change s12.alignedOmegaSourceCharacter hG hodd i j _ =
    s12.alignedOmegaSourceCharacter hG hodd i 0 _ *
      s12.alignedOmegaSourceCharacter hG hodd 0 j _
  exact DFunLike.congr_fun
    (alignedOmegaSourceCharacter_eq_mul_axes hG s12 hodd i j) _

/-- The character at the product-selected label is precisely the transported
source grid character. -/
theorem omegaMonoidHom_alignedOmegaProductIndex [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G))
    (i : Fin s12.w1) (j : Fin s12.w2) :
    omegaMonoidHom base
        (alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd i j).1
        (alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd i j).2 =
      alignedOmegaSourceCharacterOnBase hG base s12 hW hodd i j := by
  rw [show omegaMonoidHom base
      (alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd i j).1
      (alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd i j).2 =
        omegaMonoidHomEquiv base
          (alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd i j) from rfl,
    alignedOmegaProductIndex, Equiv.apply_symm_apply]
  change omegaMonoidHom base
      (alignedOmegaColumnIndex hG base s12 hW hodd j)
      ⟨0, base.p_prime.pos⟩ *
    omegaMonoidHom base ⟨0, base.q_prime.pos⟩
      (alignedOmegaRowIndex hG base s12 hW hodd i) =
    alignedOmegaSourceCharacterOnBase hG base s12 hW hodd i j
  rw [
    omegaMonoidHom_alignedOmegaColumnIndex hG base s12 hW hW1 hW2 hodd j,
    omegaMonoidHom_alignedOmegaRowIndex hG base s12 hW hW1 hW2 hodd i]
  exact (@mul_comm (↥base.W →* ℂˣ) _
      (alignedOmegaSourceCharacterOnBase hG base s12 hW hodd 0 j)
      (alignedOmegaSourceCharacterOnBase hG base s12 hW hodd i 0)).trans
    (alignedOmegaSourceCharacterOnBase_eq_mul_axes
      hG base s12 hW hodd i j).symm

/-- The factorwise product construction selects the same full omega entry as
the direct source-character pointer. -/
theorem alignedOmegaProductIndex_eq_alignedOmegaEtaIndex [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G))
    (i : Fin s12.w1) (j : Fin s12.w2) :
    alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd i j =
      alignedOmegaEtaIndex hG base s12 hW hodd i j := by
  apply (omegaMonoidHomEquiv base).injective
  rw [omegaMonoidHomEquiv_apply, omegaMonoidHomEquiv_apply,
    omegaMonoidHom_alignedOmegaProductIndex,
    omegaMonoidHom_alignedOmegaEtaIndex]

/-- On the source zero column, the product-selected label is exactly the
target zero-row axis label. -/
theorem alignedOmegaProductIndex_zero_column [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G)) (i : Fin s12.w1) :
    alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd i 0 =
      (⟨0, base.q_prime.pos⟩,
        alignedOmegaRowEquiv hG base s12 hW hW1 hW2 hodd i) := by
  apply (omegaMonoidHomEquiv base).injective
  rw [omegaMonoidHomEquiv_apply,
    omegaMonoidHom_alignedOmegaProductIndex,
    omegaMonoidHomEquiv_apply]
  change alignedOmegaSourceCharacterOnBase hG base s12 hW hodd i 0 =
    omegaMonoidHom base ⟨0, base.q_prime.pos⟩
      (alignedOmegaRowIndex hG base s12 hW hodd i)
  exact (omegaMonoidHom_alignedOmegaRowIndex
    hG base s12 hW hW1 hW2 hodd i).symm

/-- The source zero column is the target eta zero row, with the transposed
row equivalence. -/
theorem alignedOmegaEtaGrid_zero_column [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G)) (i : Fin s12.w1) :
    alignedOmegaEtaGrid hG base s12 hW hW1 hW2 hodd i 0 =
      base.eta ⟨0, base.q_prime.pos⟩
        (alignedOmegaRowEquiv hG base s12 hW hW1 hW2 hodd i) := by
  rw [alignedOmegaEtaGrid, alignedOmegaProductIndex_zero_column]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- The concrete S12 sigma-grid and the abstract S15 eta-grid agree on the
shared regular set after reindexing by `alignedOmegaEtaIndex`.  Both sides
restore the same transported multiplicative character there. -/
theorem alignedOmegaSigmaGrid_apply_eq_eta_alignedIndex [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W) (hodd : Odd (Nat.card G))
    (hV : typePV base.T s12.typeP =
      (base.W : Set G) \ ((base.W1 : Set G) ∪ (base.W2 : Set G)))
    (i : Fin s12.w1) (j : Fin s12.w2) {v : G}
    (hv : v ∈ typePV base.T s12.typeP) :
    s12.alignedOmegaSigmaGrid hG hodd i j v =
      base.eta (alignedOmegaEtaIndex hG base s12 hW hodd i j).1
        (alignedOmegaEtaIndex hG base s12 hW hodd i j).2 v := by
  have hvreg := hv
  rw [hV] at hvreg
  have hvW : v ∈ base.W := hvreg.1
  have hvnot : v ∉ (base.W1 : Set G) ∪ (base.W2 : Set G) := hvreg.2
  rw [s12.alignedOmegaSigmaGrid_apply_eq_sourceCharacter hG hodd i j hv,
    base.eta_eq_tau_omega,
    base.tau3_apply_of_regular _ v hvW hvnot]
  have hchars := omegaMonoidHom_alignedOmegaEtaIndex
    hG base s12 hW hodd i j
  have hval := DFunLike.congr_fun hchars (⟨v, hvW⟩ : ↥base.W)
  have hvalC := congrArg (fun z : ℂˣ => (z : ℂ)) hval
  rw [omegaMonoidHom_coe, alignedOmegaSourceCharacterOnBase,
    monoidHomTransportSubgroupEq_apply] at hvalC
  calc
    ((s12.alignedOmegaSourceCharacter hG hodd i j
        ⟨v, hv.1⟩ : ℂˣ) : ℂ) =
        ((s12.alignedOmegaSourceCharacter hG hodd i j
          (MulEquiv.subgroupCongr hW.symm ⟨v, hvW⟩) : ℂˣ) : ℂ) := by
            congr 2
    _ = base.omega (alignedOmegaEtaIndex hG base s12 hW hodd i j).1
          (alignedOmegaEtaIndex hG base s12 hW hodd i j).2
          ⟨v, hvW⟩ := hvalC.symm

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The concrete S12 sigma grid agrees on the regular set with the
coordinate-respecting, zero-axis-preserving eta grid. -/
theorem alignedOmegaSigmaGrid_apply_eq_alignedOmegaEtaGrid [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G))
    (hV : typePV base.T s12.typeP =
      (base.W : Set G) \ ((base.W1 : Set G) ∪ (base.W2 : Set G)))
    (i : Fin s12.w1) (j : Fin s12.w2) {v : G}
    (hv : v ∈ typePV base.T s12.typeP) :
    s12.alignedOmegaSigmaGrid hG hodd i j v =
      alignedOmegaEtaGrid hG base s12 hW hW1 hW2 hodd i j v := by
  rw [alignedOmegaEtaGrid,
    alignedOmegaProductIndex_eq_alignedOmegaEtaIndex]
  exact alignedOmegaSigmaGrid_apply_eq_eta_alignedIndex
    hG base s12 hW hodd hV i j hv

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Global sigma/eta grid identification** (Coq `cycTIisoC` for the T-side
transposition): each concrete S12 aligned sigma-grid entry *equals* the
corresponding coordinate-respecting eta-grid entry, globally.  The entry is a
norm-one virtual character agreeing with the eta entry on the shared regular
set, so (3.9)(a) rigidity applies.  This upgrades the landed regular-value
alignment to the global grid equality consumed by the transposed (11.8)
transport, with no carrier change and no sigma-map uniqueness assumption. -/
theorem alignedOmegaSigmaGrid_eq_alignedOmegaEtaGrid [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hodd : Odd (Nat.card G))
    (hV : typePV base.T s12.typeP =
      (base.W : Set G) \ ((base.W1 : Set G) ∪ (base.W2 : Set G)))
    (i : Fin s12.w1) (j : Fin s12.w2) :
    s12.alignedOmegaSigmaGrid hG hodd i j =
      alignedOmegaEtaGrid hG base s12 hW hW1 hW2 hodd i j := by
  have hnorm : ClassFunction.inner
      (s12.alignedOmegaSigmaGrid hG hodd i j)
      (s12.alignedOmegaSigmaGrid hG hodd i j) = 1 := by
    rw [s12.alignedOmegaSigmaGrid_inner hG hodd i i j j]
    simp
  exact eta_eq_of_norm_one_regular_value_eq base
    (s12.alignedOmegaSigmaGrid_mem_ZIrr hG hodd i j) hnorm
    (alignedOmegaProductIndex hG base s12 hW hW1 hW2 hodd i j)
    (fun w hwW hwnot => by
      have hv : w ∈ typePV base.T s12.typeP := by
        rw [hV]; exact ⟨hwW, hwnot⟩
      exact alignedOmegaSigmaGrid_apply_eq_alignedOmegaEtaGrid
        hG base s12 hW hW1 hW2 hodd hV i j hv)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.8), eta-grid endpoint** (Coq `FTtype34_not_ortho_cycTIiso`):
the Section 12 residual of a degree-`w₁` member `ζ` is *not* orthogonal to the
shared eta grid.  This transports the canonical refuter
`S13.zeta_residual_not_orthogonal_H0C_of_refuter` through the global sigma/eta
grid identification: the zero-column sum becomes the eta zero-row sum via the
zero-preserving transposed row enumeration, and each pairing entry is hit
through the aligned product pointer.  The Dade-image identification of the
source is taken as the `himage` input (discharged by
`s12Tau_zeroColumn_sub_eq_tSideDadeMap` at the (14.9) consumer). -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hV : typePV base.T s12.typeP =
      (base.W : Set G) \ ((base.W1 : Set G) ∪ (base.W2 : Set G)))
    (htype : IsTypeIII base.T ∨ IsTypeIV base.T)
    (hM2 : secondDerivedInAmbient base.T =
      s12.typeP.H ⊔
        (s12.typeP.U ⊓ Subgroup.centralizer (s12.typeP.H : Set G)))
    (hHcard : Nat.card ↥s12.typeP.H = s12.w2 ^ s12.w1)
    (hrefute : ∀ s13hyp : OddOrder.Peterfalvi.S13.Hypothesis base.T,
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        s13hyp.base.tau (s13hyp.SOf s13hyp.H0C) s13hyp.base.A0))
    (zeta : ClassFunction ↥base.T ℂ)
    (hzetaS : zeta ∈ OddOrder.Peterfalvi.S12.inducedFamily base.T)
    (hzetairr : IsIrreducibleCharacter zeta)
    (hzeta1 : zeta 1 = (s12.w1 : ℂ))
    (source : ClassFunction G ℂ)
    (himage : s12.tau
        ((∑ i' : Fin s12.w1, s12.muGrid hG hG.odd i' 0) - zeta) = source) :
    ¬ ∀ (i : Fin base.q) (j : Fin base.p),
      ClassFunction.inner
        (source - ∑ j' : Fin base.p, base.eta ⟨0, base.q_prime.pos⟩ j')
        (base.eta i j) = 0 := by
  intro horth
  apply OddOrder.Peterfalvi.S13.zeta_residual_not_orthogonal_H0C_of_refuter hG s12 htype hM2
    hHcard hrefute hzetaS hzetairr hzeta1
  intro i j
  have hglobal : ∀ (a : Fin s12.w1) (b : Fin s12.w2),
      s12.alignedOmegaSigmaGrid hG hG.odd a b =
        alignedOmegaEtaGrid hG base s12 hW hW1 hW2 hG.odd a b :=
    fun a b => alignedOmegaSigmaGrid_eq_alignedOmegaEtaGrid
      hG base s12 hW hW1 hW2 hG.odd hV a b
  have hsum : (∑ i' : Fin s12.w1, s12.alignedOmegaSigmaGrid hG hG.odd i' 0) =
      ∑ j' : Fin base.p, base.eta ⟨0, base.q_prime.pos⟩ j' := by
    calc (∑ i' : Fin s12.w1, s12.alignedOmegaSigmaGrid hG hG.odd i' 0)
        = ∑ i' : Fin s12.w1, base.eta ⟨0, base.q_prime.pos⟩
            (alignedOmegaRowEquiv hG base s12 hW hW1 hW2 hG.odd i') := by
          refine Finset.sum_congr rfl fun i' _ => ?_
          rw [hglobal i' 0, alignedOmegaEtaGrid_zero_column]
      _ = ∑ j' : Fin base.p, base.eta ⟨0, base.q_prime.pos⟩ j' := by
          simpa using Equiv.sum_comp
            (alignedOmegaRowEquiv hG base s12 hW hW1 hW2 hG.odd)
            (fun j' : Fin base.p => base.eta ⟨0, base.q_prime.pos⟩ j')
  rw [himage, hsum, hglobal i j]
  exact horth
    (alignedOmegaProductIndex hG base s12 hW hW1 hW2 hG.odd i j).1
    (alignedOmegaProductIndex hG base s12 hW hW1 hW2 hG.odd i j).2

end OddOrder.Peterfalvi.S16
