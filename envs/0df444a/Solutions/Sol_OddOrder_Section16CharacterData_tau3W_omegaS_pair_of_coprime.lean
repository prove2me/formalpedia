-- Prove2me | solution 1 for OddOrder.Section16CharacterData.tau3W_omegaS_pair_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T18:05:54.767455+00:00
-- url     : https://prove2.me/submissions/ebac2d15-c3e0-4c39-a097-05633fae1b19

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S06_CertainTypeCharacters.lean
--   OddOrder/FeitThompsonSetup.lean
--   OddOrder/FeitThompsonCharacterData.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_FeitThompsonCharacterData

-- ===== OddOrder/Peterfalvi/S06_CertainTypeCharacters.lean =====
namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S05

variable {L : Type*} [Group L] [Fintype L]

section CyclicPowEnum

variable (D : Type*) [Group D] [Finite D] [IsCyclic D]

variable {D} {n : ℕ}

/-- The power enumeration pairs indices summing to `0 (mod n)` into inverse elements — the
abstract form of "index negation = inversion". -/
theorem cyclicPowEnum_eq_inv_of_add_mod_eq_zero (hn : Nat.card D = n) {i j : Fin n}
    (hij : ((i : ℕ) + (j : ℕ)) % n = 0) :
    cyclicPowEnum hn i = (cyclicPowEnum hn j)⁻¹ := by
  have hord : orderOf (cyclicGenerator D) = n := (orderOf_cyclicGenerator D).trans hn
  have key : cyclicPowEnum hn i * cyclicPowEnum hn j = 1 := by
    change cyclicGenerator D ^ (i : ℕ) * cyclicGenerator D ^ (j : ℕ) = 1
    rw [← pow_add, ← pow_mod_orderOf, hord, hij, pow_zero]
  exact mul_eq_one_iff_eq_inv.mp key

end CyclicPowEnum

namespace Hypothesis

variable (h : Hypothesis L)

/-- **Index negation is character inversion** (Peterfalvi (3.5)/(3.9.a) power-grid pairing):
`w1CharEquiv ((w₁ − i) % w₁) = (w1CharEquiv i)⁻¹`.  The `(3.9.a)` `finNeg`-pairing of the
`η`-grid is honest precisely because the enumeration satisfies this. -/
theorem w1CharEquiv_finNeg [NeZero (Nat.card h.W1)] (i : Fin (Nat.card h.W1)) :
    h.w1CharEquiv ⟨(Nat.card h.W1 - (i : ℕ)) % Nat.card h.W1,
        Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))⟩
      = (h.w1CharEquiv i)⁻¹ := by
  have := h.isCyclic_w1CharGroup
  rw [w1CharEquiv]
  refine cyclicPowEnum_eq_inv_of_add_mod_eq_zero _ ?_
  change ((Nat.card h.W1 - (i : ℕ)) % Nat.card h.W1 + (i : ℕ)) % Nat.card h.W1 = 0
  rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
  · simp [h0]
  · have hi : (i : ℕ) < Nat.card h.W1 := i.2
    rw [Nat.mod_eq_of_lt (by omega : Nat.card h.W1 - (i : ℕ) < Nat.card h.W1),
      Nat.sub_add_cancel hi.le, Nat.mod_self]

end Hypothesis

end OddOrder.Peterfalvi.S06

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

/-- **Column negation is character inversion** (Peterfalvi (3.5)/(3.9.a) power-grid pairing,
`W₂`-column half): `chi2enum ((p − j) % p) = (chi2enum j)⁻¹`. -/
theorem chi2enum_finNeg (j : Fin tp.p) :
    chi2enum hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j)
      = (chi2enum hG mp tp j)⁻¹ := by
  have := (mp.certainTypeS hG).sdiffTICyclicHypothesis.isCyclic_charGroup_subgroupOf
    (mp.certainTypeS hG).sdiffTICyclicHypothesis.W2_le_W
  rw [chi2enum]
  refine OddOrder.Peterfalvi.S06.cyclicPowEnum_eq_inv_of_add_mod_eq_zero _ ?_
  change ((tp.p - (j : ℕ)) % tp.p + (j : ℕ)) % tp.p = 0
  rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | hpos
  · simp [h0]
  · have hj : (j : ℕ) < tp.p := j.2
    rw [Nat.mod_eq_of_lt (by omega : tp.p - (j : ℕ) < tp.p),
      Nat.sub_add_cancel hj.le, Nat.mod_self]

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
/-- `omegaS i j` is the `tiCyclicW`-grid character of its underlying hom. -/
theorem omegaS_eq_omega_omegaSChar (i : Fin tp.q) (j : Fin tp.p) :
    omegaS hG mp tp i j
      = ((tiCyclicW hG mp tp).omega (omegaSChar hG mp tp i j)).toClassFunction := by
  ext w
  simp only [omegaS, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    Peterfalvi.S06.Hypothesis.chiColumn, Peterfalvi.S05.TICyclicHypothesis.omega_apply,
    omegaSChar]
  rfl

omit [NeZero (Nat.card ↥(mp.certainTypeS hG).W1)] [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)] in
/-- The cyclic factor `W = W₁ ⊔ W₂` has order `|W| = q·p` (`W₁ ∩ W₂ = ⊥`, `W₁` normalizes `W₂`
since they commute). -/
theorem cardTPW : Nat.card ↥tp.W = tp.q * tp.p := by
  have hconj : ∀ x ∈ tp.W1, ∀ a ∈ tp.W2, x * a * x⁻¹ ∈ tp.W2 := by
    intro x hx a ha
    have hc : Commute x a := tp.W1_commutes_W2 x hx a ha
    have hxa : x * a * x⁻¹ = a := by rw [hc.eq]; group
    rw [hxa]; exact ha
  have hW1norm : tp.W1 ≤ Subgroup.normalizer (tp.W2 : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨fun ha => hconj x hx a ha, fun ha => ?_⟩
    have hb := hconj x⁻¹ (tp.W1.inv_mem hx) (x * a * x⁻¹) ha
    simpa [mul_assoc] using hb
  rw [tp.W_eq_join,
    OddOrder.BG.Ch3.S12.card_sup_eq_mul_of_le_normalizer_of_disjoint hW1norm
      tp.W1_inf_W2_eq_bot,
    ← tp.q_eq_card_W1, ← tp.p_eq_card_W2]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **The `eqQ` reindex commutes with index negation**: `eqQ` is a `finCongr` (value-preserving
cast along `|W₁| = q`), so the `S15.finNeg` negation on `Fin tp.q` transports to the explicit
`(w₁ − ·) % w₁` negation on `Fin |W₁|` — the index form of `w1CharEquiv_finNeg`. -/
theorem eqQ_finNeg (i : Fin tp.q) :
    eqQ hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
      = ⟨(Nat.card ↥(mp.certainTypeS hG).W1 - ((eqQ hG mp tp i : Fin _) : ℕ))
            % Nat.card ↥(mp.certainTypeS hG).W1,
          Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))⟩ := by
  apply Fin.ext
  simp only [eqQ, finCongr_apply, Fin.val_cast, OddOrder.Peterfalvi.S15.finNeg]
  rw [cardCertainTypeS_W1 hG mp tp]

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
/-- **Index negation is character inversion for the S-side grid characters** (Peterfalvi (3.5):
the grid is indexed by character powers, so `ω_{−i,−j} = ω_{ij}⁻¹`).  Assembled from the two
power-enumeration halves (`w1CharEquiv_finNeg` via the `eqQ` cast, `chi2enum_finNeg`) and the
coordinatewise inversion `omegaProdChar_inv`. -/
theorem omegaSChar_finNeg (i : Fin tp.q) (j : Fin tp.p) :
    omegaSChar hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
        (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j)
      = (omegaSChar hG mp tp i j)⁻¹ := by
  rw [omegaSChar, omegaSChar, eqQ_finNeg hG mp tp i,
    (mp.certainTypeS hG).w1CharEquiv_finNeg (eqQ hG mp tp i),
    chi2enum_finNeg hG mp tp j]
  -- `(ω(χ₁⁻¹, χ₂⁻¹)).comp e = (ω(χ₁, χ₂).comp e)⁻¹`: pointwise, `ℂˣ` values invert
  -- coordinatewise (`omegaProdChar` is the product of the two coordinate pullbacks).
  ext w
  simp only [MonoidHom.comp_apply, MonoidHom.inv_apply,
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply,
    Units.val_mul, Units.val_inv_eq_inv_val, mul_inv]
  -- the row factor's `⁻¹` sits at the (defeq) `W₁ ⊔ W₂`-form hom type, where the `simp`
  -- lemmas do not fire syntactically; close it by definitional unfolding of the pointwise inv.
  congr 1
  exact Units.val_inv_eq_inv_val _

omit [NeZero (Nat.card ↥(Section16MaximalPair.certainTypeT hG mp).W1)] in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (3.9.a) conjugate-pair symmetry on generic elements** (issue-3002 supply):
for `g` of order prime to `pq`, the `η`-grid pairs under the index negation `(i,j) ↦ (−i,−j)`
(`S15.finNeg`), `(τ₃ω)_{−i,−j}(g) = (τ₃ω)_{ij}(g)`.

Peterfalvi's (3.9.a) content: the negated-index grid character is the *inverse* linear character
(`omegaSChar_finNeg` — honest because the enumerations are **power enumerations**, Peterfalvi's
own (3.5) grid indexing), whose `ω` is the complex conjugate (`galoisMap_conj_omega`); `σ`
intertwines coefficientwise Galois action ((3.9.a), `sigma_mapRingEquiv_comm`), so
`η_{−i,−j}(g) = conj (η_{ij}(g))`; and the value `η_{ij}(g)` is a rational **integer** by (3.9.c)
(`exists_intCast_sigma_omega_apply`, `Coprime(ord g, pq)`), hence conjugation-fixed. -/
theorem _root_.solution (i : Fin tp.q) (j : Fin tp.p) {g : G}
    (hg : Nat.Coprime (orderOf g) (tp.p * tp.q)) :
    tau3W hG mp tp (omegaS hG mp tp (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
        (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j)) g
      = tau3W hG mp tp (omegaS hG mp tp i j) g := by
  classical
  have : Fintype ↥tp.W := Fintype.ofFinite _
  -- (3.9.c): the σ-value at the base index is a rational integer.
  have hdvd : orderOf (omegaSChar hG mp tp i j) ∣ tp.p * tp.q := by
    set ξ := omegaSChar hG mp tp i j with hξ
    have hpow : ξ ^ Fintype.card ↥tp.W = 1 := by
      ext w
      rw [MonoidHom.pow_apply, MonoidHom.one_apply, ← map_pow, pow_card_eq_one, map_one]
    have hcardW : Fintype.card ↥tp.W = tp.p * tp.q := by
      rw [← Nat.card_eq_fintype_card, cardTPW mp tp, Nat.mul_comm]
    rw [← hcardW]
    exact orderOf_dvd_of_pow_eq_one hpow
  obtain ⟨n, hn⟩ := (tiCyclicW hG mp tp).exists_intCast_sigma_omega_apply rfl
    (tiCyclicWDadeApp hG mp tp) (omegaSChar hG mp tp i j) (hg.coprime_dvd_right hdvd)
  -- the negated-index grid character is the Galois conjugate of the base one
  have homega : (tiCyclicW hG mp tp).omega (omegaSChar hG mp tp
        (OddOrder.Peterfalvi.S15.finNeg tp.q_prime.pos i)
        (OddOrder.Peterfalvi.S15.finNeg tp.p_prime.pos j))
      = IrreducibleCharacter.galoisMap Complex.conjAe.toRingEquiv
          ((tiCyclicW hG mp tp).omega (omegaSChar hG mp tp i j)) := by
    rw [OddOrder.Peterfalvi.S06.galoisMap_conj_omega]
    exact congrArg _ (omegaSChar_finNeg hG mp tp i j)
  rw [omegaS_eq_omega_omegaSChar, omegaS_eq_omega_omegaSChar]
  change (tiCyclicW hG mp tp).sigmaIntegral rfl (tiCyclicWDadeApp hG mp tp) _ g
    = (tiCyclicW hG mp tp).sigmaIntegral rfl (tiCyclicWDadeApp hG mp tp) _ g
  rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply,
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply, homega,
    ← (tiCyclicW hG mp tp).sigma_mapRingEquiv_comm rfl (tiCyclicWDadeApp hG mp tp),
    OddOrder.RepresentationTheory.ClassFunction.mapRingEquiv_apply]
  have hv : (tiCyclicW hG mp tp).sigma rfl (tiCyclicWDadeApp hG mp tp)
      ((tiCyclicW hG mp tp).omega (omegaSChar hG mp tp i j)).toClassFunction g = (n : ℂ) := hn
  rw [hv]
  exact map_intCast _ n

end Section16CharacterData

end

end OddOrder
