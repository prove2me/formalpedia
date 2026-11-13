-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.Hypothesis.tau1T_ofHonest_nuRow_eta_row
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:50:14.721563+00:00
-- url     : https://prove2.me/submissions/a651ce90-7d49-400d-92bf-437a2b025e89

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_Tau1T.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_Tau1T

-- ===== OddOrder/Peterfalvi/S15_Tau1T.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3.c)-at-`T`, the ν-row formula for `τ₁T = tau1T_ofHonest`** (mirror of
`tau1S_ofHonest_muColumn_formula`; Coq `FTtypeP_coherence` with `typeP_TIred_coherent`'s
global-sign disjunction, transposed): the (9.11)-`T` coherent extension sends every reducible
ν-row sum `ν_i = ∑_j ν_{ij}` (`i ≠ 0`) to the aligned `η`-row sum `∑_j η_{ij}` — either
uniformly, or (the `q = 3` sign-flip exception) with a global negative sign and the two nonzero
rows swapped.  The `.choose_spec` of the pinned carrier. -/
theorem Hypothesis.tau1T_ofHonest_nuRow_formula [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    (∀ i : Fin hyp.q, i ≠ ⟨0, hyp.q_prime.pos⟩ →
      hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (∑ j : Fin hyp.p, hyp.nu i j)
        = ∑ j : Fin hyp.p, hyp.eta i j) ∨
    (hyp.q = 3 ∧ ∀ i i' : Fin hyp.q, i ≠ ⟨0, hyp.q_prime.pos⟩ →
      i' ≠ ⟨0, hyp.q_prime.pos⟩ → i ≠ i' →
      hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (∑ j : Fin hyp.p, hyp.nu i j)
        = -∑ j : Fin hyp.p, hyp.eta i' j) :=
  (hyp.sSet_coherent_indT_A_pinned hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief).choose_spec

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The per-row (13.3.c)-`T` formula** (the row-transposed mirror of
`tau1S_ofHonest_mu_col_eta_col_one`'s shape, generalized to an arbitrary source row): for each
nonzero row `r` there are a nonzero row `r'` and a sign `δ' = ±1` with
`τ₁T(ν_r) = δ'·∑_j η_{r'j}` — clean: `r' = r`, `δ' = 1`; the `q = 3` flip: `r'` = the other
nonzero row, `δ' = −1`.  This is the exact `β`-form input of the (13.4) θ-package's conjunct 3
(where the `η`-row index must be quantified separately from the θ-row). -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    {r : Fin hyp.q} (hr : r ≠ ⟨0, hyp.q_prime.pos⟩) :
    ∃ (r' : Fin hyp.q) (δ' : ℤ), r' ≠ ⟨0, hyp.q_prime.pos⟩ ∧ (δ' = 1 ∨ δ' = -1) ∧
      hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (∑ j : Fin hyp.p, hyp.nu r j)
        = (δ' : ℂ) • ∑ j : Fin hyp.p, hyp.eta r' j := by
  classical
  rcases hyp.tau1T_ofHonest_nuRow_formula hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief with
    hclean | ⟨hq3, hflip⟩
  · -- clean branch: `r' = r`, `δ' = 1`
    exact ⟨r, 1, hr, Or.inl rfl, by rw [hclean r hr]; push_cast; rw [one_smul]⟩
  · -- `q = 3` sign-flip branch: `r'` = the other nonzero row, `δ' = −1`
    have h1lt : 1 < hyp.q := hyp.q_prime.one_lt
    have h2lt : 2 < hyp.q := by omega
    have hrval : r.val = 1 ∨ r.val = 2 := by
      have hlt := r.isLt
      have h0 : r.val ≠ 0 := fun h => hr (Fin.ext h)
      omega
    rcases hrval with h1 | h2
    · -- `r.val = 1`: the other row is `⟨2⟩`
      have hr'0 : (⟨2, h2lt⟩ : Fin hyp.q) ≠ ⟨0, hyp.q_prime.pos⟩ := by
        intro h; exact absurd (congrArg Fin.val h) (by norm_num)
      have hrne : r ≠ ⟨2, h2lt⟩ := by
        intro h
        have h2v : r.val = 2 := by rw [h]
        omega
      refine ⟨⟨2, h2lt⟩, -1, hr'0, Or.inr rfl, ?_⟩
      rw [hflip r ⟨2, h2lt⟩ hr hr'0 hrne]
      push_cast
      rw [neg_one_smul]
    · -- `r.val = 2`: the other row is `⟨1⟩`
      have hr'0 : (⟨1, h1lt⟩ : Fin hyp.q) ≠ ⟨0, hyp.q_prime.pos⟩ := by
        intro h; exact absurd (congrArg Fin.val h) one_ne_zero
      have hrne : r ≠ ⟨1, h1lt⟩ := by
        intro h
        have h1v : r.val = 1 := by rw [h]
        omega
      refine ⟨⟨1, h1lt⟩, -1, hr'0, Or.inr rfl, ?_⟩
      rw [hflip r ⟨1, h1lt⟩ hr hr'0 hrne]
      push_cast
      rw [neg_one_smul]

end OddOrder.Peterfalvi.S15
