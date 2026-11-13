-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.Hypothesis.tauS_mu_row0_vanish_on_V
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:03:52.519872+00:00
-- url     : https://prove2.me/submissions/4b062115-7933-4864-b432-063945e8b01d

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_HonestTypeP2A0.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_HonestTypeP2A0

-- ===== OddOrder/Peterfalvi/S15_HonestTypeP2A0.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **Prime-`TI` support pin, proven** (Coq `prDade_sub_TIirr_on`, `PFsection4.v`): the `μ`-column
difference `μ_{0j} − μ_{0,#1}` is supported inside `A₀(S) = A(S) ∪ V^S` — its support meets `S`
only in `P^# ∪ V_S`, because the two prime-`TI` residues share the same `1_S`-part off `A₀(S)` and
it cancels in the difference.  This is the `S`-side instance of Coq `prDade_sub_TIirr_on`
(`μ2_{ij} − μ2_{ik} ∈ 'CF(S, 'A0)`).

**Honest signature (issue 9076, 2026-07-11)**: carries `(hj0 : (j:ℕ) ≠ 0)` — the unrestricted
`∀ j` form is *false* at the trivial column `j = 0` (`μ_{00}(1) = 1 ≠ μ_{0,#1}(1)`, and `1 ∉ A₀`).
The sole consumer `tauS_mu_row0_cross` (S15_SAndT) passes its `_hj`.

**Fully discharged (2026-07-11)**: the support claim is the `(13.18)` grounding field
`mu_diff_support` (issue 9081: producer-supplied by the proven
`Section16CharacterData.muS_diff_support`, Dade-free via `hyp46SmpCore`), and the degree
hypothesis is the proven per-entry degree `mu_apply_one_eq_u` (Pf (13.3)(a): `μ_{ij}(1) = u` for
`j ≠ 0`, via `mu_j_isIndPC` + `H_index_eq_uq`) — the same two steps Coq's `defGamma` uses
(`prDade_sub_TIirr` + the `FTprTIred1` `mulfI`-cancellation, `PFsection13.v:1909`). -/
theorem Hypothesis.tauS_mu_row0_diff_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (j : Fin hyp.p) (hj0 : (j : ℕ) ≠ 0) :
    (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
        - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore0 hyp.S hyp.Sdata) hyp.S :=
  hyp.mu_diff_support ⟨0, hyp.q_prime.pos⟩
    (fun h => hj0 (congrArg Fin.val h))
    (fun h => one_ne_zero (congrArg Fin.val h))
    ((hyp.mu_apply_one_eq_u hG ⟨0, hyp.q_prime.pos⟩ j
        (fun h => hj0 (congrArg Fin.val h))).trans
      (hyp.mu_apply_one_eq_u hG ⟨0, hyp.q_prime.pos⟩
        ⟨1, by have := hyp.three_le_p; omega⟩
        (fun h => one_ne_zero (congrArg Fin.val h))).symm)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Prime-`TI` `V`-value pin** (Coq `prTIirr_id` + Dade `Dade_id` on the regular set): on the
regular classes `conjClassSet(W \ (W₁ ∪ W₂)) = V^S`, the `'A0(S)`-Dade lift
`τ_S(μ_{0j} − μ_{0,#1})` agrees with the grid difference `η_{0j} − η_{0,#1}`.  Both reduce to the
same `ω`-value there: `τ_S = Ind_S^G` on `A₀(S)`-support (`normedTI 'A0`, `H = ⊥`) followed by the
prime-`TI` restriction identity `μ_{0j}|_V = ω`-value (Coq `prTIirr_id`), matching
`η_{0j}|_V = ω_{0j}|_V` (the (3.3) `τ₃ = Dade` identity on `V`).  Prime-`TI` theory, cf. issue
9014.

**Honest signature (issue 9076, 2026-07-11)**: carries `(hj0 : (j:ℕ) ≠ 0)` — the `V`-value
identity is meaningful only for the residue columns `j ≠ 0` (same honest fix as
`tauS_mu_row0_diff_support`); the sole consumer `tauS_mu_row0_cross` passes its `_hj`.

**Fully discharged (2026-07-12)**: at a regular point `x ~ w` (`w ∈ V_W ⊆ A₀(S)`, the `V`-part
of the honest `A₀` at the trivial conjugator) the Dade lift evaluates by the §2.5 point formula
(`dadeIntegralCharacterMap_apply_of_support` at the proven pin-2 support, then `dadeValue_eq` at
`h = 1` — all `A₀(S)`-stabilizers vanish, `forall_dadeHypS0_H_eq_bot`), giving the `S`-value
`(μ_{0j} − μ_{0,#1})(w)`; the `(4.3.c)` grounding field `mu_apply_of_not_mem_W2` (Coq
`prTIirr_id`) with `δ_j = 1` (`delta_eq_one_S`, Pf (13.3.c)) turns it into the `ω`-difference,
which is exactly the `η`-difference value by `eta_eq_tau_omega` + `tau3_apply_of_regular`
(the (3.2.c) regular-set identity). -/
theorem _root_.solution [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p)
    (hj0 : (j : ℕ) ≠ 0) :
    ∀ x ∈ conjClassSet ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
          ((hyp.dadeHypS0 hG).fullDadeIsometryData)
          (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
            - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
        - (hyp.eta ⟨0, hyp.q_prime.pos⟩ j
            - hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)) x = 0 := by
  classical
  intro x hx
  obtain ⟨w, hw, g, hg⟩ := OddOrder.GroupTheory.mem_conjClassSet.mp hx
  have hwW : w ∈ hyp.W := hw.1
  have hw12 : w ∉ (hyp.W1 : Set G) ∪ (hyp.W2 : Set G) := hw.2
  have hw2 : w ∉ (hyp.W2 : Set G) := fun h => hw12 (Or.inr h)
  have hwS : w ∈ hyp.S := ((le_of_eq hyp.W_eq_inter).trans inf_le_left) hwW
  have hconjwx : IsConj w x := isConj_iff.mpr ⟨g, hg⟩
  -- `w ∈ A₀(S)`: the `V`-part of the honest `A₀`, at the trivial conjugator
  have hwV : w ∈ OddOrder.GroupTheory.typePV hyp.S hyp.Sdata := by
    constructor
    · have hWeq : (hyp.Sdata.W : Set G) = (hyp.W : Set G) := by
        rw [hyp.Sdata.W_eq, hyp.Sdata_W1_eq, hyp.Sdata_W2_eq, ← hyp.W_eq_join]
      rw [hWeq]; exact hwW
    · rw [hyp.Sdata_W1_eq, hyp.Sdata_W2_eq]; exact hw12
  have hwA0 : w ∈ S10.typePACore0 hyp.S hyp.Sdata :=
    Or.inr (OddOrder.GroupTheory.subset_conjClassSetIn hwV)
  -- the Dade lift's value at `x ~ w·1`: the `(2.5)` point formula at the pin-2 support
  have hsupp := hyp.tauS_mu_row0_diff_support hG j hj0
  rw [OddOrder.RepresentationTheory.ClassFunction.sub_apply,
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support (hyp.dadeHypS0 hG)
      ((hyp.dadeHypS0 hG).fullDadeIsometryData) hsupp,
    (hyp.dadeHypS0 hG).dadeMap_apply]
  have h1H : (1 : G) ∈ (hyp.dadeHypS0 hG).H ⟨w, hwA0⟩ := by
    rw [hyp.forall_dadeHypS0_H_eq_bot hG hnoV ⟨w, hwA0⟩]
    exact Subgroup.mem_bot.mpr rfl
  have hconj1 : IsConj ((⟨w, hwA0⟩ :
      {a : G // a ∈ S10.typePACore0 hyp.S hyp.Sdata}).1 * 1) x := by
    rw [mul_one]; exact hconjwx
  rw [(hyp.dadeHypS0 hG).dadeValue_eq _ h1H hconj1]
  -- both sides reduce to the same `ω`-difference value at `w`
  have hmu : ∀ (l : Fin hyp.p), (l : ℕ) ≠ 0 →
      hyp.mu ⟨0, hyp.q_prime.pos⟩ l ⟨w, (hyp.dadeHypS0 hG).mem_L hwA0⟩
        = hyp.omega ⟨0, hyp.q_prime.pos⟩ l ⟨w, hwW⟩ := by
    intro l hl0
    rw [hyp.mu_apply_of_not_mem_W2 ⟨0, hyp.q_prime.pos⟩ l w hwW
      ((hyp.dadeHypS0 hG).mem_L hwA0) hw2, hyp.delta_eq_one_S hG l]
    norm_num
  have heta : ∀ (l : Fin hyp.p),
      hyp.eta ⟨0, hyp.q_prime.pos⟩ l x = hyp.omega ⟨0, hyp.q_prime.pos⟩ l ⟨w, hwW⟩ := by
    intro l
    rw [(hyp.eta ⟨0, hyp.q_prime.pos⟩ l).of_isConj hconjwx.symm, hyp.eta_eq_tau_omega,
      hyp.tau3_apply_of_regular _ w hwW hw12]
  rw [OddOrder.RepresentationTheory.ClassFunction.sub_apply,
      OddOrder.RepresentationTheory.ClassFunction.sub_apply,
    hmu j hj0, hmu ⟨1, by have := hyp.three_le_p; omega⟩ one_ne_zero,
    heta j, heta ⟨1, by have := hyp.three_le_p; omega⟩]
  ring

end OddOrder.Peterfalvi.S15
