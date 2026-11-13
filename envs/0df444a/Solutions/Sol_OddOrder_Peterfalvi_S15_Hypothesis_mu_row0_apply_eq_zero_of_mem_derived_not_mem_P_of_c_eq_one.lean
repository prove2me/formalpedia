-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.Hypothesis.mu_row0_apply_eq_zero_of_mem_derived_not_mem_P_of_c_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T15:57:45.781203+00:00
-- url     : https://prove2.me/submissions/bf162d90-8aeb-47d2-bb6e-143fec1bd3dd

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

/-- **`C = ⊥` from (13.12)** — the subgroup-level form of the regularity `c = 1`
(Coq `FTtypeP_reg_Fcore`).  The explicit input keeps downstream (13.18) consumers independent of
the legacy character-degree carrier. -/
theorem Hypothesis.C_eq_bot_of_c_eq_one [Finite G] (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) : hyp.C = ⊥ :=
  Subgroup.card_eq_one.mp (by rw [← hyp.c_eq_card_C]; exact hc1)

/-- **`H = P` from (13.12)** — with `C = ⊥` the (13.5) subgroup `H = P C` collapses to `P`. -/
theorem Hypothesis.H_eq_P_of_c_eq_one [Finite G] (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) : hyp.H = hyp.P := by
  change hyp.P ⊔ hyp.C = hyp.P
  rw [hyp.C_eq_bot_of_c_eq_one hc1, sup_bot_eq]

/-- **`q ∤ |S′|` from (13.12)**: `|S′| = p^q·(u·c) = p^q·u`, with `q ∤ p^q`
(`p ≠ q`) and `q ∤ u` (`u ≡ 1 (mod q)`, `u_modEq_one`). -/
theorem Hypothesis.not_q_dvd_card_derived_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) :
    ¬ hyp.q ∣ Nat.card ↥(OddOrder.GroupTheory.derivedInG hyp.S) := by
  rw [hyp.card_deriv_S_eq, hyp.card_P_eq hG hyp.Sdata_W2_eq, hyp.card_U_eq_uc,
    hc1, mul_one]
  intro hdvd
  rcases (Nat.Prime.dvd_mul hyp.q_prime).mp hdvd with h | h
  · exact hyp.p_ne_q ((Nat.prime_dvd_prime_iff_eq hyp.q_prime hyp.p_prime).mp
      (hyp.q_prime.dvd_of_dvd_pow h)).symm
  · have hmod : hyp.u % hyp.q = 1 % hyp.q := hyp.u_modEq_one hG
    obtain ⟨k, hk⟩ := h
    have hq2 : 2 ≤ hyp.q := hyp.q_prime.two_le
    have h1q : 1 % hyp.q = 1 := Nat.one_mod_eq_one.mpr (by omega)
    rw [hk, Nat.mul_mod_right, h1q] at hmod
    omega

/-- **`W₁ ⊓ S′ = ⊥` from (13.12)**: an element of the intersection has order dividing both `q`
and `|S′|`; `q ∤ |S′|` with `q` prime forces order `1`. -/
theorem Hypothesis.W1_inf_derived_eq_bot_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) :
    hyp.W1 ⊓ OddOrder.GroupTheory.derivedInG hyp.S = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hord_q : orderOf x ∣ hyp.q := by
    rw [hyp.q_eq_card_W1]
    have h := orderOf_dvd_natCard (⟨x, hx.1⟩ : ↥hyp.W1)
    rwa [← Subgroup.orderOf_coe] at h
  have hord_D : orderOf x ∣ Nat.card ↥(OddOrder.GroupTheory.derivedInG hyp.S) := by
    have h := orderOf_dvd_natCard
      (⟨x, hx.2⟩ : ↥(OddOrder.GroupTheory.derivedInG hyp.S))
    rwa [← Subgroup.orderOf_coe] at h
  rcases (Nat.dvd_prime hyp.q_prime).mp hord_q with h1 | hq
  · exact orderOf_eq_one_iff.mp h1
  · exact absurd (hq ▸ hord_D) (hyp.not_q_dvd_card_derived_of_c_eq_one hG hc1)

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`supp(μ_j) ⊆ P`** ((13.3.a)+(13.12), the `seqInd_on` step of Coq `PVSbeta`): the column
sum `μ_j = Ind_{H}^S θ` (`mu_j_isIndPC`) with `H = P` (`H_eq_P`), and `P ◁ S` confines the
induced support to `P` (`support_induce_subset_of_normal`). -/
theorem Hypothesis.mu_colSum_support_subset_P_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1)
    (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    ((∑ i : Fin hyp.q, hyp.mu i j) : ClassFunction ↥hyp.S ℂ).support ⊆
      hyp.H.subgroupOf hyp.S := by
  classical
  obtain ⟨θ, _hθirr, _hθ1, hθeq⟩ := hyp.mu_j_isIndPC hG j hj
  have hPnorm : (hyp.H.subgroupOf hyp.S).Normal := by
    rw [hyp.H_eq_P_of_c_eq_one hc1]
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer ?_).mpr ?_
    · rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    · rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  let : Fintype ↥(hyp.H.subgroupOf hyp.S) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(hyp.H.subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [hθeq]
  exact ClassFunction.support_induce_subset_of_normal _ θ

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.18.a), the `S′−P` vanishing (`hmuD`)**: `μ_{0j}(z) = 0` for
`z ∈ S′ − P`, `j ≠ 0` (Pf p.83 "`μ_{0j}` vanishes on `S′ − P` by (13.3.a) and (13.12)";
Coq `PVSbeta`, PU-branch).

*Proof.*  Off the `W`-conjugates the `(13.1.e)` induction identity `mu_definition` has vanishing
left side, so all rows of column `j` agree at `z`; `z ∈ S′ − P` is indeed off the
`W`-conjugates, since a conjugate `x⁻¹zx ∈ W` would lie in `W ∩ S′` (`S′` is
conjugation-stable in `S`), and `W ∩ S′ ≤ P` (`W₁ ⊓ S′ = ⊥` splits the cyclic `W = W₁W₂`,
`W₂ ≤ P`), forcing `z ∈ P` (`S ≤ N_G(P)`) — contradiction.  Hence
`q·μ_{0j}(z) = ∑ᵢ μ_{ij}(z) = μ_j(z) = 0` (`mu_colSum_support_subset_P` with `H = P`), and
`q ≠ 0` cancels. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1)
    (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩)
    (z : ↥hyp.S) (hzD : (z : G) ∈ OddOrder.GroupTheory.derivedInG hyp.S)
    (hzP : (z : G) ∉ hyp.P) :
    hyp.mu ⟨0, hyp.q_prime.pos⟩ j z = 0 := by
  classical
  -- `z` avoids the `W`-conjugates.
  have hz_notin : (z : ↥hyp.S) ∉
      ClassFunction.conjugatesInto (hyp.W.subgroupOf hyp.S) := by
    rintro ⟨x, hxzx⟩
    set w : ↥hyp.S := x⁻¹ * z * x with hwdef
    have hwW : (w : G) ∈ hyp.W := Subgroup.mem_subgroupOf.mp hxzx
    have hwD : (w : G) ∈ OddOrder.GroupTheory.derivedInG hyp.S := by
      obtain ⟨z', hz', hzz'⟩ := hzD
      have hz'eq : z' = z := Subtype.ext hzz'
      exact ⟨x⁻¹ * z' * x, by
        simpa using Subgroup.Normal.conj_mem inferInstance z' hz' x⁻¹, by
        rw [hz'eq]; rfl⟩
    have := hyp.W_cyclic
    let : CommGroup ↥hyp.W := IsCyclic.commGroup
    have hW1le : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
    have hW2le : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
    have htop : (hyp.W1.subgroupOf hyp.W) ⊔ (hyp.W2.subgroupOf hyp.W) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hW1le hW2le, ← hyp.W_eq_join, Subgroup.subgroupOf_self]
    have hmem : (⟨(w : G), hwW⟩ : ↥hyp.W) ∈
        (hyp.W1.subgroupOf hyp.W) ⊔ (hyp.W2.subgroupOf hyp.W) :=
      htop ▸ Subgroup.mem_top _
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hmem
    have haW1 : (a : G) ∈ hyp.W1 := Subgroup.mem_subgroupOf.mp ha
    have hbW2 : (b : G) ∈ hyp.W2 := Subgroup.mem_subgroupOf.mp hb
    have habG : (a : G) * (b : G) = (w : G) := by
      have := congrArg (fun t : ↥hyp.W => (t : G)) hab
      simpa using this
    have hPle : hyp.P ≤ OddOrder.GroupTheory.derivedInG hyp.S := by
      rw [hyp.S_deriv_eq_PU]; exact le_sup_left
    have haD : (a : G) ∈ OddOrder.GroupTheory.derivedInG hyp.S := by
      have heq : (a : G) = (w : G) * (b : G)⁻¹ := by rw [← habG]; group
      rw [heq]
      exact Subgroup.mul_mem _ hwD (Subgroup.inv_mem _ (hPle (W2_le_P hG hyp hbW2)))
    have ha1 : (a : G) = 1 := by
      have hmem2 : (a : G) ∈ hyp.W1 ⊓ OddOrder.GroupTheory.derivedInG hyp.S := ⟨haW1, haD⟩
      rwa [hyp.W1_inf_derived_eq_bot_of_c_eq_one hG hc1, Subgroup.mem_bot] at hmem2
    have hwP : (w : G) ∈ hyp.P := by
      rw [← habG, ha1, one_mul]
      exact W2_le_P hG hyp hbW2
    apply hzP
    have hzw : (z : G) = (x : G) * (w : G) * (x : G)⁻¹ := by
      rw [hwdef]; push_cast; group
    rw [hzw]
    have hSnorm : hyp.S ≤ Subgroup.normalizer hyp.P := by
      rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
    exact (Subgroup.mem_normalizer_iff.mp (hSnorm x.2) _).mp hwP
  -- All rows of column `j` agree at `z`.
  have hall : ∀ i : Fin hyp.q, hyp.mu i j z = hyp.mu ⟨0, hyp.q_prime.pos⟩ j z := by
    intro i
    have hdef := congrArg (fun f : ClassFunction ↥hyp.S ℂ => f z) (hyp.mu_definition i j)
    have hLz : ClassFunction.induce (hyp.W.subgroupOf hyp.S)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq hyp.W_eq_inter).trans inf_le_left)).toMonoidHom
          (hyp.omega i j - hyp.omega ⟨0, hyp.q_prime.pos⟩ j)) z = 0 := by
      by_contra h
      exact hz_notin
        (ClassFunction.support_induce_subset_conjugatesInto _ _
          (ClassFunction.mem_support.mpr h))
    simp only [hLz, ClassFunction.smul_apply, ClassFunction.sub_apply] at hdef
    have hδ : (hyp.delta j : ℂ) ≠ 0 := by
      rcases hyp.delta_pm_one.1 j with h | h <;> rw [h] <;> norm_num
    have hsub := (mul_eq_zero.mp hdef.symm).resolve_left hδ
    exact sub_eq_zero.mp hsub
  -- The column sum vanishes at `z` (`supp(μ_j) ⊆ H = P`, `z ∉ P`).
  have hsum : (∑ i : Fin hyp.q, hyp.mu i j) z = 0 := by
    by_contra h
    apply hzP
    have hmem := hyp.mu_colSum_support_subset_P_of_c_eq_one hG hc1 j hj
      (ClassFunction.mem_support.mpr h)
    have hmem' : (z : G) ∈ hyp.H := Subgroup.mem_subgroupOf.mp hmem
    rwa [hyp.H_eq_P_of_c_eq_one hc1] at hmem'
  rw [ClassFunction.finset_sum_apply,
    Finset.sum_congr rfl (fun i _ => hall i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have hq0 : (hyp.q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hyp.q_prime.pos.ne'
  exact (mul_eq_zero.mp hsum).resolve_left hq0

end OddOrder.Peterfalvi.S15
