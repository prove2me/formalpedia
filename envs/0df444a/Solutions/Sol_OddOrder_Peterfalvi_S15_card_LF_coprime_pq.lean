-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.card_LF_coprime_pq
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:08:13.875168+00:00
-- url     : https://prove2.me/submissions/08de10b1-9461-43f8-9b64-c21356fdc593

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_Gate3.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

-- ===== OddOrder/Peterfalvi/S15_Gate3.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (8.17.a) coprimality (B2)**: for a type-`I` maximal subgroup `L` that is *not*
conjugate to `S` or to `T`, the Fitting kernel order `|L_F|` is prime to `p q`.

*Derivation (Pf p.82 "(8.17.a)"):* `bgTheoremE_cover_data` (Peterfalvi (8.17), BG Theorem E,
proven) exhibits representatives `M_i` of the conjugacy classes of maximal subgroups with
`π((M_i)_s)` pairwise disjoint (`BGTheoremECoverData.primeFactors_disjoint`), and
`(M_i)_s = (M_i)_σ` for every type (`mainSubgroup_eq_Msigma`).  `p ∈ π(S_σ)` (via
`Sdata.W2 ≤ S_F ≤ S_σ` with `|W₂| = p`) and `q ∈ π(T_σ)` (via the reconciled `T`-datum's
`W₂ = W₁`, `|W₁| = q`), while for the type-`I` maximal `L` one has `L_F = L_σ`
(`maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II`); transporting each along `Msigma_conj_smul`
to its representative, disjointness forces any `p`- or `q`-divisibility of `|L_F|` to place `L`
in the conjugacy class of `S` resp. `T` — excluded.  This is exactly the input the type-`I`
branch of (13.17.b) reads off before deducing `W₁ ∩ L_F = 1` and running the (9.1)
fixed-point-free argument. -/
theorem _root_.solution [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {L : Subgroup G} (hLmax : L ∈ maximalSubgroups G)
    (hLI : IsTypeI L) (hLnconjS : ¬ ∃ g : G, MulAut.conj g • L = hyp.S)
    (hLnconjT : ¬ ∃ g : G, MulAut.conj g • L = hyp.T) :
    Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) (hyp.p * hyp.q) := by
  classical
  obtain ⟨data, -⟩ := OddOrder.Peterfalvi.S10.bgTheoremE_cover_data.{_, 0} hG
  obtain ⟨k, gL, hgL⟩ := data.representatives L hLmax
  obtain ⟨iS, gS, hgS⟩ := data.representatives hyp.S hyp.S_maximal
  obtain ⟨iT, gT, hgT⟩ := data.representatives hyp.T hyp.T_maximal
  -- The main-subgroup card at a representative equals `|M_σ|` of any conjugate preimage.
  have hrepcard : ∀ (M : Subgroup G), M ∈ maximalSubgroups G → ∀ (m : data.ι) (g : G),
      MulAut.conj g • M = data.reps m →
      Nat.card ↥(mainSubgroup (data.reps m) (data.tau m)) =
        Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
    intro M hM m g hg
    rw [OddOrder.BG.Ch4.S16.mainSubgroup_eq_Msigma hG (data.maximal m) (data.typed m),
      ← hg, OddOrder.BG.Ch4.S14.Msigma_conj_smul]
    exact Nat.card_congr (Subgroup.equivSMul (MulAut.conj g)
      (OddOrder.BG.Ch3.S10.Msigma M)).toEquiv.symm
  -- `p ∈ π((M_{i_S})_s)`: `p = |W₂| = |Sdata.W₂|`, and `Sdata.W₂ ≤ S_F ≤ S_σ`.
  have hpS : hyp.p ∈ (Nat.card ↥(mainSubgroup (data.reps iS) (data.tau iS))).primeFactors := by
    rw [hrepcard hyp.S hyp.S_maximal iS gS hgS]
    refine Nat.mem_primeFactors.mpr ⟨hyp.p_prime, ?_, Nat.card_pos.ne'⟩
    have hle : hyp.Sdata.W2 ≤ OddOrder.BG.Ch3.S10.Msigma hyp.S := by
      refine le_trans (le_trans hyp.Sdata.W2_le inf_le_left) ?_
      rw [hyp.Sdata.H_eq]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hyp.S_maximal
    calc hyp.p = Nat.card ↥hyp.W2 := hyp.p_eq_card_W2
      _ = Nat.card ↥hyp.Sdata.W2 := by rw [hyp.Sdata_W2_eq]
      _ ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma hyp.S) := Subgroup.card_dvd_of_le hle
  -- `q ∈ π((M_{i_T})_s)`: the reconciled `T`-datum has `tpd.W₂ = W₁`, and `tpd.W₂ ≤ T_F ≤ T_σ`.
  have hqT : hyp.q ∈ (Nat.card ↥(mainSubgroup (data.reps iT) (data.tau iT))).primeFactors := by
    rw [hrepcard hyp.T hyp.T_maximal iT gT hgT]
    refine Nat.mem_primeFactors.mpr ⟨hyp.q_prime, ?_, Nat.card_pos.ne'⟩
    obtain ⟨tpd, -, -, htpdW2⟩ := reconciled_typePData_T hG hyp
    have hle : tpd.W2 ≤ OddOrder.BG.Ch3.S10.Msigma hyp.T := by
      refine le_trans (le_trans tpd.W2_le inf_le_left) ?_
      rw [tpd.H_eq]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hyp.T_maximal
    calc hyp.q = Nat.card ↥hyp.W1 := hyp.q_eq_card_W1
      _ = Nat.card ↥tpd.W2 := by rw [htpdW2]
      _ ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma hyp.T) := Subgroup.card_dvd_of_le hle
  -- `L`'s type-I main subgroup at its representative: `|(M_k)_s| = |L_σ| = |L_F|`.
  have hLcard : Nat.card ↥(mainSubgroup (data.reps k) (data.tau k)) =
      Nat.card ↥(maxNilpotentNormalHall L) := by
    rw [hrepcard L hLmax k gL hgL,
      OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II hG hLmax
        (Or.inl hLI)]
  -- Conjugacy transfer: if `L` and `M` land on the same representative, they are conjugate.
  have htransfer : ∀ (M : Subgroup G) (m : data.ι) (g : G), MulAut.conj g • M = data.reps m →
      k = m → ∃ g' : G, MulAut.conj g' • L = M := by
    intro M m g hg hkm
    refine ⟨g⁻¹ * gL, ?_⟩
    rw [map_mul, mul_smul, hgL, hkm, ← hg, map_inv, inv_smul_smul]
  -- Coprimality, prime by prime, via the (8.17) disjointness.
  rw [Nat.coprime_mul_iff_right]
  constructor
  · refine Nat.Coprime.symm (hyp.p_prime.coprime_iff_not_dvd.mpr fun hdvd => ?_)
    have hpL : hyp.p ∈ (Nat.card ↥(mainSubgroup (data.reps k) (data.tau k))).primeFactors := by
      rw [hLcard]
      exact Nat.mem_primeFactors.mpr ⟨hyp.p_prime, hdvd, Nat.card_pos.ne'⟩
    have hk : k = iS := by
      by_contra hne
      exact Finset.disjoint_left.mp (data.primeFactors_disjoint k iS hne) hpL hpS
    exact hLnconjS (htransfer hyp.S iS gS hgS hk)
  · refine Nat.Coprime.symm (hyp.q_prime.coprime_iff_not_dvd.mpr fun hdvd => ?_)
    have hqL : hyp.q ∈ (Nat.card ↥(mainSubgroup (data.reps k) (data.tau k))).primeFactors := by
      rw [hLcard]
      exact Nat.mem_primeFactors.mpr ⟨hyp.q_prime, hdvd, Nat.card_pos.ne'⟩
    have hk : k = iT := by
      by_contra hne
      exact Finset.disjoint_left.mp (data.primeFactors_disjoint k iT hne) hqL hqT
    exact hLnconjT (htransfer hyp.T iT gT hgT hk)

end OddOrder.Peterfalvi.S15
