-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.orderOf_coprime_q_of_not_mem_conj
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:33:10.315363+00:00
-- url     : https://prove2.me/submissions/59937058-702a-4401-abca-c24b042f185e

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndTBasic.lean
--   OddOrder/Peterfalvi/S15_Gate3.lean
--   OddOrder/Peterfalvi/S16_G0Coprime.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_G0Coprime

-- ===== OddOrder/Peterfalvi/S15_SAndTBasic.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.2.b)/(14.2.a), `T`-side dual of `W2_le_P`: `W₁ ≤ Q`.**  The cyclic factor `W₁`
(of prime order `q`) lies in `Q = T_F`, the maximal nilpotent normal Hall subgroup of `T`.  Dual to
`W2_le_P` (`W₂ ≤ P`), but read off the `T`-side type-`P` decomposition (`reconciled_typePData_T`)
rather than the coprime-index order count: the intrinsic dual cyclic factor
`data.W2 = C_{T'}(W₂#) = W₁` sits inside `data.H = maxNilpotentNormalHall T = Q`
(`data.W2_le`, `data.H_eq`, `Q_eq_TF`).  This is conjunct (1) of the (13.16)
`normalizer_W1_structure_of_D_eq_bot`
and is consumed by the `W₁`-side Maschke/Wielandt confinement (the dual of the `W₂`-side, where
`normalizer_U_inf_W2_eq_bot_of_data` uses `W2_le_P` at the analogous step). -/
theorem W1_le_Q [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.W1 ≤ hyp.Q := by
  obtain ⟨tpd, _, _, htpdW1⟩ := reconciled_typePData_T hG hyp
  have hHeq : tpd.H = hyp.Q := by rw [tpd.H_eq, hyp.Q_eq_TF]
  rw [← htpdW1, ← hHeq]
  exact le_trans tpd.W2_le inf_le_left

/-- **`T`-side Fitting-TI source** (Pf (13.16), dual of the `S`-side type-uniform TI result):
`F(T)^#` is a TI-subset of `G` (with normalizer `T`).

On the `W₂`-side, `normalizer_W2_le_S` reduces `N_G(W₂) ≤ S` using the type-uniform
`S13.fittingIsTI_of_isTypeNonI`.  The `W₁`-side dual applies BG Theorem 15.7(a) to `T`: the
(14.9) conclusion `IsTypeII T`, together with the BG type dictionary
`proposition_type_classification` (`IsTypeII M ↔ IsTypeP2 M`), makes `T` **type-`P₂`**, so
`fittingIsTI_of_isTypeP2` applies directly.  (The `q < p` κ-Hall ordering pins the *matched-pair*
labelling `S`/`T`, not the type: both members of a type-`P₂` pair are type-`P₂` — the earlier belief
that `T` is type-`P₁` and needed the `M_F ≠ M_σ` route was mistaken.) -/
theorem fittingIsTI_T [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    OddOrder.BG.Ch4.S15.FittingIsTI hyp.T := by
  have hP2 : OddOrder.BG.Ch4.S14.IsTypeP2 hyp.T :=
    ((OddOrder.BG.Ch4.S16.proposition_type_classification hG hyp.T_maximal).2.1).mp hTTypeII
  exact OddOrder.BG.Ch4.S15.fittingIsTI_of_isTypeP2 hG hyp.T_maximal hP2

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_Gate3.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.17.a) T-side Fitting order (B1)**: `|Q| = |T_F| = q^p`.

This is the `S ↔ T` symmetric companion of `BasicStructureData.P_order` (`|P| = |S_F| = p^q`), now
**proven** for the (14.9) type-II member `T`: from `IsTypeII T`, the (9.3) Wielandt order relation
`typeII_III_IV_order_relations` on the reconciled type-`P` data of `T` (`reconciled_typePData_T`)
gives `|T_F| = |tpd.W2|^|tpd.W1| = |W₁|^|W₂| = q^p` (the intrinsic factors reconcile to
`tpd.W2 = W₁`,
`tpd.W1 = W₂`).  Combined with the automorphism-equivariance of `M_F`
(`maxNilpotentNormalHall_pointwise_smul`), it gives `|L_F| = q^p` for every `L` conjugate to `T`,
which is what the `L ~ T` exclusion of (13.17.a) uses.  The `IsTypeII T` hypothesis is threaded from
`exists_LHypothesis` (§16, via the (14.9) `T_typeII`). -/
theorem card_Q_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    Nat.card ↥hyp.Q = hyp.q ^ hyp.p := by
  obtain ⟨tpd, _htpdV, htpdW1, htpdW2⟩ := reconciled_typePData_T hG hyp
  have tdata : TypeIIData hyp.T := hTTypeII.some
  have hUne : tpd.U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥tpd.U = Nat.card ↥tdata.typeP.U := by
      rw [tpd.card_U_eq_index, tdata.typeP.card_U_eq_index]
    rw [hbot, Subgroup.card_bot] at h1
    exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
  have hW1prime : (Nat.card ↥tpd.W1).Prime := by
    rw [htpdW1, ← hyp.p_eq_card_W2]; exact hyp.p_prime
  have hTI := tdata.common.2.2
  have hord := (OddOrder.Peterfalvi.S11.typeII_III_IV_order_relations hG
    { maximal := hyp.T_maximal
      typeP := tpd
      nontrivial := ⟨hUne, hW1prime, hTI⟩
      type_alt := Or.inl hTTypeII }).1 hTTypeII
  have hord2 : Nat.card ↥tpd.H = Nat.card ↥tpd.W2 ^ Nat.card ↥tpd.W1 := hord.2
  have hW2card : Nat.card ↥tpd.W2 = hyp.q := by
    rw [htpdW2, ← hyp.q_eq_card_W1]
  rw [tpd.H_eq, ← hyp.Q_eq_TF, hW2card, htpdW1, ← hyp.p_eq_card_W2] at hord2
  exact hord2

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S16_G0Coprime.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **The Fitting core `Q = T_F` is nontrivial**: it contains `W₁` of prime order `q`. -/
theorem Q_ne_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) : hyp.Q ≠ ⊥ := by
  intro hbot
  have hW1 := OddOrder.Peterfalvi.S15.W1_le_Q hG hyp
  rw [hbot, le_bot_iff] at hW1
  have hq1 : hyp.q = 1 := by rw [hyp.q_eq_card_W1, hW1, Subgroup.card_bot]
  exact hyp.q_prime.one_lt.ne' hq1

/-- **`N_G(Q) = T`**: T-side dual of `normalizer_P_eq_S`. -/
theorem normalizer_Q_eq_T [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Subgroup.normalizer (hyp.Q : Set G) = hyp.T := by
  have hQne : maxNilpotentNormalHall hyp.T ≠ ⊥ := hyp.Q_eq_TF ▸ Q_ne_bot hG hyp
  rw [hyp.Q_eq_TF]
  exact OddOrder.BG.Ch4.S16.normalizer_eq_self_of_subgroupOf_normal_of_ne_bot hG
    hyp.T_maximal (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le _)
    (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal _) hQne

/-- **Peterfalvi (13.2.e)/(8.6.a), T-side**: for `x ∈ Q#` the whole centralizer `C_G(x)`
lies in `T`.  Dual of `centralizer_le_S_of_mem_sharp_P` (`Q` TI via `fittingIsTI_T`, which
needs `T` type II — supplied by (14.9) `T_typeII` at the §16 consumer). -/
theorem centralizer_le_T_of_mem_sharp_Q [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) (hTII : IsTypeII hyp.T) {x : G}
    (hx : x ∈ sharpSubgroup hyp.Q) :
    Subgroup.centralizer ({x} : Set G) ≤ hyp.T := by
  have hTI : Subgroup.IsTI hyp.Q := by
    rw [hyp.Q_eq_TF]
    exact OddOrder.BG.Ch4.S16.maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI hG
      hyp.T_maximal (OddOrder.Peterfalvi.S15.fittingIsTI_T hG hyp hTII)
  have hle := OddOrder.GroupTheory.IsTISubset.centralizer_le hTI hx
  rwa [normalizer_Q_eq_T hG hyp] at hle

/-- **`p` is coprime to `|T'|`** (T-side dual of `coprime_q_card_derivedS`): `T' = Q ⋊ V`
with `|Q| = q^p` (`card_Q_eq`, `p ≠ q`) killing the `Q`-side, and `V ⋊ W₂` Frobenius
(`S11.typeP_uW1_frobenius` on the reconciled T-data) killing the `V`-side. -/
theorem coprime_p_card_derivedT [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) (hTII : IsTypeII hyp.T) :
    Nat.Coprime hyp.p (Nat.card ↥(derivedInG hyp.T)) := by
  obtain ⟨tpd, htpdV, htpdW1, htpdW2⟩ :=
    OddOrder.Peterfalvi.S15.reconciled_typePData_T hG hyp
  have hcard : Nat.card ↥(derivedInG hyp.T)
      = Nat.card ↥tpd.H * Nat.card ↥tpd.U := by
    have hmul := tpd.derived_complement.card_mul_card
    rw [← hmul,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.H_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.U_le).toEquiv]
  rw [hcard]
  refine Nat.Coprime.mul_right ?_ ?_
  · -- `p` is coprime to `|Q| = q^p`
    have hQcard : Nat.card ↥tpd.H = hyp.q ^ hyp.p := by
      rw [tpd.H_eq, ← hyp.Q_eq_TF]
      exact OddOrder.Peterfalvi.S15.card_Q_eq hG hyp hTII
    rw [hQcard]
    exact Nat.Coprime.pow_right _
      ((Nat.coprime_primes hyp.p_prime hyp.q_prime).mpr hyp.p_ne_q)
  · -- `p` is coprime to `|V|` (`V ⋊ W₂` Frobenius; trivial for `V = ⊥`)
    by_cases hV : tpd.U = ⊥
    · rw [hV, Subgroup.card_bot]; exact Nat.coprime_one_right _
    · have hF := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius tpd hV
      have hc := hF.coprime_card_kernel_complement
      have h1 : Nat.card ↥(tpd.U.subgroupOf (tpd.U ⊔ tpd.W1)) = Nat.card ↥tpd.U :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
      have h2 : Nat.card ↥(tpd.W1.subgroupOf (tpd.U ⊔ tpd.W1)) = Nat.card ↥tpd.W1 :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
      have hp : Nat.card ↥tpd.W1 = hyp.p := by rw [htpdW1, ← hyp.p_eq_card_W2]
      have hcUW : Nat.Coprime (Nat.card ↥tpd.U) hyp.p := by
        rw [← hp, ← h1, ← h2]; exact hc
      exact hcUW.symm

/-- **`Q` is a full Sylow `q`-subgroup of `G`** (T-side dual of `exists_sylow_coe_eq_P`).
`Q.subgroupOf T` is Sylow in `T` (`|Q| = q^p` with `q` coprime to `[T : Q]` — `Q = T_F` is a
Hall subgroup of `T`), `q ∈ σ(T)` (`N_G(Q) = T`), and the BG §10 σ-Sylow theory promotes it
to a Sylow of `G`. -/
theorem exists_sylow_coe_eq_Q [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) (hTII : IsTypeII hyp.T) :
    haveI : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
    ∃ S₀ : Sylow hyp.q G, (S₀ : Subgroup G) = hyp.Q := by
  have : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
  have hQle : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le _
  have hQcard : Nat.card ↥hyp.Q = hyp.q ^ hyp.p :=
    OddOrder.Peterfalvi.S15.card_Q_eq hG hyp hTII
  have hQsub_card : Nat.card ↥(hyp.Q.subgroupOf hyp.T) = hyp.q ^ hyp.p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv, hQcard]
  have hQsub_pg : IsPGroup hyp.q ↥(hyp.Q.subgroupOf hyp.T) :=
    IsPGroup.of_card hQsub_card
  obtain ⟨R, hRle⟩ := hQsub_pg.exists_le_sylow
  -- `Q = T_F` is Hall in `T`, so `q` is coprime to the index `[T : Q]`
  have hHall : Nat.Coprime (Nat.card ↥(hyp.Q.subgroupOf hyp.T))
      ((hyp.Q.subgroupOf hyp.T).index) := by
    have h := (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.T).coprime_index
    rwa [← hyp.Q_eq_TF] at h
  have hcopq : Nat.Coprime hyp.q ((hyp.Q.subgroupOf hyp.T).index) := by
    refine Nat.Coprime.coprime_dvd_left ?_ hHall
    rw [hQsub_card]
    exact dvd_pow_self _ hyp.p_prime.pos.ne'
  have hRQ : (R : Subgroup ↥hyp.T) = hyp.Q.subgroupOf hyp.T := by
    obtain ⟨k, hk⟩ := R.isPGroup'.exists_card_eq
    have hdvd : hyp.q ^ k ∣ hyp.q ^ hyp.p * ((hyp.Q.subgroupOf hyp.T).index) := by
      rw [← hk, ← hQsub_card, Subgroup.card_mul_index]
      exact Subgroup.card_subgroup_dvd_card _
    have hkq : hyp.q ^ k ∣ hyp.q ^ hyp.p :=
      Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left _ hcopq) hdvd
    refine (Subgroup.eq_of_le_of_card_ge hRle ?_).symm
    rw [hQsub_card, hk]
    exact Nat.le_of_dvd (pow_pos hyp.q_prime.pos _) hkq
  have hmap : (R : Subgroup ↥hyp.T).map hyp.T.subtype = hyp.Q := by
    rw [hRQ]
    exact Subgroup.map_subgroupOf_eq_of_le hQle
  have hqσ : hyp.q ∈ OddOrder.BG.Ch3.S10.sigma hyp.T := by
    refine ⟨Nat.mem_primeFactors.mpr ⟨hyp.q_prime, ?_, Nat.card_pos.ne'⟩, R, ?_⟩
    · exact dvd_trans (dvd_pow_self _ hyp.p_prime.pos.ne')
        (hQcard ▸ Subgroup.card_dvd_of_le hQle)
    · rw [hmap]
      exact (normalizer_Q_eq_T hG hyp).le
  obtain ⟨S₀, hS₀⟩ := OddOrder.BG.Ch3.S10.isSylow_sylowMap_of_mem_sigma hqσ R
  exact ⟨S₀, by rw [hS₀, hmap]⟩

/-- **`Q` absorbs the order-`q` elements of `G` up to conjugacy** (T-side dual of
`exists_conj_mem_P_of_orderOf_eq_p`). -/
theorem exists_conj_mem_Q_of_orderOf_eq_q [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) (hTII : IsTypeII hyp.T) {a : G}
    (ha : orderOf a = hyp.q) : ∃ y : G, y * a * y⁻¹ ∈ hyp.Q := by
  have : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
  obtain ⟨S₀, hS₀⟩ := exists_sylow_coe_eq_Q hG hyp hTII
  have hA : IsPGroup hyp.q ↥(Subgroup.zpowers a) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, ha, pow_one])
  obtain ⟨R, hR⟩ := hA.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq G R S₀
  refine ⟨y, ?_⟩
  have hcoe : MulAut.conj y • (R : Subgroup G) = hyp.Q := by
    have h := congrArg Sylow.toSubgroup hy
    rwa [Sylow.coe_subgroup_smul, hS₀] at h
  rw [← hcoe]
  exact ⟨a, hR (Subgroup.mem_zpowers a), rfl⟩

/-- **Peterfalvi (14.11.3), T-side core**: an element avoiding the conjugates of `W#` and of
`Q#` has order prime to `q`.  Dual of `orderOf_coprime_p_of_not_mem_conj`, along
`T = T' ⋊ W₂`, `T' = Q ⋊ V`, `C_{T'}(w) = W₁` (`w ∈ W₂#`), with (14.4)/(13.12) in place of
(14.6)/(13.12) for the `hfrobT` Frobenius-kernel input. -/
theorem _root_.solution [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) (hTII : IsTypeII hyp.T)
    (hfrobT : ∀ x ∈ sharpSubgroup hyp.Q,
      derivedInG hyp.T ⊓ Subgroup.centralizer ({x} : Set G) ≤ hyp.Q) {g : G}
    (hW : g ∉ conjClassSet (sharpSubgroup hyp.W))
    (hQ : g ∉ conjClassSet (sharpSubgroup hyp.Q)) :
    Nat.Coprime (orderOf g) hyp.q := by
  obtain ⟨tpd, htpdV, htpdW1, htpdW2⟩ :=
    OddOrder.Peterfalvi.S15.reconciled_typePData_T hG hyp
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hyp.q_prime]
  intro hdvd
  -- `g ≠ 1` and the order-`q` power `a₀` of `g`
  have hord_ne : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one, Nat.dvd_one] at hdvd
    exact hyp.q_prime.one_lt.ne' hdvd
  set a₀ : G := g ^ (orderOf g / hyp.q) with ha₀def
  have ha₀ord : orderOf a₀ = hyp.q := by
    rw [ha₀def, orderOf_pow, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hdvd),
      Nat.div_div_self hdvd hord_ne]
  have ha₀ne : a₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha₀ord
    exact hyp.q_prime.one_lt.ne ha₀ord
  have hcomm : Commute g a₀ := (Commute.refl g).pow_right _
  -- conjugate the `q`-part into `Q#`
  obtain ⟨y, hyQ⟩ := exists_conj_mem_Q_of_orderOf_eq_q hG hyp hTII ha₀ord
  set a : G := y * a₀ * y⁻¹ with hadef
  have haQ : a ∈ sharpSubgroup hyp.Q := by
    refine ⟨hyQ, ?_⟩
    intro h1
    refine ha₀ne ?_
    have ha1 : a = 1 := h1
    have : a₀ = y⁻¹ * a * y := by rw [hadef]; group
    rw [this, ha1, mul_one, inv_mul_cancel]
  -- the conjugate `g' = y g y⁻¹` centralizes `a`, hence lies in `T`
  set g' : G := y * g * y⁻¹ with hg'def
  have hg'ne : g' ≠ 1 := by
    intro h
    refine hg1 ?_
    have : g = y⁻¹ * g' * y := by rw [hg'def]; group
    rw [this, h, mul_one, inv_mul_cancel]
  have hg'cent : g' ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g' * a = y * (g * a₀) * y⁻¹ := by rw [hg'def, hadef]; group
      _ = y * (a₀ * g) * y⁻¹ := by rw [hcomm.eq]
      _ = a * g' := by rw [hg'def, hadef]; group
  have hg'T : g' ∈ hyp.T := centralizer_le_T_of_mem_sharp_Q hG hyp hTII haQ hg'cent
  -- decompose `g' = d · w` along `T = T' ⋊ W₂`
  obtain ⟨⟨d, w⟩, hdw⟩ :=
    (Subgroup.IsComplement.existsUnique tpd.M_complement
      (⟨g', hg'T⟩ : ↥hyp.T)).exists
  have hdmem : ((d : ↥hyp.T) : G) ∈ derivedInG hyp.T := Subgroup.mem_subgroupOf.mp d.2
  have hg'eq : ((d : ↥hyp.T) : G) * ((w : ↥hyp.T) : G) = g' := by
    have h := congrArg (fun x : ↥hyp.T => (x : G)) hdw
    simpa using h
  by_cases hw1 : (w : ↥hyp.T) = (1 : ↥hyp.T)
  · -- `w = 1`: `g' ∈ C_{T'}(a) ≤ Q`, contradicting `g ∉ (Q#)^G`
    have hg'derived : g' ∈ derivedInG hyp.T := by
      rw [← hg'eq, hw1]
      simpa using hdmem
    have hg'Q : g' ∈ hyp.Q := hfrobT a haQ ⟨hg'derived, hg'cent⟩
    refine hQ ⟨g', ⟨hg'Q, fun h => hg'ne h⟩, y⁻¹, ?_⟩
    rw [hg'def]; group
  · -- `w ≠ 1`: the (2.1) coset collapse conjugates `g` into `W₁ · w ⊆ W#`
    set w₀ : G := ((w : ↥hyp.T) : G) with hw₀def
    have hw₀W2 : w₀ ∈ hyp.W2 := by
      rw [← htpdW1]
      exact Subgroup.mem_subgroupOf.mp w.2
    have hw₀ne : w₀ ≠ 1 := by
      intro h
      exact hw1 (Subtype.ext (by simpa [hw₀def] using h))
    have hw₀ord : orderOf w₀ = hyp.p := by
      have hdvd' : orderOf w₀ ∣ hyp.p := by
        rw [hyp.p_eq_card_W2]
        exact Subgroup.orderOf_dvd_natCard _ hw₀W2
      rcases (Nat.Prime.eq_one_or_self_of_dvd hyp.p_prime _ hdvd') with h1 | hp
      · exact absurd (orderOf_eq_one_iff.mp h1) hw₀ne
      · exact hp
    have hnorm : ∀ x ∈ derivedInG hyp.T, w₀ * x * w₀⁻¹ ∈ derivedInG hyp.T := by
      intro x hx
      have hw₀norm : w₀ ∈ Subgroup.normalizer (derivedInG hyp.T) :=
        OddOrder.BG.Ch3.S10.le_normalizer_derivedInG hyp.T (SetLike.coe_mem (w : ↥hyp.T))
      exact (Subgroup.mem_normalizer_iff.mp hw₀norm x).mp hx
    have hcop : Nat.Coprime (orderOf w₀) (Nat.card ↥(derivedInG hyp.T)) := by
      rw [hw₀ord]; exact coprime_p_card_derivedT hG hyp hTII
    obtain ⟨c, hc, x, hx, hxeq⟩ :=
      OddOrder.GroupTheory.exists_mem_centralizer_conj hcop hnorm hdmem
    -- `C_{T'}(w₀) = W₁` ((8.4) regularity, T-side)
    have hcW1 : c ∈ hyp.W1 := by
      have hw₀tpd : w₀ ∈ tpd.W1 := by rw [htpdW1]; exact hw₀W2
      have hreg := tpd.centralizer_W1 w₀ hw₀tpd hw₀ne
      rw [← htpdW2, ← hreg]
      exact hc
    have hW1le : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
    have hW2le : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
    have hcwW : c * w₀ ∈ hyp.W := hyp.W.mul_mem (hW1le hcW1) (hW2le hw₀W2)
    have hcwne : c * w₀ ≠ 1 := by
      intro h
      have hw₀W1 : w₀ ∈ hyp.W1 := by
        have hinv : w₀ = c⁻¹ := eq_inv_of_mul_eq_one_right h
        rw [hinv]
        exact hyp.W1.inv_mem hcW1
      have hbot : w₀ ∈ hyp.W1 ⊓ hyp.W2 := ⟨hw₀W1, hw₀W2⟩
      rw [hyp.W1_inf_W2_eq_bot, Subgroup.mem_bot] at hbot
      exact hw₀ne hbot
    refine hW ⟨c * w₀, ⟨hcwW, fun h => hcwne h⟩, (x * y)⁻¹, ?_⟩
    have h1 : c * w₀ = x * g' * x⁻¹ := by
      rw [← hxeq, hg'eq]
    rw [h1, hg'def]; group

end OddOrder.Peterfalvi.S16
