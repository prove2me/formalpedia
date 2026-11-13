-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.MHypothesis.line83_le_displayed_upper
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:32:48.1549+00:00
-- url     : https://prove2.me/submissions/d6bab397-15f7-439c-8c8f-6142f4445065

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndTDefs.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupM.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupM

-- ===== OddOrder/Peterfalvi/S15_SAndTDefs.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (14.11)**, base-derived: `|W₁| + |W₂| = p + q`.  Immediate from the (13.1) prime
data `q = |W₁|`, `p = |W₂|`.  Supplies the `card_W1_add_W2_eq` field of `MHypothesis` (currently
isolated to the §16 carrier), de-gating it to an elementary consequence of the base `Hypothesis`. -/
theorem card_W1_add_W2 (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.W1 + Nat.card ↥hyp.W2 = hyp.p + hyp.q := by
  rw [← hyp.q_eq_card_W1, ← hyp.p_eq_card_W2]; omega

/-- **Peterfalvi (14.11.3)**, base-derived: the exceptional set `W − (W₁ ∪ W₂)` is nonempty.
`|W| = p q` (`card_W_eq_pq`) strictly exceeds `|W₁ ∪ W₂| ≤ |W₁| + |W₂| = q + p` since
`(p−1)(q−1) > 0`
for the odd primes `p, q ≥ 3`, so `W` cannot be covered by `W₁ ∪ W₂`.  Supplies the `W_set_nonempty`
field of `MHypothesis`. -/
theorem W_sdiff_nonempty [Finite G] (hyp : Hypothesis (G := G)) :
    ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))).Nonempty := by
  rw [Set.sdiff_nonempty]
  intro hsub
  have hWc : (hyp.W : Set G).ncard = hyp.p * hyp.q := by
    rw [← Nat.card_coe_set_eq]; simp only [SetLike.coe_sort_coe]; exact card_W_eq_pq hyp
  have hW1c : (hyp.W1 : Set G).ncard = hyp.q := by
    rw [← Nat.card_coe_set_eq]; simp only [SetLike.coe_sort_coe]; exact hyp.q_eq_card_W1.symm
  have hW2c : (hyp.W2 : Set G).ncard = hyp.p := by
    rw [← Nat.card_coe_set_eq]; simp only [SetLike.coe_sort_coe]; exact hyp.p_eq_card_W2.symm
  have hle : (hyp.W : Set G).ncard ≤ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G)).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have hunion : ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G)).ncard ≤
      (hyp.W1 : Set G).ncard + (hyp.W2 : Set G).ncard := Set.ncard_union_le _ _
  rw [hWc] at hle
  rw [hW1c, hW2c] at hunion
  have hp3 : 3 ≤ hyp.p := hyp.three_le_p
  have hq3 : 3 ≤ hyp.q := hyp.three_le_q
  have hkey : hyp.p * hyp.q ≤ hyp.q + hyp.p := le_trans hle hunion
  have h3q : 3 * hyp.q ≤ hyp.p * hyp.q := mul_le_mul_left hp3 hyp.q
  have h3p : hyp.p * 3 ≤ hyp.p * hyp.q := mul_le_mul_right hq3 hyp.p
  omega

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- **Peterfalvi (14.11.4), the upper-bound loosening step** (04.16 line 115).  The raw `(7.8.b)`
upper estimate
`1 − 1/p − 1/q + 1/(pq) + (|P|−1)/(|P|uq) + (|Q|−1)/(|Q|vp) + (k−1)/(kpq)`
is loosened to the displayed `NormCascadeData.upper`
`1 − 1/p − 1/q + 2/(pq) + 1/(uq) + 1/(vp)`
via `(|P|−1)/|P| ≤ 1`, `(|Q|−1)/|Q| ≤ 1`, and `(k−1)/k ≤ 1` (so `(k−1)/(kpq) ≤ 1/(pq)`).  Pure `ℝ`
arithmetic; reusable by the `normCascadeData` producer to discharge `NormCascadeData.upper` once the
§8 TI-counting has produced the raw bound. -/
theorem normCascade_upper_loosen {p q u v k cardP cardQ : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hu : 0 < u) (hv : 0 < v)
    (hk : 0 < k) (hP : 0 < cardP) (hQ : 0 < cardQ) :
    (1 : ℝ) - 1 / (p : ℝ) - 1 / (q : ℝ) + 1 / ((p * q : ℕ) : ℝ)
        + ((cardP : ℝ) - 1) / ((cardP * u * q : ℕ) : ℝ)
        + ((cardQ : ℝ) - 1) / ((cardQ * v * p : ℕ) : ℝ)
        + ((k : ℝ) - 1) / ((k * p * q : ℕ) : ℝ)
      ≤ 1 - 1 / (p : ℝ) - 1 / (q : ℝ) + 2 / ((p * q : ℕ) : ℝ)
        + 1 / ((u * q : ℕ) : ℝ) + 1 / ((v * p : ℕ) : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hPR : (0 : ℝ) < cardP := by exact_mod_cast hP
  have hQR : (0 : ℝ) < cardQ := by exact_mod_cast hQ
  -- `(|P|−1)/(|P|uq) ≤ 1/(uq)`.
  have h1 : ((cardP : ℝ) - 1) / ((cardP * u * q : ℕ) : ℝ) ≤ 1 / ((u * q : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith [hPR, huR, hqR, mul_pos huR hqR]
  -- `(|Q|−1)/(|Q|vp) ≤ 1/(vp)`.
  have h2 : ((cardQ : ℝ) - 1) / ((cardQ * v * p : ℕ) : ℝ) ≤ 1 / ((v * p : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith [hQR, hvR, hpR, mul_pos hvR hpR]
  -- `(k−1)/(kpq) ≤ 1/(pq)`.
  have h3 : ((k : ℝ) - 1) / ((k * p * q : ℕ) : ℝ) ≤ 1 / ((p * q : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith [hkR, hpR, hqR, mul_pos hpR hqR]
  -- `1/(pq) + (k−1)/(kpq) ≤ 2/(pq)`, plus the two complement bounds.
  have hpq2 : (2 : ℝ) / ((p * q : ℕ) : ℝ)
      = 1 / ((p * q : ℕ) : ℝ) + 1 / ((p * q : ℕ) : ℝ) := by ring
  linarith [h1, h2, h3, hpq2]

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupM.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- **The type-I Dade support is the kernel sharp** `A(M) = K#`, the §8 cardinality input
`|A(M)| = |K#| = k − 1` of Peterfalvi (14.11.4) (Coq `PFsection14`: the `Dade_cover_inequality`
support term `#|A| = k.-1`).  For a Frobenius group `M` with kernel `N` (the complement acts
fixed-point-freely on `N#`), the centralizer-support
`centralizerSupport N# M = {y ∈ M : y ≠ 1, ∃ x ∈ N#, [y,x]=1}` is exactly `N#`: the forward
inclusion is the Frobenius FPF property `centralizer_kernel_le` (`C_M(x) ≤ N` for `x ∈ N#`), the
reverse takes `x = y`.  Applied with `N = K = M_F`, this is `typeIA M = K#`. -/
theorem centralizerSupport_sharpSubgroup_eq_of_frobenius [Finite G] {M N : Subgroup G}
    {C : Subgroup ↥M}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (N.subgroupOf M) C) (hNM : N ≤ M) :
    OddOrder.GroupTheory.centralizerSupport (OddOrder.GroupTheory.sharpSubgroup N) M
      = OddOrder.GroupTheory.sharpSubgroup N := by
  ext y
  simp only [OddOrder.GroupTheory.centralizerSupport, OddOrder.GroupTheory.sharpSubgroup,
    Set.mem_ofPred_eq, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hyM, hy1, x, ⟨hxN, hx1⟩, hyx⟩
    have hxM : x ∈ M := hNM hxN
    have hxMsub : (⟨x, hxM⟩ : ↥M) ∈ N.subgroupOf M := (Subgroup.mem_subgroupOf).mpr hxN
    have hx1' : (⟨x, hxM⟩ : ↥M) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hycomm : (⟨y, hyM⟩ : ↥M) ∈ Subgroup.centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hyx ⊢
      exact Subtype.ext hyx
    have hyN : (⟨y, hyM⟩ : ↥M) ∈ N.subgroupOf M :=
      hfrob.centralizer_kernel_le _ hxMsub hx1' hycomm
    exact ⟨(Subgroup.mem_subgroupOf).mp hyN, hy1⟩
  · rintro ⟨hyN, hy1⟩
    refine ⟨hNM hyN, hy1, y, ⟨hyN, hy1⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]

/-- **Peterfalvi (14.11.4): `|A(M)| = k − 1`** — the §8 cardinality input of the upper bound.  The
type-I Dade support `A(M) = typeIA M` equals `K#`
(`centralizerSupport_sharpSubgroup_eq_of_frobenius`
applied to the Frobenius structure of `M` from `typeI_frobenius` (12.7), kernel `K = M_F`), so its
cardinality is `|K| − 1 = k − 1`. -/
theorem MHypothesis.card_typeIA_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    Nat.card ↥(OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI) = Mdata.k - 1 := by
  -- Frobenius witness for `M` (kernel `M_F`), from (12.7).
  obtain ⟨fdata, _⟩ :=
    OddOrder.Peterfalvi.S14.typeI_frobenius hG hnoV Mdata.M_maximal ⟨Mdata.typeIHyp.typeI⟩
  -- The two kernels both equal `maxNilpotentNormalHall M`.
  have hKf : fdata.typeI.typeF.H = Mdata.typeIHyp.typeI.typeF.H := by
    rw [fdata.typeI.typeF.H_eq, Mdata.typeIHyp.typeI.typeF.H_eq]
  have hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥Mdata.M
      (Mdata.typeIHyp.typeI.typeF.H.subgroupOf Mdata.M) fdata.complement := hKf ▸ fdata.frobenius
  -- `typeIA M = K#` (FPF support identity).
  have hTI : OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI
      = OddOrder.GroupTheory.sharpSubgroup Mdata.typeIHyp.typeI.typeF.H :=
    centralizerSupport_sharpSubgroup_eq_of_frobenius hfrob Mdata.typeIHyp.typeI.typeF.H_le
  -- `typeF.H = K`, so `|K#| = |K| − 1 = k − 1`.
  have hHK : Mdata.typeIHyp.typeI.typeF.H = Mdata.K := by
    rw [Mdata.typeIHyp.typeI.typeF.H_eq, Mdata.K_eq_MF]
  have hc : Nat.card ↥Mdata.K = ((Mdata.K : Set G)).ncard := by
    rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
  rw [hTI, hHK, Mdata.k_eq_card_K, Nat.card_coe_set_eq, OddOrder.GroupTheory.sharpSubgroup,
    Set.ncard_sdiff (Set.singleton_subset_iff.mpr Mdata.K.one_mem), Set.ncard_singleton, hc]

/-- **Peterfalvi (14.10): `|M| = e k`** — the unconditional order of the type-I maximal `M`,
from `[M : K] = e` (`e_eq_index`) and `|K| = k` (`k_eq_card_K`) by Lagrange.  The conditional
(14.11.4) upper bound substitutes `e = p q` only after (14.11.2). -/
theorem MHypothesis.card_M_eq {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    Nat.card ↥Mdata.M = Mdata.e * Mdata.k := by
  have hKleM : Mdata.K ≤ Mdata.M :=
    Mdata.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le Mdata.M
  have hcardK : Nat.card ↥(Mdata.K.subgroupOf Mdata.M) = Nat.card ↥Mdata.K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKleM).toEquiv
  have hidx : Nat.card ↥Mdata.K * (Mdata.K.subgroupOf Mdata.M).index = Nat.card ↥Mdata.M := by
    rw [← hcardK]; exact Subgroup.card_mul_index _
  have hidxe : (Mdata.K.subgroupOf Mdata.M).index = Mdata.e :=
    Mdata.e_eq_index.symm
  rw [hidxe] at hidx
  rw [← hidx, Mdata.k_eq_card_K]; ring

/-- **The exceptional set `W − (W₁ ∪ W₂)` of a cyclic `W = W₁ × W₂` is a TI-subset with
normalizer-bound `W`** — the abstract core of Peterfalvi's `V`-set TI property, generalising
`S12.typePData_V_ti` to take the singleton/subset normalizer fact `N_G(X) = W` (`hnorm`) directly.
Given `g` conjugating some `a` of the set into it, `N_G({a}) = W = N_G({g a g⁻¹})` forces `g` to
normalize `W`, and cyclic-uniqueness (`cyclic_subgroup_eq_of_card_eq`) makes `W₁`, `W₂`
`g`-stable, so `g` normalizes the set, whence `g ∈ N_G(set) = W`.  The `W`-orbit TI input to the
(14.11.4) §8 count (`hnorm` is the genuine §13 structural fact, supplied from the partner type-`P`
structure). -/
theorem isTISubset_sdiff_sup_of_normalizer_eq [Finite G] {W W1 W2 : Subgroup G}
    (hWcyc : IsCyclic ↥W) (hWeq : W = W1 ⊔ W2)
    (hnorm : ∀ X : Set G, X.Nonempty →
      X ⊆ (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) → Subgroup.normalizer X = W) :
    OddOrder.GroupTheory.IsTISubset ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) W := by
  classical
  set vset : Set G := (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) with hvset
  have : IsCyclic ↥W := hWcyc
  have hW1le : W1 ≤ W := hWeq ▸ le_sup_left
  have hW2le : W2 ≤ W := hWeq ▸ le_sup_right
  have mem_norm_sing : ∀ c z : G,
      z ∈ Subgroup.normalizer ({c} : Set G) ↔ z * c * z⁻¹ = c := by
    intro c z
    rw [Subgroup.mem_set_normalizer_iff]
    constructor
    · intro hz; have := (hz c).mp rfl; simpa using this
    · intro hz h
      simp only [Set.mem_singleton_iff]
      refine ⟨fun hrfl => hrfl ▸ hz, fun hh => ?_⟩
      have hcc : z * h * z⁻¹ = z * c * z⁻¹ := by rw [hh, hz]
      exact mul_left_cancel (mul_right_cancel hcc)
  intro g hg
  obtain ⟨a, haV, hbV⟩ := hg
  have hNa : Subgroup.normalizer ({a} : Set G) = W :=
    hnorm {a} (Set.singleton_nonempty a) (Set.singleton_subset_iff.mpr haV)
  have hNb : Subgroup.normalizer ({g * a * g⁻¹} : Set G) = W :=
    hnorm {g * a * g⁻¹} (Set.singleton_nonempty _) (Set.singleton_subset_iff.mpr hbV)
  have hgW : ∀ h, h ∈ W ↔ g * h * g⁻¹ ∈ W := by
    intro h
    have e1 : (h ∈ W) ↔ h * a * h⁻¹ = a := by rw [← hNa, mem_norm_sing]
    have e2 : (g * h * g⁻¹ ∈ W) ↔ h * a * h⁻¹ = a := by
      rw [← hNb, mem_norm_sing]
      have hexp : g * h * g⁻¹ * (g * a * g⁻¹) * (g * h * g⁻¹)⁻¹ = g * (h * a * h⁻¹) * g⁻¹ := by
        group
      rw [hexp]
      exact ⟨fun hh => mul_left_cancel (mul_right_cancel hh), fun hh => by rw [hh]⟩
    rw [e1, e2]
  have hstab : ∀ (A : Subgroup G), A ≤ W → ∀ x : G, g * x * g⁻¹ ∈ A ↔ x ∈ A := by
    intro A hAW
    have hmap_le : A.map (MulAut.conj g).toMonoidHom ≤ W := by
      rintro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨z, hzA, rfl⟩ := hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (hgW z).mp (hAW hzA)
    have hcard : Nat.card ↥(A.map (MulAut.conj g).toMonoidHom) = Nat.card ↥A :=
      (Nat.card_congr (Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toEquiv).symm
    have hsubeq : (A.map (MulAut.conj g).toMonoidHom).subgroupOf W = A.subgroupOf W := by
      apply OddOrder.GroupTheory.cyclic_subgroup_eq_of_card_eq (C := ↥W)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmap_le).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAW).toEquiv, hcard]
    have hmapeq : A.map (MulAut.conj g).toMonoidHom = A := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hmap_le, hsubeq,
        Subgroup.map_subgroupOf_eq_of_le hAW]
    intro x
    constructor
    · intro hx
      have hmem : g * x * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom := by rw [hmapeq]; exact hx
      rw [Subgroup.mem_map] at hmem
      obtain ⟨z, hzA, hz⟩ := hmem
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hz
      have hzx : z = x := mul_left_cancel (mul_right_cancel hz)
      rwa [hzx] at hzA
    · intro hx
      have hmem : (MulAut.conj g).toMonoidHom x ∈ A.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      rw [hmapeq] at hmem
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem
  rw [← hnorm vset ⟨a, haV⟩ Set.Subset.rfl, Subgroup.mem_set_normalizer_iff]
  intro h
  simp only [hvset, Set.mem_sdiff, Set.mem_union, SetLike.mem_coe]
  rw [hgW h, hstab W1 hW1le h, hstab W2 hW2le h]

/-- **`W` stabilises its exceptional set `W − (W₁ ∪ W₂)` under conjugation** — the `hstab` input to
the `W`-orbit count `ncard_conjClassSet_of_isTISubset`/`orbit_normSq_term`, generalising
`S12.typePData_W_normalizes_typePV`.  Every `l ∈ W = N_G(set)` (via `hnorm`) normalizes the set. -/
theorem conj_smul_sdiff_sup_eq_of_normalizer_eq [Finite G] {W W1 W2 : Subgroup G}
    (hnorm : ∀ X : Set G, X.Nonempty →
      X ⊆ (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) → Subgroup.normalizer X = W)
    (hne : ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))).Nonempty) :
    ∀ l ∈ W, MulAut.conj l • ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)))
      = (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) := by
  intro l hl
  have hlN : l ∈ Subgroup.normalizer ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) := by
    rw [hnorm _ hne Set.Subset.rfl]; exact hl
  rw [Subgroup.mem_set_normalizer_iff] at hlN
  ext x
  simp only [Set.mem_smul_set, MulAut.smul_def, MulAut.conj_apply]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact (hlN v).mp hv
  · intro hx
    refine ⟨l⁻¹ * x * l, (hlN _).mpr ?_, by group⟩
    rw [show l * (l⁻¹ * x * l) * l⁻¹ = x by group]; exact hx

/-- **Orbit measure of a TI-subset** `|𝒞_G(A)|/|G| = |A|/|N|` — the real-valued form of the §8
TI-counting `ncard_conjClassSet_of_isTISubset` (`|𝒞_G(A)| = |A|·[G:N]`).  For a TI-subset `A` with
normalizer-bound `N` stabilizing `A`, the conjugacy-saturation `𝒞_G(A) = A^G` has relative measure
`|A|/|N|` in `G`.  The reusable bridge turning each (14.11.4) orbit `(W#)^G`/`(P#)^G`/`(Q#)^G` into
a
`1/|N_G(·)|`-term (Pf 04.16 lines 109–115). -/
theorem orbit_normSq_term [Finite G] {A : Set G} {L : Subgroup G}
    (hTI : OddOrder.GroupTheory.IsTISubset A L)
    (hstab : ∀ l ∈ L, MulAut.conj l • A = A) :
    ((OddOrder.GroupTheory.conjClassSet A).ncard : ℝ) / (Nat.card G : ℝ)
      = (A.ncard : ℝ) / (Nat.card ↥L : ℝ) := by
  rw [OddOrder.BG.Ch4.S14.ncard_conjClassSet_of_isTISubset hTI hstab, ← L.card_mul_index]
  have hidx : (L.index : ℝ) ≠ 0 := by exact_mod_cast Subgroup.index_ne_zero_of_finite
  push_cast
  rw [mul_div_mul_right _ _ hidx]

/-- **`W`-orbit relative measure** `|(W − (W₁ ∪ W₂))^G|/|G| = |W − (W₁ ∪ W₂)|/|W|` — the assembled
`W`-orbit term of Peterfalvi (14.11.4), combining the TI core
(`isTISubset_sdiff_sup_of_normalizer_eq`), the `W`-stability
(`conj_smul_sdiff_sup_eq_of_normalizer_eq`), and the orbit bridge (`orbit_normSq_term`).  Given the
cyclic structure `W = W₁ × W₂` and the singleton/subset normalizer fact `N_G(X) = W` (`hnorm`). -/
theorem orbit_sdiff_sup_normSq_term [Finite G] {W W1 W2 : Subgroup G}
    (hWcyc : IsCyclic ↥W) (hWeq : W = W1 ⊔ W2)
    (hnorm : ∀ X : Set G, X.Nonempty →
      X ⊆ (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) → Subgroup.normalizer X = W)
    (hne : ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))).Nonempty) :
    ((OddOrder.GroupTheory.conjClassSet
        ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)))).ncard : ℝ) / (Nat.card G : ℝ)
      = (((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))).ncard : ℝ) / (Nat.card ↥W : ℝ) :=
  orbit_normSq_term (isTISubset_sdiff_sup_of_normalizer_eq hWcyc hWeq hnorm)
    (conj_smul_sdiff_sup_eq_of_normalizer_eq hnorm hne)

/-- **The normalizer of `P` stabilises `P# = P ∖ {1}` under conjugation** — the `hstab` input to the
`P#`-orbit count `orbit_normSq_term`.  For `l ∈ N_G(P)`, conjugation by `l` permutes `P` and fixes
`1`, so it permutes `P#`.  (With `IsTI P` — definitionally `IsTISubset (P ∖ {1}) (N_G(P))` — this
gives `|(P#)^G|/|G| = (|P|−1)/|N_G(P)|`, the `P`/`Q` orbit terms of Peterfalvi (14.11.4).) -/
theorem conj_smul_sharpSubgroup_eq_of_mem_normalizer {P : Subgroup G} {l : G}
    (hl : l ∈ Subgroup.normalizer (P : Set G)) :
    MulAut.conj l • (OddOrder.GroupTheory.sharpSubgroup P)
      = OddOrder.GroupTheory.sharpSubgroup P := by
  rw [Subgroup.mem_set_normalizer_iff] at hl
  ext x
  simp only [Set.mem_smul_set, MulAut.smul_def, MulAut.conj_apply,
    OddOrder.GroupTheory.sharpSubgroup, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨v, ⟨hvP, hv1⟩, rfl⟩
    refine ⟨(hl v).mp hvP, fun h => hv1 ?_⟩
    have : v = l⁻¹ * (l * v * l⁻¹) * l := by group
    rw [this, h]; group
  · rintro ⟨hxP, hx1⟩
    refine ⟨l⁻¹ * x * l, ⟨(hl _).mpr ?_, fun h => hx1 ?_⟩, by group⟩
    · rw [show l * (l⁻¹ * x * l) * l⁻¹ = x by group]; exact hxP
    · rw [show x = l * (l⁻¹ * x * l) * l⁻¹ by group, h]; group

/-- **`P#`-orbit relative measure** `|(P#)^G|/|G| = |P#|/|N_G(P)|` — the `P`/`Q` orbit term of
Peterfalvi (14.11.4), for a TI-subgroup `P` (`Subgroup.IsTI P`, definitionally
`IsTISubset (P ∖ {1}) (N_G(P))`).  Combines the TI property with the `P#`-stability
(`conj_smul_sharpSubgroup_eq_of_mem_normalizer`) via the orbit bridge `orbit_normSq_term`. -/
theorem orbit_sharpSubgroup_normSq_term [Finite G] {P : Subgroup G} (hTI : Subgroup.IsTI P) :
    ((OddOrder.GroupTheory.conjClassSet (OddOrder.GroupTheory.sharpSubgroup P)).ncard : ℝ)
        / (Nat.card G : ℝ)
      = ((OddOrder.GroupTheory.sharpSubgroup P).ncard : ℝ)
        / (Nat.card ↥(Subgroup.normalizer (P : Set G)) : ℝ) :=
  orbit_normSq_term hTI (fun _ hl => conj_smul_sharpSubgroup_eq_of_mem_normalizer hl)

/-- **`|P#| + 1 = |P|`** — the cardinality of the sharp subgroup (the `|P| − 1` numerator of the
`P`/`Q` orbit term of (14.11.4)), additive form. -/
theorem ncard_sharpSubgroup_add_one {P : Subgroup G} [Finite ↥P] :
    (OddOrder.GroupTheory.sharpSubgroup P).ncard + 1 = Nat.card ↥P := by
  have hc : Nat.card ↥P = (P : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
  rw [hc, OddOrder.GroupTheory.sharpSubgroup, ← Set.ncard_singleton (1 : G),
    Set.ncard_sdiff_add_ncard_of_subset (Set.singleton_subset_iff.mpr P.one_mem)]

/-- **`|W − (W₁ ∪ W₂)| + |W₁| + |W₂| = |W| + 1`** — the cardinality of the exceptional set, by
inclusion–exclusion with `W₁ ∩ W₂ = {1}` (`hdisj`).  The numerator of the `W`-orbit term
`|W − (W₁ ∪ W₂)|/|W|` of Peterfalvi (14.11.4) (additive form, avoiding `ℕ`-truncation). -/
theorem ncard_sdiff_sup_add_eq [Finite G] {W W1 W2 : Subgroup G}
    (hW1le : W1 ≤ W) (hW2le : W2 ≤ W) (hdisj : W1 ⊓ W2 = ⊥) :
    ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))).ncard + Nat.card ↥W1 + Nat.card ↥W2
      = Nat.card ↥W + 1 := by
  have hsub : ((W1 : Set G) ∪ (W2 : Set G)) ⊆ (W : Set G) :=
    Set.union_subset (SetLike.coe_subset_coe.mpr hW1le) (SetLike.coe_subset_coe.mpr hW2le)
  have h1 := Set.ncard_sdiff_add_ncard_of_subset hsub
  have h2 := Set.ncard_union_add_ncard_inter (W1 : Set G) (W2 : Set G)
  have h3 : ((W1 : Set G) ∩ (W2 : Set G)).ncard = 1 := by
    rw [← Subgroup.coe_inf, hdisj, Subgroup.coe_bot, Set.ncard_singleton]
  have hcW : Nat.card ↥W = (W : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
  have hcW1 : Nat.card ↥W1 = (W1 : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
  have hcW2 : Nat.card ↥W2 = (W2 : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
  rw [hcW, hcW1, hcW2]
  omega

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.4), the `G₀`-drop set reduction** — `|famG₀| − |G₀| ≤ |(W−(W₁∪W₂))^G| +
|(P#)^G| + |(Q#)^G|` (as `ncard`s).  Since `G₀ ⊆ famG₀` (`G0_off_dadeSupport`) and `famG₀ ∖ G₀` is
covered by the three orbits (`G0_orbit_cover`, the (14.11.3) `G₀ = G − [Ã(M) ∪ orbits]`), the
difference is bounded by the orbit cardinalities (`Set.ncard_sdiff` + `Set.ncard_union_le`).  The
set-theoretic core of the (14.11.4) §8 TI-counting, feeding `orbit_normSq_term` per orbit. -/
theorem MHypothesis.famG0_sub_filter_card_le_orbit_ncard [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) :
    (Nat.card (Mdata.toFamilyHypothesis71).G0 : ℝ)
        - ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ)
      ≤ ((OddOrder.GroupTheory.conjClassSet
            ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))).ncard : ℝ)
        + ((OddOrder.GroupTheory.conjClassSet
            (OddOrder.GroupTheory.sharpSubgroup hyp.base.P)).ncard : ℝ)
        + ((OddOrder.GroupTheory.conjClassSet
            (OddOrder.GroupTheory.sharpSubgroup hyp.base.Q)).ncard : ℝ) := by
  classical
  have := Mdata.finiteG
  set famG0 := (Mdata.toFamilyHypothesis71).G0 with hfamdef
  set Worb := OddOrder.GroupTheory.conjClassSet
    ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))
  set Porb := OddOrder.GroupTheory.conjClassSet (OddOrder.GroupTheory.sharpSubgroup hyp.base.P)
  set Qorb := OddOrder.GroupTheory.conjClassSet (OddOrder.GroupTheory.sharpSubgroup hyp.base.Q)
  -- `g ∈ famG₀ ↔ g ∉ Ã(M)` (single-member family).
  have hmemfam : ∀ g : G, g ∈ famG0 ↔ g ∉ Mdata.typeIHyp.dadeData.dade.dadeSupport := by
    intro g
    refine ⟨fun hg => hg 0, fun hg i => ?_⟩
    fin_cases i; exact hg
  -- `G₀ ⊆ famG₀` and `famG₀ ∖ G₀ ⊆ orbits`.
  have hsub : Mdata.G0 ⊆ famG0 := fun g hg => (hmemfam g).mpr (Mdata.G0_off_dadeSupport g hg)
  have hcover : famG0 \ Mdata.G0 ⊆ Worb ∪ Porb ∪ Qorb := by
    rintro g ⟨hgfam, hgG0⟩
    exact Mdata.G0_orbit_cover g ((hmemfam g).mp hgfam) hgG0
  -- ncard reduction.
  have hdiff : (famG0 \ Mdata.G0).ncard ≤ Worb.ncard + Porb.ncard + Qorb.ncard :=
    le_trans (Set.ncard_le_ncard hcover)
      (le_trans (Set.ncard_union_le _ _) (by gcongr; exact Set.ncard_union_le _ _))
  have hdeq : (famG0 \ Mdata.G0).ncard = famG0.ncard - Mdata.G0.ncard := Set.ncard_sdiff hsub
  have hG0le : Mdata.G0.ncard ≤ famG0.ncard := Set.ncard_le_ncard hsub
  -- `Nat.card famG₀ = famG₀.ncard`, `|filter| = G₀.ncard`.
  have hfamcard : Nat.card famG0 = famG0.ncard := Nat.card_coe_set_eq famG0
  have hfiltcard : (Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card = Mdata.G0.ncard := by
    rw [Set.ncard_eq_toFinset_card']; congr 1; ext g; simp
  rw [hfamcard, hfiltcard]
  have hcast : (famG0.ncard : ℝ) - (Mdata.G0.ncard : ℝ)
      = ((famG0.ncard - Mdata.G0.ncard : ℕ) : ℝ) := (Nat.cast_sub hG0le).symm
  rw [hcast, ← hdeq]
  calc ((famG0 \ Mdata.G0).ncard : ℝ) ≤ ((Worb.ncard + Porb.ncard + Qorb.ncard : ℕ) : ℝ) := by
        exact_mod_cast hdiff
    _ = (Worb.ncard : ℝ) + (Porb.ncard : ℝ) + (Qorb.ncard : ℝ) := by push_cast; ring

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.4), the upper-bound §8 TI-counting step** (04.16 lines 109–115).  Brings the
line-83 bound `|A(M)|/|M| + (1/|G|)(|famG₀| − |G₀|)` (`chiRhoNormSq_psi_le_line83`, proven) up to
the displayed `NormCascadeData.upper`.  The genuine §8 content: `|A(M)|/|M| = (k−1)/(kpq)`
(`card_typeIA_eq`/`card_M_eq`); the `G₀`-drop `famG0_sub_filter_card_le_orbit_ncard` (set-reduction,
proven) plus the orbit measures (`orbit_sdiff_sup_normSq_term`/`orbit_sharpSubgroup_normSq_term`)
and the structural values (`|W|`/`|N_G(P)|`, `IsTI P`/`IsTI Q`, `normalizer_V`) bound the orbits,
then `normCascade_upper_loosen`.  The remaining §8 structural input is the TI/normalizer data of the
Frobenius pieces `W`, `P`, `Q` (the type-I analogue of S12 (10.8)'s `G₁ ⊆ (H#)^G ∪ V^G`). -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) (hepq : Mdata.e = hyp.base.p * hyp.base.q) :
    (Nat.card ↥(OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI) : ℝ)
        / (Nat.card ↥Mdata.M : ℝ)
      + (Nat.card G : ℝ)⁻¹ * ((Nat.card (Mdata.toFamilyHypothesis71).G0 : ℝ)
        - ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ))
      ≤ 1 - (1 : ℝ) / (hyp.base.p : ℝ) - 1 / (hyp.base.q : ℝ)
        + 2 / ((hyp.base.p * hyp.base.q : ℕ) : ℝ)
        + 1 / ((hyp.base.u * hyp.base.q : ℕ) : ℝ)
        + 1 / ((hyp.base.v * hyp.base.p : ℕ) : ℝ) := by
  have := Mdata.finiteG
  -- abbreviations
  have hW1le : hyp.base.W1 ≤ hyp.base.W := hyp.base.W_eq_join ▸ le_sup_left
  have hW2le : hyp.base.W2 ≤ hyp.base.W := hyp.base.W_eq_join ▸ le_sup_right
  -- positivity (`p`, `q` prime; `u`, `v` from the faithful normalizer carriers; `k`/cards `> 0`).
  have hp : (0 : ℝ) < hyp.base.p := by exact_mod_cast hyp.base.p_prime.pos
  have hq : (0 : ℝ) < hyp.base.q := by exact_mod_cast hyp.base.q_prime.pos
  have hkpos : 0 < Mdata.k := Mdata.k_eq_card_K ▸ Nat.card_pos
  have hPpos : 0 < Nat.card ↥hyp.base.P := Nat.card_pos
  have hQpos : 0 < Nat.card ↥hyp.base.Q := Nat.card_pos
  have hNPpos : 0 < Nat.card ↥(Subgroup.normalizer (hyp.base.P : Set G)) := Nat.card_pos
  have hNQpos : 0 < Nat.card ↥(Subgroup.normalizer (hyp.base.Q : Set G)) := Nat.card_pos
  have hupos : 0 < hyp.base.u := by
    by_contra hc
    have hu0 : hyp.base.u = 0 := Nat.le_zero.mp (not_lt.mp hc)
    have : Nat.card ↥(Subgroup.normalizer (hyp.base.P : Set G)) = 0 := by
      rw [Mdata.card_normalizer_P_eq, hu0, mul_zero, zero_mul]
    omega
  have hvpos : 0 < hyp.base.v := by
    by_contra hc
    have hv0 : hyp.base.v = 0 := Nat.le_zero.mp (not_lt.mp hc)
    have : Nat.card ↥(Subgroup.normalizer (hyp.base.Q : Set G)) = 0 := by
      rw [Mdata.card_normalizer_Q_eq, hv0, mul_zero, zero_mul]
    omega
  -- orbit measures (equalities).
  have hWm := orbit_sdiff_sup_normSq_term hyp.base.W_cyclic hyp.base.W_eq_join
    Mdata.W_normalizer_V (S15.W_sdiff_nonempty hyp.base)
  have hPm := orbit_sharpSubgroup_normSq_term Mdata.P_isTI
  have hQm := orbit_sharpSubgroup_normSq_term Mdata.Q_isTI
  -- cardinalities of the supports.
  have hWc := ncard_sdiff_sup_add_eq hW1le hW2le hyp.base.W1_inf_W2_eq_bot
  have hPc := ncard_sharpSubgroup_add_one (P := hyp.base.P)
  have hQc := ncard_sharpSubgroup_add_one (P := hyp.base.Q)
  -- `|W-set| = pq + 1 − (p+q)`, `|N_G(P)| = |P| u q`, etc. (`ℕ`-level facts → `ℝ`).
  have hWsetR : (((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))).ncard : ℝ)
      = (hyp.base.p : ℝ) * hyp.base.q + 1 - hyp.base.p - hyp.base.q := by
    have : ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))).ncard
        + (hyp.base.p + hyp.base.q) = hyp.base.p * hyp.base.q + 1 := by
      rw [← S15.card_W1_add_W2 hyp.base,
        ← S15.card_W_eq_pq hyp.base]
      omega
    have hR : (((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G))).ncard : ℝ)
        + ((hyp.base.p : ℝ) + hyp.base.q) = (hyp.base.p : ℝ) * hyp.base.q + 1 := by
      exact_mod_cast this
    linarith
  -- the three orbit-term values (equalities).
  have hWterm : (OddOrder.GroupTheory.conjClassSet
        ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))).ncard
        / (Nat.card G : ℝ)
      = 1 - 1 / (hyp.base.p : ℝ) - 1 / (hyp.base.q : ℝ)
        + 1 / ((hyp.base.p * hyp.base.q : ℕ) : ℝ) := by
    rw [hWm, hWsetR]
    have hWcardR : (Nat.card ↥hyp.base.W : ℝ) = (hyp.base.p : ℝ) * hyp.base.q := by
      rw [S15.card_W_eq_pq hyp.base]; push_cast; ring
    rw [hWcardR]; push_cast; field_simp; ring
  have hPterm : (OddOrder.GroupTheory.conjClassSet
        (OddOrder.GroupTheory.sharpSubgroup hyp.base.P)).ncard / (Nat.card G : ℝ)
      = ((Nat.card ↥hyp.base.P : ℝ) - 1)
        / ((Nat.card ↥hyp.base.P * hyp.base.u * hyp.base.q : ℕ) : ℝ) := by
    rw [hPm]
    have hsharpR : ((OddOrder.GroupTheory.sharpSubgroup hyp.base.P).ncard : ℝ)
        = (Nat.card ↥hyp.base.P : ℝ) - 1 := by
      have hR : ((OddOrder.GroupTheory.sharpSubgroup hyp.base.P).ncard : ℝ) + 1
          = (Nat.card ↥hyp.base.P : ℝ) := by exact_mod_cast hPc
      linarith
    rw [hsharpR, Mdata.card_normalizer_P_eq]
  have hQterm : (OddOrder.GroupTheory.conjClassSet
        (OddOrder.GroupTheory.sharpSubgroup hyp.base.Q)).ncard / (Nat.card G : ℝ)
      = ((Nat.card ↥hyp.base.Q : ℝ) - 1)
        / ((Nat.card ↥hyp.base.Q * hyp.base.v * hyp.base.p : ℕ) : ℝ) := by
    rw [hQm]
    have hsharpR : ((OddOrder.GroupTheory.sharpSubgroup hyp.base.Q).ncard : ℝ)
        = (Nat.card ↥hyp.base.Q : ℝ) - 1 := by
      have hR : ((OddOrder.GroupTheory.sharpSubgroup hyp.base.Q).ncard : ℝ) + 1
          = (Nat.card ↥hyp.base.Q : ℝ) := by exact_mod_cast hQc
      linarith
    rw [hsharpR, Mdata.card_normalizer_Q_eq]
  -- `|A(M)|/|M| = (k−1)/(kpq)`.
  have hAterm : (Nat.card ↥(OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI) : ℝ)
        / (Nat.card ↥Mdata.M : ℝ)
      = ((Mdata.k : ℝ) - 1) / ((Mdata.k * hyp.base.p * hyp.base.q : ℕ) : ℝ) := by
    rw [Mdata.card_typeIA_eq hG hnoV, Mdata.card_M_eq, hepq]
    have hkR : ((Mdata.k - 1 : ℕ) : ℝ) = (Mdata.k : ℝ) - 1 := by
      have : 1 ≤ Mdata.k := hkpos
      push_cast [Nat.cast_sub this]; ring
    rw [hkR]; push_cast; ring
  -- the `G₀`-drop, scaled by `1/|G|`.
  have hGinv : (0 : ℝ) ≤ (Nat.card G : ℝ)⁻¹ := by positivity
  have hdrop := mul_le_mul_of_nonneg_left Mdata.famG0_sub_filter_card_le_orbit_ncard hGinv
  -- `(1/|G|)·Σ ncard = Σ (ncard/|G|) = hWterm + hPterm + hQterm`.
  have hsum : (Nat.card G : ℝ)⁻¹ * (((OddOrder.GroupTheory.conjClassSet
        ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))).ncard : ℝ)
      + ((OddOrder.GroupTheory.conjClassSet
          (OddOrder.GroupTheory.sharpSubgroup hyp.base.P)).ncard : ℝ)
      + ((OddOrder.GroupTheory.conjClassSet
          (OddOrder.GroupTheory.sharpSubgroup hyp.base.Q)).ncard : ℝ))
      = (1 - 1 / (hyp.base.p : ℝ) - 1 / (hyp.base.q : ℝ) + 1 / ((hyp.base.p * hyp.base.q : ℕ) : ℝ))
        + ((Nat.card ↥hyp.base.P : ℝ) - 1)
            / ((Nat.card ↥hyp.base.P * hyp.base.u * hyp.base.q : ℕ) : ℝ)
        + ((Nat.card ↥hyp.base.Q : ℝ) - 1)
            / ((Nat.card ↥hyp.base.Q * hyp.base.v * hyp.base.p : ℕ) : ℝ) := by
    rw [← hWterm, ← hPterm, ← hQterm]; ring
  -- assemble: `line83-RHS ≤ raw bound`.
  have hraw : (Nat.card ↥(OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI) : ℝ)
        / (Nat.card ↥Mdata.M : ℝ)
      + (Nat.card G : ℝ)⁻¹ * ((Nat.card (Mdata.toFamilyHypothesis71).G0 : ℝ)
        - ((Finset.univ.filter (fun g : G => g ∈ Mdata.G0)).card : ℝ))
      ≤ 1 - 1 / (hyp.base.p : ℝ) - 1 / (hyp.base.q : ℝ)
          + 1 / ((hyp.base.p * hyp.base.q : ℕ) : ℝ)
        + ((Nat.card ↥hyp.base.P : ℝ) - 1)
            / ((Nat.card ↥hyp.base.P * hyp.base.u * hyp.base.q : ℕ) : ℝ)
        + ((Nat.card ↥hyp.base.Q : ℝ) - 1)
            / ((Nat.card ↥hyp.base.Q * hyp.base.v * hyp.base.p : ℕ) : ℝ)
        + ((Mdata.k : ℝ) - 1) / ((Mdata.k * hyp.base.p * hyp.base.q : ℕ) : ℝ) := by
    rw [hAterm]; rw [hsum] at hdrop; linarith
  -- loosen the raw bound to the displayed one.
  exact le_trans hraw (normCascade_upper_loosen hyp.base.p_prime.pos hyp.base.q_prime.pos
    hupos hvpos hkpos hPpos hQpos)

end OddOrder.Peterfalvi.S16
