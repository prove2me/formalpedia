-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.normalizer_V_inf_W1_le_centralizer_W1
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:08:14.680316+00:00
-- url     : https://prove2.me/submissions/38b00f60-95ca-4c02-814e-b38ddaa2f76f

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndTBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Theorems.Thm_OddOrder_Peterfalvi_S15_isMulCommutative_V

-- ===== OddOrder/Peterfalvi/S15_SAndTBasic.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.16), Frobenius fixed-point-freeness of `W₂` on `V`**: `C_V(W₂) = ⊥` — no
nonidentity element of the complement `V` centralizes `W₂`.

The `T`-side dual of `centralizer_W1_inf_U_eq_bot`.  On the `S`-side the `U ⋊ W₁` Frobenius
structure
comes from `basic_structure`; here the `V ⋊ W₂` Frobenius structure is read off the reconciled
type-`P`
decomposition of `T` (`reconciled_typePData_T` + `typeP_uW1_frobenius`), with `V ≠ ⊥` supplied by
the
(14.9) `T_typeII` core (`tdata.common`).  A nonidentity `x ∈ V` centralizing a nonidentity `w ∈ W₂`
would give `w x w⁻¹ = x`, contradicting the Frobenius condition (`IsFrobeniusGroup.conj_frobenius`).
This is the `C_D(W₂) ≤ C_V(W₂) = ⊥` input to the (13.16) `W₁`-side core. -/
theorem centralizer_W2_inf_V_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) :
    hyp.V ⊓ Subgroup.centralizer (hyp.W2 : Set G) = ⊥ := by
  obtain ⟨tdata⟩ := hTTypeII
  obtain ⟨tpd, htpdV, htpdW2, _⟩ := reconciled_typePData_T hG hyp
  have htpdVne : tpd.U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥tpd.U = Nat.card ↥tdata.typeP.U := by
      rw [tpd.card_U_eq_index, tdata.typeP.card_U_eq_index]
    rw [hbot, Subgroup.card_bot] at h1
    exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
  have hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
      ↥(hyp.V ⊔ hyp.W2) (hyp.V.subgroupOf (hyp.V ⊔ hyp.W2))
        (hyp.W2.subgroupOf (hyp.V ⊔ hyp.W2)) := by
    have h := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius tpd htpdVne
    rwa [htpdV, htpdW2] at h
  -- a nonidentity `w ∈ W₂` (`|W₂| = p` prime).
  have hW2ne : hyp.W2 ≠ ⊥ := by
    intro hbot
    have hp1 : hyp.p = 1 := by rw [hyp.p_eq_card_W2, hbot, Subgroup.card_bot]
    exact hyp.p_prime.one_lt.ne' hp1
  have : Nontrivial ↥hyp.W2 := (Subgroup.nontrivial_iff_ne_bot _).mpr hW2ne
  obtain ⟨w0, hw0⟩ := exists_ne (1 : ↥hyp.W2)
  set w : G := (w0 : G) with hw
  have hwW2 : w ∈ hyp.W2 := w0.2
  have hwne : w ≠ 1 := fun h => hw0 (OneMemClass.coe_eq_one.mp (hw ▸ h))
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxV, hxC⟩ := hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hxVW2 : x ∈ hyp.V ⊔ hyp.W2 := Subgroup.mem_sup_left hxV
  have hwVW2 : w ∈ hyp.V ⊔ hyp.W2 := Subgroup.mem_sup_right hwW2
  have hxN : (⟨x, hxVW2⟩ : ↥(hyp.V ⊔ hyp.W2)) ∈ hyp.V.subgroupOf (hyp.V ⊔ hyp.W2) := by
    rw [Subgroup.mem_subgroupOf]; exact hxV
  have hwA : (⟨w, hwVW2⟩ : ↥(hyp.V ⊔ hyp.W2)) ∈ hyp.W2.subgroupOf (hyp.V ⊔ hyp.W2) := by
    rw [Subgroup.mem_subgroupOf]; exact hwW2
  have hxN1 : (⟨x, hxVW2⟩ : ↥(hyp.V ⊔ hyp.W2)) ≠ 1 :=
    fun h => hx1 (by simpa using congrArg (Subgroup.subtype _) h)
  have hwA1 : (⟨w, hwVW2⟩ : ↥(hyp.V ⊔ hyp.W2)) ≠ 1 :=
    fun h => hwne (by simpa using congrArg (Subgroup.subtype _) h)
  have hcomm : w * x = x * w := (Subgroup.mem_centralizer_iff.mp hxC) w hwW2
  exact hfrob.conj_frobenius _ hwA hwA1 _ hxN hxN1 (by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    rw [hcomm]; group)

/-- **Peterfalvi (13.16), trivial `W₂`-action on `K/C_K(W₁)` (`W₁`-side)**: for `g ∈ N_G(W₁)` and
`w ∈ W₂`, the "commutator representative" `g⁻¹ (w g w⁻¹)` centralizes `W₁`.

The `T`-side dual of `conj_W1_mem_centralizer_W2`, pure group theory: `w ∈ W₂` centralizes `W₁`
(`W₁ × W₂` abelian), and `g` normalizes `W₁`, so `w g w⁻¹` and `g` induce the same conjugation on
every `y ∈ W₁`, whence `g⁻¹ (w g w⁻¹)` fixes `y`.  Feeds the coprime fixed-point lifting of the
`W₁`-side crux `N_V(W₁) ≤ C_G(W₁)`. -/
theorem conj_W2_mem_centralizer_W1 [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {g : G} (hg : g ∈ Subgroup.normalizer (hyp.W1 : Set G))
    {w : G} (hw : w ∈ hyp.W2) :
    g⁻¹ * (w * g * w⁻¹) ∈ Subgroup.centralizer (hyp.W1 : Set G) := by
  -- `w` centralizes `W₁`.
  have hwC : ∀ z ∈ hyp.W1, w * z = z * w := fun z hz => (hyp.W1_commutes_W2 z hz w hw).symm
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyW1 : y ∈ hyp.W1 := hy
  -- `g y g⁻¹ ∈ W₁`.
  have hy1 : g * y * g⁻¹ ∈ hyp.W1 := (Subgroup.mem_normalizer_iff.mp hg y).mp hyW1
  -- `w⁻¹ y w = y` and `w (g y g⁻¹) w⁻¹ = g y g⁻¹`.
  have h1 : w⁻¹ * y * w = y := by
    rw [mul_assoc, ← hwC y hyW1, inv_mul_cancel_left]
  have h2 : w * (g * y * g⁻¹) * w⁻¹ = g * y * g⁻¹ := by
    rw [hwC _ hy1, mul_assoc, mul_inv_cancel, mul_one]
  -- `w g w⁻¹` and `g` induce the same conjugation on `y`.
  have hsame : (w * g * w⁻¹) * y * (w * g * w⁻¹)⁻¹ = g * y * g⁻¹ := by
    calc (w * g * w⁻¹) * y * (w * g * w⁻¹)⁻¹
        = w * g * (w⁻¹ * y * w) * g⁻¹ * w⁻¹ := by group
      _ = w * g * y * g⁻¹ * w⁻¹ := by rw [h1]
      _ = w * (g * y * g⁻¹) * w⁻¹ := by group
      _ = g * y * g⁻¹ := h2
  -- hence `n' := g⁻¹ (w g w⁻¹)` fixes `y`.
  have hn' : (g⁻¹ * (w * g * w⁻¹)) * y * (g⁻¹ * (w * g * w⁻¹))⁻¹ = y := by
    calc (g⁻¹ * (w * g * w⁻¹)) * y * (g⁻¹ * (w * g * w⁻¹))⁻¹
        = g⁻¹ * ((w * g * w⁻¹) * y * (w * g * w⁻¹)⁻¹) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [hsame]
      _ = y := by group
  exact (mul_inv_eq_iff_eq_mul.mp hn').symm

/-- **Peterfalvi (13.16), the crux `N_V(W₁) ≤ C_G(W₁)`** (`W₁`-side dual of
`normalizer_U_inf_W2_le_centralizer_W2`): every element of `N_V(W₁) := V ⊓ N_G(W₁)` centralizes
`W₁`.

The conjugation action of `W₂` on the abelian `V` is coprime (`(|W₂|, |V|) = 1` from the `V ⋊ W₂`
Frobenius structure) with fixed points `C_V(W₂) = ⊥` (`centralizer_W2_inf_V_eq_bot`). For
`g ∈ N_V(W₁)`,
`W₂` fixes the coset `g · C_V(W₁)` (`conj_W2_mem_centralizer_W1`), so the coprime fixed-point
lifting
(`Isaacs.Ch04.coprime_fixedPoints_quotient`) produces a `W₂`-fixed representative `c ∈ C_V(W₂) = ⊥`;
hence `g ≡ 1 (mod C_V(W₁))`, i.e. `g ∈ C_G(W₁)`.  Gated on the (14.9) `T_typeII` structure (via the
`V ⋊ W₂` Frobenius and the abelianness of `V`, both from the reconciled type-`P` data of `T`). -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTTypeII : IsTypeII hyp.T) :
    hyp.V ⊓ Subgroup.normalizer (hyp.W1 : Set G) ≤ Subgroup.centralizer (hyp.W1 : Set G) := by
  obtain ⟨tdata⟩ := hTTypeII
  obtain ⟨tpd, htpdV, htpdW2, _⟩ := reconciled_typePData_T hG hyp
  have htpdVne : tpd.U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥tpd.U = Nat.card ↥tdata.typeP.U := by
      rw [tpd.card_U_eq_index, tdata.typeP.card_U_eq_index]
    rw [hbot, Subgroup.card_bot] at h1
    exact tdata.common.1 (Subgroup.card_eq_one.mp h1.symm)
  have hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
      ↥(hyp.V ⊔ hyp.W2) (hyp.V.subgroupOf (hyp.V ⊔ hyp.W2))
        (hyp.W2.subgroupOf (hyp.V ⊔ hyp.W2)) := by
    have h := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius tpd htpdVne
    rwa [htpdV, htpdW2] at h
  have hVcomm : IsMulCommutative ↥hyp.V := isMulCommutative_V hG hyp ⟨tdata⟩
  -- conjugation action `φ : ↥W₂ → MulAut ↥V`.
  let actV : MulDistribMulAction ↥hyp.W2 ↥hyp.V :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (hyp.V : Set G))) ↥hyp.V
      (Subgroup.inclusion hyp.W2_normalizes_V)
  set φ : ↥hyp.W2 →* MulAut ↥hyp.V := MulDistribMulAction.toMulAut ↥hyp.W2 ↥hyp.V with hφ
  have hφ_coe : ∀ (a : ↥hyp.W2) (x : ↥hyp.V),
      (hyp.V.subtype ((φ a) x)) = (↑a) * (hyp.V.subtype x) * (↑a)⁻¹ := fun _ _ => rfl
  -- `N := C_V(W₁)`, normal in the abelian `↥V`.
  set N : Subgroup ↥hyp.V :=
    (hyp.V ⊓ Subgroup.centralizer (hyp.W1 : Set G)).subgroupOf hyp.V with hN_def
  have hNnorm : N.Normal := by
    refine ⟨fun n _ g => ?_⟩
    have hc : g * n * g⁻¹ = n := by rw [mul_comm' g n, mul_inv_cancel_right]
    rw [hc]; assumption
  -- coprimality `(|W₂|, |V|) = 1`.
  have hCop : Nat.Coprime (Nat.card ↥hyp.W2) (Nat.card ↥hyp.V) := by
    have hk := hfrob.coprime_card_kernel_complement
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv,
      Nat.coprime_comm] at hk
  -- `W₂ ≤ C_G(W₁)`, so `N` is `W₂`-invariant.
  have hW2_le_C : hyp.W2 ≤ Subgroup.centralizer (hyp.W1 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact hyp.W1_commutes_W2 z hz x hx
  have hN_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ N := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a x hx
    rw [hN_def, Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨_, hxC⟩ := Subgroup.mem_inf.mp hx
    have hval : (hyp.V.subtype ((φ a) x)) = (↑a) * (hyp.V.subtype x) * (↑a)⁻¹ := hφ_coe a x
    refine Subgroup.mem_inf.mpr ⟨((φ a) x).2, ?_⟩
    rw [show ((φ a) x : G) = (hyp.V.subtype ((φ a) x)) from rfl, hval]
    exact (Subgroup.centralizer (hyp.W1 : Set G)).mul_mem
      (Subgroup.mul_mem _ (hW2_le_C a.2) hxC) (Subgroup.inv_mem _ (hW2_le_C a.2))
  -- main: `g ∈ V ⊓ N_G(W₁)` ⟹ `g ∈ C_G(W₁)`.
  intro g hg
  obtain ⟨hgV, hgNW1⟩ := Subgroup.mem_inf.mp hg
  set gg : ↥hyp.V := ⟨g, hgV⟩ with hgg
  -- `W₂` fixes the coset `gg · N`.
  have hg_fix : ∀ a : ↥hyp.W2, ∃ n ∈ N, (φ a) gg = gg * n := by
    intro a
    refine ⟨gg⁻¹ * (φ a) gg, ?_, (mul_inv_cancel_left _ _).symm⟩
    rw [hN_def, Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.mpr ⟨(gg⁻¹ * (φ a) gg).2, ?_⟩
    have hval : ((gg⁻¹ * (φ a) gg : ↥hyp.V) : G) = g⁻¹ * ((a : G) * g * (a : G)⁻¹) := by
      rw [Subgroup.coe_mul, InvMemClass.coe_inv,
        show ((φ a) gg : G) = (hyp.V.subtype ((φ a) gg)) from rfl, hφ_coe a gg]
      rfl
    rw [hval]
    exact conj_W2_mem_centralizer_W1 hG hyp hgNW1 a.2
  obtain ⟨c, hc_fix, m, hm, hc_eq⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient (φ := φ) hCop
      (Or.inr (Group.isSolvable_of_comm (fun a b => mul_comm' a b))) hN_inv hg_fix
  -- `c` is `W₂`-fixed ⟹ `(c:G) ∈ C_V(W₂) = ⊥` ⟹ `c = 1`.
  have hc1 : c = 1 := by
    have hcmem : (c : G) ∈ hyp.V ⊓ Subgroup.centralizer (hyp.W2 : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨c.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hfix := hc_fix ⟨w, hw⟩
      have hco : (hyp.V.subtype c) = (w : G) * (hyp.V.subtype c) * (w : G)⁻¹ := by
        have e1 := hφ_coe ⟨w, hw⟩ c
        rw [hfix] at e1
        exact e1
      exact mul_inv_eq_iff_eq_mul.mp hco.symm
    rw [centralizer_W2_inf_V_eq_bot hG hyp ⟨tdata⟩, Subgroup.mem_bot] at hcmem
    exact Subtype.ext hcmem
  -- `gg = m⁻¹ ∈ N` ⟹ `g ∈ C_G(W₁)`.
  rw [hc1, eq_comm, mul_eq_one_iff_eq_inv] at hc_eq
  have hggN : gg ∈ N := by rw [hc_eq]; exact N.inv_mem hm
  rw [hN_def, Subgroup.mem_subgroupOf] at hggN
  exact (Subgroup.mem_inf.mp hggN).2

end OddOrder.Peterfalvi.S15
