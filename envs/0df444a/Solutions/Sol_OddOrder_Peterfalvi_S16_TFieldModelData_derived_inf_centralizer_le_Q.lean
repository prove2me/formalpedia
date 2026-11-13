-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.TFieldModelData.derived_inf_centralizer_le_Q
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:36:53.506201+00:00
-- url     : https://prove2.me/submissions/6786114d-420f-4f59-9b74-828dd61272ee

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_G0Coprime.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_G0Coprime

-- ===== OddOrder/Peterfalvi/S16_G0Coprime.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **The concrete BG Frobenius group `F ⋊ U*` has Frobenius kernel `F`** — an element
commuting with a nontrivial additive point lies in the additive kernel.  The norm-one units
act by field multiplication (`normOneMulAction_apply`), which is fixed-point-free on `F#`:
`u·m = m` with `m ≠ 0` forces `u = 1`. -/
theorem commute_inl_mem_range_inl {p q : ℕ} [Fact p.Prime]
    {m : OddOrder.BG.AppC.NormSet.additiveFieldGroup p q} (hm : m ≠ 1)
    {w : OddOrder.BG.AppC.NormSet.normOneFrobeniusGroup p q}
    (hcomm : w * SemidirectProduct.inl m = SemidirectProduct.inl m * w) :
    w ∈ (SemidirectProduct.inl :
      OddOrder.BG.AppC.NormSet.additiveFieldGroup p q →*
        OddOrder.BG.AppC.NormSet.normOneFrobeniusGroup p q).range := by
  -- compare left components: `w.left · φ(w.right)(m) = m · w.left`
  have hleft := congrArg SemidirectProduct.left hcomm
  simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
    SemidirectProduct.right_inl, map_one, MulAut.one_apply] at hleft
  -- the additive group is commutative: cancel `w.left`
  have hfix : OddOrder.BG.AppC.NormSet.normOneMulAction p q w.right m = m := by
    have hcomm' : m * w.left = w.left * m := mul_comm _ _
    rw [hcomm'] at hleft
    exact mul_left_cancel hleft
  -- fixed point of field multiplication with `m ≠ 0` forces the unit to be `1`
  have hm0 : Multiplicative.toAdd m ≠ 0 := by
    intro h0
    exact hm (by simpa using congrArg Multiplicative.ofAdd h0)
  have humul : ((w.right : (GaloisField p q)ˣ) : GaloisField p q)
      * Multiplicative.toAdd m = Multiplicative.toAdd m := by
    have h := OddOrder.BG.AppC.NormSet.normOneMulAction_apply p q w.right
      (Multiplicative.toAdd m)
    rw [ofAdd_toAdd] at h
    rw [← h, hfix]
  have hu1 : ((w.right : (GaloisField p q)ˣ) : GaloisField p q) = 1 :=
    mul_right_cancel₀ hm0 (by rw [humul, one_mul])
  have hright : w.right = 1 := Subtype.ext (Units.ext hu1)
  refine ⟨w.left, ?_⟩
  have h := SemidirectProduct.inl_left_mul_inr_right w
  rwa [hright, map_one, mul_one] at h

/-- **Peterfalvi (14.4)/(13.12)-dual, the Frobenius-kernel property of `T' = QV`, transported
from the T-side field model**: `C_{T'}(x) ≤ Q` for `x ∈ Q#`.  Mirror of
`FieldNormalizerData.derived_inf_centralizer_le_P` through `commute_inl_mem_range_inl`
(which is generic in the two primes).  Discharges the `hfrobT` input of
`orderOf_coprime_q_of_not_mem_conj` as soon as the (14.4) carrier is supplied. -/
theorem _root_.solution [Finite G]
    {hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)} (data : TFieldModelData hyp)
    {x : G} (hx : x ∈ sharpSubgroup hyp.Q) :
    derivedInG hyp.T ⊓ Subgroup.centralizer ({x} : Set G) ≤ hyp.Q := by
  let : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
  rintro g' ⟨hg'T', hg'cent⟩
  -- `T' = Q ⊔ V` is the image of `kernel ⊔ complement` under `σ`
  have hg'mem : g' ∈ (tFieldKernel hyp ⊔ tFieldComplement hyp).map data.sigma := by
    rw [Subgroup.map_sup, data.sigma_Q_eq_Q, data.sigma_V_eq_V, ← hyp.T_deriv_eq_QV]
    exact hg'T'
  obtain ⟨w, -, rfl⟩ := hg'mem
  -- `x = σ (inl m)` for a nontrivial additive point `m`
  have hxmem : x ∈ (tFieldKernel hyp).map data.sigma := by
    rw [data.sigma_Q_eq_Q]; exact hx.1
  obtain ⟨wx, hwx, hxeq⟩ := hxmem
  have hwx' : wx ∈ (SemidirectProduct.inl :
      OddOrder.BG.AppC.NormSet.additiveFieldGroup hyp.q hyp.p →*
        tFieldFrobeniusGroup hyp).range := hwx
  obtain ⟨m, rfl⟩ := hwx'
  have hmne : m ≠ 1 := by
    rintro rfl
    refine hx.2 ?_
    have hx1 : x = 1 := by rw [← hxeq, map_one, map_one]
    simp [hx1]
  -- pull the commutation back through the injective `σ`
  have hgx : data.sigma w * x = x * data.sigma w :=
    Subgroup.mem_centralizer_singleton_iff.mp hg'cent
  have hcomm : w * SemidirectProduct.inl m = SemidirectProduct.inl m * w := by
    apply data.sigma_injective
    rw [map_mul, map_mul, hxeq]
    exact hgx
  -- concrete Frobenius kernel + push forward
  obtain ⟨mw, hmw⟩ := commute_inl_mem_range_inl hmne hcomm
  rw [← data.sigma_Q_eq_Q]
  exact ⟨w, ⟨mw, hmw⟩, rfl⟩

end OddOrder.Peterfalvi.S16
