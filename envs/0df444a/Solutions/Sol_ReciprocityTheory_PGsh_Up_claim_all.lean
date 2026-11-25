-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.claim_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:29:31.442505+00:00
-- url     : https://prove2.me/submissions/365537ef-3dca-4bf1-883f-621d4d592fcd

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthCotangentBoundStatementOfClaim
import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderOfAddEquiv
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLat
import Definitions.Def_ReciprocityTheory_DualLattices_ImportsBis
import Definitions.Def_ReciprocityTheory_DualLattices_SqIdeal
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier
import Theorems.Thm_ReciprocityTheory_PGsh_Up_sq_eq_mul
import Theorems.Thm_ReciprocityTheory_PGsh_Up_mem_aug
import Theorems.Thm_ReciprocityTheory_PGsh_Up_pow_mem_carrier
import Theorems.Thm_ReciprocityTheory_PGsh_Up_pullQ_aug
import Theorems.Thm_ReciprocityTheory_PGsh_Up_pullQ_sq
import Theorems.Thm_ReciprocityTheory_PGsh_Up_IK_mul_le
import Theorems.Thm_ReciprocityTheory_PGsh_Up_hasColen_of_lat
import Theorems.Thm_ReciprocityTheory_PGsh_Up_claim_base
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_hasColength_eq_pow_mul_pow
import Theorems.Thm_ReciprocityTheory_PGsh_L2_mem_of_restrictToSubgroup_eq_zero
import Theorems.Thm_ReciprocityTheory_PGsh_L2_mem_sup_of_restrictToSubgroup_mem_sq
import Theorems.Thm_ReciprocityTheory_PGsh_Up_primeHopfOrder_of_addEquiv
import Theorems.Thm_ReciprocityTheory_PGsh_Up_u3


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] (hv : v.Integers R)
    (hvp : v (p : C) < 1) :
    ∀ (k : ℕ) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], Fintype.card N = k →
      (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ClaimBody C v R N AA := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro N _ _ _ hk hN AA
  by_cases htriv : ∀ x : N, x = 0
  · exact claim_base v hv N htriv AA
  push_neg at htriv
  obtain ⟨x, hx0⟩ := htriv
  set K : AddSubgroup N := AddSubgroup.zmultiples x with hKdef
  let e : ZMod p ≃+ K := zmodEquiv p x (hN x) hx0
  letI : DecidablePred (· ∈ K) := Classical.decPred _
  letI : DecidableEq (N ⧸ K) := Classical.decEq _
  letI : Fintype (N ⧸ K) :=
    Fintype.ofSurjective (QuotientAddGroup.mk : N → N ⧸ K) QuotientAddGroup.mk_surjective
  obtain ⟨⟨AK, hAK⟩, ⟨AQ, hAQ⟩, -, -⟩ := h2 C R v hv N K AA
  have hcardK : Fintype.card K = p := by
    rw [← Fintype.card_congr e.toEquiv, ZMod.card]
  have hcardN : Fintype.card N = Fintype.card (N ⧸ K) * p := by
    have h0 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup K
    simp only [Nat.card_eq_fintype_card] at h0
    rw [h0, hcardK]
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hlt : Fintype.card (N ⧸ K) < k := by
    rw [← hk, hcardN]
    have hpos : 0 < Fintype.card (N ⧸ K) := Fintype.card_pos
    nlinarith
  have hNQ : ∀ q : N ⧸ K, p • q = 0 := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H a => rw [← QuotientAddGroup.mk_nsmul, hN a, QuotientAddGroup.mk_zero]
  obtain ⟨n, g, δ, hg1, hg2, hg3, hg4⟩ := ih _ hlt (N ⧸ K) rfl hNQ AQ
  obtain ⟨xK, δK, x1, hxK, hxKp, hδK, hxKgen, hcK⟩ := primeHopfOrder_of_addEquiv u3 p C v R hv hvp e AK
  have hxKA : xK ∈ AA.carrier.map (resK (R := R) K) := by
    rw [← hAK]; exact ((mem_aug _ _).1 hxK).1
  obtain ⟨y0, hy0, hy0x⟩ := Submodule.mem_map.1 hxKA
  have hyx : ∀ a : K, y0 (a : N) = xK a := fun a => by rw [← hy0x]; rfl
  have hyaug : y0 ∈ augIdeal AA.carrier := by
    rw [mem_aug]
    refine ⟨hy0, ?_⟩
    have h0 := hyx 0
    rw [((mem_aug _ _).1 hxK).2] at h0
    simpa using h0

  have hIK : ∀ z ∈ (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K),
      ∃ r : Fin n → R, z - ∑ j, r j • pullQ (R := R) K (g j) ∈ sqIdeal (augIdeal AA.carrier) := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 hz
    rw [← hAQ] at hb
    obtain ⟨r, hr⟩ := hg2 b hb
    refine ⟨r, ?_⟩
    have h1 := pullQ_sq K AA AQ hAQ hr
    simpa [map_sub, map_sum, map_smul] using h1
  have hsup : ∀ z ∈ (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) ⊔
        augIdeal AA.carrier * augIdeal AA.carrier,
      ∃ r : Fin n → R, z - ∑ j, r j • pullQ (R := R) K (g j) ∈ sqIdeal (augIdeal AA.carrier) := by
    intro z hz
    obtain ⟨z1, hz1, z2, hz2, rfl⟩ := Submodule.mem_sup.1 hz
    obtain ⟨r, hr⟩ := hIK z1 hz1
    refine ⟨r, ?_⟩
    have hz2' : z2 ∈ sqIdeal (augIdeal AA.carrier) := by rw [sq_eq_mul]; exact hz2
    have h1 := Submodule.add_mem _ hr hz2'
    convert h1 using 1
    abel
  refine ⟨n + 1, Fin.snoc (fun i => pullQ (R := R) K (g i)) y0, Fin.snoc δ δK, ?_, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using hyaug
    | cast i0 =>
      simp only [Fin.snoc_castSucc]
      exact pullQ_aug K AA AQ hAQ (hg1 i0)
  · intro f hf
    have hrf : resK (R := R) K f ∈ augIdeal AK.carrier := by
      rw [mem_aug, hAK]
      refine ⟨Submodule.mem_map_of_mem ((mem_aug _ _).1 hf).1, ?_⟩
      have h0 := ((mem_aug _ _).1 hf).2
      simpa [resK, LinearMap.funLeft_apply] using h0
    obtain ⟨r0, hr0⟩ := hxKgen _ hrf
    have hgm : f - r0 • y0 ∈ augIdeal AA.carrier :=
      Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hyaug)
    have hres : resK (R := R) K (f - r0 • y0) ∈ augIdeal (AA.carrier.map (resK (R := R) K)) *
        augIdeal (AA.carrier.map (resK (R := R) K)) := by
      rw [← hAK, map_sub, map_smul, hy0x]; exact hr0
    obtain ⟨r, hr⟩ := hsup _ (mem_sup_of_restrictToSubgroup_mem_sq hv AA K _ hgm hres)
    refine ⟨Fin.snoc r r0, ?_⟩
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    convert hr using 1
    abel
  · intro i
    induction i using Fin.lastCases with
    | last =>
      have hmemA : y0 ^ p - δK • y0 ∈ AA.carrier :=
        AA.carrier.sub_mem (pow_mem_carrier AA hy0 p) (AA.carrier.smul_mem δK hy0)
      have hres0 : resK (R := R) K (y0 ^ p - δK • y0) = 0 := by
        funext a
        have h2 := congrFun hxKp a
        simp only [Pi.pow_apply] at h2
        simp [resK, LinearMap.funLeft_apply, hyx, h2, Algebra.smul_def]
      have hIKA := mem_of_restrictToSubgroup_eq_zero hv AA K _ hmemA hres0
      obtain ⟨a, ha⟩ := hsup _ (IK_mul_le K AA AQ hAQ hIKA)
      have hpow : y0 ^ p ∈ sqIdeal (augIdeal AA.carrier) := by
        have hp0 : p = (p - 1) + 1 := by omega
        rw [hp0, pow_succ]
        apply Submodule.subset_span
        refine ⟨y0 ^ (p - 1), ?_, y0, hyaug, rfl⟩
        rw [mem_aug]
        refine ⟨pow_mem_carrier AA hy0 _, ?_⟩
        have h0 := ((mem_aug _ _).1 hyaug).2
        simp [h0, show p - 1 ≠ 0 by omega]
      refine ⟨Fin.snoc (fun j => -a j) 0, ?_⟩
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_last, Fin.snoc_castSucc, Fin.castSucc_lt_last, if_true,
        lt_self_iff_false, if_false, zero_smul, add_zero]
      have h1 := Submodule.sub_mem _ hpow ha
      convert h1 using 1
      simp only [neg_smul, Finset.sum_neg_distrib, sub_neg_eq_add]
      abel
    | cast i0 =>
      obtain ⟨a, ha⟩ := hg3 i0
      refine ⟨Fin.snoc a 0, ?_⟩
      have hnl : ¬ (Fin.last n < Fin.castSucc i0) := not_lt.2 (Fin.castSucc_lt_last i0).le
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.castSucc_lt_castSucc_iff, hnl, if_false,
        zero_smul, add_zero]
      have h1 := pullQ_sq K AA AQ hAQ ha
      simpa [map_sub, map_sum, map_smul, apply_ite (pullQ (R := R) K), map_zero] using h1
  · intro c hc
    obtain ⟨cB, hcB⟩ := hasColen_of_lat v AQ.lat
    have hB2 := hg4 cB hcB
    have hcB' : HasColen R v (AA.carrier.comap (pullQ (R := R) K)) cB := by
      rw [← hAQ]; exact hcB
    have hcK' : HasColen R v (AA.carrier.map (resK (R := R) K)) (v x1 ^ (p * (p - 1) / 2)) := by
      rw [← hAK]; exact hcK
    have hc_eq := hasColength_eq_pow_mul_pow hv AA K c cB _ hc hcB' hcK'
    have hK2 : (v x1 ^ (p * (p - 1) / 2)) ^ 2 = v (algebraMap R C δK) ^ p := by
      rw [hδK, ← pow_mul, ← pow_mul]
      congr 1
      have h2 : 2 ∣ p * (p - 1) := (Nat.even_mul_pred_self p).two_dvd
      rw [Nat.div_mul_cancel h2, mul_comm]
    rw [hc_eq, hcardK, Fin.prod_univ_castSucc, hcardN]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    calc (cB ^ p * (v x1 ^ (p * (p - 1) / 2)) ^ Fintype.card (N ⧸ K)) ^ 2
        = (cB ^ 2) ^ p * ((v x1 ^ (p * (p - 1) / 2)) ^ 2) ^ Fintype.card (N ⧸ K) := by ring
      _ = ((∏ i, v (algebraMap R C (δ i))) ^ Fintype.card (N ⧸ K)) ^ p *
          (v (algebraMap R C δK) ^ p) ^ Fintype.card (N ⧸ K) := by rw [hB2, hK2]
      _ = _ := by ring
end ReciprocityTheory.PGsh.Up
