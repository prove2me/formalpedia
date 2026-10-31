-- Prove2me | solution 1 for OfflineCensoredPricing.Identifiability.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T17:44:22.38751+00:00
-- url     : https://prove2.me/submissions/3d25a352-94fb-478b-8c99-f300b390069e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model
import Definitions.Def_OfflineCensoredPricing_Identifiability_D2ACD
import Theorems.Thm_OfflineCensoredPricing_Identifiability_proposition_3
import Theorems.Thm_OfflineCensoredPricing_Identifiability_proposition_7
import Theorems.Thm_OfflineCensoredPricing_Identifiability_lemma_2

open MeasureTheory Set OfflineCensoredPricing.Identifiability

namespace OCPThm2Aux

lemma argmax_isGreatest (lo hi : ℝ) (R : ℝ → ℝ) (hc : Continuous R) (hlohi : lo ≤ hi) :
    IsGreatest {q ∈ Icc lo hi | ∀ q' ∈ Icc lo hi, R q' ≤ R q} (argmaxIcc lo hi R) := by
  set M := {q ∈ Icc lo hi | ∀ q' ∈ Icc lo hi, R q' ≤ R q} with hM
  obtain ⟨m0, hm0, hm0max⟩ := (isCompact_Icc (a := lo) (b := hi)).exists_isMaxOn
    ⟨lo, le_rfl, hlohi⟩ hc.continuousOn
  have hm0M : m0 ∈ M := ⟨hm0, fun q' hq' => hm0max hq'⟩
  have hbdd : BddAbove M := ⟨hi, fun q hq => hq.1.2⟩
  have hclosed : IsClosed M := by
    have : M = Icc lo hi ∩ ⋂ q' ∈ Icc lo hi, {q | R q' ≤ R q} := by
      ext q; simp [hM]
    rw [this]
    exact isClosed_Icc.inter (isClosed_biInter (fun q' _ => isClosed_le continuous_const hc))
  exact ⟨hclosed.csSup_mem ⟨m0, hm0M⟩ hbdd, fun q hq => le_csSup hbdd hq⟩

section Hat

variable {K : ℕ} [NeZero K] (P : Public K) {Nv : Fin K → ℕ} (S : Sample K Nv)

lemma bHat_pos (hb : 0 < P.blo) : 0 < bHat P S := lt_of_lt_of_le hb (le_max_left _ _)

lemma junction (hb : 0 < P.blo) (hS : ∀ i j, S i j ≤ P.yh i) (hN : 0 < Nv (iStar P S)) :
    RHat P S (pTildeHat P S) = R1Hat P S (pTildeHat P S) ∧
      RHat P S (pTildeHat P S) = R2Hat P S (pTildeHat P S) := by
  have hbp := bHat_pos P S hb
  set i := iStar P S with hi
  set bh := bHat P S with hbh
  set a := pTildeHat P S with ha
  have hba : bh * a = lamHat P S - P.y := by
    rw [ha]; unfold pTildeHat; rw [← hbh]; field_simp
  have hlam : lamHat P S = P.yh i + bh * P.p i := rfl
  have hN' : (Nv i : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hR : RHat P S a = a * (shiftedMean P S - (lamHat P S - P.y)) := by
    unfold RHat shiftedMean
    have : ∀ j, min (S i j + bh * P.p i - bh * a) P.y = (S i j + bh * P.p i) - bh * a := by
      intro j
      apply min_eq_left
      have := hS i j
      rw [hba, hlam]; linarith
    rw [← hi, ← hbh]
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hba]
    field_simp
  refine ⟨?_, ?_⟩
  · rw [hR]; unfold R1Hat
    have : gammaHatMax P S * bh * a = gammaHatMax P S * (lamHat P S - P.y) := by
      rw [mul_assoc, hba]
    rw [show -gammaHatMax P S * bh * a = -(gammaHatMax P S * bh * a) by ring, this]
    ring
  · rw [hR]; unfold R2Hat
    rw [show -bh * a = -(bh * a) by ring, hba]
    ring

lemma RHat_cont : Continuous (RHat P S) := by
  unfold RHat; fun_prop

lemma cont_piece (a : ℝ) (g h : ℝ → ℝ) (hg : Continuous g) (hh : Continuous h)
    (hj : g a = h a) : Continuous (fun q => if q < a then g q else h q) := by
  have e : (fun q => if q < a then g q else h q) = fun q => if a ≤ q then h q else g q := by
    funext q
    by_cases hq : q < a
    · rw [if_pos hq, if_neg (not_le.2 hq)]
    · rw [if_neg hq, if_pos (not_lt.1 hq)]
  rw [e]
  exact Continuous.if_le hh hg continuous_const continuous_id (fun x hx => by rw [← hx, hj])

lemma RHatMax_cont (hb : 0 < P.blo) (hS : ∀ i j, S i j ≤ P.yh i) (hN : 0 < Nv (iStar P S)) :
    Continuous (RHatMax P S) := by
  have := cont_piece (pTildeHat P S) (RHat P S) (R1Hat P S) (RHat_cont P S)
    (by unfold R1Hat; fun_prop) (junction P S hb hS hN).1
  exact this

lemma RHatMin_cont (hb : 0 < P.blo) (hS : ∀ i j, S i j ≤ P.yh i) (hN : 0 < Nv (iStar P S)) :
    Continuous (RHatMin P S) := by
  have := cont_piece (pTildeHat P S) (RHat P S) (R2Hat P S) (RHat_cont P S)
    (by unfold R2Hat; fun_prop) (junction P S hb hS hN).2
  exact this

end Hat

/-- The deterministic chain (10) of the paper (Appendix, p. 32), with `Δ = 0`. -/
lemma chain {K : ℕ} [NeZero K] (I : Instance K) (hI : I.Standing) (heq : pStarMax I = pStarMin I)
    {Nv : Fin K → ℕ} (S : Sample K Nv) (hS : ∀ i j, S i j ≤ I.yh i)
    (hN : ∀ i, 0 < Nv i) {α : ℝ}
    (hx : ∀ q ∈ Icc I.plo I.phi, |RHatMax I.toPublic S q - Rmax I q| ≤ α)
    (hn : ∀ q ∈ Icc I.plo I.phi, |RHatMin I.toPublic S q - Rmin I q| ≤ α) :
    worstLoss I (d2acd I.toPublic Nv S) ≤ 4 * α := by
  set P := I.toPublic with hP
  have hlohi : I.plo ≤ I.phi := hI.2.2.2.1.le
  have hblo : 0 < P.blo := hI.2.2.2.2.1
  have hcx := RHatMax_cont P S hblo hS (hN _)
  have hcn := RHatMin_cont P S hblo hS (hN _)
  -- `d2acd = pD2ACD`
  have hd : d2acd P Nv S = pD2ACD P S := by
    unfold d2acd
    rw [if_neg]
    push_neg
    exact fun i => (hN i).ne'
  -- the empirical maximizers
  obtain ⟨⟨hxI, hxmax⟩, -⟩ : IsGreatest {q ∈ Icc P.plo P.phi | ∀ q' ∈ Icc P.plo P.phi,
      RHatMax P S q' ≤ RHatMax P S q} (pHatMax P S) :=
    argmax_isGreatest P.plo P.phi (RHatMax P S) hcx hlohi
  obtain ⟨⟨hnI, hnmax⟩, -⟩ : IsGreatest {q ∈ Icc P.plo P.phi | ∀ q' ∈ Icc P.plo P.phi,
      RHatMin P S q' ≤ RHatMin P S q} (pHatMin P S) :=
    argmax_isGreatest P.plo P.phi (RHatMin P S) hcn hlohi
  -- the minimax price
  set W : ℝ → ℝ := fun q => max (WHatMax P S q) (WHatMin P S q) with hW
  have hWc : Continuous (fun q => -W q) := by
    simp only [hW]; unfold WHatMax WHatMin; fun_prop
  have hset : pD2ACDSet P S = {q ∈ Icc P.plo P.phi | ∀ q' ∈ Icc P.plo P.phi, -W q' ≤ -W q} := by
    ext q; simp only [pD2ACDSet, mem_setOf_eq, neg_le_neg_iff, hW]
  obtain ⟨⟨hDI, hDmin⟩, -⟩ := argmax_isGreatest P.plo P.phi (fun q => -W q) hWc hlohi
  have hne : (pD2ACDSet P S).Nonempty := by rw [hset]; exact ⟨_, hDI, hDmin⟩
  have hpD : pD2ACD P S = argmaxIcc P.plo P.phi (fun q => -W q) := by
    unfold pD2ACD; rw [if_pos hne, hset]; rfl
  rw [hd, hpD]
  set pD := argmaxIcc P.plo P.phi (fun q => -W q) with hpDdef
  -- the true maximizers
  obtain ⟨⟨hpxI, hpxmax⟩, -⟩ := (proposition_3 I hI).1
  obtain ⟨⟨hpnI, hpnmax⟩, -⟩ := (proposition_3 I hI).2.1
  rw [(proposition_7 I hI pD hDI).2]
  set px := pStarMax I
  have hpnx : pStarMin I = px := heq.symm
  rw [hpnx] at hpnI hpnmax ⊢
  have hW1 := hDmin px hpxI
  simp only [hW, neg_le_neg_iff, WHatMax, WHatMin] at hW1
  set a := pHatMax P S
  set c := pHatMin P S
  have e1 := abs_le.1 (hx pD hDI); have e2 := abs_le.1 (hn pD hDI)
  have e3 := abs_le.1 (hx px hpxI); have e4 := abs_le.1 (hn px hpxI)
  have e5 := abs_le.1 (hx a hxI); have e6 := abs_le.1 (hn c hnI)
  have f1 := hxmax px hpxI; have f2 := hnmax px hpxI
  have g1 := hpxmax a hxI; have g2 := hpnmax c hnI
  have m1 := le_max_left (RHatMax P S a - RHatMax P S pD) (RHatMin P S c - RHatMin P S pD)
  have m2 := le_max_right (RHatMax P S a - RHatMax P S pD) (RHatMin P S c - RHatMin P S pD)
  have hW1' : max (RHatMax P S a - RHatMax P S pD) (RHatMin P S c - RHatMin P S pD) ≤
      max (RHatMax P S a - RHatMax P S px) (RHatMin P S c - RHatMin P S px) := hW1
  have b1 : RHatMax P S a - RHatMax P S px ≤ 2 * α := by linarith
  have b2 : RHatMin P S c - RHatMin P S px ≤ 2 * α := by linarith
  have hM := le_trans hW1' (max_le b1 b2)
  have hM1 := le_trans m1 hM
  have hM2 := le_trans m2 hM
  refine max_le ?_ ?_
  · linarith
  · linarith

end OCPThm2Aux

namespace OCPThm2Aux

lemma priceVar_pos {K : ℕ} (P : Public K) (hK : 2 ≤ K) (hinj : Function.Injective P.p) :
    0 < priceVar P := by
  unfold priceVar
  set m := (1 / (K : ℝ)) * ∑ j, P.p j
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hsum : 0 < ∑ i, (P.p i - m) ^ 2 := by
    rcases (Finset.sum_nonneg (fun i _ => sq_nonneg (P.p i - m))).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (P.p i - m))).1 h.symm
      have a := h0 ⟨0, by omega⟩ (Finset.mem_univ _)
      have b := h0 ⟨1, by omega⟩ (Finset.mem_univ _)
      have ha : P.p ⟨0, by omega⟩ = m := by nlinarith [sq_nonneg (P.p ⟨0, by omega⟩ - m)]
      have hb : P.p ⟨1, by omega⟩ = m := by nlinarith [sq_nonneg (P.p ⟨1, by omega⟩ - m)]
      have := hinj (ha.trans hb.symm)
      simp [Fin.ext_iff] at this
  exact mul_pos (by positivity) hsum

lemma tail (N ε D C L : ℝ) (hD : 0 < D) (hDC : D ≤ C) (hε : 0 < ε) (hL : 0 ≤ L)
    (hN : C * (1 / ε ^ 2) * L ≤ N) : L ≤ N * ε ^ 2 / D := by
  have hC : 0 < C := lt_of_lt_of_le hD hDC
  have h1 : C * L ≤ N * ε ^ 2 := by
    have := mul_le_mul_of_nonneg_right hN (sq_nonneg ε)
    have e : C * (1 / ε ^ 2) * L * ε ^ 2 = C * L := by field_simp
    linarith
  rw [le_div_iff₀ hD]
  nlinarith

lemma term (K : ℕ) (hK : 0 < (K : ℝ)) (δ x L : ℝ) (hδ : 0 < δ) (hLdef : L = Real.log (8 * K / δ))
    (hx : L ≤ x) : 2 * K * Real.exp (-x) ≤ δ / 4 := by
  have h8 : 0 < 8 * (K : ℝ) / δ := by positivity
  have h1 : Real.exp (-x) ≤ Real.exp (-L) := Real.exp_le_exp.2 (by linarith)
  have e1 : Real.exp (-L) = (8 * K / δ)⁻¹ := by rw [hLdef, Real.exp_neg, Real.exp_log h8]
  have this : Real.exp (-x) ≤ (8 * K / δ)⁻¹ := e1 ▸ h1
  have e : 2 * (K : ℝ) * (8 * K / δ)⁻¹ = δ / 4 := by field_simp; ring
  calc 2 * K * Real.exp (-x) ≤ 2 * K * (8 * K / δ)⁻¹ :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = δ / 4 := e

end OCPThm2Aux

open OCPThm2Aux in
theorem solution {K : ℕ} [NeZero K] (I : Instance K) (hI : I.Standing)
    (heq : pStarMax I = pStarMin I) {ε δ : ℝ} (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (Nv : Fin K → ℕ) (hN : Cthm2 I * (1 / ε ^ 2) * Real.log (8 * K / δ) ≤ (Nmin Nv : ℝ)) :
    dataLaw I Nv {ω | ε < worstLoss I (d2acd I.toPublic Nv (sales I ω)) ∧
        ∀ i, 0 < gammaHat I.toPublic (sales I ω) i} ≤ ENNReal.ofReal δ := by
  have hI' := hI
  obtain ⟨hP, hy, hplo, hlohi, hblo, hbb, hbhi, hK, hinj, hpi, hyh, -, -, hA1⟩ := hI'
  set α := ε / 4 with hα
  have hα0 : 0 < α := by positivity
  -- the bad event is contained in the event of Lemma 2
  have hsub : {ω | ε < worstLoss I (d2acd I.toPublic Nv (sales I ω)) ∧
        ∀ i, 0 < gammaHat I.toPublic (sales I ω) i} ⊆
      {ω | ((∃ q ∈ Icc I.plo I.phi, α < |RHatMax I.toPublic (sales I ω) q - Rmax I q|) ∨
          (∃ q ∈ Icc I.plo I.phi, α < |RHatMin I.toPublic (sales I ω) q - Rmin I q|)) ∧
        ∀ i, 0 < gammaHat I.toPublic (sales I ω) i} := by
    rintro ω ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    by_contra hb
    push_neg at hb
    have hNpos : ∀ i, 0 < Nv i := by
      intro i
      by_contra h0
      push_neg at h0
      have h0' : Nv i = 0 := by omega
      have := h2 i
      unfold gammaHat at this
      have hz : ((Nv i : ℕ) : ℝ) = 0 := by exact_mod_cast h0'
      rw [hz, div_zero] at this
      exact lt_irrefl _ this
    have := chain I hI heq (sales I ω) (fun i j => min_le_right _ _) hNpos hb.1 hb.2
    linarith
  refine le_trans (measure_mono hsub) (le_trans (lemma_2 I hI Nv hα0) ?_)
  apply ENNReal.ofReal_le_ofReal
  -- arithmetic
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hphi : 0 < I.phi := lt_trans hplo hlohi
  have hb : 0 < I.b := lt_of_lt_of_le hblo hbb
  have hbh : 0 < I.bhi := lt_of_lt_of_le hb hbhi
  have i0 : Fin K := ⟨0, by omega⟩
  have hlamBar : 0 < lamBar I := by
    have hle : I.yh i0 + I.bhi * I.p i0 ≤ lamBar I :=
      le_ciSup (Finite.bddAbove_range (fun i => I.yh i + I.bhi * I.p i)) i0
    have := hyh i0
    have := mul_pos hbh (lt_of_lt_of_le hplo (hpi i0).1)
    linarith
  have hyb : 0 < I.y + I.bhi * I.phi := by have := mul_pos hbh hphi; linarith
  have hC2 : 0 < C2 I := by unfold C2; have := mul_pos hphi hbh; positivity
  have hC1 : 0 < C1 I := by unfold C1; positivity
  have hpv := priceVar_pos I.toPublic hK hinj
  have hg : 0 < I.g := hA1.1
  have hL : 0 ≤ Real.log (8 * K / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ0]
    have : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
    linarith
  set N := (Nmin Nv : ℝ)
  set L := Real.log (8 * K / δ) with hLdef
  have D1 := tail N ε (576 * (I.y + I.bhi * I.phi) ^ 2 * I.phi ^ 2) (Cthm2 I) L (by positivity)
    (le_trans (le_max_left _ _) (le_max_left _ _)) hε hL hN
  have D2 := tail N ε (576 * C1 I ^ 2 / (priceVar I.toPublic * I.g ^ 2)) (Cthm2 I) L
    (by positivity) (le_trans (le_max_right _ _) (le_max_left _ _)) hε hL hN
  have D3 := tail N ε (288 * C2 I ^ 2) (Cthm2 I) L (by positivity)
    (le_trans (le_max_left _ _) (le_max_right _ _)) hε hL hN
  have D4 := tail N ε (288 * I.phi ^ 2 * lamBar I ^ 2) (Cthm2 I) L (by positivity)
    (le_trans (le_max_right _ _) (le_max_right _ _)) hε hL hN
  have t1 := term K hKpos δ (N * α ^ 2 / (36 * (I.y + I.bhi * I.phi) ^ 2 *
    I.phi ^ 2)) L hδ0 hLdef (by
      rw [show N * α ^ 2 / (36 * (I.y + I.bhi * I.phi) ^ 2 * I.phi ^ 2) =
        N * ε ^ 2 / (576 * (I.y + I.bhi * I.phi) ^ 2 * I.phi ^ 2) by
          rw [hα]; field_simp; ring]
      exact D1)
  have t2 := term K hKpos δ (priceVar I.toPublic * I.g ^ 2 / (36 * C1 I ^ 2) *
    N * α ^ 2) L hδ0 hLdef (by
      rw [show priceVar I.toPublic * I.g ^ 2 / (36 * C1 I ^ 2) * N * α ^ 2 =
        N * ε ^ 2 / (576 * C1 I ^ 2 / (priceVar I.toPublic * I.g ^ 2)) by
          rw [hα]; field_simp; ring]
      exact D2)
  have t3 := term K hKpos δ (N * α ^ 2 / (18 * C2 I ^ 2)) L hδ0 hLdef (by
      rw [show N * α ^ 2 / (18 * C2 I ^ 2) = N * ε ^ 2 / (288 * C2 I ^ 2) by
          rw [hα]; field_simp; ring]
      exact D3)
  have t4 := term K hKpos δ (N * α ^ 2 / (18 * I.phi ^ 2 * lamBar I ^ 2)) L hδ0 hLdef (by
      rw [show N * α ^ 2 / (18 * I.phi ^ 2 * lamBar I ^ 2) =
        N * ε ^ 2 / (288 * I.phi ^ 2 * lamBar I ^ 2) by
          rw [hα]; field_simp; ring]
      exact D4)
  linarith
