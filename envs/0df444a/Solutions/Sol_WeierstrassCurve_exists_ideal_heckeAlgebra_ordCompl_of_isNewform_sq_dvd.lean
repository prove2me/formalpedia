-- Prove2me | solution 1 for WeierstrassCurve.exists_ideal_heckeAlgebra_ordCompl_of_isNewform_sq_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/66267516-aa61-52f6-919b-1dcec0ae4060

import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Theorems.Thm_CuspForm_exists_coe_eq_add_smul_heckeU_alSlash
import Theorems.Thm_CuspForm_exists_cuspForm_mul_ordCompl_qCoeff_congr_pow_of_sq_dvd
import Theorems.Thm_CuspForm_exists_eigenform_qCoeff_congr_of_heckeT_sub_mem
import Theorems.Thm_CuspForm_exists_normalized_eigenvector
import Theorems.Thm_CuspForm_exists_weight_ge_qCoeff_congr_level_div_of_alSlash_p_integral
import Theorems.Thm_CuspForm_finiteDimensional_adjoin_qCoeff
import Theorems.Thm_CuspForm_forall_exists_qCoeff_eq_of_isNormalizedEigenform
import Theorems.Thm_CuspForm_heckeAlgebra_exists_isMaximal_heckeT_sub_mem_of_qCoeff_congr
import Theorems.Thm_ModularForm_alSlash_eq_neg_heckeU_of_trace_alSlash_eq_zero
import Theorems.Thm_ModularForm_heckeT_trace_alSlash_of_eigen
import Theorems.Thm_PowerSeries_coeff_heckeT_pow_sub_mem_span
import Theorems.Thm_CuspForm_qCoeff_eq_zero_of_isNewform_of_sq_dvd
import Theorems.Thm_CuspForm_qCoeff_zero
import Theorems.Thm_ModularFormClass_qExpansion_heckeU_eq_heckeU
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_ideal_heckeAlgebra_ordCompl_of_isNewform_sq_dvd
p2m_attr_erase "simp" "CuspForm.coe_heckeULowerLin_apply"

set_option autoImplicit false

open CuspForm ModularFormClass

namespace LevelStripAux

private lemma sub_pow_mem {R : Type} [CommRing R] (I : Ideal R) {x y : R}
    (h : x - y ∈ I) (m : ℕ) : x ^ m - y ^ m ∈ I := by
  induction m with
  | zero => simp
  | succ t ih =>
      have hid : x ^ (t + 1) - y ^ (t + 1) = x * (x ^ t - y ^ t) + (x - y) * y ^ t := by ring
      rw [hid]
      exact I.add_mem (I.mul_mem_left _ ih) (I.mul_mem_right _ h)

private lemma sub_one_dvd_pow_sub_one (x : ℤ) (m : ℕ) : (x - 1) ∣ x ^ m - 1 := by
  induction m with
  | zero => simp
  | succ t ih =>
      have hid : x ^ (t + 1) - 1 = x * (x ^ t - 1) + (x - 1) := by ring
      rw [hid]
      exact dvd_add (ih.mul_left x) dvd_rfl

private lemma int_fermat_span (p : ℕ) [Fact p.Prime] (a : ℤ) (j : ℕ) :
    ((a ^ p ^ j : ℤ) : integralClosure ℤ ℂ) - ((a : ℤ) : integralClosure ℤ ℂ) ∈
      Ideal.span {(p : integralClosure ℤ ℂ)} := by
  have key : ∀ x : ZMod p, x ^ p ^ j = x := by
    intro x
    induction j with
    | zero => simp
    | succ t ih => rw [pow_succ, pow_mul, ih, ZMod.pow_card]
  have hz : (p : ℤ) ∣ a ^ p ^ j - a := by
    have h0 : ((a ^ p ^ j - a : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [key]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
  obtain ⟨t, ht⟩ := hz
  refine Ideal.mem_span_singleton.mpr ⟨(t : integralClosure ℤ ℂ), ?_⟩
  have := congrArg (fun z : ℤ => ((z : ℤ) : integralClosure ℤ ℂ)) ht
  push_cast at this ⊢
  linear_combination this

private lemma pow_congr_of_dvd_sub (p : ℕ) [Fact p.Prime] {ℓ : ℕ} (hℓp : ¬ p ∣ ℓ)
    (a b : ℕ) (hab : (p - 1 : ℕ) ∣ b - a) (hba : a ≤ b) :
    (ℓ : integralClosure ℤ ℂ) ^ b - (ℓ : integralClosure ℤ ℂ) ^ a ∈
      Ideal.span {(p : integralClosure ℤ ℂ)} := by
  obtain ⟨t, ht⟩ := hab
  have hz : (p : ℤ) ∣ ℓ ^ (b - a) - 1 := by
    have h0 : ((ℓ ^ (b - a) - 1 : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [ht, pow_mul, ZMod.pow_card_sub_one_eq_one (by
        intro h
        apply hℓp
        have h' : ((ℓ : ℤ) : ZMod p) = 0 := by exact_mod_cast h
        exact Int.natCast_dvd_natCast.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h')), one_pow]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
  obtain ⟨u, hu⟩ := hz
  have hsplit : (ℓ : integralClosure ℤ ℂ) ^ b =
      (ℓ : integralClosure ℤ ℂ) ^ a * (ℓ : integralClosure ℤ ℂ) ^ (b - a) := by
    rw [← pow_add]
    congr 1
    omega
  refine Ideal.mem_span_singleton.mpr ⟨(ℓ : integralClosure ℤ ℂ) ^ a * (u : integralClosure ℤ ℂ), ?_⟩
  have hcast := congrArg (fun z : ℤ => ((z : ℤ) : integralClosure ℤ ℂ)) hu
  push_cast at hcast
  rw [hsplit]
  linear_combination (ℓ : integralClosure ℤ ℂ) ^ a * hcast

private theorem qCoeff_heckeULin_eq {M : ℕ} [NeZero M] (p : ℕ) (hp0 : p ≠ 0) (w : ℤ) (hpM : p ∣ M)
    (F : CuspForm (CongruenceSubgroup.Gamma0 M) w) (n : ℕ) :
    ModularFormClass.qCoeff (heckeULin w hpM F) n = ModularFormClass.qCoeff F (p * n) := by
  unfold ModularFormClass.qCoeff
  rw [show ⇑(heckeULin w hpM F) = ModularForm.heckeU w p ⇑F from rfl]
  rw [ModularFormClass.qExpansion_heckeU_eq_heckeU F
    (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 M) hp0]
  rw [PowerSeries.coeff_heckeU]

private theorem qCoeff_heckeTLin_eq {M : ℕ} [NeZero M] (w : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (F : CuspForm (CongruenceSubgroup.Gamma0 M) w) (n : ℕ) :
    ModularFormClass.qCoeff (heckeTLin w hℓ hℓM F) n =
      ModularFormClass.qCoeff F (ℓ * n) +
        (ℓ : ℂ) ^ (w - 1) * (if ℓ ∣ n then ModularFormClass.qCoeff F (n / ℓ) else 0) := by
  have hcoe : (⇑(heckeTLin w hℓ hℓM F) : UpperHalfPlane → ℂ) = ModularForm.heckeT w ℓ ⇑F :=
    coe_heckeTLin_apply w hℓ hℓM F
  show ModularFormClass.qCoeff (⇑(heckeTLin w hℓ hℓM F)) n = _
  rw [hcoe]
  rw [show ModularFormClass.qCoeff (ModularForm.heckeT w ℓ ⇑F) n =
      ModularForm.coeffHeckeT w ℓ (ModularFormClass.qCoeff F) n from
    ModularFormClass.qCoeff_heckeT F
      (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 M) hℓ.ne_zero n]
  rw [ModularForm.coeffHeckeT_apply, mul_comm n ℓ]
  by_cases hdvd : ℓ ∣ n <;> simp [hdvd]

private lemma qCoeff_pmul_eq_zero {L p : ℕ} [NeZero L] (hp : p.Prime)
    {g : CuspForm (CongruenceSubgroup.Gamma0 L) 2} (hg : g.IsNewform) (hpL : p ^ 2 ∣ L)
    (n : ℕ) : ModularFormClass.qCoeff g (p * n) = 0 := by
  have hap : ModularFormClass.qCoeff g p = 0 :=
    CuspForm.qCoeff_eq_zero_of_isNewform_of_sq_dvd hg p hp hpL
  have hpdvd : p ∣ L := (dvd_pow_self p two_ne_zero).trans hpL
  have hpow : ∀ s : ℕ, ModularFormClass.qCoeff g (p ^ (s + 1)) = 0 := by
    intro s
    induction s with
    | zero => simpa using hap
    | succ t ih =>
      have hrec := hg.isNormalizedEigenform.qCoeff_prime_pow_of_dvd p t hp hpdvd
      rw [hrec, hap, zero_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using CuspForm.qCoeff_zero g
  · have hn0 : n ≠ 0 := hn.ne'
    set r := n.factorization p with hr
    set m := n / p ^ r with hm
    have hnm : n = p ^ r * m := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
    have hcopm : Nat.Coprime p m := Nat.coprime_ordCompl hp hn0
    have hpn : p * n = p ^ (r + 1) * m := by
      rw [hnm]; ring
    have hcop' : Nat.Coprime (p ^ (r + 1)) m := Nat.Coprime.pow_left _ hcopm
    rw [hpn, hg.isNormalizedEigenform.qCoeff_mul_of_coprime _ _ hcop', hpow r, zero_mul]

end LevelStripAux

set_option maxHeartbeats 1600000 in

theorem solution (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ)
    (hΔ : W.Δ ≠ 0) (hirr : W.ModRepIsIrreducible p)
    {L : ℕ} [NeZero L] (hpL : p ^ 2 ∣ L)
    (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (hS₀p : p ∈ S₀)
    (hS₀L : ∀ q : ℕ, q.Prime → q ∣ L → q ∈ S₀)
    (hS₀Δ : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ W.Δ → q ∈ S₀)
    (g : CuspForm (CongruenceSubgroup.Gamma0 L) 2) (𝔪 : Ideal (integralClosure ℤ ℂ))
    (hg : g.IsNewform) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ℓ ∉ S₀ →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff g ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪)
    (N' : ℕ) [NeZero N'] (hN' : N' = L / p ^ (L.factorization p)) :
    ∃ k : ℤ, 2 ≤ k ∧
      ∃ 𝔪ₖ : Ideal (heckeAlgebra N' k S₀), 𝔪ₖ.IsMaximal ∧
        (p : heckeAlgebra N' k S₀) ∈ 𝔪ₖ ∧
        ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N'),
          W.IsGoodPrimeFor ℓ →
            heckeAlgebra.T hℓ hℓN hℓS -
              ((W.apOfModel ℓ : ℤ) : heckeAlgebra N' k S₀) ∈ 𝔪ₖ := by
  have _ := hΔ
  have _ := hirr
  classical
  subst hN'
  have hp' : p.Prime := Fact.out
  have hL0 : L ≠ 0 := NeZero.ne L
  have hv2 : 2 ≤ L.factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp' hL0).mp hpL
  have hpN' : ¬ p ∣ L / p ^ (L.factorization p) := Nat.not_dvd_ordCompl hp' hL0
  haveI hMne : NeZero (p * (L / p ^ (L.factorization p))) :=
    ⟨mul_ne_zero hp'.ne_zero (NeZero.ne _)⟩
  have hgint := CuspForm.forall_exists_qCoeff_eq_of_isNormalizedEigenform hg.isNormalizedEigenform
  haveI hKfd : FiniteDimensional ℚ
      (IntermediateField.adjoin ℚ (Set.range fun n : ℕ => ModularFormClass.qCoeff g n)) :=
    CuspForm.finiteDimensional_adjoin_qCoeff hg.isNormalizedEigenform
  have hgK : ∀ n : ℕ, ModularFormClass.qCoeff g n ∈
      IntermediateField.adjoin ℚ (Set.range fun n : ℕ => ModularFormClass.qCoeff g n) :=
    fun n => IntermediateField.subset_adjoin _ _ ⟨n, rfl⟩
  obtain ⟨F, hFint, hFK, hFcong⟩ := CuspForm.exists_cuspForm_mul_ordCompl_qCoeff_congr_pow_of_sq_dvd p hv2 rfl g hgint
  have hFKmem := hFK _ hgK
  have hspan𝔪 : Ideal.span {(p : integralClosure ℤ ℂ)} ≤ 𝔪 :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hp𝔪)
  have glue_hFne : ∃ (n : ℕ) (x : integralClosure ℤ ℂ),
      (x : ℂ) = ModularFormClass.qCoeff F n ∧ x ∉ 𝔪 := by
    obtain ⟨A1, hA1⟩ := hFint 1
    refine ⟨1, A1, hA1, fun hA1m => ?_⟩
    have h1g : ((1 : integralClosure ℤ ℂ) : ℂ) = ModularFormClass.qCoeff g 1 := by
      rw [hg.isNormalizedEigenform.qCoeff_one]; push_cast; ring
    have hc := hFcong 1 1 A1 h1g hA1
    rw [one_pow] at hc
    have h1m : (1 : integralClosure ℤ ℂ) ∈ 𝔪 := by
      have heq : (1 : integralClosure ℤ ℂ) = A1 - (A1 - 1) := by ring
      rw [heq]
      exact Ideal.sub_mem 𝔪 hA1m (hspan𝔪 hc)
    exact h𝔪.ne_top ((Ideal.eq_top_iff_one 𝔪).mpr h1m)
  have hkN2 : 2 ≤ 2 * p ^ (L.factorization p - 1) := by
    have : 1 ≤ p ^ (L.factorization p - 1) := Nat.one_le_pow _ _ hp'.pos
    omega
  have hwkN : (2 * (p : ℤ) ^ (L.factorization p - 1)) =
      ((2 * p ^ (L.factorization p - 1) : ℕ) : ℤ) := by
    push_cast; ring
  have glue_hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀)
      (hℓM : ¬ ℓ ∣ p * (L / p ^ (L.factorization p))) (n : ℕ)
      (x x' : integralClosure ℤ ℂ),
      (x : ℂ) = ModularFormClass.qCoeff
        (heckeTLin (2 * (p : ℤ) ^ (L.factorization p - 1)) hℓ hℓM F) n →
      (x' : ℂ) = ModularFormClass.qCoeff F n →
      x - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) * x' ∈ 𝔪 := by
    intro ℓ hℓ hℓS hℓM n x x' hx hx'
    let ag : ℕ → integralClosure ℤ ℂ := fun m => (hgint m).choose
    have hag : ∀ m : ℕ, ((ag m : integralClosure ℤ ℂ) : ℂ) = ModularFormClass.qCoeff g m :=
      fun m => (hgint m).choose_spec
    let AF : ℕ → integralClosure ℤ ℂ := fun m => (hFint m).choose
    have hAF : ∀ m : ℕ, ((AF m : integralClosure ℤ ℂ) : ℂ) = ModularFormClass.qCoeff F m :=
      fun m => (hFint m).choose_spec
    have hgood : W.IsGoodPrimeFor ℓ := fun hd => hℓS (hS₀Δ ℓ hℓ hd)
    have hℓL : ¬ ℓ ∣ L := fun hd => hℓS (hS₀L ℓ hℓ hd)
    set c : integralClosure ℤ ℂ := ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) with hcdef
    set X : integralClosure ℤ ℂ :=
      AF (ℓ * n) + (ℓ : integralClosure ℤ ℂ) ^ (2 * p ^ (L.factorization p - 1) - 1) *
        (if ℓ ∣ n then AF (n / ℓ) else 0) with hXdef
    have hzn : (2 * (p : ℤ) ^ (L.factorization p - 1)) - 1 = ((2 * p ^ (L.factorization p - 1) - 1 : ℕ) : ℤ) := by
      have h1p : 1 ≤ p ^ (L.factorization p - 1) := Nat.one_le_pow _ _ hp'.pos
      rw [hwkN]; omega
    have hxX : x = X := by
      apply Subtype.coe_injective
      show (x : ℂ) = (X : ℂ)
      by_cases hdvd : ℓ ∣ n
      · rw [hx, LevelStripAux.qCoeff_heckeTLin_eq _ hℓ hℓM F n, hzn, zpow_natCast]
        simp only [hXdef, if_pos hdvd]
        push_cast [hAF (ℓ * n), hAF (n / ℓ)]
        try ring
      · rw [hx, LevelStripAux.qCoeff_heckeTLin_eq _ hℓ hℓM F n, hzn, zpow_natCast]
        simp only [hXdef, if_neg hdvd]
        push_cast [hAF (ℓ * n)]
        try ring
    set Y : integralClosure ℤ ℂ :=
      ag (ℓ * n) ^ p ^ (L.factorization p - 1) + (ℓ : integralClosure ℤ ℂ) ^ (2 * p ^ (L.factorization p - 1) - 1) *
        (if ℓ ∣ n then ag (n / ℓ) ^ p ^ (L.factorization p - 1) else 0) with hYdef
    have hXY : X - Y ∈ Ideal.span {(p : integralClosure ℤ ℂ)} := by
      have h1 := hFcong (ℓ * n) (ag (ℓ * n)) (AF (ℓ * n)) (hag _) (hAF _)
      have h2 : (ℓ : integralClosure ℤ ℂ) ^ (2 * p ^ (L.factorization p - 1) - 1) * (if ℓ ∣ n then AF (n / ℓ) else 0) -
          (ℓ : integralClosure ℤ ℂ) ^ (2 * p ^ (L.factorization p - 1) - 1) *
            (if ℓ ∣ n then ag (n / ℓ) ^ p ^ (L.factorization p - 1) else 0) ∈
          Ideal.span {(p : integralClosure ℤ ℂ)} := by
        by_cases hdvd : ℓ ∣ n
        · simp only [if_pos hdvd]
          rw [← mul_sub]
          exact Ideal.mul_mem_left _ _
            (hFcong (n / ℓ) (ag (n / ℓ)) (AF (n / ℓ)) (hag _) (hAF _))
        · simp only [if_neg hdvd, mul_zero, sub_self]
          exact Ideal.zero_mem _
      have hsum := Ideal.add_mem _ h1 h2
      rw [hXdef, hYdef]
      convert hsum using 1
      ring
    have hk2N : (p - 1 : ℕ) ∣ 2 * p ^ (L.factorization p - 1) - 2 := by
      have h1 : (p - 1 : ℕ) ∣ p ^ (L.factorization p - 1) - 1 := by
        have hz : ((p : ℤ) - 1) ∣ (p : ℤ) ^ (L.factorization p - 1) - 1 := LevelStripAux.sub_one_dvd_pow_sub_one _ _
        have h1p : 1 ≤ p ^ (L.factorization p - 1) := Nat.one_le_pow _ _ hp'.pos
        have hcast : ((p ^ (L.factorization p - 1) - 1 : ℕ) : ℤ) = (p : ℤ) ^ (L.factorization p - 1) - 1 := by push_cast [h1p]; ring
        have hcast2 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
          push_cast [hp'.one_lt.le]
          ring
        rw [← Int.natCast_dvd_natCast, hcast, hcast2]
        exact hz
      have h1p : 1 ≤ p ^ (L.factorization p - 1) := Nat.one_le_pow _ _ hp'.pos
      have h2 : 2 * p ^ (L.factorization p - 1) - 2 = 2 * (p ^ (L.factorization p - 1) - 1) := by omega
      rw [h2]
      exact h1.mul_left 2
    have hhead := PowerSeries.coeff_heckeT_pow_sub_mem_span p hg.isNormalizedEigenform ag hag (L.factorization p - 1) (2 * p ^ (L.factorization p - 1)) hkN2 hk2N
      ℓ hℓ hℓL n
    rw [PowerSeries.coeff_heckeT] at hhead
    simp only [PowerSeries.coeff_mk] at hhead
    have hYhead : Y - ag ℓ ^ p ^ (L.factorization p - 1) * ag n ^ p ^ (L.factorization p - 1) ∈ Ideal.span {(p : integralClosure ℤ ℂ)} := by
      rw [hYdef]
      exact hhead
    obtain ⟨aW, haWℂ, haW𝔪⟩ := hcong ℓ hℓ hgood hℓS
    have hagℓ : ag ℓ = aW := Subtype.coe_injective (by
      show ((ag ℓ : integralClosure ℤ ℂ) : ℂ) = (aW : ℂ)
      rw [hag ℓ, haWℂ])
    have hb1 : ag ℓ - c ∈ 𝔪 := by rw [hagℓ, hcdef]; exact haW𝔪
    have hb2 : ag ℓ ^ p ^ (L.factorization p - 1) - c ^ p ^ (L.factorization p - 1) ∈ 𝔪 := LevelStripAux.sub_pow_mem 𝔪 hb1 _
    have hb3 : c ^ p ^ (L.factorization p - 1) - c ∈ 𝔪 := by
      have hf := LevelStripAux.int_fermat_span p (W.apOfModel ℓ) (L.factorization p - 1)
      rw [hcdef]
      push_cast at hf
      exact hspan𝔪 hf
    have hb4 : x' - ag n ^ p ^ (L.factorization p - 1) ∈ 𝔪 := hspan𝔪 (hFcong n (ag n) x' (hag n) hx')
    have hfin : x - c * x' =
        (X - Y) + (Y - ag ℓ ^ p ^ (L.factorization p - 1) * ag n ^ p ^ (L.factorization p - 1)) +
        ((ag ℓ ^ p ^ (L.factorization p - 1) - c ^ p ^ (L.factorization p - 1)) * ag n ^ p ^ (L.factorization p - 1) + (c ^ p ^ (L.factorization p - 1) - c) * ag n ^ p ^ (L.factorization p - 1)
          - c * (x' - ag n ^ p ^ (L.factorization p - 1))) := by
      rw [hxX]; ring
    rw [hfin]
    exact Ideal.add_mem _ (Ideal.add_mem _ (hspan𝔪 hXY) (hspan𝔪 hYhead))
      (Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hb2)
        (Ideal.mul_mem_right _ _ hb3)) (Ideal.mul_mem_left _ _ hb4))
  have glue_hU : ∀ (n : ℕ) (x x' : integralClosure ℤ ℂ),
      (x : ℂ) = ModularFormClass.qCoeff
        (heckeULin (2 * (p : ℤ) ^ (L.factorization p - 1)) (dvd_mul_right p _) F) n →
      (x' : ℂ) = ModularFormClass.qCoeff F n →
      x - ((0 : ℤ) : integralClosure ℤ ℂ) * x' ∈ 𝔪 := by
    intro n x x' hx _hx'
    have hxF : (x : ℂ) = ModularFormClass.qCoeff F (p * n) := by
      rw [hx, LevelStripAux.qCoeff_heckeULin_eq p hp'.ne_zero _ (dvd_mul_right p _) F n]
    have h0g : ((0 : integralClosure ℤ ℂ) : ℂ) = ModularFormClass.qCoeff g (p * n) := by
      rw [LevelStripAux.qCoeff_pmul_eq_zero hp' hg hpL n]; push_cast; ring
    have hc := hFcong (p * n) 0 x h0g hxF
    have hpvpos : p ^ (L.factorization p - 1) ≠ 0 := pow_ne_zero _ hp'.ne_zero
    rw [zero_pow hpvpos, sub_zero] at hc
    have hxm : x ∈ 𝔪 := hspan𝔪 hc
    have : x - ((0 : ℤ) : integralClosure ℤ ℂ) * x' = x := by push_cast; ring
    rw [this]
    exact hxm
  obtain ⟨𝔪', h𝔪', hp𝔪', f, hfint, hfne, hfT, hfU⟩ :=
    CuspForm.exists_eigenform_qCoeff_congr_of_heckeT_sub_mem p (p * (L / p ^ (L.factorization p))) (dvd_mul_right p _)
      (2 * (p : ℤ) ^ (L.factorization p - 1)) S₀ 𝔪 h𝔪 hp𝔪 _ F hFKmem hFint glue_hFne
      (fun ℓ => W.apOfModel ℓ) 0 glue_hT glue_hU
  choose lamf hlamf hlamfeq using hfT
  obtain ⟨α, hα0, hαeq⟩ := hfU
  have hcop : Nat.Coprime p (L / p ^ (L.factorization p)) := Nat.coprime_ordCompl hp' hL0
  obtain ⟨a0, b0, hab⟩ :
      ∃ a0 b0 : ℤ, (p : ℤ) * a0 - ((L / p ^ (L.factorization p) : ℕ) : ℤ) * b0 = 1 := by
    refine ⟨Nat.gcdA p (L / p ^ (L.factorization p)),
      - Nat.gcdB p (L / p ^ (L.factorization p)), ?_⟩
    have hg1 : Nat.gcd p (L / p ^ (L.factorization p)) = 1 := hcop
    have hbez := Nat.gcd_eq_gcd_ab p (L / p ^ (L.factorization p))
    rw [hg1] at hbez
    push_cast at hbez ⊢
    linarith
  set A : ModularForm.AtkinLehnerDatum (p * (L / p ^ (L.factorization p))) p :=
    ⟨L / p ^ (L.factorization p), rfl, a0, b0, hab⟩ with hAdef
  have hw2 : (2 : ℤ) ≤ 2 * (p : ℤ) ^ (L.factorization p - 1) := by
    nlinarith [pow_pos (by exact_mod_cast hp'.pos : (0 : ℤ) < (p : ℤ)) (L.factorization p - 1)]
  have hS₀N' : ∀ q : ℕ, q.Prime → q ∣ L / p ^ (L.factorization p) → q ∈ S₀ := fun q hq hqd =>
    hS₀L q hq (hqd.trans (Nat.ordCompl_dvd L p))
  by_cases hTrW : ModularForm.alSlash A (2 * (p : ℤ) ^ (L.factorization p - 1)) ⇑f +
      (p : ℂ) ^ (2 - 2 * (p : ℤ) ^ (L.factorization p - 1)) •
        ModularForm.heckeU (2 * (p : ℤ) ^ (L.factorization p - 1)) p
          (ModularForm.alSlash A (2 * (p : ℤ) ^ (L.factorization p - 1))
            (ModularForm.alSlash A (2 * (p : ℤ) ^ (L.factorization p - 1)) ⇑f)) = 0
  ·
    have halS := ModularForm.alSlash_eq_neg_heckeU_of_trace_alSlash_eq_zero p A
      (2 * (p : ℤ) ^ (L.factorization p - 1)) f hTrW
    have glueA_hFW : ∃ c : ℕ, ∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪' ∧
        (x : ℂ) = y * (p : ℂ) ^ c *
          ModularFormClass.qCoeff
            (ModularForm.alSlash A (2 * (p : ℤ) ^ (L.factorization p - 1)) ⇑f) n := by
      have hUcoe : ModularForm.heckeU (2 * (p : ℤ) ^ (L.factorization p - 1)) p ⇑f
          = (α : ℂ) • ⇑f := by
        have h : ⇑(heckeULin (2 * (p : ℤ) ^ (L.factorization p - 1))
            (dvd_mul_right p (L / p ^ (L.factorization p))) f) = ⇑((α : ℂ) • f) := by
          rw [hαeq]
        simpa using h
      have hA : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 ⇑f) 0 :=
        ModularFormClass.analyticAt_cuspFunction_zero f one_pos
          (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 _)
      have hq : ∀ n : ℕ, ModularFormClass.qCoeff
          (ModularForm.alSlash A (2 * (p : ℤ) ^ (L.factorization p - 1)) ⇑f) n
          = -(α : ℂ) * ModularFormClass.qCoeff f n := by
        intro n
        rw [halS, hUcoe]
        unfold ModularFormClass.qCoeff
        rw [show -((α : ℂ) • ⇑f) = (-(α : ℂ)) • ⇑f from (neg_smul _ _).symm,
          UpperHalfPlane.qExpansion_smul hA (-(α : ℂ))]
        simp
      refine ⟨0, fun n => ?_⟩
      obtain ⟨x, y, hy, hxy⟩ := hfint n
      refine ⟨-α * x, y, hy, ?_⟩
      rw [hq n]
      push_cast
      rw [hxy]
      ring
    obtain ⟨k, G, hwk, hkw, hGint, hGF⟩ := CuspForm.exists_weight_ge_qCoeff_congr_level_div_of_alSlash_p_integral p hp2
      (L / p ^ (L.factorization p)) A 𝔪' h𝔪'.isPrime hp𝔪'
      (2 * (p : ℤ) ^ (L.factorization p - 1)) hw2 f hfint glueA_hFW
    have hk2 : (2 : ℤ) ≤ k := le_trans hw2 hwk
    have hprime𝔪' : 𝔪'.IsPrime := h𝔪'.isPrime
    have hnm : ∀ {u v : integralClosure ℤ ℂ}, u ∉ 𝔪' → v ∉ 𝔪' → u * v ∉ 𝔪' := by
      intro u v hu hv hmem
      rcases (hprime𝔪'.mul_mem_iff_mem_or_mem).mp hmem with h | h
      · exact hu h
      · exact hv h
    have hA : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 ⇑f) 0 :=
      ModularFormClass.analyticAt_cuspFunction_zero f one_pos
        (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 _)
    have glueA_entry :
        (∃ (n : ℕ) (x y : integralClosure ℤ ℂ), n.Coprime 1 ∧ y ∉ 𝔪' ∧
          (x : ℂ) = y * ModularFormClass.qCoeff G n ∧ x ∉ 𝔪') ∧
        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀)
            (hℓN : ¬ ℓ ∣ L / p ^ (L.factorization p)),
          ∃ e : integralClosure ℤ ℂ,
            (W.IsGoodPrimeFor ℓ → e - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪') ∧
            ∀ (n : ℕ) (x x' y : integralClosure ℤ ℂ), n.Coprime 1 → y ∉ 𝔪' →
              (x : ℂ) = y * ModularFormClass.qCoeff
                (((heckeAlgebra.T hℓ hℓN hℓS :
                    heckeAlgebra (L / p ^ (L.factorization p)) k S₀) :
                  Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0
                    (L / p ^ (L.factorization p))) k)) G) n →
              (x' : ℂ) = y * ModularFormClass.qCoeff G n → x - e * x' ∈ 𝔪') := by
      constructor
      ·
        obtain ⟨n, x, y, hy, hxy, hxnot⟩ := hfne
        obtain ⟨x', y', hy', hx'y'⟩ := hGint n
        have hcross := hGF n x y x' y' hy hy' hxy hx'y'
        have hxy'not : x * y' ∉ 𝔪' := hnm hxnot hy'
        have hx'ynot : x' * y ∉ 𝔪' := by
          intro hmem
          exact hxy'not (by
            have hid : x * y' = (x * y' - x' * y) + x' * y := by ring
            rw [hid]
            exact Ideal.add_mem _ hcross hmem)
        have hx'not : x' ∉ 𝔪' := fun h => hx'ynot (Ideal.mul_mem_right _ _ h)
        exact ⟨n, x', y', Nat.coprime_one_right n, hy', hx'y', hx'not⟩
      ·
        intro ℓ hℓ hℓS hℓN
        have hℓnp : ℓ ≠ p := fun h => hℓS (h ▸ hS₀p)
        have hpℓ : ¬ p ∣ ℓ := fun h => hℓnp ((Nat.prime_dvd_prime_iff_eq hp' hℓ).mp h).symm
        have hℓM : ¬ ℓ ∣ p * (L / p ^ (L.factorization p)) := by
          intro hdvd
          rcases (Nat.Prime.dvd_mul hℓ).mp hdvd with h | h
          · exact hℓnp ((Nat.prime_dvd_prime_iff_eq hℓ hp').mp h)
          · exact hℓN h
        refine ⟨lamf ℓ hℓ hℓS hℓM, fun _ => hlamf ℓ hℓ hℓS hℓM, ?_⟩
        intro n x x' y _ hy hx hx'
        rw [show ((heckeAlgebra.T hℓ hℓN hℓS :
              heckeAlgebra (L / p ^ (L.factorization p)) k S₀) :
            Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0
              (L / p ^ (L.factorization p))) k)) G = heckeTLin k hℓ hℓN G from by
          rw [heckeAlgebra.coe_T], LevelStripAux.qCoeff_heckeTLin_eq _ hℓ hℓN G n] at hx
        have heigf : ModularFormClass.qCoeff f (ℓ * n) +
            (ℓ : ℂ) ^ ((2 * (p : ℤ) ^ (L.factorization p - 1)) - 1) *
              (if ℓ ∣ n then ModularFormClass.qCoeff f (n / ℓ) else 0) =
            ((lamf ℓ hℓ hℓS hℓM : integralClosure ℤ ℂ) : ℂ) * ModularFormClass.qCoeff f n := by
          have hco : ModularFormClass.qCoeff
              (⇑(heckeTLin (2 * (p : ℤ) ^ (L.factorization p - 1)) hℓ hℓM f)) n =
              ModularFormClass.qCoeff
                (⇑(((lamf ℓ hℓ hℓS hℓM : integralClosure ℤ ℂ) : ℂ) • f)) n := by
            rw [hlamfeq ℓ hℓ hℓS hℓM]
          rw [LevelStripAux.qCoeff_heckeTLin_eq _ hℓ hℓM f n] at hco
          rw [hco]
          show ModularFormClass.qCoeff (⇑(((lamf ℓ hℓ hℓS hℓM : integralClosure ℤ ℂ) : ℂ) • f)) n = _
          unfold ModularFormClass.qCoeff
          rw [show (⇑(((lamf ℓ hℓ hℓS hℓM : integralClosure ℤ ℂ) : ℂ) • f) :
              UpperHalfPlane → ℂ) = ((lamf ℓ hℓ hℓS hℓM : integralClosure ℤ ℂ) : ℂ) • ⇑f from rfl,
            UpperHalfPlane.qExpansion_smul hA]
          simp
        have hw1 : (1 : ℤ) ≤ 2 * (p : ℤ) ^ (L.factorization p - 1) := le_trans one_le_two (by
          nlinarith [pow_pos (by exact_mod_cast hp'.pos : (0 : ℤ) < (p : ℤ)) (L.factorization p - 1)])
        have hzk : (k - 1 : ℤ) = (((k - 1).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
        have hzw : ((2 * (p : ℤ) ^ (L.factorization p - 1)) - 1 : ℤ) =
            ((((2 * (p : ℤ) ^ (L.factorization p - 1)) - 1).toNat : ℕ) : ℤ) :=
          (Int.toNat_of_nonneg (by omega)).symm
        set aw : ℕ := ((2 * (p : ℤ) ^ (L.factorization p - 1)) - 1).toNat with hawdef
        set ak : ℕ := (k - 1).toNat with hakdef
        have hfermat : (ℓ : integralClosure ℤ ℂ) ^ ak - (ℓ : integralClosure ℤ ℂ) ^ aw ∈
            Ideal.span {(p : integralClosure ℤ ℂ)} := by
          refine LevelStripAux.pow_congr_of_dvd_sub p hpℓ aw ak ?_ ?_
          · obtain ⟨t, ht⟩ := hkw
            have h1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
              push_cast [hp'.one_lt.le]; ring
            refine (Int.natCast_dvd_natCast).mp ?_
            have h2 : ((ak - aw : ℕ) : ℤ) = (k - 1) - ((2 * (p : ℤ) ^ (L.factorization p - 1)) - 1) := by
              rw [Nat.cast_sub (by omega : aw ≤ ak), hakdef, hawdef,
                ← hzk, ← hzw]
            rw [h1, h2]
            exact ⟨t, by linarith [ht]⟩
          · omega
        obtain ⟨gx1, gy1, hgy1, hg1⟩ := hGint (ℓ * n)
        obtain ⟨fx0, fy0, hfy0, hf0⟩ := hfint n
        obtain ⟨fx1, fy1, hfy1, hf1⟩ := hfint (ℓ * n)
        by_cases hdvd : ℓ ∣ n
        ·
          obtain ⟨gx2, gy2, hgy2, hg2⟩ := hGint (n / ℓ)
          obtain ⟨fx2, fy2, hfy2, hf2⟩ := hfint (n / ℓ)
          have hx𝕫 : x * (gy1 * gy2) = y * (gx1 * gy2 +
              (ℓ : integralClosure ℤ ℂ) ^ ak * (gx2 * gy1)) := by
            apply Subtype.coe_injective
            push_cast
            rw [hx]
            simp only [if_pos hdvd]
            rw [hzk, zpow_natCast]
            rw [hg1, hg2]
            ring
          have hf𝕫 : fx1 * (fy0 * fy2) + (ℓ : integralClosure ℤ ℂ) ^ aw * (fx2 * (fy0 * fy1)) -
              lamf ℓ hℓ hℓS hℓM * (fx0 * (fy1 * fy2)) = 0 := by
            apply Subtype.coe_injective
            push_cast
            rw [hzw, zpow_natCast] at heigf
            simp only [if_pos hdvd] at heigf
            rw [hf0, hf1, hf2]
            linear_combination ((fy0 : integralClosure ℤ ℂ) : ℂ) *
              ((fy1 : integralClosure ℤ ℂ) : ℂ) * ((fy2 : integralClosure ℤ ℂ) : ℂ) * heigf
          have hm2 := hGF (ℓ * n) fx1 fy1 gx1 gy1 hfy1 hgy1 hf1 hg1
          have hm3 := hGF (n / ℓ) fx2 fy2 gx2 gy2 hfy2 hgy2 hf2 hg2
          have hm4 := hGF n fx0 fy0 x' y hfy0 hy hf0 hx'
          have hm1 : (ℓ : integralClosure ℤ ℂ) ^ ak - (ℓ : integralClosure ℤ ℂ) ^ aw ∈ 𝔪' :=
            Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hp𝔪') hfermat
          have hfin : (x - lamf ℓ hℓ hℓS hℓM * x') * (gy1 * (gy2 * (fy0 * (fy1 * fy2)))) =
              (y * (gy1 * (fy0 * (fy1 * (fx2 * gy2))))) *
                ((ℓ : integralClosure ℤ ℂ) ^ ak - (ℓ : integralClosure ℤ ℂ) ^ aw)
              - (y * (gy2 * (fy0 * fy2))) * (fx1 * gy1 - gx1 * fy1)
              - (y * (((ℓ : integralClosure ℤ ℂ) ^ ak) * (gy1 * (fy0 * fy1)))) *
                (fx2 * gy2 - gx2 * fy2)
              + (lamf ℓ hℓ hℓS hℓM * (gy1 * (gy2 * (fy1 * fy2)))) * (fx0 * y - x' * fy0) := by
            linear_combination (fy0 * (fy1 * fy2)) * hx𝕫 + (y * (gy1 * gy2)) * hf𝕫
          have hUmem : (x - lamf ℓ hℓ hℓS hℓM * x') * (gy1 * (gy2 * (fy0 * (fy1 * fy2)))) ∈ 𝔪' := by
            rw [hfin]
            exact Ideal.add_mem _ (Ideal.sub_mem _ (Ideal.sub_mem _
              (Ideal.mul_mem_left _ _ hm1) (Ideal.mul_mem_left _ _ hm2))
              (Ideal.mul_mem_left _ _ hm3)) (Ideal.mul_mem_left _ _ hm4)
          rcases hprime𝔪'.mul_mem_iff_mem_or_mem.mp hUmem with h | h
          · exact h
          · exact absurd h (hnm hgy1 (hnm hgy2 (hnm hfy0 (hnm hfy1 hfy2))))
        ·
          have hx𝕫 : x * gy1 = y * gx1 := by
            apply Subtype.coe_injective
            push_cast
            rw [hx]
            simp only [if_neg hdvd, mul_zero, add_zero]
            rw [hg1]
            ring
          have hf𝕫 : fx1 * fy0 - lamf ℓ hℓ hℓS hℓM * (fx0 * fy1) = 0 := by
            apply Subtype.coe_injective
            push_cast
            simp only [if_neg hdvd, mul_zero, add_zero] at heigf
            rw [hf0, hf1]
            linear_combination ((fy0 : integralClosure ℤ ℂ) : ℂ) *
              ((fy1 : integralClosure ℤ ℂ) : ℂ) * heigf
          have hm2 := hGF (ℓ * n) fx1 fy1 gx1 gy1 hfy1 hgy1 hf1 hg1
          have hm4 := hGF n fx0 fy0 x' y hfy0 hy hf0 hx'
          have hfin : (x - lamf ℓ hℓ hℓS hℓM * x') * (gy1 * (fy0 * fy1)) =
              - (y * fy0) * (fx1 * gy1 - gx1 * fy1)
              + (lamf ℓ hℓ hℓS hℓM * (gy1 * fy1)) * (fx0 * y - x' * fy0) := by
            linear_combination (fy0 * fy1) * hx𝕫 + (y * gy1) * hf𝕫
          have hUmem : (x - lamf ℓ hℓ hℓS hℓM * x') * (gy1 * (fy0 * fy1)) ∈ 𝔪' := by
            rw [hfin]
            exact Ideal.add_mem _ (Ideal.mul_mem_left _ (-(y * fy0)) hm2)
              (Ideal.mul_mem_left _ _ hm4)
          rcases hprime𝔪'.mul_mem_iff_mem_or_mem.mp hUmem with h | h
          · exact h
          · exact absurd h (hnm hgy1 (hnm hfy0 hfy1))
    obtain ⟨hGne, heig⟩ := glueA_entry
    have hc1 : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → ¬ ℓ ∣ L / p ^ (L.factorization p) → ¬ ℓ ∣ 1 :=
      fun ℓ hℓ _ _ hd => hℓ.one_lt.ne' (Nat.dvd_one.mp hd)
    have hGint1 : ∀ n : ℕ, n.Coprime 1 → ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪' ∧
        (x : ℂ) = y * ModularFormClass.qCoeff G n := fun n _ => hGint n
    obtain ⟨𝔪ₖ, h1, h2, h3⟩ := CuspForm.heckeAlgebra.exists_isMaximal_heckeT_sub_mem_of_qCoeff_congr p (L / p ^ (L.factorization p)) k S₀ hS₀N' 1 hc1
      𝔪' h𝔪' hp𝔪' G hGint1 hGne (fun ℓ => W.apOfModel ℓ) W.IsGoodPrimeFor heig
    exact ⟨k, hk2, 𝔪ₖ, h1, h2, fun ℓ hℓ hℓS hℓN hQ => h3 ℓ hℓ hℓS hℓN hQ⟩
  ·
    obtain ⟨G_B, hG_B⟩ := CuspForm.exists_coe_eq_add_smul_heckeU_alSlash p hp' A
      (2 * (p : ℤ) ^ (L.factorization p - 1)) (CuspForm.atkinLehnerLin A _ f)
    have hG_Bne : G_B ≠ 0 := by
      intro h0
      apply hTrW
      have hcoe := hG_B
      rw [h0] at hcoe
      simpa [CuspForm.coe_atkinLehnerLin_apply] using hcoe.symm
    set sP : Finset ℕ := hS₀fin.toFinset.filter Nat.Prime with hsP
    set c : ℕ := sP.prod id with hcdef
    have hcpos : 0 < c := Finset.prod_pos fun ℓ hℓ => (Finset.mem_filter.mp hℓ).2.pos
    have hc_dvd : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∈ S₀ → ℓ ∣ c := fun ℓ hℓ hℓS =>
      Finset.dvd_prod_of_mem id (Finset.mem_filter.mpr ⟨hS₀fin.mem_toFinset.mpr hℓS, hℓ⟩)
    have hc_not : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → ¬ ℓ ∣ c := by
      intro ℓ hℓ hℓS hdiv
      obtain ⟨q, hq, hℓq⟩ := (Nat.Prime.prime hℓ).exists_mem_finset_dvd hdiv
      obtain ⟨hqS₀, hqP⟩ := Finset.mem_filter.mp hq
      exact hℓS (((Nat.prime_dvd_prime_iff_eq hℓ hqP).mp hℓq) ▸ hS₀fin.mem_toFinset.mp hqS₀)
    have hpc : p ∣ c := hc_dvd p hp' hS₀p
    have hMof : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ L / p ^ (L.factorization p) → ¬ ℓ ∣ c →
        ℓ ∉ S₀ ∧ ¬ ℓ ∣ p * (L / p ^ (L.factorization p)) := by
      intro ℓ hℓ hℓN hℓc
      refine ⟨fun h => hℓc (hc_dvd ℓ hℓ h), fun hd => ?_⟩
      rcases (Nat.Prime.dvd_mul hℓ).mp hd with h | h
      · exact hℓc (((Nat.prime_dvd_prime_iff_eq hℓ hp').mp h) ▸ hpc)
      · exact hℓN h
    let lamc : ℕ → ℂ := fun ℓ =>
      if h : ℓ.Prime ∧ ¬ ℓ ∣ L / p ^ (L.factorization p) ∧ ¬ ℓ ∣ c
      then (lamf ℓ h.1 (hMof ℓ h.1 h.2.1 h.2.2).1 (hMof ℓ h.1 h.2.1 h.2.2).2 : ℂ) else 0
    have hG_Beig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ L / p ^ (L.factorization p)),
        ¬ ℓ ∣ c → heckeTLin (2 * (p : ℤ) ^ (L.factorization p - 1)) hℓ hℓN G_B = lamc ℓ • G_B := by
      intro ℓ hℓ hℓN hℓc
      have hℓM : ¬ ℓ ∣ p * (L / p ^ (L.factorization p)) := (hMof ℓ hℓ hℓN hℓc).2
      have hℓS₀ : ℓ ∉ S₀ := (hMof ℓ hℓ hℓN hℓc).1
      have hlamc : lamc ℓ = (lamf ℓ hℓ hℓS₀ hℓM : ℂ) := by
        simp only [lamc, dif_pos (And.intro hℓ (And.intro hℓN hℓc))]
      have hG_Bcoe : ⇑G_B = ModularForm.alSlash A (2 * (p : ℤ) ^ (L.factorization p - 1)) ⇑f +
          (p : ℂ) ^ (2 - 2 * (p : ℤ) ^ (L.factorization p - 1)) •
            ModularForm.heckeU (2 * (p : ℤ) ^ (L.factorization p - 1)) p
              (ModularForm.alSlash A (2 * (p : ℤ) ^ (L.factorization p - 1))
                (ModularForm.alSlash A (2 * (p : ℤ) ^ (L.factorization p - 1)) ⇑f)) := by
        rw [hG_B, CuspForm.coe_atkinLehnerLin_apply]
      have htrc := ModularForm.heckeT_trace_alSlash_of_eigen p A
        (2 * (p : ℤ) ^ (L.factorization p - 1)) hℓ hℓM f
        (lamf ℓ hℓ hℓS₀ hℓM : ℂ) (hlamfeq ℓ hℓ hℓS₀ hℓM)
      rw [← hG_Bcoe] at htrc
      have hcoe : (⇑(heckeTLin (2 * (p : ℤ) ^ (L.factorization p - 1)) hℓ hℓN G_B) :
          UpperHalfPlane → ℂ) = ⇑(lamc ℓ • G_B) := by
        rw [CuspForm.coe_heckeTLin_apply, CuspForm.IsGLPos.coe_smul, hlamc]
        exact htrc
      exact DFunLike.coe_injective hcoe
    obtain ⟨h', hh'1, hh'eig, hh'coef⟩ :=
      CuspForm.exists_normalized_eigenvector (L / p ^ (L.factorization p))
        (2 * (p : ℤ) ^ (L.factorization p - 1)) c hcpos G_B hG_Bne lamc hG_Beig
    have hc_entry : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → ¬ ℓ ∣ L / p ^ (L.factorization p) →
        ¬ ℓ ∣ c * (L / p ^ (L.factorization p)) := fun ℓ hℓ hℓS hℓN hdiv =>
      ((Nat.Prime.dvd_mul hℓ).mp hdiv).elim (hc_not ℓ hℓ hℓS) hℓN
    have hone : (1 : integralClosure ℤ ℂ) ∉ 𝔪' := fun h1 =>
      h𝔪'.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
    have hh'ne : ∃ (n : ℕ) (x y : integralClosure ℤ ℂ),
        n.Coprime (c * (L / p ^ (L.factorization p))) ∧ y ∉ 𝔪' ∧
        (x : ℂ) = y * ModularFormClass.qCoeff h' n ∧ x ∉ 𝔪' :=
      ⟨1, 1, 1, Nat.coprime_one_left _, hone, by simp [hh'1], hone⟩
    have hh'int : ∀ n : ℕ, n.Coprime (c * (L / p ^ (L.factorization p))) →
        ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪' ∧ (x : ℂ) = y * ModularFormClass.qCoeff h' n := by
      intro n hn
      have hmem : ModularFormClass.qCoeff h' n ∈ (integralClosure ℤ ℂ : Subalgebra ℤ ℂ) := by
        refine Algebra.adjoin_le ?_ (hh'coef n hn)
        rintro z ⟨ℓ, hℓ, hℓcN, rfl⟩
        have hℓc : ¬ ℓ ∣ c := fun h => hℓcN (h.mul_right _)
        have hℓN : ¬ ℓ ∣ L / p ^ (L.factorization p) := fun h => hℓcN (h.mul_left _)
        show lamc ℓ ∈ _
        simp only [lamc, dif_pos (And.intro hℓ (And.intro hℓN hℓc))]
        exact SetLike.coe_mem _
      exact ⟨⟨_, hmem⟩, 1, hone, by simp⟩
    have hAh' : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 ⇑h') 0 :=
      ModularFormClass.analyticAt_cuspFunction_zero h' one_pos
        (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 _)
    have hh'heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀)
        (hℓN : ¬ ℓ ∣ L / p ^ (L.factorization p)),
        ∃ e : integralClosure ℤ ℂ,
          (W.IsGoodPrimeFor ℓ → e - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪') ∧
          ∀ (n : ℕ) (x x' y : integralClosure ℤ ℂ),
            n.Coprime (c * (L / p ^ (L.factorization p))) → y ∉ 𝔪' →
            (x : ℂ) = y * ModularFormClass.qCoeff
              (((heckeAlgebra.T hℓ hℓN hℓS : heckeAlgebra (L / p ^ (L.factorization p))
                    (2 * (p : ℤ) ^ (L.factorization p - 1)) S₀) :
                Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0
                  (L / p ^ (L.factorization p))) (2 * (p : ℤ) ^ (L.factorization p - 1)))) h') n →
            (x' : ℂ) = y * ModularFormClass.qCoeff h' n → x - e * x' ∈ 𝔪' := by
      intro ℓ hℓ hℓS hℓN
      have hℓc : ¬ ℓ ∣ c := hc_not ℓ hℓ hℓS
      have hℓM : ¬ ℓ ∣ p * (L / p ^ (L.factorization p)) := (hMof ℓ hℓ hℓN hℓc).2
      have hlamc : lamc ℓ = (lamf ℓ hℓ hℓS hℓM : ℂ) := by
        simp only [lamc, dif_pos (And.intro hℓ (And.intro hℓN hℓc))]
      refine ⟨lamf ℓ hℓ hℓS hℓM, fun _ => by simpa using hlamf ℓ hℓ hℓS hℓM, ?_⟩
      intro n x x' y _ _ hx hx'
      have hTcoeff : ModularFormClass.qCoeff
          (((heckeAlgebra.T hℓ hℓN hℓS :
              heckeAlgebra (L / p ^ (L.factorization p))
                (2 * (p : ℤ) ^ (L.factorization p - 1)) S₀) :
            Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0
              (L / p ^ (L.factorization p))) (2 * (p : ℤ) ^ (L.factorization p - 1)))) h') n =
          lamc ℓ * ModularFormClass.qCoeff h' n := by
        rw [heckeAlgebra.coe_T, hh'eig ℓ hℓ hℓN hℓc]
        show ModularFormClass.qCoeff (⇑((lamc ℓ) • h')) n = _
        unfold ModularFormClass.qCoeff
        rw [show (⇑((lamc ℓ) • h') : UpperHalfPlane → ℂ) = (lamc ℓ) • ⇑h' from rfl,
          UpperHalfPlane.qExpansion_smul hAh' (lamc ℓ)]
        simp
      rw [hTcoeff, hlamc, ← mul_assoc, mul_comm ((y : ℂ)) _, mul_assoc, ← hx'] at hx
      have hxeq : (x : ℂ) = ((lamf ℓ hℓ hℓS hℓM * x' : integralClosure ℤ ℂ) : ℂ) := by
        push_cast; rw [hx]
      have hx𝕫 : x = lamf ℓ hℓ hℓS hℓM * x' := Subtype.coe_injective hxeq
      simp [hx𝕫]
    obtain ⟨𝔪ₖ, h1, h2, h3⟩ := CuspForm.heckeAlgebra.exists_isMaximal_heckeT_sub_mem_of_qCoeff_congr p (L / p ^ (L.factorization p))
      (2 * (p : ℤ) ^ (L.factorization p - 1)) S₀ hS₀N'
      (c * (L / p ^ (L.factorization p))) hc_entry 𝔪' h𝔪' hp𝔪' h'
      hh'int hh'ne (fun ℓ => W.apOfModel ℓ) W.IsGoodPrimeFor hh'heig
    exact ⟨2 * (p : ℤ) ^ (L.factorization p - 1), hw2, 𝔪ₖ, h1, h2,
      fun ℓ hℓ hℓS hℓN hQ => h3 ℓ hℓ hℓS hℓN hQ⟩

end S_WeierstrassCurve_exists_ideal_heckeAlgebra_ordCompl_of_isNewform_sq_dvd
end P2MW
export P2MW.S_WeierstrassCurve_exists_ideal_heckeAlgebra_ordCompl_of_isNewform_sq_dvd (solution)
