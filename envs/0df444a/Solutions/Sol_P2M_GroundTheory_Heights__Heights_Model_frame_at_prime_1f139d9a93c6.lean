-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_frame_at_prime_1f139d9a93c6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:33.409386+00:00
-- url     : https://prove2.me/submissions/48d08613-b8fa-497f-a066-16a068d97abd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueFrame
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueFrameP
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_repr_of_eq_sum_364fe3530fcd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_chartBundle_exists_gens_5a8ab43d7914
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_mul_mem_chartRing_int_66c778c3b43b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_mul_mem_chartRing_int_fin_b3379bd7b808
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_prime_pow_smul_mem_5244231e3dc8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_uniform_mul_df136692fe23
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_glueLat_stable_271b11ede81b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_intCast_mem_chartRing_8f356cccfc37
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_intCast_not_mem_of_not_dvd_821321de1520
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_intCast_subtype_163f87f566d3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_Bp_iff_bcee018890a1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_glueLat_7887799b35f2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_ideal_of_sum_10ad4e89fd6e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_of_prime_pow_mul_mem_59b855d6fd12
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_primeTo_af81357ada47
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_not_dvd_primeProdErase_f3d914f81af6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_primeProd_eq_mul_2dccd2fab054
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_smul_mem_of_chart_c43618aeade3


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω : Type} [Field Ω] [CharZero Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
  {E : Type} [AddCommGroup E] [Module Ω E] {S : Finset Nat.Primes}
  {o₀ : Type} [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
  {o : S → Type} [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
  [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
  [∀ p, Algebra (o p) Ω]
  {B₀ : ChartBundle o₀ x r E} {Bp : ∀ p, ChartBundle (o p) x r E}
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {i : τ} (hi : x i ≠ 0)
    (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i)) (Q : Ideal (chartRing ℤ x i))
    (hQ : Q.IsPrime) (p : S) (hpQ : ((((p : Nat.Primes) : ℕ) : ℤ) : (chartRing ℤ x i)) ∈ Q) :
    ∃ h : Ω, ∃ hh : h ∈ (chartRing ℤ x i), (⟨h, hh⟩ : (chartRing ℤ x i)) ∉ Q ∧
      IsFrameAt (chartRing ℤ x i) r (glueLat B₀ Bp i) h := by
  classical
  have hPp : Prime (((p : Nat.Primes) : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp (p : Nat.Primes).2
  have hnot : ∀ {s : ℤ}, ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ s → (s : (chartRing ℤ x i)) ∉ Q := fun hs =>
    intCast_not_mem_of_not_dvd hQ.ne_top (p : Nat.Primes).2 (by simpa using hpQ) hs
  obtain ⟨k, g, d, hg, hd, hsum, hb⟩ := (Bp p).frame i hi
  obtain ⟨t, ht, htg⟩ := exists_mul_mem_chartRing_int_fin x i (o p) (primeTo (p : Nat.Primes)) g hg
  obtain ⟨t', ht', htd⟩ := exists_mul_mem_chartRing_int_fin x i (o p) (primeTo (p : Nat.Primes)) d hd
  have hex : ∃ l, (⟨(t : Ω) * g l, htg l⟩ : (chartRing ℤ x i)) ∉ Q := by
    by_contra hall
    push Not at hall
    have hmem := mem_ideal_of_sum Q (fun l => (t' : Ω) * d l) (fun l => (t : Ω) * g l) htd htg hall
      (z := ((t' * t : ℤ) : Ω)) (intCast_mem (chartRing ℤ x i) _) (by
        have : ∑ l, (t' : Ω) * d l * ((t : Ω) * g l) = ((t' : Ω) * t) * ∑ l, d l * g l := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
        rw [this, hsum]; push_cast; ring)
    rw [intCast_subtype] at hmem
    exact hnot (mem_primeTo.1 (mul_mem ht' ht)) hmem
  obtain ⟨l, hl⟩ := hex
  have hγA : (t : Ω) * g l ∈ (chartRing ℤ x i) := htg l
  obtain ⟨b, hli, hsp, hiff⟩ := hb l

  have hγpow : ∀ (n : ℕ) {y : Ω}, g l ^ n * y ∈ chartRing (o p) x i →
      ((t : Ω) * g l) ^ n * y ∈ chartRing (o p) x i := fun n y hy => by
    rw [mul_pow, mul_assoc]; exact mul_mem (pow_mem (intCast_mem_chartRing x i _ _) _) hy
  have hsingle : ∀ q q' : Fin r, ∃ n : ℕ, g l ^ n * (Pi.single q (1 : Ω) : Fin r → Ω) q' ∈
      chartRing (o p) x i := fun q q' => ⟨0, by
    rw [pow_zero, one_mul]
    by_cases h : q' = q
    · subst h; simp only [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _⟩

  obtain ⟨σ₁, hσ₁, n₁, hC1⟩ : ∃ σ ∈ primeTo (p : Nat.Primes), ∃ n : ℕ, ∀ q, ∀ n' ≥ n,
      ((σ : Ω) * ((t : Ω) * g l) ^ n') • b q ∈ glueLat B₀ Bp i := by
    refine exists_uniform_mul _ (chartRing ℤ x i) (glueLat B₀ Bp i) (glueLat_stable i) hγA b fun q => ?_
    obtain ⟨n, hn⟩ := (hiff (b q)).2 ⟨Pi.single q 1, hsingle q, by simp [Pi.single_apply]⟩
    have hγn : ((t : Ω) * g l) ^ n • b q ∈ (Bp p).lat i := by
      rw [mul_pow, mul_smul]
      exact smul_mem_of_chart (Bp p) (pow_mem (intCast_mem_chartRing x i _ _) _) hn
    obtain ⟨s, hs, hsm⟩ := (mem_Bp_iff hSR p _).1 hγn
    refine ⟨s, mem_primeTo.2 hs, n, ?_⟩
    rw [← Int.cast_smul_eq_zsmul Ω, smul_smul] at hsm
    exact hsm
  let bb := Module.Basis.mk hli hsp.ge
  have hbb : ∀ q, bb q = b q := fun q => by simp [bb, Module.Basis.coe_mk]

  obtain ⟨K₀, Gn, hG, hGspan⟩ := chartBundle_exists_gens B₀ hi

  obtain ⟨σ₂, hσ₂, n₂, hC2⟩ : ∃ σ ∈ primeTo (p : Nat.Primes), ∃ n : ℕ,
      ∀ jq : (Fin K₀ × Fin r) × Fin r, ∀ n' ≥ n,
        ((σ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n') • bb.repr (Gn jq.1) jq.2 ∈ (chartRing ℤ x i).toSubring.toAddSubgroup := by
    refine exists_uniform_mul (E := Ω) _ (chartRing ℤ x i) (chartRing ℤ x i).toSubring.toAddSubgroup
      (fun a ha e he => show a * e ∈ (chartRing ℤ x i) from mul_mem ha he)
      (mul_mem (intCast_mem (chartRing ℤ x i) _) hγA) _ fun jq => ?_
    obtain ⟨v, hv⟩ := exists_prime_pow_smul_mem p (hSR p) (hG jq.1)
    obtain ⟨a, ha, hae⟩ := (hiff (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ v • Gn jq.1)).1 ⟨0, by rw [pow_zero, one_smul]; exact hv⟩
    have hq : ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ v * bb.repr (Gn jq.1) jq.2 = a jq.2 := by
      have := repr_of_eq_sum hli hsp hae jq.2
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul] at this
      exact this
    obtain ⟨n, hn⟩ := ha jq.2
    obtain ⟨s, hs, hsA⟩ := exists_mul_mem_chartRing_int x i (o p) (primeTo (p : Nat.Primes)) (hγpow n hn)
    refine ⟨s, hs, v + n, ?_⟩
    show (s : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ (v + n) * bb.repr (Gn jq.1) jq.2 ∈ (chartRing ℤ x i)
    have : (s : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ (v + n) * bb.repr (Gn jq.1) jq.2 =
        (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ n * ((t : Ω) * g l) ^ v) * ((s : Ω) * (((t : Ω) * g l) ^ n * a jq.2)) := by
      rw [← hq]; ring
    rw [this]
    exact mul_mem (mul_mem (pow_mem (intCast_mem (chartRing ℤ x i) _) _) (pow_mem hγA _)) hsA
  have hσ : ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) := by
    rw [hPp.dvd_mul, hPp.dvd_mul]
    rintro ((h | h) | h)
    · exact mem_primeTo.1 hσ₁ h
    · exact mem_primeTo.1 hσ₂ h
    · exact not_dvd_primeProdErase _ h
  have hmPμ : ((primeProd S : ℤ) : Ω) = ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) := by
    rw [primeProd_eq_mul p.2, Int.cast_mul]
  have hhA : ((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) * ((t : Ω) * g l) ∈ (chartRing ℤ x i) :=
    mul_mem (intCast_mem (chartRing ℤ x i) _) hγA

  have hC3 : ∀ e ∈ glueLat B₀ Bp i, ∀ q, ∃ n : ℕ,
      (((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n * bb.repr e q ∈ (chartRing ℤ x i) := by
    intro e he q
    obtain ⟨he0, hep⟩ := (mem_glueLat B₀ Bp).1 he
    obtain ⟨a, ha, hae⟩ := (hiff e).1 ⟨0, by simpa using hep p⟩
    have hra : bb.repr e q = a q := repr_of_eq_sum hli hsp hae q
    obtain ⟨n, hn⟩ := ha q
    obtain ⟨se, hse, hseA⟩ := exists_mul_mem_chartRing_int x i (o p) (primeTo (p : Nat.Primes)) (hγpow n hn)
    obtain ⟨β, hβ, heβ⟩ := hGspan e he0
    obtain ⟨t₀, ht₀, ht₀β⟩ :=
      exists_mul_mem_chartRing_int_fin x i o₀ (Submonoid.powers (primeProd S)) β hβ
    obtain ⟨κ, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 ht₀
    have hrepr_e : bb.repr e q = ∑ j, β j * bb.repr (Gn j) q := by
      conv_lhs => rw [heβ]
      simp [map_sum, map_smul]
    have hii : (σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * (((primeProd S : ℤ) : Ω) ^ κ * bb.repr e q) ∈ (chartRing ℤ x i) := by
      rw [hrepr_e, Finset.mul_sum, Finset.mul_sum]
      refine sum_mem fun j _ => ?_
      have h1 : (σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * bb.repr (Gn j) q ∈ (chartRing ℤ x i) := hC2 (j, q) n₂ le_rfl
      have h2 := ht₀β j
      have : (σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * (((primeProd S : ℤ) : Ω) ^ κ * (β j * bb.repr (Gn j) q)) =
          ((((primeProd S) ^ κ : ℤ) : Ω) * β j) *
            ((σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * bb.repr (Gn j) q) := by
        rw [Int.cast_pow]; ring
      rw [this]
      exact mul_mem h2 h1
    have hc1 : ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ (n₂ + κ) *
        ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) ∈ (chartRing ℤ x i) := by
      have : ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ (n₂ + κ) * ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) =
          ((t : Ω) * g l) ^ n * ((σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * (((primeProd S : ℤ) : Ω) ^ κ * bb.repr e q)) := by
        rw [hmPμ]; ring
      rw [this]
      exact mul_mem (pow_mem hγA _) hii
    have hc2 : (se : Ω) * ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) ∈ (chartRing ℤ x i) := by
      have : (se : Ω) * ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) =
          ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ n₂) * ((se : Ω) * (((t : Ω) * g l) ^ n * a q)) := by
        rw [hra]; ring
      rw [this]
      exact mul_mem (mul_mem (mul_mem (intCast_mem (chartRing ℤ x i) _) (pow_mem (intCast_mem (chartRing ℤ x i) _) _))
        (pow_mem hγA _)) hseA
    have hc := mem_of_prime_pow_mul_mem (A := (chartRing ℤ x i)) (p : Nat.Primes).2 (mem_primeTo.1 hse)
      (n₂ + κ) hc1 hc2
    refine ⟨κ + n + n₂ + 1, ?_⟩
    have : (((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) * ((t : Ω) * g l)) ^ (κ + n + n₂ + 1) *
        bb.repr e q = ((σ₁ : Ω) ^ (κ + n + n₂ + 1) * (σ₂ : Ω) ^ (κ + n + n₂) *
          ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ (n + n₂ + 1) * ((t : Ω) * g l) ^ (κ + 1)) *
          ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) := by
      rw [Int.cast_mul, Int.cast_mul]; ring
    rw [this]
    exact mul_mem (mul_mem (mul_mem (mul_mem (pow_mem (intCast_mem (chartRing ℤ x i) _) _)
      (pow_mem (intCast_mem (chartRing ℤ x i) _) _)) (pow_mem (intCast_mem (chartRing ℤ x i) _) _)) (pow_mem hγA _)) hc

  have hhQ : (⟨_, hhA⟩ : (chartRing ℤ x i)) ∉ Q := by
    have : (⟨_, hhA⟩ : (chartRing ℤ x i)) =
        ((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : (chartRing ℤ x i)) * ⟨_, hγA⟩ :=
      Subtype.ext (by simp)
    rw [this]
    intro hmem
    rcases hQ.mem_or_mem hmem with h | h
    · exact hnot hσ h
    · exact hl h
  refine ⟨_, hhA, hhQ, b, hli, hsp, fun e => ⟨fun ⟨n, hn⟩ => ?_, fun ⟨a, ha, hae⟩ => ?_⟩⟩
  · refine ⟨fun q => bb.repr e q, fun q => ?_, ?_⟩
    · obtain ⟨n', hn'⟩ := hC3 _ hn q
      refine ⟨n' + n, ?_⟩
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, ← mul_assoc, ← pow_add] at hn'
      exact hn'
    · conv_lhs => rw [← bb.sum_repr e]
      simp only [hbb]
  · choose nq hnq using ha
    refine ⟨Finset.univ.sup nq + (n₁ + 1), ?_⟩
    rw [hae, Finset.smul_sum]
    refine sum_mem fun q _ => ?_
    set h := ((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) * ((t : Ω) * g l) with hh
    have hbq : h ^ (n₁ + 1) • b q ∈ glueLat B₀ Bp i := by
      have : h ^ (n₁ + 1) = ((σ₁ : Ω) ^ n₁ * ((σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ (n₁ + 1) *
          ((t : Ω) * g l)) * ((σ₁ : Ω) * ((t : Ω) * g l) ^ n₁) := by
        rw [hh]; push_cast; ring
      rw [this, mul_smul]
      exact glueLat_stable i _ (mul_mem (mul_mem (pow_mem (intCast_mem (chartRing ℤ x i) _) _)
        (pow_mem (intCast_mem (chartRing ℤ x i) _) _)) hγA) _ (hC1 q n₁ le_rfl)
    have haq : h ^ (Finset.univ.sup nq) * a q ∈ (chartRing ℤ x i) := by
      rw [← pow_sub_mul_pow h (Finset.le_sup (f := nq) (Finset.mem_univ q)), mul_assoc]
      exact mul_mem (pow_mem hhA _) (hnq q)
    have : h ^ (Finset.univ.sup nq + (n₁ + 1)) • (a q • b q) =
        (h ^ (Finset.univ.sup nq) * a q) • (h ^ (n₁ + 1) • b q) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [this]
    exact glueLat_stable i _ haq _ hbq
end GroundTheory.Heights₂.Heights.Model
