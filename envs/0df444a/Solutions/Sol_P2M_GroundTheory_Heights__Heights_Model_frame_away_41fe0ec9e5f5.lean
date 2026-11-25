-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_frame_away_41fe0ec9e5f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:34.40338+00:00
-- url     : https://prove2.me/submissions/4fb93e28-0a38-4704-b95f-4b3aebea9b94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueFrame
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_ideal_of_sum_10ad4e89fd6e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_intCast_subtype_163f87f566d3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_mul_mem_chartRing_int_66c778c3b43b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_mul_mem_chartRing_int_fin_b3379bd7b808
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_pow_smul_mem_iff_of_loc_5644dbfd8277
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_glueLat_stable_271b11ede81b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_inv_prod_mem_chartRing_6138e0eacf84
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_B__iff_9151688a4893
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_chartRing_of_int_e441a7136a3a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_glueLat_7887799b35f2
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
variable {Ω : Type} [Field Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
  {E : Type} [AddCommGroup E] [Module Ω E] {S : Finset Nat.Primes}
  {o₀ : Type} [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
  {o : S → Type} [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
  [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
  [∀ p, Algebra (o p) Ω]
  {B₀ : ChartBundle o₀ x r E} {Bp : ∀ p, ChartBundle (o p) x r E}
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {i : τ} (hi : x i ≠ 0)
    (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i)) (Q : Ideal (chartRing ℤ x i))
    (hQ : Q.IsPrime) (hmQ : ((primeProd S : ℤ) : chartRing ℤ x i) ∉ Q) :
    ∃ h : Ω, ∃ hh : h ∈ chartRing ℤ x i, (⟨h, hh⟩ : chartRing ℤ x i) ∉ Q ∧
      IsFrameAt (chartRing ℤ x i) r (glueLat B₀ Bp i) h := by
  classical
  set m : ℤ := primeProd S with hm
  obtain ⟨hm0, hminv⟩ := inv_prod_mem_chartRing x o₀ (S := S) i
  obtain ⟨k, f, c, hf, hc, hsum, hb⟩ := B₀.frame i hi
  obtain ⟨t, ht, htf⟩ := exists_mul_mem_chartRing_int_fin x i o₀ (Submonoid.powers m) f hf
  obtain ⟨t', ht', htc⟩ := exists_mul_mem_chartRing_int_fin x i o₀ (Submonoid.powers m) c hc
  obtain ⟨J, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 ht
  obtain ⟨J', rfl⟩ := (Submonoid.mem_powers_iff _ _).1 ht'
  have hmA : (m : Ω) ∈ chartRing ℤ x i := intCast_mem (chartRing ℤ x i) m
  have hJ : ∀ l, (m : Ω) ^ J * f l ∈ chartRing ℤ x i := fun l => by simpa using htf l
  have hφ : ∀ l, (m : Ω) ^ (J + 1) * f l ∈ chartRing ℤ x i := fun l => by
    have : (m : Ω) ^ (J + 1) * f l = (m : Ω) * ((m : Ω) ^ J * f l) := by ring
    rw [this]; exact mul_mem hmA (hJ l)
  have hex : ∃ l, (⟨(m : Ω) ^ (J + 1) * f l, hφ l⟩ : chartRing ℤ x i) ∉ Q := by
    by_contra hall
    push Not at hall
    have hmem := mem_ideal_of_sum Q (fun l => ((m ^ J' : ℤ) : Ω) * c l)
      (fun l => (m : Ω) ^ (J + 1) * f l) htc hφ hall (z := ((m ^ (J + 1 + J') : ℤ) : Ω))
      (intCast_mem (chartRing ℤ x i) _) (by
        have : ∑ l, ((m ^ J' : ℤ) : Ω) * c l * ((m : Ω) ^ (J + 1) * f l) =
            ((m : Ω) ^ J' * (m : Ω) ^ (J + 1)) * ∑ l, c l * f l := by
          rw [Finset.mul_sum]; push_cast; exact Finset.sum_congr rfl fun l _ => by ring
        rw [this, hsum]; push_cast; ring)
    rw [intCast_subtype] at hmem
    push_cast at hmem
    exact hmQ (hQ.mem_of_pow_mem _ hmem)
  obtain ⟨l, hl⟩ := hex
  obtain ⟨b, hli, hsp, hiff⟩ := hb l
  refine ⟨_, hφ l, hl, b, hli, hsp, fun e => ?_⟩
  have hYX : ∀ v ∈ B₀.lat i, ∃ k : ℕ, (m : Ω) ^ k • v ∈ glueLat B₀ Bp i := fun v hv => by
    obtain ⟨n, hn⟩ := (mem_B₀_iff hSR v).1 hv
    rw [← Int.cast_smul_eq_zsmul Ω, Int.cast_pow] at hn
    exact ⟨n, hn⟩
  rw [exists_pow_smul_mem_iff_of_loc (chartRing ℤ x i) (glueLat B₀ Bp i) (B₀.lat i) J hm0 hmA (hJ l)
    (glueLat_stable i) (fun e he => ((mem_glueLat B₀ Bp).1 he).1)
    (fun e he => smul_mem_of_chart B₀ hminv he) hYX e, hiff e]
  refine exists_congr fun a => and_congr (forall_congr' fun q => ?_) Iff.rfl
  have key := exists_pow_smul_mem_iff_of_loc (E := Ω) (chartRing ℤ x i) (chartRing ℤ x i).toSubring.toAddSubgroup
    (chartRing o₀ x i).toSubring.toAddSubgroup J hm0 hmA (hJ l)
    (fun a ha e he => show a * e ∈ chartRing ℤ x i from mul_mem ha he) (fun y hy => mem_chartRing_of_int x i o₀ hy)
    (fun y hy => show _ * y ∈ chartRing o₀ x i from mul_mem hminv hy)
    (fun y hy => by
      obtain ⟨t, ht, hty⟩ := exists_mul_mem_chartRing_int x i o₀ (Submonoid.powers m) hy
      obtain ⟨K, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 ht
      exact ⟨K, by simpa using hty⟩) (a q)
  simpa [smul_eq_mul] using key.symm
end GroundTheory.Heights₂.Heights.Model
