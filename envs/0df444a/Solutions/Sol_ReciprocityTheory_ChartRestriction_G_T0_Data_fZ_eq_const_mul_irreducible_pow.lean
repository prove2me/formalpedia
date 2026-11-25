-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.fZ_eq_const_mul_irreducible_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:42:47.257152+00:00
-- url     : https://prove2.me/submissions/73e5f5ba-1d63-4a66-89df-6e636e8074c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockSphereProbIsProbabilityMeasure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZEqConstMulIrreduciblePow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_relation_ker_le_valuation_prime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_ker_relation_map_ne_bot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_fZ_factor_positive_places
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_height_one_prime_eq_span_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_height_const_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c)
    (hpos : 0 < ReciprocityTheory.MultiplicativeHeights.h0 F) :
    ∃ (F0 : KTp K d.D d.N) (κ : K) (m : ℕ), κ ≠ 0 ∧ 1 ≤ m ∧ Irreducible F0 ∧
      F = MvPolynomial.C κ * F0 ^ m ∧
      ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q := by
  obtain ⟨κ, T, e, hκ, hT, hFe, hpl⟩ := fZ_factor_positive_places (d := d) hd h c F hF
  set I : Ideal (KTp K d.D d.N) := RingHom.ker (d.relationEliminateColumn c) with hIdef
  have hIp : I.IsPrime := RingHom.ker_isPrime _
  have hIb : I ≠ ⊥ := ker_relation_map_ne_bot (d := d) hd c
  obtain ⟨q, hqI, hq⟩ := hIp.exists_mem_prime_of_ne_bot hIb
  have hprime : ∀ p ∈ d.HtOne, q ∈ p → Prime (d.gen p) := by
    intro p hp1 hqp
    have hsp := height_one_prime_eq_span_gen (d := d) p hp1
    have hgq : d.gen p ∣ q := by
      rw [hsp] at hqp
      exact Ideal.mem_span_singleton.1 hqp
    have hg0 : d.gen p ≠ 0 := by
      intro h0
      rw [h0] at hgq
      exact hq.ne_zero (zero_dvd_iff.1 hgq)
    have hpr : (Ideal.span {d.gen p}).IsPrime := by
      rw [← hsp]
      exact hp1.1
    exact (Ideal.span_singleton_prime hg0).1 hpr
  have hcont : ∀ p ∈ T, 0 < e p → p = I := by
    intro p hpT hep
    obtain ⟨w, hw, htriv, hpos'⟩ := hpl p hpT hep
    have hIle : I ≤ p := fun Q hQ => relation_ker_le_valuation_prime (d := d) hd c p w hw htriv hpos' Q (RingHom.mem_ker.1 hQ)
    have hp1 : p ∈ d.HtOne := hT hpT
    have hsp := height_one_prime_eq_span_gen (d := d) p hp1
    have hgp := hprime p hp1 (hIle hqI)
    have hgq : d.gen p ∣ q := by
      have hqp := hIle hqI
      rw [hsp] at hqp
      exact Ideal.mem_span_singleton.1 hqp
    obtain ⟨v, hv⟩ := hgp.irreducible.dvd_symm hq.irreducible hgq
    have hgI : d.gen p ∈ I := by
      rw [hv]
      exact I.mul_mem_right v hqI
    refine le_antisymm ?_ hIle
    rw [hsp]
    exact (Ideal.span_singleton_le_iff_mem I).2 hgI
  by_cases hIT : I ∈ T ∧ 0 < e I
  · obtain ⟨hIT, heI⟩ := hIT
    have hI1 : I ∈ d.HtOne := hT hIT
    have hsp := height_one_prime_eq_span_gen (d := d) I hI1
    refine ⟨d.gen I, κ, e I, hκ, heI, (hprime I hI1 hqI).irreducible, ?_, ?_⟩
    · rw [hFe, Finset.prod_eq_single I (fun b hb hbI => ?_) (fun hn => absurd hIT hn)]
      rcases Nat.eq_zero_or_pos (e b) with h0 | h0
      · rw [h0, pow_zero]
      · exact absurd (hcont b hb h0) hbI
    · intro Q
      rw [← Ideal.mem_span_singleton, ← hsp]
      exact RingHom.mem_ker.symm
  · exfalso
    have hone : ∏ p ∈ T, d.gen p ^ e p = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      rcases Nat.eq_zero_or_pos (e p) with h0 | h0
      · rw [h0, pow_zero]
      · have hpI := hcont p hp h0
        subst hpI
        exact absurd ⟨hp, h0⟩ hIT
    rw [hFe, hone, mul_one, height_const_eq_zero (Nat.succ_pos _)] at hpos
    exact lt_irrefl _ hpos
end ReciprocityTheory.ChartRestriction.G.T0.Data
