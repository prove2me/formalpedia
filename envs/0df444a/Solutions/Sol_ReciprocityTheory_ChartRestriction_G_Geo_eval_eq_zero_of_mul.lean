-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.eval_eq_zero_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:05:22.313844+00:00
-- url     : https://prove2.me/submissions/7223e592-1440-4567-b8f3-a565c1b7fa4f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeO
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeQ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mcPts_eq_pC


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (hM : PCMinContractStatement) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ} (hP : IsArithVar P (e + 1)) {u : MRing ι}
    (hu : u ∉ P) {H : MRingOver ℂ ι}
    (h : ∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) u) * eval z H = 0) :
    ∀ z ∈ mcPts P, eval z H = 0 := by
  classical
  have hPp : P.IsPrime := hP.2.1.1
  choose i hi using hP.2.1.2.2
  set m : MRing ι := ∏ k, X ⟨k, i k⟩ with hmdef
  have hm : m ∉ P := fun h' => by
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hPp)).mp h'
    exact hi k hk
  have hv : u * m ∉ P := fun h' => (hPp.mem_or_mem h').elim hu hm
  have hvan : map (Int.castRingHom ℂ) (u * m) * H ∈ (pC P).radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
      MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    change eval x _ = 0
    rw [MvPolynomial.mem_zeroLocus_iff] at hx
    by_cases hb : ∀ k, x ⟨k, i k⟩ ≠ 0
    · have hxm : x ∈ mcPts P := by
        rw [mcPts_eq_pC]
        exact ⟨fun k => ⟨i k, hb k⟩, fun f hf => hx f hf⟩
      rw [map_mul, map_mul, map_mul, mul_right_comm, h x hxm, zero_mul]
    · push Not at hb
      obtain ⟨k, hk⟩ := hb
      have : eval x (map (Int.castRingHom ℂ) m) = 0 := by
        rw [hmdef, map_prod, map_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])
      rw [map_mul, map_mul, map_mul, this, mul_zero, zero_mul]
  have hHrad : H ∈ (pC P).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    refine Submodule.mem_sInf.mpr fun Q hQ => ?_
    have hQp : Ideal.IsPrime Q := hQ.1.1
    have hle : (pC P).radical ≤ Q := (Ideal.IsPrime.radical_le_iff hQp).mpr hQ.1.2
    have hvQ : map (Int.castRingHom ℂ) (u * m) ∉ Q := fun h' => by
      apply hv
      rw [← hM K ι P e hP Q hQ]
      exact h'
    exact (hQp.mem_or_mem (hle hvan)).resolve_left hvQ
  intro z hz
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
    MvPolynomial.mem_vanishingIdeal_iff] at hHrad
  have := hHrad z (by
    rw [MvPolynomial.mem_zeroLocus_iff]
    intro p hp
    exact (by rw [mcPts_eq_pC] at hz; exact hz.2 p hp))
  exact this
end ReciprocityTheory.ChartRestriction.G.Geo
