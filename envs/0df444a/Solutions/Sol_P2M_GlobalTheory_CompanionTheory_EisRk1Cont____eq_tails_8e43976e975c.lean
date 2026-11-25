-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_EisRk1Cont____eq_tails_8e43976e975c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:50:23.769246+00:00
-- url     : https://prove2.me/submissions/b544c34a-f1f4-4355-94b0-f9a24dc1730a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousSetIntegralIoiOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisRk1Cont
namespace GlobalTheory.CompanionTheory.EisRk1Cont
theorem _root_.solution (P : WeakFEPair ℂ) (s : ℂ) :
    P.Λ₀ s = (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (s - 1) * (P.f x - P.f₀)) +
      P.ε * ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ ((P.k : ℂ) - s - 1) * (P.g x - P.g₀) := by
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℂ, G = fun t => P.f t - (P.ε * ((t ^ (-P.k) : ℝ) : ℂ)) • P.g₀ :=
    ⟨_, rfl⟩
  have htop : P.f_modif =O[atTop] fun x : ℝ => x ^ (-(s.re + 1)) := by
    simpa using P.hf_modif_top (-(s.re + 1))
  have hbot : P.f_modif =O[𝓝[>] 0] fun x : ℝ => x ^ (-(s.re - 1)) := by
    refine (P.hf_zero (-(s.re - 1))).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with t ht
    have ht' : t ∉ Ioi (1 : ℝ) := fun h => lt_irrefl _ (ht.2.trans h)
    simp only [WeakFEPair.f_modif, Pi.add_apply, Set.indicator_of_notMem ht',
      Set.indicator_of_mem ht, zero_add]
  have hconv : MellinConvergent P.f_modif s :=
    mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1) P.hf_modif_int htop
      (by linarith) hbot (by linarith)
  have hint : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • P.f_modif t) (Ioi 0) := hconv
  have hsplit : P.Λ₀ s = (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • P.f_modif t) +
      ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • P.f_modif t := by
    rw [WeakFEPair.Λ₀, mellin, ← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
    exact setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint.mono_set Set.Ioc_subset_Ioi_self)
      (hint.mono_set (Set.Ioi_subset_Ioi zero_le_one))
  have hA : ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • P.f_modif t =
      ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (s - 1) * (P.f x - P.f₀) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : t ∉ Ioo (0 : ℝ) 1 := fun h => lt_irrefl _ (h.2.trans ht)
    simp only [WeakFEPair.f_modif, Pi.add_apply, Set.indicator_of_mem ht,
      Set.indicator_of_notMem ht', add_zero, smul_eq_mul]
  have hfm : ∀ t ∈ Ioo (0 : ℝ) 1, P.f_modif t = G t := fun t ht => by
    have ht' : t ∉ Ioi (1 : ℝ) := fun h => lt_irrefl _ (ht.2.trans h)
    rw [hG]
    simp only [WeakFEPair.f_modif, Pi.add_apply, Set.indicator_of_notMem ht',
      Set.indicator_of_mem ht, zero_add]
  have hB : ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • P.f_modif t =
      P.ε * ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ ((P.k : ℂ) - s - 1) * (P.g x - P.g₀) := by
    calc ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • P.f_modif t
        = ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • P.f_modif t := integral_Ioc_eq_integral_Ioo
      _ = ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • G t :=
          setIntegral_congr_fun measurableSet_Ioo fun t ht => by rw [hfm t ht]
      _ = ∫ t in Ioi (0 : ℝ) ∩ Ioo 0 1, (t : ℂ) ^ (s - 1) • G t := by
          rw [Set.inter_eq_right.mpr Set.Ioo_subset_Ioi_self]
      _ = ∫ t in Ioi (0 : ℝ), Set.indicator (Ioo 0 1) (fun t : ℝ => (t : ℂ) ^ (s - 1) • G t) t :=
          (setIntegral_indicator measurableSet_Ioo).symm
      _ = mellin (Set.indicator (Ioo 0 1) G) s := by
          rw [mellin]; congr 1; funext t
          by_cases ht : t ∈ Ioo (0 : ℝ) 1
          · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
          · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
      _ = mellin (fun u : ℝ => Set.indicator (Ioo 0 1) G u⁻¹) (-s) := by
          rw [← mellin_comp_inv]; simp only [inv_inv]
      _ = ∫ u in Ioi (0 : ℝ), Set.indicator (Ioi 1)
            (fun x : ℝ => P.ε * ((x : ℂ) ^ ((P.k : ℂ) - s - 1) * (P.g x - P.g₀))) u := by
          rw [mellin]
          refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
          have hu0 : (0 : ℝ) < u := hu
          rcases le_or_gt u 1 with hu1 | hu1
          · have h1 : u⁻¹ ∉ Ioo (0 : ℝ) 1 := fun h =>
              (not_lt.mpr ((one_le_inv₀ hu0).mpr hu1)) h.2
            have h2 : u ∉ Ioi (1 : ℝ) := fun h => (not_lt.mpr hu1) h
            rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, smul_zero]
          · have h1 : u⁻¹ ∈ Ioo (0 : ℝ) 1 := ⟨inv_pos.mpr hu0, inv_lt_one_of_one_lt₀ hu1⟩
            have h2 : u ∈ Ioi (1 : ℝ) := hu1
            have hfe : P.f u⁻¹ = (P.ε * ((u ^ P.k : ℝ) : ℂ)) • P.g u := by
              rw [← one_div]; exact P.h_feq u hu0
            have hpow : u⁻¹ ^ (-P.k) = u ^ P.k := by
              rw [Real.inv_rpow hu0.le, Real.rpow_neg hu0.le, inv_inv]
            rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, hG]
            simp only [hfe, hpow, smul_eq_mul]
            rw [Complex.ofReal_cpow hu0.le, show (P.k : ℂ) - s - 1 = (P.k : ℂ) + (-s - 1) by ring,
              Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu0.ne')]
            ring
      _ = ∫ u in Ioi (0 : ℝ) ∩ Ioi 1, P.ε * ((u : ℂ) ^ ((P.k : ℂ) - s - 1) * (P.g u - P.g₀)) :=
          setIntegral_indicator measurableSet_Ioi
      _ = ∫ u in Ioi (1 : ℝ), P.ε * ((u : ℂ) ^ ((P.k : ℂ) - s - 1) * (P.g u - P.g₀)) := by
          rw [Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi zero_le_one)]
      _ = P.ε * ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ ((P.k : ℂ) - s - 1) * (P.g x - P.g₀) :=
          integral_const_mul _ _
  rw [hsplit, hA, hB]
  exact add_comm _ _
end GlobalTheory.CompanionTheory.EisRk1Cont
