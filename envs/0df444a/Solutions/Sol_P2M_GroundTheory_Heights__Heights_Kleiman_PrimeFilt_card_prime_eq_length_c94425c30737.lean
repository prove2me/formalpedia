-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFilt_card_prime_eq_length_c94425c30737
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:03.508055+00:00
-- url     : https://prove2.me/submissions/43a54f80-59ee-4640-83b8-357ba520cfec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationExists
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_length_sup_span_singleton_4adf65ed3ac1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.PrimeFilt
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  {𝓜 : GradedPMod S N M}
namespace GroundTheory.Heights₂.Heights.Kleiman.PrimeFilt
theorem _root_.solution (F : PrimeFilt 𝓜) (pp : Ideal (Poly S N)) [pp.IsPrime]
    (hpp : pp ∈ (Module.annihilator (Poly S N) M).minimalPrimes) :
    (((Finset.univ.filter fun k => F.prime k = pp).card : ℕ) : ℕ∞) =
      Module.length (Localization.AtPrime pp) (LocalizedModule pp.primeCompl M) := by
  classical
  let R := Localization.AtPrime pp
  let f := LocalizedModule.mkLinearMap pp.primeCompl M
  let Loc : Submodule (Poly S N) M → Submodule R (LocalizedModule pp.primeCompl M) :=
    fun A => A.localized' R pp.primeCompl f
  have hstep : ∀ k : Fin F.n, Module.length R (Loc (F.step k.succ)) =
      Module.length R (Loc (F.step k.castSucc)) + if F.prime k = pp then 1 else 0 := by
    intro k
    have hsup : Loc (F.step k.succ) =
        Loc (F.step k.castSucc) ⊔ Submodule.span R {f (F.gen k)} := by
      simp only [Loc]
      rw [F.step_succ k, (Submodule.localized'gi R pp.primeCompl f).gc.l_sup,
        Submodule.localized'_span, Set.image_singleton]
    rw [hsup, length_sup_span_singleton]
    congr 1
    have hmemloc : ∀ r : Poly S N, r • F.gen k ∈ F.step k.castSucc →
        algebraMap (Poly S N) R r ∈ colonIdeal (Loc (F.step k.castSucc)) (f (F.gen k)) := by
      intro r hr
      rw [mem_colonIdeal, algebraMap_smul, ← LinearMap.map_smul]
      exact ⟨r • F.gen k, hr, 1, IsLocalizedModule.mk'_one _ _ _⟩
    split_ifs with h
    · have hI : colonIdeal (Loc (F.step k.castSucc)) (f (F.gen k)) = IsLocalRing.maximalIdeal R := by
        apply le_antisymm
        · apply IsLocalRing.le_maximalIdeal
          intro htop
          have h1 : (1 : R) ∈ colonIdeal (Loc (F.step k.castSucc)) (f (F.gen k)) :=
            htop ▸ Submodule.mem_top
          rw [mem_colonIdeal, one_smul] at h1
          obtain ⟨m, hm, s, hms⟩ := h1
          rw [IsLocalizedModule.mk'_eq_iff, ← LinearMap.map_smul_of_tower] at hms
          obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := pp.primeCompl) hms
          have hcs : ((c : Poly S N) * s) ∈ F.prime k := by
            rw [F.mem_prime, mul_smul]
            change (c : Poly S N) • ((s : Poly S N) • F.gen k) ∈ _
            rw [← Submonoid.smul_def s, ← Submonoid.smul_def c, ← hc, Submonoid.smul_def]
            exact Submodule.smul_mem _ _ hm
          rw [h] at hcs
          exact (pp.primeCompl.mul_mem c.2 s.2) hcs
        · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
          intro r hr
          exact hmemloc r ((F.mem_prime k r).mp (h ▸ hr))
      rw [hI]
      have : IsSimpleModule R (R ⧸ IsLocalRing.maximalIdeal R) :=
        isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal R))
      exact Module.length_eq_one _ _
    · have hnle : ¬ F.prime k ≤ pp := fun hle =>
        h (le_antisymm hle (hpp.2 ⟨F.isPrime k, F.ann_le k⟩ hle))
      obtain ⟨t, ht, htp⟩ := Set.not_subset.mp hnle
      have hI : colonIdeal (Loc (F.step k.castSucc)) (f (F.gen k)) = ⊤ :=
        Ideal.eq_top_of_isUnit_mem _ (hmemloc t ((F.mem_prime k t).mp ht))
          (IsLocalization.map_units R (⟨t, htp⟩ : pp.primeCompl))
      rw [hI]
      exact Module.length_eq_zero_iff.mpr (Submodule.Quotient.subsingleton_iff.mpr rfl)
  have key : ∀ j (hj : j ≤ F.n), Module.length R (Loc (F.step ⟨j, by omega⟩)) =
      ∑ i ∈ Finset.range j, (if h : i < F.n then (if F.prime ⟨i, h⟩ = pp then 1 else 0) else 0 : ℕ∞) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [Finset.sum_range_zero, show (⟨0, by omega⟩ : Fin (F.n + 1)) = 0 from rfl, F.step_zero]
      change Module.length R (Submodule.localized' R pp.primeCompl f ⊥) = 0
      rw [Submodule.localized'_bot]
      exact Module.length_bot
    | succ j ih =>
      intro hj
      rw [Finset.sum_range_succ, ← ih (by omega), dif_pos (by omega)]
      exact hstep ⟨j, by omega⟩
  calc (((Finset.univ.filter fun k => F.prime k = pp).card : ℕ) : ℕ∞)
      = ∑ k : Fin F.n, (if F.prime k = pp then 1 else 0 : ℕ∞) := by
        rw [Finset.card_filter]; push_cast; rfl
    _ = ∑ i ∈ Finset.range F.n,
          (if h : i < F.n then (if F.prime ⟨i, h⟩ = pp then 1 else 0) else 0 : ℕ∞) := by
        rw [← Fin.sum_univ_eq_sum_range]
        exact Finset.sum_congr rfl fun k _ => by rw [dif_pos k.isLt]
    _ = Module.length R (Loc (F.step ⟨F.n, by omega⟩)) := (key _ le_rfl).symm
    _ = Module.length R (LocalizedModule pp.primeCompl M) := by
        rw [show (⟨F.n, by omega⟩ : Fin (F.n + 1)) = Fin.last F.n from rfl, F.step_last]
        change Module.length R (Submodule.localized' R pp.primeCompl f ⊤) = _
        rw [Submodule.localized'_top]
        exact Module.length_top
end GroundTheory.Heights₂.Heights.Kleiman.PrimeFilt
