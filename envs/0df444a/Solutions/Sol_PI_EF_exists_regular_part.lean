-- Prove2me | solution 1 for PI.EF.exists_regular_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:41:04.514379+00:00
-- url     : https://prove2.me/submissions/d73a941a-1b4a-4b6e-aaca-63d76eeae920

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructA
import Theorems.Thm_PI_EF_logDeriv_local

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Filter Topology Set
namespace PI.EF
theorem _root_.solution {f : ℂ → ℂ} {K : Set ℂ} (hf : AnalyticOnNhd ℂ f K) (Z : Finset ℂ)
    (hZ0 : ∀ ρ ∈ Z, f ρ = 0) (hK : ∀ s ∈ K, f s = 0 → s ∈ Z)
    (hfin : ∀ ρ ∈ K, analyticOrderAt f ρ ≠ ⊤) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H K ∧ ∀ s ∈ K, f s ≠ 0 →
      logDeriv f s = H s + ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ) := by
  classical
  have hloc : ∀ ρ, ρ ∈ K → ∃ k : ℂ → ℂ, AnalyticAt ℂ k ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, f s ≠ 0 ∧
      logDeriv f s = (analyticOrderNatAt f ρ : ℂ) / (s - ρ) + k s :=
    fun ρ hρ => logDeriv_local (hf ρ hρ) (hfin ρ hρ)
  choose! k hk hkev using hloc
  have hsumA : ∀ (W : Finset ℂ) (s0 : ℂ), s0 ∉ W →
      AnalyticAt ℂ (fun s => ∑ ρ ∈ W, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)) s0 := by
    intro W s0 hW
    have h := Finset.analyticAt_sum (𝕜 := ℂ) (c := s0) W
      (f := fun ρ (s : ℂ) => (analyticOrderNatAt f ρ : ℂ) / (s - ρ))
      (fun ρ hρ => analyticAt_const.div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.2 fun h => hW (h ▸ hρ)))
    convert h using 1
    ext s
    simp [Finset.sum_apply]
  let H : ℂ → ℂ := fun s => if s ∈ Z ∧ s ∈ K then
      k s s - ∑ ρ ∈ Z.erase s, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)
    else logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)
  refine ⟨H, ?_, ?_⟩
  · intro s0 hs0
    by_cases hz : s0 ∈ Z
    · have hRa : AnalyticAt ℂ
          (fun s => k s0 s - ∑ ρ ∈ Z.erase s0, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)) s0 :=
        (hk s0 hs0).sub (hsumA _ s0 (by simp))
      have h1 := hkev s0 hs0
      rw [eventually_nhdsWithin_iff] at h1
      have h2 : ∀ᶠ s in 𝓝 s0, s ∉ Z.erase s0 :=
        (Z.erase s0).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
      refine hRa.congr ?_
      filter_upwards [h1, h2] with s hs1 hs2
      by_cases hss : s = s0
      · subst hss
        simp only [H, if_pos (And.intro hz hs0)]
      · have hsZ : s ∉ Z := fun h => hs2 (Finset.mem_erase.2 ⟨hss, h⟩)
        obtain ⟨_, hl⟩ := hs1 hss
        simp only [H, hsZ, false_and, if_false]
        rw [hl, ← Finset.add_sum_erase Z _ hz]
        ring
    · have hf0 : f s0 ≠ 0 := fun h => hz (hK s0 hs0 h)
      have h2 : ∀ᶠ s in 𝓝 s0, s ∉ Z :=
        Z.finite_toSet.isClosed.isOpen_compl.mem_nhds (by simpa using hz)
      have hA : AnalyticAt ℂ (fun s => logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)) s0 := by
        refine AnalyticAt.sub ?_ (hsumA Z s0 hz)
        have e : logDeriv f = fun s => deriv f s / f s := funext fun s => logDeriv_apply f s
        rw [e]
        exact (hf s0 hs0).deriv.div (hf s0 hs0) hf0
      refine hA.congr ?_
      filter_upwards [h2] with s hs
      simp only [H, hs, false_and, if_false]
  · intro s _ hfs
    have hsZ : s ∉ Z := fun h => hfs (hZ0 s h)
    simp only [H, hsZ, false_and, if_false]
    ring
end PI.EF
