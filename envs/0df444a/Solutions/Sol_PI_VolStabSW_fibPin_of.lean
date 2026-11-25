-- Prove2me | solution 1 for PI.VolStabSW.fibPin_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:45:13.56219+00:00
-- url     : https://prove2.me/submissions/dd393bbe-cdc7-4af5-85d3-e9f06f887836

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SWeqOm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocExOf
import Theorems.Thm_PI_VolStabSW_rapidDecay_of_compact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
namespace PI.VolStabSW
theorem _root_.solution (h1 : DensFibInf) (h2 : DensFibV) (hL : LatSB) : FibPin := by
  classical
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hE.2.2.1]; norm_num)
  let b := Module.finBasis F E
  let Lv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ :=
    fun v => (latV b v).indicator 1
  refine ⟨fun μinf hμinf νinf hνinf fib1 fib2 hf1 hf2 Φinf hci hsi => ?_, ?_⟩
  · have hp : IsPureFin b (fun X => ∏ᶠ v, Lv v (projV v X)) Lv :=
      ⟨fun v => hL F E _ M a b v, Filter.Eventually.of_forall fun v => rfl, fun X => rfl⟩
    have hS := hc a ha2 (gramE σ J X0) hT hdet _ b
      (fun X => Φinf (projInf X) * (fun X => ∏ᶠ v, Lv v (projV v X)) (projFin X)) Φinf _ Lv
      hci (rapidDecay_of_compact b Φinf hci hsi) hp (fun X => rfl)
    obtain ⟨μ, hμ⟩ := hS.1
    obtain ⟨𝓕, h𝓕⟩ := (hS.2 μ hμ).1
    have h3 := (((((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ).2 μinf hμinf).2 νinf hνinf)
    obtain ⟨μv, hμv⟩ := h3.1
    obtain ⟨νv, hνv⟩ := (h3.2 μv hμv).1
    obtain ⟨ginf, gv, hdi, _, _, _⟩ := (h3.2 μv hμv).2 νv hνv
    rw [← h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf fib1 hf1
      Φinf ginf hci hsi hdi, h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf
      hνinf fib2 hf2 Φinf ginf hci hsi hdi]
  · intro v0 μ0 hμ0 ν0 hν0 fib1 fib2 hf1 hf2 Φ0 hΦ0
    let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ :=
      Function.update Lv v0 Φ0
    have hp : IsPureFin b (fun X => ∏ᶠ v, Φv v (projV v X)) Φv := by
      refine ⟨fun v => ?_, ?_, fun X => rfl⟩
      · by_cases hv : v = v0
        · subst hv; simp only [Φv, Function.update_self]; exact hΦ0
        · simp only [Φv, Function.update_of_ne hv]; exact hL F E _ M a b v
      · filter_upwards [(Set.finite_singleton v0).compl_mem_cofinite] with v hv
        simp only [Φv, Function.update_of_ne (show v ≠ v0 from hv)]
        rfl
    have hS := hc a ha2 (gramE σ J X0) hT hdet _ b (fun _ => (0 : ℂ)) (fun _ => (0 : ℂ))
      (fun X => ∏ᶠ v, Φv v (projV v X)) Φv continuous_const
      (rapidDecay_of_compact b _ continuous_const HasCompactSupport.zero) hp (fun X => by simp)
    obtain ⟨μ, hμ⟩ := hS.1
    obtain ⟨𝓕, h𝓕⟩ := (hS.2 μ hμ).1
    have h3 := ((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ
    obtain ⟨μinf, hμinf⟩ := h3.1
    obtain ⟨νinf, hνinf⟩ := (h3.2 μinf hμinf).1
    have h4 := ((h3.2 μinf hμinf).2 νinf hνinf)
    obtain ⟨μv', hμv'⟩ := h4.1
    let μv := Function.update μv' v0 μ0
    have hμv : ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) a (μv v) := by
      intro v
      by_cases hv : v = v0
      · subst hv; simp only [μv, Function.update_self]; exact hμ0
      · simp only [μv, Function.update_of_ne hv]; exact hμv' v
    obtain ⟨νv', hνv'⟩ := (h4.2 μv hμv).1
    let νv := Function.update νv' v0 ν0
    have hνv : ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (νv v) := by
      intro v
      by_cases hv : v = v0
      · subst hv; simp only [νv, Function.update_self]; exact hν0
      · simp only [νv, Function.update_of_ne hv]; exact hνv' v
    obtain ⟨ginf, gv, _, hdv, _, _⟩ := (h4.2 μv hμv).2 νv hνv
    have hd0 := hdv v0
    simp only [μv, νv, Φv, Function.update_self] at hd0
    rw [← h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v0 μ0 hμ0 ν0 hν0 fib1 hf1 Φ0 (gv v0)
      hΦ0 hd0, h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v0 μ0 hμ0 ν0 hν0 fib2 hf2 Φ0
      (gv v0) hΦ0 hd0]
end PI.VolStabSW
