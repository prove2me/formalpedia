-- Prove2me | solution 1 for PI.VolSemiDirect.W.semiStep_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:16:58.20528+00:00
-- url     : https://prove2.me/submissions/0c13be6c-8113-490b-9875-05772e7b4623

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_SemiDefs
import Theorems.Thm_PI_VolSemiDirect_W_heisenberg_le_stabilizer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
namespace PI.VolSemiDirect.W
theorem _root_.solution (hL : LcscHA) (hN : NormStep) (hP : ProjStep) : SemiStep := by
  intro F E _ _ _ _ _ σ hCM M J hJ r P T hr hS
  obtain ⟨_, _, _, _⟩ := hL F E σ hCM M J hJ
  obtain ⟨π, hπc, hπH, hπN, hπS, hπR⟩ := hP F E σ hCM M J hJ r P T hr hS
  have hHS := heisenberg_le_stabilizer (AF F) σ J P
  have hNS : FrameUnipotentSubgroup (AF F) σ J P ≤ S0 (AF F) σ J P := inf_le_right
  have hπh : ∀ h : Hsub (AF F) σ J P, π ⟨h, hHS h.2⟩ = h := fun h => Subtype.ext (hπH _ h.2)
  have hπn : ∀ n : FrameUnipotentSubgroup (AF F) σ J P, π ⟨n, hNS n.2⟩ = 1 := fun n => hπN _ n.2
  have hπnh : ∀ (n : FrameUnipotentSubgroup (AF F) σ J P) (h : Hsub (AF F) σ J P),
      π ⟨(n : HA (AF F) σ J) * h, (S0 (AF F) σ J P).mul_mem (hNS n.2) (hHS h.2)⟩ = h := by
    intro n h
    have : (⟨(n : HA (AF F) σ J) * h, (S0 (AF F) σ J P).mul_mem (hNS n.2) (hHS h.2)⟩ :
        S0 (AF F) σ J P) = ⟨n, hNS n.2⟩ * ⟨h, hHS h.2⟩ := rfl
    rw [this, map_mul, hπn, hπh, one_mul]
  refine ⟨⟨fun h hh n hn => hN F E σ hCM M J hJ r P T hr hS h hh n hn, ?_⟩, ?_⟩
  · refine ⟨{
      toFun := fun p => ⟨(p.1 : HA (AF F) σ J) * p.2,
        (S0 (AF F) σ J P).mul_mem (hNS p.1.2) (hHS p.2.2)⟩
      invFun := fun s => (⟨(s : HA (AF F) σ J) * ((π s : Hsub (AF F) σ J P) : HA (AF F) σ J)⁻¹,
        hπS s⟩, π s)
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }, fun p => rfl⟩
    · rintro ⟨n, h⟩
      simp only [hπnh]
      refine Prod.ext (Subtype.ext ?_) rfl
      show (n : HA (AF F) σ J) * h * (h : HA (AF F) σ J)⁻¹ = n
      group
    · intro s
      apply Subtype.ext
      show (s : HA (AF F) σ J) * ((π s : Hsub (AF F) σ J P) : HA (AF F) σ J)⁻¹ *
        ((π s : Hsub (AF F) σ J P) : HA (AF F) σ J) = s
      group
    · exact ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)).subtype_mk _
    · exact ((continuous_subtype_val.mul
        (continuous_subtype_val.comp hπc).inv).subtype_mk _).prodMk hπc
  · intro n hn h hh hmem
    have hs : (n : HA (AF F) σ J) * h ∈ S0 (AF F) σ J P :=
      (S0 (AF F) σ J P).mul_mem (hNS hn) (hHS hh)
    have := hπR ⟨n * h, hs⟩ hmem
    have e : π ⟨n * h, hs⟩ = ⟨h, hh⟩ := hπnh ⟨n, hn⟩ ⟨h, hh⟩
    rw [e] at this
    exact this
end PI.VolSemiDirect.W
