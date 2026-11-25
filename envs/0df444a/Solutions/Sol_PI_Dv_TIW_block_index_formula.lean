-- Prove2me | solution 1 for PI.Dv.TIW.block_index_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:44:35.087953+00:00
-- url     : https://prove2.me/submissions/97c5b8b7-94ce-446c-b424-5374d7b030b4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_BlockHyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_BlockMain
import Theorems.Thm_PI_Dv_TIW_BlockHyp_side
import Theorems.Thm_PI_Dv_TIW_BlockHyp_finrank
import Theorems.Thm_PI_Dv_TIW_BlockHyp_phi_inj
import Theorems.Thm_PI_Dv_TIW_cut_span
import Theorems.Thm_PI_Dv_TIW_fg_cut
import Theorems.Thm_PI_Dv_TIW_idx_anti
import Theorems.Thm_PI_Dv_TIW_idx_chain
import Theorems.Thm_PI_Dv_TIW_idx_map_inj
import Theorems.Thm_PI_Dv_TIW_idx_pi
import Theorems.Thm_PI_Dv_TIW_rk_cut
import Theorems.Thm_PI_Dv_TIW_span_latPow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
namespace PI.Dv.TIW
theorem _root_.solution (hI : IdxCalc) : BlockIdx := by
  intro K _ _ V _ _ _ _ n X Y Φ Ψ Γ hdet h1 h2 h3 h4 M N hMfg hNfg hMsp hNsp hΦM hΨM hΦN hΨN
  haveI : FiniteDimensional K V := by
    obtain ⟨s, hs⟩ := hMfg
    refine Module.finite_def.mpr ⟨s, ?_⟩
    rw [← hMsp, ← hs, Submodule.span_span_of_tower]
  set Γk : Matrix (Fin n) (Fin n) K := Γ.map (algebraMap (𝓞 K) K) with hΓk
  have hdetk : Γk.det = algebraMap (𝓞 K) K Γ.det := (RingHom.map_det _ _).symm
  have H : BlockHyp X Y Φ Ψ Γk :=
    ⟨by rw [hdetk]; exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hdet,
      fun i j x hx => by rw [h1 i j x hx]; rfl, h2, h3, h4⟩
  have hrX : ∀ L : Submodule (𝓞 K) V, Submodule.span K (L : Set V) = ⊤ →
      Formalism.HN.rkK (L ⊓ X.restrictScalars (𝓞 K)) = Module.finrank K X := fun L hL => rk_cut L hL X
  refine ⟨by rw [rk_cut M hMsp Y, rk_cut M hMsp X, H.finrank], fun w => ?_⟩
  obtain ⟨hAle, hAsp, hA0, hA1⟩ := H.side hI w M hMfg hMsp hΦM hΨM
  obtain ⟨hBle, hBsp, hB0, hB1⟩ := H.side hI w N hNfg hNsp hΦN hΨN
  rw [hdetk] at hA1 hB1
  rw [hrX N hNsp, ← hrX M hMsp] at hB1
  set MX := M ⊓ X.restrictScalars (𝓞 K)
  set NX := N ⊓ X.restrictScalars (𝓞 K)
  set MY := M ⊓ Y.restrictScalars (𝓞 K)
  set NY := N ⊓ Y.restrictScalars (𝓞 K)
  set A := (latPow (Fin n) MX).map ((Φt Φ).restrictScalars (𝓞 K))
  set B := (latPow (Fin n) NX).map ((Φt Φ).restrictScalars (𝓞 K))
  have fgMX : MX.FG := fg_cut M hMfg X
  have fgNX : NX.FG := fg_cut N hNfg X
  have fgMY : MY.FG := fg_cut M hMfg Y
  have fgNY : NY.FG := fg_cut N hNfg Y
  have fgA : A.FG := (Submodule.fg_pi fun _ => fgMX).map _
  have fgB : B.FG := (Submodule.fg_pi fun _ => fgNX).map _
  have sMY : Submodule.span K (MY : Set V) = Y := cut_span M hMsp Y
  have sNY : Submodule.span K (NY : Set V) = Y := cut_span N hNsp Y
  have c1 := idx_chain hI w MY A NY fgMY fgA fgNY (sMY.trans hAsp.symm) (sNY.trans hAsp.symm)
  have c2 := idx_chain hI w A B NY fgA fgB fgNY (hAsp.trans hBsp.symm) (sNY.trans hBsp.symm)
  have hLX : ∀ L : Submodule (𝓞 K) V, ∀ x ∈ latPow (Fin n) (L ⊓ X.restrictScalars (𝓞 K)),
      x ∈ Submodule.pi Set.univ fun _ : Fin n => X := fun L x hx i _ =>
    (Submodule.mem_inf.mp (hx i (Set.mem_univ i))).2
  have c3 := idx_map_inj hI w (Φt Φ) (latPow (Fin n) MX) (latPow (Fin n) NX)
    (Submodule.fg_pi fun _ => fgMX) (Submodule.fg_pi fun _ => fgNX)
    (by rw [span_latPow, span_latPow, cut_span M hMsp X, cut_span N hNsp X])
    (fun x hx h0 => H.phi_inj x (hLX M x hx) h0) (fun x hx h0 => H.phi_inj x (hLX N x hx) h0)
  have c4 := idx_pi hI w (fun _ : Fin n => MX) (fun _ : Fin n => NX) (fun _ => fgMX) (fun _ => fgNX)
    (fun _ => by rw [cut_span M hMsp X, cut_span N hNsp X])
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at c4
  have c5 : idxAt w B NY = -idxAt w NY B := idx_anti w B NY
  have key : idxAt w MY NY = idxAt w MY A + (n : ℤ) * idxAt w MX NX - idxAt w NY B := by
    rw [c1, c2, c5, ← c3]
    have : idxAt w (latPow (Fin n) MX) (latPow (Fin n) NX) = (n : ℤ) * idxAt w MX NX := c4
    rw [this]; ring
  have hD1 : -((Formalism.HN.rkK MX : ℤ) * vAdd w (algebraMap (𝓞 K) K Γ.det)) ≤
      idxAt w MY NY - (n : ℤ) * idxAt w MX NX := by rw [key]; linarith
  have hD2 : idxAt w MY NY - (n : ℤ) * idxAt w MX NX ≤
      (Formalism.HN.rkK MX : ℤ) * vAdd w (algebraMap (𝓞 K) K Γ.det) := by rw [key]; linarith
  have hfin : |((idxAt w MY NY - (n : ℤ) * idxAt w MX NX : ℤ) : ℝ)| ≤
      (((Formalism.HN.rkK MX : ℤ) * vAdd w (algebraMap (𝓞 K) K Γ.det) : ℤ) : ℝ) := by
    rw [abs_le]; constructor
    · exact_mod_cast hD1
    · exact_mod_cast hD2
  push_cast at hfin
  exact hfin
end PI.Dv.TIW
