-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreA.PosH.mem_perp
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:26:32.835964+00:00
-- url     : https://prove2.me/submissions/d9e912a4-445e-44e6-9470-fe5d7d1ff7ee

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ZeroRight


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreA
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {φ : V → V → ℂ}
open PositivityTheory.Rg.Sw.LC.CoreA.PosH
variable (h : PosH φ)
include h
theorem _root_.solution (W : Submodule ℂ V) (v : V) : v ∈ h.perp W ↔ ∀ w ∈ W, φ w v = 0 := by
  first
    | (intros; simp [PosH, perp])
    | (intros; unfold PosH perp; simp)
    | (intros; simp [PosH, perp]; done)
    | (intros; ext; simp [PosH, perp])
    | (intros; simp only [PosH, perp]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [PosH, perp])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [PosH, perp])
    | (intros; unfold PosH perp; split_ifs <;> simp_all)
    | (intros; unfold PosH perp; positivity)
    | (intros; unfold PosH perp; ring)
    | (intros; unfold PosH perp; exact?)
    | (intros; aesop (add norm simp [PosH, perp]))
    | (intros; simp [PosH, perp] <;> aesop)
    | (intros; exact PosH.symm ..)
    | (intros; exact PosH.comm ..)
    | (intros; exact perp.symm ..)
    | (intros; exact perp.comm ..)
  trace "HIT_169_0"

end 
