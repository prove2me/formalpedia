-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.JLatOf.linInd_ej
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:47:47.743026+00:00
-- url     : https://prove2.me/submissions/5856815b-1c4f-406a-9899-83b9c40c8f5c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_LatticeReduction_LatticeHeightZeroEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.JLatOf
open PositivityTheory.Rg.Rs
variable {k : Type} [Field k] {N : ℕ}
namespace PositivityTheory.Rg.Rs.JLatOf
theorem _root_.solution (N j m : ℕ) (h : m + j = N) : LinearIndependent k (ej (k := k) N j m h) := by
  have hf : Function.Injective (fun i : Fin m => (⟨j + i, by omega⟩ : Fin N)) := by
    intro a b hab
    simp only [Fin.mk.injEq] at hab
    exact Fin.ext (by omega)
  have h2 := (Pi.basisFun k (Fin N)).linearIndependent.comp _ hf
  convert h2 using 1
  funext i
  simp [ej]
end PositivityTheory.Rg.Rs.JLatOf
