-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.JLatOf.exists_gmap_Mj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:20:55.857279+00:00
-- url     : https://prove2.me/submissions/98ecf6bc-10f6-4fde-841c-e3f895e099d1

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_LatticeReduction_LatticeHeightZeroEq
import Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_Mj_eq_span
import Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_gmap_span
import Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_span_basis_coe
import Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_exists_frame

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
theorem _root_.solution [Finite k] (M : Submodule k (Fin N → k)) (j : ℕ) (h : finrank k M + j = N) :
    ∃ g : GL (Fin N) k, gmap g (Mj k N j) = M := by
  let b := Module.finBasis k M
  have hli : LinearIndependent k (fun i => (b i : Fin N → k)) :=
    b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  obtain ⟨g, hg⟩ := exists_frame N j (finrank k M) h (fun i => (b i : Fin N → k)) hli
  refine ⟨g, ?_⟩
  rw [Mj_eq_span N j _ h, gmap_span]
  simp only [hg]
  exact span_basis_coe b
end PositivityTheory.Rg.Rs.JLatOf
