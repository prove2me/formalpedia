-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.JLatOf.mem_par_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:21:10.392687+00:00
-- url     : https://prove2.me/submissions/13b59a9c-ae3d-49f6-9ded-663b2e82b3e8

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_LatticeReduction_LatticeHeightZeroEq
import Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_finrank_gmap
import Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_gmap_le_Mj_iff

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
theorem _root_.solution [Finite k] (g : GL (Fin N) k) (j : ℕ) :
    g ∈ Formalism.UG.P.tjcosets_par N j ↔ gmap g (Mj k N j) = Mj k N j := by
  have hmem : g ∈ Formalism.UG.P.tjcosets_par N j ↔
      ∀ a b : Fin N, (a : ℕ) < j → j ≤ (b : ℕ) → (g : Matrix (Fin N) (Fin N) k) a b = 0 := Iff.rfl
  rw [hmem, ← gmap_le_Mj_iff]
  constructor
  · intro hle
    exact Submodule.eq_of_le_of_finrank_eq hle (finrank_gmap g _)
  · intro heq
    exact heq.le
end PositivityTheory.Rg.Rs.JLatOf
